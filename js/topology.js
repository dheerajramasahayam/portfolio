/*
 * topology.js — self-healing Clos topology canvas simulation.
 *
 * 4 spines x 8 leaves, full bipartite mesh (32 edges). Packets ride
 * leaf -> spine -> leaf paths. Every ~6s a random up edge fails, a
 * 0.8s red pulse plays, affected packets re-path to a spine whose
 * both hops are still up, the edge stays down 3s, then a 0.8s green
 * heal sweep brings it back. Only one edge is ever down at a time,
 * which — on a full bipartite mesh — guarantees every leaf always
 * keeps at least one other up spine path (never stranded).
 *
 * Self-contained, strict-mode IIFE. No globals, no external libs.
 */
(function () {
  'use strict';

  var canvas = document.getElementById('topology');
  if (!canvas || !canvas.getContext) return;
  var ctx = canvas.getContext('2d');
  if (!ctx) return;

  // ---------------------------------------------------------------------
  // Theme colors (read from CSS custom properties, hex fallback)
  // ---------------------------------------------------------------------
  var rootStyle = getComputedStyle(document.documentElement);
  function themeColor(name, fallback) {
    var v = rootStyle.getPropertyValue(name);
    v = v ? v.trim() : '';
    return v || fallback;
  }
  var COLOR_ACCENT = themeColor('--accent', '#22d3ee');
  var COLOR_HEAL = themeColor('--heal', '#34d399');
  var COLOR_FAIL = themeColor('--fail', '#f87171');
  var COLOR_UP = '#ffffff';

  var EMPTY_DASH = [];
  var DASH_PATTERN = [4, 4];
  var TAU = Math.PI * 2;

  // ---------------------------------------------------------------------
  // Graph: 4 spines (top row) x 8 leaves (bottom row), 32 edges
  // ---------------------------------------------------------------------
  var SPINE_N = 4;
  var LEAF_N = 8;
  var EDGE_N = SPINE_N * LEAF_N;

  var spineX = new Float32Array(SPINE_N);
  var leafX = new Float32Array(LEAF_N);
  var spineY = 0;
  var leafY = 0;

  // Edge state, flattened index = spineIdx * LEAF_N + leafIdx
  var EDGE_UP = 0, EDGE_FAILING = 1, EDGE_DOWN = 2, EDGE_HEALING = 3;
  var edgeState = new Uint8Array(EDGE_N); // all start EDGE_UP (0)
  var edgePhaseStart = new Float64Array(EDGE_N);

  function edgeIndex(spineIdx, leafIdx) { return spineIdx * LEAF_N + leafIdx; }

  function leafUpCount(leafIdx) {
    var n = 0;
    for (var s = 0; s < SPINE_N; s++) {
      if (edgeState[edgeIndex(s, leafIdx)] === EDGE_UP) n++;
    }
    return n;
  }

  // Pick a spine such that both (leafA,spine) and (leafB,spine) are up.
  // Linear scan over 4 spines starting from a random offset — no
  // allocation, no closures.
  function pickValidSpine(leafA, leafB) {
    var offset = (Math.random() * SPINE_N) | 0;
    for (var k = 0; k < SPINE_N; k++) {
      var s = (offset + k) % SPINE_N;
      if (edgeState[edgeIndex(s, leafA)] === EDGE_UP &&
          edgeState[edgeIndex(s, leafB)] === EDGE_UP) {
        return s;
      }
    }
    return -1; // should not happen: single-edge-down invariant guarantees a hit
  }

  // ---------------------------------------------------------------------
  // Packet pool — fixed size 40, reused slots, zero per-frame allocation
  // ---------------------------------------------------------------------
  var POOL_SIZE = 40;
  var pLeafStart = new Int8Array(POOL_SIZE);
  var pLeafEnd = new Int8Array(POOL_SIZE);
  var pSpine = new Int8Array(POOL_SIZE);
  var pHop = new Uint8Array(POOL_SIZE); // 0 = leaf->spine, 1 = spine->leaf
  var pT = new Float32Array(POOL_SIZE); // progress along current hop, 0..1
  var pSpeed = new Float32Array(POOL_SIZE); // hops per second

  function randomLeafPair(out) {
    var a = (Math.random() * LEAF_N) | 0;
    var b = (Math.random() * LEAF_N) | 0;
    if (b === a) b = (b + 1 + ((Math.random() * (LEAF_N - 1)) | 0)) % LEAF_N;
    out[0] = a;
    out[1] = b;
  }
  var pairScratch = [0, 0]; // reused scratch, mutated in place — not per-frame

  function spawnPacket(i) {
    randomLeafPair(pairScratch);
    var a = pairScratch[0], b = pairScratch[1];
    var s = pickValidSpine(a, b);
    if (s === -1) s = 0;
    pLeafStart[i] = a;
    pLeafEnd[i] = b;
    pSpine[i] = s;
    pHop[i] = 0;
    pT[i] = Math.random() * 0.3; // stagger initial phase so packets don't clump
    pSpeed[i] = 0.6 + Math.random() * 0.7;
  }

  function initPackets() {
    for (var i = 0; i < POOL_SIZE; i++) spawnPacket(i);
  }

  // Re-path any packet currently riding the given (now-failing) edge.
  function repathPacketsOnEdge(spineIdx, leafIdx) {
    for (var i = 0; i < POOL_SIZE; i++) {
      var usesEdge =
        (pHop[i] === 0 && pSpine[i] === spineIdx && pLeafStart[i] === leafIdx) ||
        (pHop[i] === 1 && pSpine[i] === spineIdx && pLeafEnd[i] === leafIdx);
      if (!usesEdge) continue;
      var s = pickValidSpine(pLeafStart[i], pLeafEnd[i]);
      if (s === -1) continue; // guarded to not happen; leave packet as-is
      pSpine[i] = s;
      pHop[i] = 0;
      pT[i] = 0;
    }
  }

  // ---------------------------------------------------------------------
  // Failure cycle — driven off elapsed time inside the rAF loop, no
  // setInterval for the render loop.
  // ---------------------------------------------------------------------
  var FAIL_INTERVAL = 6000; // ms between failure triggers
  var FAIL_PULSE = 800;     // ms red pulse before going down
  var FAIL_DOWN = 3000;     // ms fully down
  var HEAL_SWEEP = 800;     // ms green heal sweep before back up

  var activeEdge = -1; // flattened index of edge currently in the cycle, or -1
  var lastFailAt = 0;  // timestamp of last failure trigger

  function tryStartFailure(now) {
    if (activeEdge !== -1) return;
    if (now - lastFailAt < FAIL_INTERVAL) return;

    // Candidates: up edges whose leaf would still keep >=1 other up
    // spine path after this one fails (guards against stranding a leaf).
    var candidates = [];
    for (var e = 0; e < EDGE_N; e++) {
      if (edgeState[e] !== EDGE_UP) continue;
      var leafIdx = e % LEAF_N;
      if (leafUpCount(leafIdx) > 1) candidates.push(e);
    }
    if (candidates.length === 0) return;

    lastFailAt = now;
    var pick = candidates[(Math.random() * candidates.length) | 0];
    edgeState[pick] = EDGE_FAILING;
    edgePhaseStart[pick] = now;
    activeEdge = pick;
  }

  // repathPacketsOnEdge only needs to run once, at the moment an edge
  // enters EDGE_FAILING — this flag stops it re-running every frame
  // during the 0.8s pulse.
  var repathDone = false;

  function updateFailureCycle(now) {
    tryStartFailure(now);
    if (activeEdge === -1) return;

    var e = activeEdge;
    var phase = now - edgePhaseStart[e];

    if (edgeState[e] === EDGE_FAILING) {
      if (!repathDone) {
        repathPacketsOnEdge((e / LEAF_N) | 0, e % LEAF_N);
        repathDone = true;
      }
      if (phase >= FAIL_PULSE) {
        edgeState[e] = EDGE_DOWN;
        edgePhaseStart[e] = now;
      }
    } else if (edgeState[e] === EDGE_DOWN) {
      if (phase >= FAIL_DOWN) {
        edgeState[e] = EDGE_HEALING;
        edgePhaseStart[e] = now;
      }
    } else if (edgeState[e] === EDGE_HEALING) {
      if (phase >= HEAL_SWEEP) {
        edgeState[e] = EDGE_UP;
        activeEdge = -1;
        repathDone = false;
      }
    }
  }

  // ---------------------------------------------------------------------
  // Layout — devicePixelRatio-aware sizing, positions recomputed on resize
  // ---------------------------------------------------------------------
  function layout() {
    var w = canvas.clientWidth || canvas.parentElement.clientWidth || 1;
    var h = canvas.clientHeight || canvas.parentElement.clientHeight || 1;
    var dpr = window.devicePixelRatio || 1;
    canvas.width = Math.round(w * dpr);
    canvas.height = Math.round(h * dpr);
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);

    var spineMarginFrac = 0.16;
    var leafMarginFrac = 0.06;
    spineY = h * 0.24;
    leafY = h * 0.78;
    var i;
    for (i = 0; i < SPINE_N; i++) {
      var sf = SPINE_N === 1 ? 0.5 : i / (SPINE_N - 1);
      spineX[i] = w * spineMarginFrac + (w * (1 - 2 * spineMarginFrac)) * sf;
    }
    for (i = 0; i < LEAF_N; i++) {
      var lf = LEAF_N === 1 ? 0.5 : i / (LEAF_N - 1);
      leafX[i] = w * leafMarginFrac + (w * (1 - 2 * leafMarginFrac)) * lf;
    }
    if (reducedMotion) drawStatic();
  }

  // ---------------------------------------------------------------------
  // Update
  // ---------------------------------------------------------------------
  function lerp(a, b, t) { return a + (b - a) * t; }

  function updatePackets(dt) {
    for (var i = 0; i < POOL_SIZE; i++) {
      pT[i] += dt * pSpeed[i];
      if (pT[i] >= 1) {
        if (pHop[i] === 0) {
          pHop[i] = 1;
          pT[i] = 0;
        } else {
          spawnPacket(i);
        }
      }
    }
  }

  function update(now, dt) {
    updateFailureCycle(now);
    updatePackets(dt);
  }

  // ---------------------------------------------------------------------
  // Draw
  // ---------------------------------------------------------------------
  var NODE_R = 3;

  function drawEdges(now) {
    ctx.lineWidth = 1;
    for (var s = 0; s < SPINE_N; s++) {
      for (var l = 0; l < LEAF_N; l++) {
        var e = edgeIndex(s, l);
        var state = edgeState[e];
        var x1 = spineX[s], y1 = spineY, x2 = leafX[l], y2 = leafY;

        if (state === EDGE_UP) {
          ctx.globalAlpha = 0.12;
          ctx.strokeStyle = COLOR_UP;
          ctx.setLineDash(EMPTY_DASH);
          ctx.beginPath();
          ctx.moveTo(x1, y1);
          ctx.lineTo(x2, y2);
          ctx.stroke();
        } else if (state === EDGE_FAILING) {
          var phase = (now - edgePhaseStart[e]) / FAIL_PULSE;
          var pulse = 0.4 + 0.5 * Math.abs(Math.sin(phase * Math.PI * 3));
          ctx.globalAlpha = pulse;
          ctx.strokeStyle = COLOR_FAIL;
          ctx.setLineDash(DASH_PATTERN);
          ctx.beginPath();
          ctx.moveTo(x1, y1);
          ctx.lineTo(x2, y2);
          ctx.stroke();
        } else if (state === EDGE_DOWN) {
          ctx.globalAlpha = 0.3;
          ctx.strokeStyle = COLOR_FAIL;
          ctx.setLineDash(DASH_PATTERN);
          ctx.beginPath();
          ctx.moveTo(x1, y1);
          ctx.lineTo(x2, y2);
          ctx.stroke();
        } else if (state === EDGE_HEALING) {
          var hp = (now - edgePhaseStart[e]) / HEAL_SWEEP;
          if (hp > 1) hp = 1;
          ctx.globalAlpha = 0.35;
          ctx.strokeStyle = COLOR_HEAL;
          ctx.setLineDash(EMPTY_DASH);
          ctx.beginPath();
          ctx.moveTo(x1, y1);
          ctx.lineTo(x2, y2);
          ctx.stroke();
          // sweep dot travelling spine -> leaf as the link heals
          var hx = lerp(x1, x2, hp);
          var hy = lerp(y1, y2, hp);
          ctx.globalAlpha = 0.9;
          ctx.fillStyle = COLOR_HEAL;
          ctx.beginPath();
          ctx.arc(hx, hy, 2.5, 0, TAU);
          ctx.fill();
        }
      }
    }
    ctx.setLineDash(EMPTY_DASH);
    ctx.globalAlpha = 1;
  }

  function drawNodes() {
    ctx.globalAlpha = 0.9;
    ctx.fillStyle = COLOR_ACCENT;
    var i;
    for (i = 0; i < SPINE_N; i++) {
      ctx.fillRect(spineX[i] - NODE_R, spineY - NODE_R, NODE_R * 2, NODE_R * 2);
    }
    for (i = 0; i < LEAF_N; i++) {
      ctx.beginPath();
      ctx.arc(leafX[i], leafY, NODE_R, 0, TAU);
      ctx.fill();
    }
    ctx.globalAlpha = 1;
  }

  function drawPackets() {
    ctx.shadowColor = COLOR_ACCENT;
    ctx.shadowBlur = 6;
    ctx.fillStyle = COLOR_ACCENT;
    for (var i = 0; i < POOL_SIZE; i++) {
      var x, y;
      if (pHop[i] === 0) {
        x = lerp(leafX[pLeafStart[i]], spineX[pSpine[i]], pT[i]);
        y = lerp(leafY, spineY, pT[i]);
      } else {
        x = lerp(spineX[pSpine[i]], leafX[pLeafEnd[i]], pT[i]);
        y = lerp(spineY, leafY, pT[i]);
      }
      ctx.beginPath();
      ctx.arc(x, y, 2, 0, TAU);
      ctx.fill();
    }
    ctx.shadowBlur = 0;
  }

  function draw(now) {
    ctx.clearRect(0, 0, canvas.clientWidth, canvas.clientHeight);
    drawEdges(now);
    drawPackets();
    drawNodes();
  }

  function drawStatic() {
    ctx.clearRect(0, 0, canvas.clientWidth, canvas.clientHeight);
    ctx.lineWidth = 1;
    ctx.globalAlpha = 0.12;
    ctx.strokeStyle = COLOR_UP;
    ctx.setLineDash(EMPTY_DASH);
    for (var s = 0; s < SPINE_N; s++) {
      for (var l = 0; l < LEAF_N; l++) {
        ctx.beginPath();
        ctx.moveTo(spineX[s], spineY);
        ctx.lineTo(leafX[l], leafY);
        ctx.stroke();
      }
    }
    ctx.globalAlpha = 1;
    drawNodes();
  }

  // ---------------------------------------------------------------------
  // Reduced motion — static frame, no loop, no failure cycle
  // ---------------------------------------------------------------------
  var reducedMotion = false;
  try {
    reducedMotion = window.matchMedia &&
      window.matchMedia('(prefers-reduced-motion: reduce)').matches;
  } catch (err) {
    reducedMotion = false;
  }

  // ---------------------------------------------------------------------
  // rAF loop with visibility / intersection guards
  // ---------------------------------------------------------------------
  var rafId = 0;
  var lastTime = 0;
  var heroVisible = true;

  function frame(now) {
    var dt = (now - lastTime) / 1000;
    if (dt > 0.1) dt = 0.1; // clamp after tab-throttled gaps
    lastTime = now;
    update(now, dt);
    draw(now);
    rafId = requestAnimationFrame(frame);
  }

  function startLoop() {
    if (rafId || reducedMotion) return;
    // lastTime resets every (re)start so a paused gap never produces a
    // huge dt on the first resumed frame. lastFailAt is NOT reset here —
    // it's seeded once at init — so pausing/resuming (tab switch, hero
    // scrolled out of view) never postpones the failure cadence.
    lastTime = performance.now();
    rafId = requestAnimationFrame(frame);
  }

  function stopLoop() {
    if (rafId) {
      cancelAnimationFrame(rafId);
      rafId = 0;
    }
  }

  function evaluateRunState() {
    if (reducedMotion) return;
    if (heroVisible && !document.hidden) {
      startLoop();
    } else {
      stopLoop();
    }
  }

  document.addEventListener('visibilitychange', evaluateRunState);

  var hero = document.querySelector('.hero');
  if (hero && 'IntersectionObserver' in window) {
    var io = new IntersectionObserver(function (entries) {
      heroVisible = entries[entries.length - 1].isIntersecting;
      evaluateRunState();
    }, { threshold: 0.01 });
    io.observe(hero);
  }

  // ---------------------------------------------------------------------
  // Resize
  // ---------------------------------------------------------------------
  if ('ResizeObserver' in window) {
    var ro = new ResizeObserver(function () { layout(); });
    ro.observe(canvas);
  } else {
    var resizeTimer = 0;
    window.addEventListener('resize', function () {
      clearTimeout(resizeTimer);
      resizeTimer = setTimeout(layout, 150);
    });
  }

  // ---------------------------------------------------------------------
  // Init
  // ---------------------------------------------------------------------
  layout();
  initPackets();
  lastFailAt = performance.now();

  if (reducedMotion) {
    drawStatic();
  } else {
    evaluateRunState();
  }
})();
