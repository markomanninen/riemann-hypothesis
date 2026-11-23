/* Tours: camera runs over the landscape.
   A tour is a list of steps. Tour.load turns the steps into a timeline, and Tour.seek sets the
   picture for one moment of it. Playing calls seek with the clock, and recording calls it once
   per frame, so a recorded run is the played run. ANIMATIONS.md describes the steps. */
(() => {
'use strict';
const M = window.Mountain, T = window.Tour = { tour: null, playing: false, time: 0, duration: 0, onTick: () => {} };
const KEYS = ['tx', 'ty', 'tz', 'd', 'az', 'pol', 'zs', 'fov'], TURN = 2 * Math.PI, RAD = Math.PI / 180;
const ease = t => t < 0.5 ? 2 * t * t : 1 - Math.pow(-2 * t + 2, 2) / 2;
let segs = [], look = null, raf = 0, clock = 0, shown = null, marked = -1;

function blend(a, b, t) { const o = {}; for (const k of KEYS) o[k] = a[k] + (b[k] - a[k]) * t; return o; }
/* Pose b with its turn angle moved to within half a turn of pose a, so the camera takes the short way round. */
function shortWay(a, b) {
  const o = { ...b };
  while (o.az - a.az > Math.PI) o.az -= TURN;
  while (a.az - o.az > Math.PI) o.az += TURN;
  return o;
}
/* The height of the camera target for a module of height h, at the vertical stretch zs. */
const lift = (h, zs) => h * Math.max(zs, 0.002) / M.meta.top;

function chainIds(spec) {
  if (spec === 'longest') return M.meta.chain;
  if (Array.isArray(spec)) return spec.map(v => typeof v === 'number' ? v : look.module(v));
  const a = look.module(spec.from), b = look.module(spec.to), ids = M.path(a, b);
  if (!ids) throw new Error(spec.from + ' does not rest on ' + spec.to);
  return ids;
}
/* A run along a chain. The head moves from module to module, one hop in `hop` seconds. The camera
   looks at the average of the chain over `smooth` modules either side of the head, so it glides
   while the head jumps, and it turns by `turn` degrees a second. With `ride` the camera is the
   head. It travels along the chain, `above` levels over it, and looks the way it travels, with
   an angle of view of `fov` degrees. It looks down by `down` degrees at the height of the summit
   and by 8 degrees at the ground, so the landscape below fills the picture while the chain is
   high. It turns towards the next hop during the last third of a hop and the first third of
   the next. A ride with `smooth` above zero glides along the averaged chain and faces from the
   place `ahead` modules behind it to the place `ahead` modules in front of it. */
function chainRun(ids, step, from) {
  const ride = step.ride ? { above: 10, down: 35, fov: 70, ...(step.ride === true ? {} : step.ride) } : null;
  const n = ids.length, hop = step.hop || (ride ? 1.5 : 0.3), reach = step.smooth === undefined ? (ride ? 0 : 3) : step.smooth;
  const d = step.distance || 0.7, rate = (step.turn === undefined ? 3 : step.turn) * RAD;
  const pts = new Float32Array(3 * n);
  ids.forEach((id, k) => pts.set(M.at(id), 3 * k));
  const point = u => {
    u = Math.max(0, Math.min(n - 1, u));
    const k = Math.max(0, Math.min(n - 2, Math.floor(u))), f = n > 1 ? u - k : 0, j = n > 1 ? 3 : 0;
    return [0, 1, 2].map(c => pts[3 * k + c] + (pts[3 * k + j + c] - pts[3 * k + c]) * f);
  };
  const target = u => {
    const sum = [0, 0, 0];
    for (let j = -6; j <= 6; j++) { const p = point(u + j * reach / 6); sum[0] += p[0]; sum[1] += p[1]; sum[2] += p[2]; }
    return sum.map(v => v / 13);
  };
  // The compass direction of hop k, and the direction the rider faces at the place u on the chain.
  const bearing = k => { k = Math.max(0, Math.min(n - 2, k)); return n > 1 ? Math.atan2(pts[3 * k + 4] - pts[3 * k + 1], pts[3 * k + 3] - pts[3 * k]) : 0; };
  const facing = u => {
    const k = Math.max(0, Math.min(n - 2, Math.floor(u))), f = u - k, share = 1 / 3;
    let a = bearing(k), b = a, w = 0;
    if (f < share && k > 0) { a = bearing(k - 1); w = 0.5 + f / (2 * share); }
    else if (f > 1 - share && k < n - 2) { b = bearing(k + 1); w = (f - 1 + share) / (2 * share); }
    let turn = b - a;
    while (turn > Math.PI) turn -= TURN;
    while (turn < -Math.PI) turn += TURN;
    return a + turn * w * w * (3 - 2 * w);
  };
  // On a smoothed ride the rider faces along the averaged chain, measured over `ahead` modules either side.
  const ahead = step.ahead === undefined ? 0.5 : step.ahead;
  const heading = u => {
    const a = target(u - ahead), b = target(u + ahead), dx = b[0] - a[0], dy = b[1] - a[1];
    return dx * dx + dy * dy > 1e-12 ? Math.atan2(dy, dx) : facing(u);
  };
  const pose = tau => {
    const u = Math.min(n - 1, tau / hop), c = target(u), zs = from.zs;
    if (!ride) return { tx: c[0], ty: c[1], tz: lift(c[2], zs), d, az: from.az + rate * tau, pol: from.pol, zs, fov: from.fov };
    // The eye is over the chain at c and looks ahead and down. The pose holds the same thing as
    // a point looked at, a short way along the line of sight, a distance and two angles.
    const way = reach > 0 ? heading(u) : facing(u), far = 0.05, tilt = (8 + (ride.down - 8) * c[2] / M.meta.top) * RAD, flat = far * Math.cos(tilt);
    return { tx: c[0] + flat * Math.cos(way), ty: c[1] + flat * Math.sin(way), tz: lift(c[2] + ride.above, zs) - far * Math.sin(tilt),
      d: far, az: way + Math.PI, pol: Math.PI / 2 - tilt, zs, fov: ride.fov };
  };
  return { ids, pts, hop, pose, ride: !!ride, time: hop * (n - 1) };
}

T.load = function (tour, lookup) {
  look = lookup; segs = []; shown = null; marked = -1;
  let t = 0, pose = M.getPose(), lit = { kind: 'none' }, litAt = 0;
  // litAt is the head's place on a chain that an earlier step lit. Later steps keep the head there.
  const push = s => { if (s.at === undefined) s.at = litAt; s.t0 = t; t += s.time; s.t1 = t; segs.push(s); };
  tour.steps.forEach((step, index) => {
    try {
      const move = step.move === undefined ? 2 : step.move, hold = step.hold || 0, cam = step.camera || {};
      const cap = typeof step.caption === 'string' ? (step.caption === 'module' ? 'module' : { title: step.caption }) : step.caption || null;
      const dim = step.dim === undefined ? 0.8 : step.dim, dot = step.maxDot || (step.ride ? 24 : 256);
      if (step.select === false) { lit = { kind: 'none' }; litAt = 0; }
      if (step.chain) {
        const all = chainIds(step.chain), first = step.from || 0, last = step.to === undefined ? all.length - 1 : step.to;
        const run = chainRun(all.slice(first, last + 1), step, { ...pose, ...cam });
        lit = { kind: 'chain', run };
        if (move) push({ kind: 'move', time: move, a: pose, b: shortWay(pose, run.pose(0)), lit, at: 0, cap, dim, dot });
        push({ kind: 'chain', time: run.time, run, lit, cap, dim, dot });
        pose = run.pose(run.time); litAt = run.ids.length - 1;
        if (hold) push({ kind: 'hold', time: hold, a: pose, lit, cap, dim, dot });
        return;
      }
      if (step.orbit) {
        push({ kind: 'orbit', time: move, a: pose, turn: step.orbit * RAD, lit, cap, dim, dot });
        pose = { ...pose, az: pose.az + step.orbit * RAD };
        if (hold) push({ kind: 'hold', time: hold, a: pose, lit, cap, dim, dot });
        return;
      }
      let to = { ...pose }, h;
      if (step.view) to = M.home(step.view);
      else if (step.pose) to = { ...pose, ...step.pose };
      else if (step.module) {
        const i = look.module(step.module), p = M.at(i);
        to.tx = p[0]; to.ty = p[1]; h = p[2]; to.d = Math.min(pose.d, 0.45);
        if (step.select !== false) { lit = { kind: 'module', id: i }; litAt = 0; }
      } else if (step.area) {
        const a = look.area(step.area), p = M.areaPlace(a);
        to.tx = p.x; to.ty = p.y; h = p.h; to.d = p.d;
        if (step.select !== false) { lit = { kind: 'area', id: a }; litAt = 0; }
      }
      Object.assign(to, cam);
      if (h !== undefined && cam.tz === undefined) to.tz = lift(h, to.zs);
      to = shortWay(pose, to);
      if (move && KEYS.some(k => to[k] !== pose[k])) push({ kind: 'move', time: move, a: pose, b: to, lit, cap, dim, dot });
      pose = to;
      if (hold) push({ kind: 'hold', time: hold, a: pose, lit, cap, dim, dot });
    } catch (err) {
      throw new Error('Step ' + (index + 1) + ' of the tour failed, because ' + err.message);
    }
  });
  if (!segs.length) throw new Error('The tour has no step that takes time');
  T.tour = tour; T.duration = t; T.time = 0; M.showLabels = tour.labels !== false;
  T.seek(0); T.onTick();
};

function light(lit, at) {
  if (lit.kind === 'chain') {
    // Seen from outside, the modules behind the head are marked. On a ride the whole chain is.
    const count = lit.run.ride ? lit.run.ids.length : Math.min(lit.run.ids.length, Math.floor(at) + 1);
    if (shown !== lit || marked !== count) { M.mark(lit.run.ids, count); marked = count; }
    // A ride shows the chain ahead while it lasts. After it, the trail is the ridden chain, as from outside.
    const forward = lit.run.ride && at < lit.run.ids.length - 1;
    M.trail = { pts: lit.run.pts, upto: at, tail: forward ? 3 : 12, forward };
  } else {
    M.trail = null;
    if (shown !== lit) {
      if (lit.kind === 'module') M.selectModule(lit.id, false, true);
      else if (lit.kind === 'area') M.selectArea(lit.id, false, true);
      else M.clear(true);
    }
  }
  shown = lit;
}

/* Set the picture for the moment t, in seconds from the start of the tour. */
T.seek = function (t) {
  t = Math.max(0, Math.min(T.duration, t)); T.time = t;
  let s = segs[segs.length - 1];
  for (const g of segs) if (t < g.t1) { s = g; break; }
  const u = s.time ? Math.min(1, (t - s.t0) / s.time) : 1;
  let pose = s.a, at = s.at || 0;
  if (s.kind === 'move') pose = blend(s.a, s.b, ease(u));
  else if (s.kind === 'orbit') pose = { ...s.a, az: s.a.az + s.turn * u };
  else if (s.kind === 'chain') { pose = s.run.pose(t - s.t0); at = (t - s.t0) / s.run.hop; }
  light(s.lit, at);
  M.dimming = s.dim; M.maxDot = s.dot;
  M.caption = null;
  if (s.cap && T.tour.captions !== false) {
    if (s.cap !== 'module') M.caption = s.cap;
    else if (s.lit.kind === 'chain') { const ids = s.lit.run.ids, k = Math.max(0, Math.min(ids.length - 1, Math.floor(at + 0.5))); M.caption = look.caption(ids[k], k + 1, ids.length); }
    else if (s.lit.kind === 'module') M.caption = look.caption(s.lit.id);
  }
  M.setPose(pose);
};

T.play = function () {
  if (!T.tour) return;
  if (T.time >= T.duration) T.time = 0;
  T.playing = true; clock = performance.now() - T.time * 1000;
  const tick = () => {
    if (!T.playing) return;
    const t = (performance.now() - clock) / 1000;
    T.seek(t);
    if (t >= T.duration) T.playing = false; else raf = requestAnimationFrame(tick);
    T.onTick();
  };
  cancelAnimationFrame(raf); tick();
};
T.pause = function () { T.playing = false; cancelAnimationFrame(raf); T.onTick(); };
T.stop = function () {
  T.playing = false; cancelAnimationFrame(raf);
  segs = []; shown = null; T.tour = null; T.duration = 0; T.time = 0;
  M.trail = null; M.caption = null; M.dimming = 0.8; M.maxDot = 256; M.showLabels = true; M.setPose({ fov: 35 }); M.clear();
  T.onTick();
};

/* Render the frames from second `from` to second `to` and hand each one to `post`. */
T.record = async function (fps, from, to, post) {
  const a = Math.max(0, from || 0), b = Math.min(T.duration, to === undefined ? T.duration : to);
  const frames = Math.floor((b - a) * fps + 1e-6) + 1;
  await post('begin?frames=' + frames);
  for (let f = 0; f < frames; f++) { T.seek(a + f / fps); await post('frame?n=' + f, M.grab()); }
  await post('done');
};
})();
