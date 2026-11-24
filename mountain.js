/* The mountain view: every module as a point in WebGL.
   Ground position comes from the folder map, height from the longest import chain below
   the module. Exposes window.Mountain, which index.html drives. */
(() => {
'use strict';
const FOV = 35, TAN0 = Math.tan(FOV * Math.PI / 360), ZS = 0.55, HALF = Math.PI / 2;
let TAN = TAN0;   // half of the camera's angle of view, as a tangent. matrices() sets it from cam.fov.
const SURF = [0.102, 0.102, 0.098];
const M = window.Mountain = { ready: false, sel: null, mode: 'mountain', lit: false, dimming: 0.8, maxDot: 256, showLabels: true, trail: null, caption: null };
let canvas, gl, ov, octx, comp, fixed = null, meta, areas, n, top;
let wx, wy, hgt, lines, area, off, tgt, roff, rsrc, state;
let progP, progL, bXY, bH, bLn, bSt, bGroundP, bGroundC, nGround, bChainP, bChainC, nChain, bDynP, bDynC, nDyn = 0;
let W = 1, H = 1, dpr = 1, raf = 0, anim = null, maxPoint = 64;
const mvp = new Float32Array(16), eye = [0, 0, 0], bR = [1, 0, 0], bU = [0, 1, 0], bF = [0, 0, -1];
const cam = { tx: 0, ty: 0, tz: 0.1, d: 3.4, az: -HALF + 0.55, pol: 1.1, zs: ZS, fov: FOV };
const reduced = matchMedia('(prefers-reduced-motion: reduce)').matches;

async function gunzip(url) {
  if (!('DecompressionStream' in window)) throw new Error('nogzip');
  const r = await fetch(url);
  if (!r.ok) throw new Error(url + ' ' + r.status);
  // The file is gzip written as base64 text.
  const bin = atob(await r.text()), bytes = new Uint8Array(bin.length);
  for (let i = 0; i < bin.length; i++) bytes[i] = bin.charCodeAt(i);
  return new Response(new Blob([bytes]).stream().pipeThrough(new DecompressionStream('gzip'))).arrayBuffer();
}
M.gunzip = gunzip;

/* A module or folder name as words: DivisorProofs reads Divisor Proofs, GLCounts reads GL Counts.
   Every name the page shows passes through here. */
const words = M.words = s => s.replace(/([A-Z])([A-Z][a-z])/g, '$1 $2').replace(/([a-z0-9])([A-Z])/g, '$1 $2').replace(/_+/g, ' ').trim();

function program(vs, fs, attribs) {
  const p = gl.createProgram();
  for (const [type, src] of [[gl.VERTEX_SHADER, vs], [gl.FRAGMENT_SHADER, fs]]) {
    const s = gl.createShader(type);
    gl.shaderSource(s, src); gl.compileShader(s);
    if (!gl.getShaderParameter(s, gl.COMPILE_STATUS)) throw new Error(gl.getShaderInfoLog(s));
    gl.attachShader(p, s);
  }
  attribs.forEach((a, i) => gl.bindAttribLocation(p, i, a));
  gl.linkProgram(p);
  if (!gl.getProgramParameter(p, gl.LINK_STATUS)) throw new Error(gl.getProgramInfoLog(p));
  const u = {};
  for (let i = 0, c = gl.getProgramParameter(p, gl.ACTIVE_UNIFORMS); i < c; i++) {
    const name = gl.getActiveUniform(p, i).name;
    u[name] = gl.getUniformLocation(p, name);
  }
  return { p, u };
}

const VS_POINTS = `
attribute vec2 aXY; attribute float aH; attribute float aLn; attribute float aSt;
uniform mat4 uM; uniform float uZ, uPx, uMin, uSel, uPass, uTop, uMax, uDim;
varying vec3 vC;
vec3 ramp(float t){
  vec3 c0=vec3(.094,.310,.584), c1=vec3(.165,.471,.839), c2=vec3(.427,.655,.925), c3=vec3(.804,.886,.984);
  t=clamp(t,0.,1.)*3.;
  return t<1. ? mix(c0,c1,t) : t<2. ? mix(c1,c2,t-1.) : mix(c2,c3,t-2.);
}
void main(){
  vec4 pos = uM*vec4(aXY*2.-1., aH*uZ, 1.);
  float size = max(uPx*sqrt(max(aLn,4.))/pos.w, uMin);
  vec3 col = ramp(aH/uTop);
  bool hi = aSt>.5 && aSt<3.5;
  if(uSel>.5){
    if(aSt<.5) col = mix(col, vec3(${SURF.join(',')}), uDim);
    else if(aSt<1.5){ col = vec3(.851,.349,.149); size = max(size, uMin*1.7); }
    else if(aSt<2.5){ col = vec3(.098,.620,.439); size = max(size, uMin*1.7); }
    else if(aSt<3.5){ col = vec3(1.); size = max(size*1.5, uMin*5.); }
  }
  // Pass 0 draws the modules that are not lit, pass 1 the lit ones and pass 2 the selected one alone.
  bool mine = uPass<.5 ? !(hi && uSel>.5) : uPass<1.5 ? (hi && aSt<2.5) : aSt>2.5 && aSt<3.5;
  if(!mine) pos = vec4(2.,2.,2.,1.);
  gl_Position = pos; gl_PointSize = min(size, uMax); vC = col;
}`;
const FS_POINTS = `precision mediump float; varying vec3 vC;
void main(){ vec2 c=gl_PointCoord-.5; if(dot(c,c)>.25) discard; gl_FragColor=vec4(vC,1.); }`;
const VS_LINES = `attribute vec3 aP; attribute vec4 aC; uniform mat4 uM; uniform float uZ; varying vec4 vC;
void main(){ gl_Position = uM*vec4(aP.xy, aP.z*uZ, 1.); vC = aC; }`;
const FS_LINES = `precision mediump float; varying vec4 vC; void main(){ gl_FragColor = vC; }`;

function buffer(data, usage) {
  const b = gl.createBuffer();
  gl.bindBuffer(gl.ARRAY_BUFFER, b);
  gl.bufferData(gl.ARRAY_BUFFER, data, usage || gl.STATIC_DRAW);
  return b;
}

M.init = async function (opts) {
  canvas = opts.canvas; ov = opts.overlay; octx = ov.getContext('2d'); fixed = opts.stage || null;
  M.onSelect = opts.onSelect || (() => {}); M.onHover = opts.onHover || (() => {});
  gl = canvas.getContext('webgl', { antialias: true, alpha: false });
  if (!gl) throw new Error('nowebgl');
  const [m, buf] = await Promise.all([fetch('data/mountain.json').then(r => r.json()), gunzip('data/mountain.gz.txt')]);
  meta = M.meta = m; n = m.modules; top = m.top;
  const sec = {};
  for (const s of m.sections) {
    const T = s.type === 'u32' ? Uint32Array : s.type === 'u16' ? Uint16Array : Uint8Array;
    sec[s.name] = new T(buf, s.offset, s.length);
  }
  off = sec.off; tgt = sec.tgt; lines = sec.lines; area = sec.area; hgt = sec.height;
  wx = new Float32Array(n); wy = new Float32Array(n);
  for (let i = 0; i < n; i++) { wx[i] = sec.xy[2 * i] / 65535 * 2 - 1; wy[i] = sec.xy[2 * i + 1] / 65535 * 2 - 1; }
  // Importers, as the reverse of the import lists.
  const E = tgt.length; roff = new Uint32Array(n + 1);
  for (let e = 0; e < E; e++) roff[tgt[e] + 1]++;
  for (let i = 0; i < n; i++) roff[i + 1] += roff[i];
  rsrc = new Uint32Array(E); const fill = roff.slice(0, n);
  for (let i = 0; i < n; i++) for (let e = off[i]; e < off[i + 1]; e++) rsrc[fill[tgt[e]]++] = i;
  state = new Uint8Array(n);
  areas = M.areas = m.areas.map(a => ({ name: a[0], parent: a[1], x: a[2], y: a[3], r: a[4], span: a[5], modules: a[6],
    lines: a[7], h: [a[8], a[9], a[10]], level: a[0].split('.').length, label: words(a[0].slice(a[0].lastIndexOf('.') + 1)) }));

  progP = program(VS_POINTS, FS_POINTS, ['aXY', 'aH', 'aLn', 'aSt']);
  progL = program(VS_LINES, FS_LINES, ['aP', 'aC']);
  maxPoint = Math.min(256, gl.getParameter(gl.ALIASED_POINT_SIZE_RANGE)[1]);
  bXY = buffer(sec.xy); bH = buffer(hgt); bLn = buffer(lines); bSt = buffer(state, gl.DYNAMIC_DRAW);
  // Rings on the ground, one per folder, fainter with depth in the folder tree.
  const gp = [], gc = [];
  for (const a of areas) {
    const seg = Math.max(14, Math.min(96, Math.round(a.r * 500)));
    const alpha = a.level === 1 ? 150 : a.level === 2 ? 95 : a.level === 3 ? 60 : 36;
    for (let s = 0; s < seg; s++) {
      const t0 = s / seg * 2 * Math.PI, t1 = (s + 1) / seg * 2 * Math.PI;
      gp.push(a.x + a.r * Math.cos(t0), a.y + a.r * Math.sin(t0), 0, a.x + a.r * Math.cos(t1), a.y + a.r * Math.sin(t1), 0);
      gc.push(190, 205, 230, alpha, 190, 205, 230, alpha);
    }
  }
  nGround = gp.length / 3; bGroundP = buffer(new Float32Array(gp)); bGroundC = buffer(new Uint8Array(gc));
  const cp = [], cc = [];
  for (let k = 0; k + 1 < m.chain.length; k++) {
    const a = m.chain[k], b = m.chain[k + 1];
    cp.push(wx[a], wy[a], hgt[a], wx[b], wy[b], hgt[b]); cc.push(255, 236, 200, 200, 255, 236, 200, 200);
  }
  nChain = cp.length / 3; bChainP = buffer(new Float32Array(cp)); bChainC = buffer(new Uint8Array(cc));
  bDynP = gl.createBuffer(); bDynC = gl.createBuffer();

  new ResizeObserver(resize).observe(canvas.parentElement);
  if (document.fonts) document.fonts.addEventListener('loadingdone', () => { widths.clear(); schedule(); });
  resize(); M.reset(true); bindInput();
  M.ready = true; schedule();
};

function resize() {
  // A stage has a fixed size and scale, so a recording gives the same picture on every machine.
  const box = canvas.parentElement.getBoundingClientRect();
  W = fixed ? fixed.w : Math.max(1, box.width); H = fixed ? fixed.h : Math.max(1, box.height);
  dpr = fixed ? fixed.scale : Math.min(window.devicePixelRatio || 1, 2);
  ov.width = canvas.width = Math.round(W * dpr); ov.height = canvas.height = Math.round(H * dpr);
  schedule();
}
const fitD = () => 1.1 / (TAN0 * Math.min(1, W / H));
const fitTilted = () => Math.max(1.05 / (TAN0 * W / H), 0.78 / TAN0);
const zk = () => Math.max(cam.zs, 0.002) / top;

function matrices() {
  TAN = Math.tan(cam.fov * Math.PI / 360);
  const sp = Math.sin(cam.pol), cp = Math.cos(cam.pol), ca = Math.cos(cam.az), sa = Math.sin(cam.az);
  eye[0] = cam.tx + cam.d * sp * ca; eye[1] = cam.ty + cam.d * sp * sa; eye[2] = cam.tz + cam.d * cp;
  bF[0] = -sp * ca; bF[1] = -sp * sa; bF[2] = -cp;
  bR[0] = -sa; bR[1] = ca; bR[2] = 0;
  bU[0] = bR[1] * bF[2] - bR[2] * bF[1]; bU[1] = bR[2] * bF[0] - bR[0] * bF[2]; bU[2] = bR[0] * bF[1] - bR[1] * bF[0];
  const near = Math.max(0.0008, cam.d * 0.02), far = cam.d + 5, f = 1 / TAN, asp = W / H;
  const dot = v => -(v[0] * eye[0] + v[1] * eye[1] + v[2] * eye[2]);
  const rows = [[bR[0], bR[1], bR[2], dot(bR)], [bU[0], bU[1], bU[2], dot(bU)], [-bF[0], -bF[1], -bF[2], -dot(bF)]];
  const A = (far + near) / (near - far), B = 2 * far * near / (near - far);
  for (let c = 0; c < 4; c++) {
    mvp[c * 4] = f / asp * rows[0][c]; mvp[c * 4 + 1] = f * rows[1][c];
    mvp[c * 4 + 2] = A * rows[2][c] + (c === 3 ? B : 0); mvp[c * 4 + 3] = -rows[2][c];
  }
}
function project(x, y, z) {
  const w = mvp[3] * x + mvp[7] * y + mvp[11] * z + mvp[15];
  if (w <= 0) return null;
  return [((mvp[0] * x + mvp[4] * y + mvp[8] * z + mvp[12]) / w * 0.5 + 0.5) * W,
          (1 - ((mvp[1] * x + mvp[5] * y + mvp[9] * z + mvp[13]) / w * 0.5 + 0.5)) * H, w];
}
function ground(px, py) {
  const nx = (px / W * 2 - 1) * TAN * W / H, ny = (1 - py / H * 2) * TAN;
  const dx = bF[0] + bR[0] * nx + bU[0] * ny, dy = bF[1] + bR[1] * nx + bU[1] * ny, dz = bF[2] + bR[2] * nx + bU[2] * ny;
  if (dz > -1e-4) return null;
  const t = -eye[2] / dz;
  return [eye[0] + t * dx, eye[1] + t * dy];
}

function attrib(i, buf, size, type, norm) {
  gl.bindBuffer(gl.ARRAY_BUFFER, buf); gl.enableVertexAttribArray(i); gl.vertexAttribPointer(i, size, type, norm, 0, 0);
}
function drawLines(bp, bc, count) {
  if (!count) return;
  attrib(0, bp, 3, gl.FLOAT, false); attrib(1, bc, 4, gl.UNSIGNED_BYTE, true);
  gl.drawArrays(gl.LINES, 0, count);
}
function draw() {
  matrices();
  gl.viewport(0, 0, canvas.width, canvas.height);
  // The last pass of a frame leaves depth writes off, and a clear skips a buffer that is closed to writes.
  gl.depthMask(true);
  gl.clearColor(SURF[0], SURF[1], SURF[2], 1); gl.clear(gl.COLOR_BUFFER_BIT | gl.DEPTH_BUFFER_BIT);
  gl.enable(gl.DEPTH_TEST); gl.depthFunc(gl.LEQUAL);
  gl.blendFunc(gl.SRC_ALPHA, gl.ONE_MINUS_SRC_ALPHA);
  const focal = H * dpr / (2 * TAN), uSel = M.sel || M.lit ? 1 : 0;
  const lineSetup = () => {
    gl.useProgram(progL.p); gl.uniformMatrix4fv(progL.u.uM, false, mvp); gl.uniform1f(progL.u.uZ, zk());
    gl.disableVertexAttribArray(2); gl.disableVertexAttribArray(3); gl.enable(gl.BLEND); gl.depthMask(false);
  };
  const pointSetup = pass => {
    gl.useProgram(progP.p); gl.disable(gl.BLEND); gl.depthMask(true);
    gl.uniformMatrix4fv(progP.u.uM, false, mvp); gl.uniform1f(progP.u.uZ, zk()); gl.uniform1f(progP.u.uTop, top);
    gl.uniform1f(progP.u.uPx, 0.9 * 2 * focal / meta.radius);
    gl.uniform1f(progP.u.uMin, dpr * Math.max(0.6, Math.min(2.2, 0.55 + 0.25 * fitD() / cam.d)));
    gl.uniform1f(progP.u.uMax, Math.min(maxPoint, M.maxDot * dpr)); gl.uniform1f(progP.u.uSel, uSel); gl.uniform1f(progP.u.uPass, pass); gl.uniform1f(progP.u.uDim, M.dimming);
    attrib(0, bXY, 2, gl.UNSIGNED_SHORT, true); attrib(1, bH, 1, gl.UNSIGNED_BYTE, false);
    attrib(2, bLn, 1, gl.UNSIGNED_SHORT, false); attrib(3, bSt, 1, gl.UNSIGNED_BYTE, false);
    gl.drawArrays(gl.POINTS, 0, n);
  };
  lineSetup(); drawLines(bGroundP, bGroundC, nGround);
  pointSetup(0);
  // The lit modules stand over everything drawn so far, and among themselves the nearer one covers
  // the farther one, so they get a depth buffer of their own. The lines of the selection are drawn
  // after them against that buffer, so a line passes in front of the lit modules that lie behind it
  // and behind those that lie in front of it. The selected module is drawn last without a depth
  // test, which keeps it in sight from every side.
  const lit = (M.sel && M.sel.type === 'module') || M.lit;
  if (lit) { gl.depthMask(true); gl.clear(gl.DEPTH_BUFFER_BIT); pointSetup(1); }
  lineSetup(); if (!lit) gl.disable(gl.DEPTH_TEST);
  if (M.chain) drawLines(bChainP, bChainC, nChain); drawLines(bDynP, bDynC, nDyn);
  if (M.sel && M.sel.type === 'module') { gl.disable(gl.DEPTH_TEST); pointSetup(2); }
  overlay();
}
function schedule() { if (!raf && M.ready !== null) raf = requestAnimationFrame(frame); }
function frame() { raf = 0; if (anim) anim(); if (gl) draw(); if (anim) schedule(); }

function animate(to, ms) {
  if ('az' in to) { while (to.az - cam.az > Math.PI) to.az -= 2 * Math.PI; while (cam.az - to.az > Math.PI) to.az += 2 * Math.PI; }
  if (reduced || ms === 0) { Object.assign(cam, to); anim = null; schedule(); return; }
  const from = { ...cam }, t0 = performance.now();
  anim = () => {
    const t = Math.min(1, (performance.now() - t0) / (ms || 700)), e = t < 0.5 ? 2 * t * t : 1 - Math.pow(-2 * t + 2, 2) / 2;
    for (const k in to) cam[k] = from[k] + (to[k] - from[k]) * e;
    if (t >= 1) anim = null;
  };
  schedule();
}
M.view = function (mode, instant) {
  M.mode = mode;
  animate(mode === 'map' ? { pol: 0, az: -HALF, zs: 0, tz: 0, fov: FOV } : { pol: 1.1, az: -HALF + 0.55, zs: ZS, tz: Math.max(cam.tz, 0.1), fov: FOV }, instant ? 0 : 800);
};
M.home = mode => mode === 'map' ? { tx: 0, ty: 0, tz: 0, d: fitD(), pol: 0, az: -HALF, zs: 0, fov: FOV }
  : { tx: 0, ty: 0, tz: 0.16, d: fitTilted(), pol: 1.1, az: -HALF + 0.55, zs: ZS, fov: FOV };
M.reset = function (instant) { animate(M.home(M.mode), instant ? 0 : 700); };
M.flyToModule = i => animate({ tx: wx[i], ty: wy[i], tz: M.mode === 'map' ? 0 : hgt[i] * zk(), d: Math.min(cam.d, 0.45) }, 800);
M.flyToArea = a => {
  const A = areas[a];
  animate({ tx: A.x, ty: A.y, tz: M.mode === 'map' ? 0 : A.h[1] * zk(), d: Math.max(0.02, A.r * 1.35 / (TAN * Math.min(1, W / H))) }, 800);
};

/* The overlay is a 2D canvas over the points. It carries the folder names, the trail of a tour and
   its caption, so a recording of the two canvases holds everything the plate shows. */
const FONT = 'Literata, Georgia, serif', widths = new Map();
function write(text, x, y, size, bold, align, colour) {
  octx.font = (bold ? '600 ' : '') + size + 'px ' + FONT;
  octx.textAlign = align; octx.textBaseline = 'middle'; octx.lineJoin = 'round';
  octx.lineWidth = size / 3.5; octx.strokeStyle = 'rgba(26,26,25,.9)'; octx.strokeText(text, x, y);
  octx.fillStyle = colour; octx.fillText(text, x, y);
}
function width(text, size, bold) {
  const key = size + (bold ? 'b' : 'n') + text; let w = widths.get(key);
  if (w === undefined) { octx.font = (bold ? '600 ' : '') + size + 'px ' + FONT; w = octx.measureText(text).width; widths.set(key, w); }
  return w;
}
function overlay() {
  octx.setTransform(dpr, 0, 0, dpr, 0, 0); octx.clearRect(0, 0, W, H);
  if (M.trail) trail();
  if (M.showLabels) labels();
  if (M.caption) caption();
}
/* Folder names: the areas whose rings are large enough on screen, largest first, without overlaps. */
function labels() {
  // A caption owns the top of the plate and the height legend of the page its lower edge, so the names stay between them.
  const cand = [], focal = H / (2 * TAN), tilt = Math.cos(cam.pol), big = 0.8 * Math.max(W, H), roof = M.caption ? 84 : 8, floor = fixed ? H - 8 : H - 48;
  for (let i = 0; i < areas.length; i++) {
    const a = areas[i], p = project(a.x, a.y, 0);
    if (!p) continue;
    const sr = a.r * focal / p[2];
    if (sr < 30 || sr > big) continue;
    const y = p[1] - sr * tilt + 11;
    if (p[0] < 20 || p[0] > W - 20 || y < roof || y > floor) continue;
    cand.push([sr, p[0], y, a.label, a.level === 1]);
  }
  cand.sort((u, v) => v[0] - u[0]);
  const placed = [], peak = project(wx[0], wy[0], hgt[0] * zk()), summit = 'Main Conclusion, the summit';
  // A label near an edge moves inwards until its whole text is on the plate.
  const inside = (x, w) => Math.max(w / 2 + 4, Math.min(W - w / 2 - 4, x));
  if (peak && cam.zs > 0.02 && peak[1] - 16 > roof) { const w = width(summit, 14, true); placed.push([inside(peak[0], w), peak[1] - 16, summit, true, w + 14]); }
  for (const c of cand) {
    if (placed.length >= 24) break;
    const w = width(c[3], c[4] ? 14 : 13, c[4]), x = inside(c[1], w);
    if (placed.some(q => Math.abs(q[0] - x) < (q[4] + w + 14) / 2 && Math.abs(q[1] - c[2]) < 21)) continue;
    placed.push([x, c[2], c[3], c[4], w + 14]);
  }
  for (const q of placed) write(q[2], q[0], q[1], q[3] ? 14 : 13, q[3], 'center', q[3] ? '#fff' : '#dfe5f0');
}
/* The trail of a tour. Seen from outside it is the chain up to the head, its last modules bright
   and the older part faint, with the head as a dot. On a ride the camera is the head, so the trail
   is the chain ahead, with rings on the next modules. */
function trail() {
  const { pts, upto, tail, forward } = M.trail, z = zk(), count = pts.length / 3, reach = tail || 12;
  const last = Math.max(0, Math.min(count - 1, Math.floor(upto))), f = last + 1 < count ? upto - last : 0;
  const at = k => project(pts[3 * k], pts[3 * k + 1], pts[3 * k + 2] * z);
  // A point on the hop that the head is on, a share g of the way from module `last` to the next one.
  const onHop = g => { const i = 3 * last, j = i + (last + 1 < count ? 3 : 0); return project(pts[i] + (pts[j] - pts[i]) * g, pts[i + 1] + (pts[j + 1] - pts[i + 1]) * g, (pts[i + 2] + (pts[j + 2] - pts[i + 2]) * g) * z); };
  const head = onHop(f);
  const stroke = (from, to, colour, wide) => {
    octx.beginPath(); let pen = false;
    const go = p => { if (!p) { pen = false; return; } if (pen) octx.lineTo(p[0], p[1]); else octx.moveTo(p[0], p[1]); pen = true; };
    if (forward) go(onHop(f + (1 - f) * 0.12));
    for (let k = from; k <= to; k++) go(at(k));
    if (!forward) go(head);
    octx.strokeStyle = colour; octx.lineWidth = wide; octx.stroke();
  };
  octx.lineJoin = octx.lineCap = 'round';
  if (forward) {
    const next = last + 1, near = Math.min(count - 1, next + reach - 1);
    stroke(next, count - 1, 'rgba(255,233,196,.38)', 1);
    stroke(next, near, 'rgba(255,214,150,.25)', 6);
    stroke(next, near, '#ffe9c4', 1.8);
    for (let k = Math.min(count - 1, next + 2); k >= next; k--) {
      const p = at(k); if (!p) continue;
      octx.strokeStyle = k === next ? '#fff' : 'rgba(255,255,255,.55)'; octx.lineWidth = k === next ? 2 : 1.2;
      octx.beginPath(); octx.arc(p[0], p[1], k === next ? 9 : 6, 0, 7); octx.stroke();
    }
    return;
  }
  const recent = Math.max(0, last - reach);
  stroke(0, last, 'rgba(255,233,196,.38)', 1);
  stroke(recent, last, 'rgba(255,214,150,.25)', 6);
  stroke(recent, last, '#ffe9c4', 1.8);
  if (head) {
    octx.fillStyle = 'rgba(255,255,255,.28)'; octx.beginPath(); octx.arc(head[0], head[1], 9, 0, 7); octx.fill();
    octx.fillStyle = '#fff'; octx.beginPath(); octx.arc(head[0], head[1], 4, 0, 7); octx.fill();
  }
}
/* The caption of a tour, at the top left, so the lower edge stays free for subtitles. */
function caption() {
  const c = M.caption, room = W - 44;
  // A line that is too wide gets smaller type, down to 11. If it is still too wide, it loses
  // characters, the title from its end and the smaller line from its start.
  const fit = (text, size, bold, fromStart) => {
    const small = Math.max(11, Math.min(size, size * room / width(text, size, bold))), wide = t => width(t, size, bold) * small / size;
    if (wide(text) <= room) return [text, small];
    let keep = text.length;
    while (keep > 4 && wide(fromStart ? '… ' + text.slice(-keep) : text.slice(0, keep) + ' …') > room) keep--;
    return [fromStart ? '… ' + text.slice(-keep).trimStart() : text.slice(0, keep).trimEnd() + ' …', small];
  };
  if (c.title) { const [text, size] = fit(c.title, 22, true, false); write(text, 22, 30, size, true, 'left', '#fff'); }
  if (c.text) { const [text, size] = fit(c.text, 14, false, true); write(text, 22, c.title ? 58 : 30, size, false, 'left', '#dfe5f0'); }
}

/* Picking */
function pickPoint(px, py, rad) {
  const z = zk(), k = 0.9 * (H / (2 * TAN)) / meta.radius, lo = rad;
  let best = -1, bs = 1;
  for (let i = 0; i < n; i++) {
    const x = wx[i], y = wy[i], h = hgt[i] * z;
    const w = mvp[3] * x + mvp[7] * y + mvp[11] * h + mvp[15];
    if (w <= 0) continue;
    const reach = Math.max(lo, k * Math.sqrt(lines[i] > 4 ? lines[i] : 4) / w);
    const sx = ((mvp[0] * x + mvp[4] * y + mvp[8] * h + mvp[12]) / w * 0.5 + 0.5) * W - px;
    if (sx > reach || sx < -reach) continue;
    const sy = (1 - ((mvp[1] * x + mvp[5] * y + mvp[9] * h + mvp[13]) / w * 0.5 + 0.5)) * H - py;
    const s = (sx * sx + sy * sy) / (reach * reach);
    if (s < bs) { bs = s; best = i; }
  }
  return best;
}
function pickArea(px, py) {
  const g = ground(px, py);
  if (!g) return -1;
  const focal = H / (2 * TAN);
  let best = -1, br = 9;
  for (let i = 0; i < areas.length; i++) {
    const a = areas[i], dx = g[0] - a.x, dy = g[1] - a.y;
    if (dx * dx + dy * dy > a.r * a.r || a.r >= br) continue;
    const p = project(a.x, a.y, 0);
    if (p && a.r * focal / p[2] >= 26) { best = i; br = a.r; }
  }
  return best;
}

/* Selection */
function dynLines(pos, col) {
  gl.bindBuffer(gl.ARRAY_BUFFER, bDynP); gl.bufferData(gl.ARRAY_BUFFER, new Float32Array(pos), gl.DYNAMIC_DRAW);
  gl.bindBuffer(gl.ARRAY_BUFFER, bDynC); gl.bufferData(gl.ARRAY_BUFFER, new Uint8Array(col), gl.DYNAMIC_DRAW);
  nDyn = pos.length / 3;
}
function pushState() { gl.bindBuffer(gl.ARRAY_BUFFER, bSt); gl.bufferSubData(gl.ARRAY_BUFFER, 0, state); schedule(); }

M.selectModule = function (i, fly, quiet) {
  state.fill(0); M.lit = false;
  const cone = (offs, arr, mark) => {
    const stack = [i]; let count = 0, sum = 0;
    while (stack.length) {
      const v = stack.pop();
      for (let e = offs[v]; e < offs[v + 1]; e++) { const t = arr[e]; if (!state[t]) { state[t] = mark; count++; sum += lines[t]; stack.push(t); } }
    }
    return [count, sum];
  };
  state[i] = 3;
  const below = cone(off, tgt, 1), above = cone(roff, rsrc, 2);
  const pos = [], col = [];
  for (let e = off[i]; e < off[i + 1]; e++) { const t = tgt[e]; pos.push(wx[i], wy[i], hgt[i], wx[t], wy[t], hgt[t]); col.push(255, 150, 100, 230, 255, 150, 100, 110); }
  for (let e = roff[i], c = 0; e < roff[i + 1] && c < 400; e++, c++) { const t = rsrc[e]; pos.push(wx[i], wy[i], hgt[i], wx[t], wy[t], hgt[t]); col.push(110, 230, 180, 200, 110, 230, 180, 70); }
  dynLines(pos, col);
  M.sel = { type: 'module', id: i, height: hgt[i], lines: lines[i], area: area[i], below: below[0], belowLines: below[1],
    above: above[0], aboveLines: above[1], imports: off[i + 1] - off[i], importers: roff[i + 1] - roff[i] };
  pushState(); if (fly) M.flyToModule(i); if (!quiet) M.onSelect(M.sel);
};
M.selectArea = function (a, fly, quiet) {
  const A = areas[a], end = a + A.span; M.lit = false;
  for (let i = 0; i < n; i++) state[i] = area[i] >= a && area[i] < end ? 4 : 0;
  const pos = [], col = [], seg = 120;
  for (let s = 0; s < seg; s++) {
    const t0 = s / seg * 2 * Math.PI, t1 = (s + 1) / seg * 2 * Math.PI;
    pos.push(A.x + A.r * Math.cos(t0), A.y + A.r * Math.sin(t0), 0, A.x + A.r * Math.cos(t1), A.y + A.r * Math.sin(t1), 0);
    col.push(255, 255, 255, 235, 255, 255, 255, 235);
  }
  dynLines(pos, col);
  M.sel = { type: 'area', id: a, name: A.name, label: A.label, modules: A.modules, lines: A.lines, h: A.h, subareas: A.span - 1, level: A.level };
  pushState(); if (fly) M.flyToArea(a); if (!quiet) M.onSelect(M.sel);
};
M.showChain = function (on) { M.chain = on; schedule(); };
M.clear = function (quiet) { state.fill(0); nDyn = 0; M.sel = null; M.lit = false; pushState(); if (!quiet) M.onSelect(null); };

/* What a tour needs: the camera as numbers, places, marks on a list of modules, and the picture as pixels. */
M.getPose = () => ({ tx: cam.tx, ty: cam.ty, tz: cam.tz, d: cam.d, az: cam.az, pol: cam.pol, zs: cam.zs, fov: cam.fov });
M.setPose = function (p) { anim = null; Object.assign(cam, p); schedule(); };
M.at = i => [wx[i], wy[i], hgt[i]];
M.screen = (x, y, h) => project(x, y, h * zk());
M.areaPlace = a => ({ x: areas[a].x, y: areas[a].y, h: areas[a].h[1], d: Math.max(0.02, areas[a].r * 1.35 / (TAN0 * Math.min(1, W / H))) });
M.mark = function (ids, count) {
  state.fill(0); for (let k = 0; k < count; k++) state[ids[k]] = 1;
  nDyn = 0; M.sel = null; M.lit = count > 0; pushState();
};
/* The shortest chain of imports from module a down to module b, or null when a does not rest on b. */
M.path = function (a, b) {
  const prev = new Int32Array(n).fill(-1), queue = [a]; prev[a] = a;
  for (let h = 0; h < queue.length && prev[b] < 0; h++) {
    const v = queue[h];
    for (let e = off[v]; e < off[v + 1]; e++) { const t = tgt[e]; if (prev[t] < 0) { prev[t] = v; queue.push(t); } }
  }
  if (prev[b] < 0) return null;
  const out = [b]; while (out[out.length - 1] !== a) out.push(prev[out[out.length - 1]]);
  return out.reverse();
};
/* Draw now and return the picture, points and overlay together, as RGBA bytes from the top row down. */
M.grab = function () {
  draw();
  comp = comp || document.createElement('canvas');
  if (comp.width !== canvas.width || comp.height !== canvas.height) { comp.width = canvas.width; comp.height = canvas.height; }
  const c = comp.getContext('2d', { willReadFrequently: true });
  c.drawImage(canvas, 0, 0); c.drawImage(ov, 0, 0);
  return c.getImageData(0, 0, comp.width, comp.height).data;
};
M.areaChain = function (a) { const out = []; while (a >= 0) { out.unshift(a); a = areas[a].parent; } return out; };
M.moduleInfo = i => ({ height: hgt[i], lines: lines[i], area: area[i] });

/* Input: drag turns the mountain or moves the map, pinch and wheel zoom, tap selects. */
function bindInput() {
  const pts = new Map(); let moved = 0, downAt = 0, lastTap = [0, 0, 0], pinch = 0, hoverPending = false;
  const local = e => { const b = canvas.getBoundingClientRect(); return [e.clientX - b.left, e.clientY - b.top]; };
  const pan = (dx, dy) => {
    const wpp = 2 * cam.d * TAN / H;
    cam.tx += (-dx * bR[0] + dy * -Math.cos(cam.az)) * wpp; cam.ty += (-dx * bR[1] + dy * -Math.sin(cam.az)) * wpp;
    cam.tx = Math.max(-1.3, Math.min(1.3, cam.tx)); cam.ty = Math.max(-1.3, Math.min(1.3, cam.ty));
  };
  const zoomAt = (px, py, factor) => {
    matrices(); const g0 = ground(px, py);
    cam.d = Math.max(0.012, Math.min(8, cam.d * factor));
    matrices(); const g1 = ground(px, py);
    if (g0 && g1 && Math.hypot(g0[0] - g1[0], g0[1] - g1[1]) < 1.5) { cam.tx += g0[0] - g1[0]; cam.ty += g0[1] - g1[1]; }
  };
  canvas.addEventListener('pointerdown', e => {
    canvas.setPointerCapture(e.pointerId); pts.set(e.pointerId, local(e)); anim = null; if (M.onGrab) M.onGrab();
    if (pts.size === 1) { moved = 0; downAt = performance.now(); }
    if (pts.size === 2) { const [a, b] = [...pts.values()]; pinch = Math.hypot(a[0] - b[0], a[1] - b[1]); moved = 99; }
    M.onHover(-1);
  });
  canvas.addEventListener('pointermove', e => {
    const p = local(e);
    if (!pts.has(e.pointerId)) {
      if (e.pointerType === 'mouse' && !hoverPending) {
        hoverPending = true;
        requestAnimationFrame(() => { hoverPending = false; if (!pts.size) M.onHover(pickPoint(p[0], p[1], 9), e.clientX, e.clientY); });
      }
      return;
    }
    const q = pts.get(e.pointerId), dx = p[0] - q[0], dy = p[1] - q[1];
    if (pts.size === 1) {
      moved += Math.abs(dx) + Math.abs(dy);
      if (moved > 6) {
        if (M.mode === 'map' || e.shiftKey || (e.buttons & 2)) pan(dx, dy);
        else { cam.az -= dx * 0.006; cam.pol = Math.max(0.02, Math.min(1.5, cam.pol - dy * 0.006)); }
      }
      pts.set(e.pointerId, p);
    } else if (pts.size === 2) {
      pts.set(e.pointerId, p);
      const [a, b] = [...pts.values()], dist = Math.hypot(a[0] - b[0], a[1] - b[1]);
      pan(dx / 2, dy / 2);
      if (pinch > 0 && dist > 0) zoomAt((a[0] + b[0]) / 2, (a[1] + b[1]) / 2, pinch / dist);
      pinch = dist;
    }
    schedule();
  });
  const up = e => {
    if (!pts.has(e.pointerId)) return;
    const p = pts.get(e.pointerId); pts.delete(e.pointerId);
    if (pts.size || moved > 6 || performance.now() - downAt > 600 || e.type === 'pointercancel') return;
    const now = performance.now();
    if (now - lastTap[2] < 320 && Math.hypot(p[0] - lastTap[0], p[1] - lastTap[1]) < 28) {
      const from = { d: cam.d, tx: cam.tx, ty: cam.ty }; zoomAt(p[0], p[1], 0.45); const to = { d: cam.d, tx: cam.tx, ty: cam.ty }; Object.assign(cam, from); animate(to, 350);
      lastTap = [0, 0, 0]; return;
    }
    lastTap = [p[0], p[1], now];
    matrices();
    const i = pickPoint(p[0], p[1], e.pointerType === 'mouse' ? 9 : 16);
    if (i >= 0) return M.selectModule(i);
    const a = pickArea(p[0], p[1]);
    if (a >= 0) M.selectArea(a); else if (M.sel) M.clear();
  };
  canvas.addEventListener('pointerup', up); canvas.addEventListener('pointercancel', up);
  canvas.addEventListener('pointerleave', () => M.onHover(-1));
  canvas.addEventListener('wheel', e => { e.preventDefault(); anim = null; if (M.onGrab) M.onGrab(); zoomAt(...local(e), Math.exp(e.deltaY * 0.0016)); schedule(); }, { passive: false });
  canvas.addEventListener('contextmenu', e => e.preventDefault());
}
})();
