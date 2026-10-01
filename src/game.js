'use strict';
(() => {
// ============================================================
//  RAT PROTO — 2D quarter-view (isometric) roguelike swarm
//  World logic runs in top-down coordinates; rendering projects
//  them to an isometric screen: sx = x - y, sy = (x + y)/2 - z
// ============================================================

const cvs = document.getElementById('game');
const ctx = cvs.getContext('2d');
let W = 0, H = 0, DPR = 1;
function resize() {
  DPR = Math.min(2, window.devicePixelRatio || 1);
  W = innerWidth; H = innerHeight;
  cvs.width = Math.floor(W * DPR); cvs.height = Math.floor(H * DPR);
  cvs.style.width = W + 'px'; cvs.style.height = H + 'px';
}
addEventListener('resize', resize); resize();

// ---------- constants ----------
const TS = 20;            // tile size (world units)
const RI = 19;            // room interior size (tiles)
const P = RI + 1;         // room pitch (interior + 1 wall)
const WALL_H = 18;        // wall height
const CAP = 300;          // max circles
const MAX_TIER = 10;
const G = 900;            // gravity for flying boxes
const TAU = Math.PI * 2;

const TIERS = [
  { c: '#9be15d', d: '#5c9a2c', l: '#d4f7b0' },
  { c: '#4fd6e0', d: '#21909a', l: '#b8f3f7' },
  { c: '#4f86f7', d: '#2a52b0', l: '#b5ccff' },
  { c: '#a46bf2', d: '#6a38b5', l: '#dcc4ff' },
  { c: '#f26bc4', d: '#ad3585', l: '#ffc4ea' },
  { c: '#f2555a', d: '#a8282d', l: '#ffbcbe' },
  { c: '#f29a3d', d: '#b0611a', l: '#ffd8ae' },
  { c: '#f2d43d', d: '#a88f16', l: '#fff3b0' },
  { c: '#f4f4f4', d: '#a8a8b8', l: '#ffffff' },
  { c: '#2b2b3a', d: '#111118', l: '#ffd257' },
];
// ---------- balance knobs (tuned with __rat.sim) ----------
// Sim results (bot keeps 20 per tier, no clicks): ~3–7 min per floor through floor 8,
// top tier rising about one step per floor.
const BAL = {
  dmgGrow: 20,      // damage per tier: DMG(t) = dmgGrow^(t-1) → a 10:1 promotion doubles raw damage
  wallHP: 30,       // floor-1 wall HP (±25%)
  stairHP: 110,     // floor-1 stair wall HP
  floorGrow: 3,     // wall / box / explosion multiplier per floor
  budRate: 0.015,   // solo budding chance per second, per tier (scaled by crowding)
};
const DMG = t => Math.pow(BAL.dmgGrow, t - 1);
const crowd = n => 1 / (1 + n / 25);
// Breeding chance per collision: drops as the population grows, rises with the tiers involved.
//   crowd: 3 circles ≈ 89%, 25 ≈ 50%, 100 ≈ 20%, 300 ≈ 8%
//   tier : +60% per tier above 1, for each of the two circles
const breedChance = (ta, tb, n) => Math.min(0.95, 0.6 * crowd(n) * (1 + 0.6 * (ta - 1 + tb - 1)));
const RADIUS = t => 5 + (t - 1) * 2.6;
// Newborn tier: higher floors give a chance to be born above T1 (rolls upward, capped by floor number).
//   floor 1: always T1 · floor 2: 12% T2 · floor 3: 24% T2, ~6% T3 · ...
const upChance = f => Math.min(0.5, 0.12 * (f - 1));
function babyTier() {
  let t = 1;
  const cap = Math.min(floorN, MAX_TIER);
  while (t < cap && Math.random() < upChance(floorN)) t++;
  return t;
}
const fmt = n => n >= 1e9 ? (n / 1e9).toFixed(n >= 1e10 ? 0 : 1) + 'B' : n >= 1e6 ? (n / 1e6).toFixed(n >= 1e7 ? 0 : 1) + 'M' : n >= 1e3 ? (n / 1e3).toFixed(n >= 1e4 ? 0 : 1) + 'k' : String(Math.round(n));

const rand = (a, b) => a + Math.random() * (b - a);
const randi = (a, b) => Math.floor(rand(a, b + 1));
const clamp = (v, a, b) => v < a ? a : v > b ? b : v;
const pick = arr => arr[Math.floor(Math.random() * arr.length)];

// ---------- state ----------
let floorN = 1, GW, GH, MW, MH, tiles, segOf, segs, rooms, stairRoom, startRoom, stairFound;
let circles = [], boxes = [], parts = [], rings = [], links = [], texts = [];
let wallList = [], brokenTiles = [], visDirty = true;
let speed = 1, paused = false, started = false, autoPromote = false;
let shake = 0, trans = null, T = 0;
let boxTimer = 0, autoTimer = 0;
let rally = null;          // { x, y, life, max } — click-to-rally target
const RALLY_TIME = 3;
const cam = { x: 0, y: 0, z: 1, auto: true };
const scale = () => Math.pow(BAL.floorGrow, floorN - 1);

// ---------- projection ----------
const PX = (x, y) => x - y;
const PY = (x, y, z) => (x + y) * 0.5 - z;

// ============================================================
//  Map generation
// ============================================================
function genFloor() {
  const n = Math.min(3 + floorN, 7);
  GW = n; GH = n;
  MW = GW * P + 1; MH = GH * P + 1;
  tiles = new Uint8Array(MW * MH);
  segOf = new Int32Array(MW * MH).fill(-1);
  rooms = [];
  for (let j = 0; j < GH; j++) for (let i = 0; i < GW; i++) rooms.push({ i, j, explored: false, disc: false });
  segs = [];
  const segMap = new Map();
  for (let ty = 0; ty < MH; ty++) for (let tx = 0; tx < MW; tx++) {
    const vx = tx % P === 0, hy = ty % P === 0;
    if (!vx && !hy) continue;
    const idx = ty * MW + tx;
    if (tx === 0 || ty === 0 || tx === MW - 1 || ty === MH - 1 || (vx && hy)) { tiles[idx] = 2; continue; }
    tiles[idx] = 1;
    let key, a, b;
    if (vx) { const i = tx / P, j = Math.floor(ty / P); key = 'v' + i + '_' + j; a = j * GW + i - 1; b = j * GW + i; }
    else    { const j = ty / P, i = Math.floor(tx / P); key = 'h' + i + '_' + j; a = (j - 1) * GW + i; b = j * GW + i; }
    let id = segMap.get(key);
    if (id === undefined) {
      id = segs.length; segMap.set(key, id);
      segs.push({ a, b, tiles: [], hp: 0, max: 0, stair: false, broken: false, flash: 0 });
    }
    segOf[idx] = id; segs[id].tiles.push(idx);
  }
  startRoom = randi(0, rooms.length - 1);
  const sr = rooms[startRoom];
  const dist = r => Math.abs(r.i - sr.i) + Math.abs(r.j - sr.j);
  let maxD = 0; for (const r of rooms) maxD = Math.max(maxD, dist(r));
  const far = rooms.map((r, k) => k).filter(k => dist(rooms[k]) >= Math.max(2, maxD - 1));
  stairRoom = pick(far);
  stairFound = false;
  const fs = scale();
  for (const s of segs) {
    s.stair = s.a === stairRoom || s.b === stairRoom;
    s.max = s.hp = Math.round((s.stair ? BAL.stairHP : BAL.wallHP * rand(0.75, 1.25)) * fs);
  }
  visDirty = true;
  reveal(startRoom, true);
}

function roomBounds(ri) {
  const r = rooms[ri];
  const x0 = (r.i * P + 1) * TS, y0 = (r.j * P + 1) * TS;
  return { x0, y0, x1: x0 + RI * TS, y1: y0 + RI * TS };
}

function neighbors(ri) {
  const r = rooms[ri], out = [];
  if (r.i > 0) out.push(ri - 1);
  if (r.i < GW - 1) out.push(ri + 1);
  if (r.j > 0) out.push(ri - GW);
  if (r.j < GH - 1) out.push(ri + GW);
  return out;
}

function reveal(ri, silent) {
  const R = rooms[ri];
  if (R.explored || ri === stairRoom) return;
  R.explored = true; R.disc = true; visDirty = true;
  for (const n of neighbors(ri)) {
    rooms[n].disc = true;
    if (n === stairRoom && !stairFound) {
      stairFound = true;
      toast('계단방 발견! 금색 벽을 부수세요');
      chime([523, 659, 784, 1046], 0.08);
    }
  }
  const k = ri === startRoom && silent ? 6 : randi(5, 8);
  for (let i = 0; i < k; i++) spawnBox(ri);
  if (!silent) toast('새로운 방이 열렸다!');
}

// tile visibility: wall tile is drawn if any room adjacent to it is explored
function tileVisible(tx, ty) {
  const is = tx % P === 0 ? [tx / P - 1, tx / P] : [Math.floor(tx / P)];
  const js = ty % P === 0 ? [ty / P - 1, ty / P] : [Math.floor(ty / P)];
  for (const i of is) for (const j of js) {
    if (i < 0 || j < 0 || i >= GW || j >= GH) continue;
    if (rooms[j * GW + i].explored) return true;
  }
  return false;
}
function segVisible(s) {
  return (s.a >= 0 && rooms[s.a].explored) || (s.b >= 0 && rooms[s.b].explored);
}

function rebuildVis() {
  wallList = []; brokenTiles = [];
  for (let ty = 0; ty < MH; ty++) for (let tx = 0; tx < MW; tx++) {
    if (tx % P !== 0 && ty % P !== 0) continue;
    const idx = ty * MW + tx;
    if (!tileVisible(tx, ty)) continue;
    if (tiles[idx] === 0) brokenTiles.push(idx);
    else wallList.push({ tx, ty, idx, d: (tx + ty + 1) * TS });
  }
  wallList.sort((a, b) => a.d - b.d);
  visDirty = false;
}

const isSolid = (tx, ty) => tx < 0 || ty < 0 || tx >= MW || ty >= MH || tiles[ty * MW + tx] !== 0;

// ============================================================
//  Entities
// ============================================================
function newCircle(t, x, y) {
  return {
    x, y, vx: 0, vy: 0, r: RADIUS(t), tier: t, state: 'rest', t: rand(0, 0.4),
    breed: rand(1.5, 3), hitCd: 0, wallCd: 0, phase: rand(0, TAU), dir: rand(0, TAU), dead: false,
  };
}

function spawnBox(ri) {
  const b = roomBounds(ri), m = TS * 1.6;
  for (let tries = 0; tries < 8; tries++) {
    const x = rand(b.x0 + m, b.x1 - m), y = rand(b.y0 + m, b.y1 - m);
    let ok = true;
    for (const o of boxes) if (!o.fly && (o.x - x) ** 2 + (o.y - y) ** 2 < 30 * 30) { ok = false; break; }
    if (!ok) continue;
    const tnt = Math.random() < 0.13;
    const size = tnt ? rand(14, 18) : rand(14, 26);
    const hp = Math.round((tnt ? 3 + size * 0.2 : 4 + size * 0.45) * scale());
    boxes.push({
      x, y, vx: 0, vy: 0, z: 0, vz: 0, size, r: size * 0.55, hp, max: hp, tnt,
      fly: false, rot: rand(0, TAU), vrot: 0, flash: 0, dead: false, born: 0,
    });
    return;
  }
}

function launch(b, nx, ny, power) {
  if (b.fly || b.dead) return;
  b.fly = true;
  const sp = rand(260, 420) * power;
  b.vx = nx * sp; b.vy = ny * sp;
  b.vz = rand(260, 360) * Math.min(1.25, 0.3 + power);
  b.vrot = rand(-12, 12); b.z = 0.5;
  for (let i = 0; i < 6; i++) addPart(b.x, b.y, 4, rand(-60, 60), rand(-60, 60), rand(40, 120), '#c9a46a', 0.4, 2.5, 1);
  blip(220, 0.06, 0.05, 'square');
}

// ============================================================
//  Physics helpers
// ============================================================
function collideTiles(o, rest, onHit) {
  const r = o.r;
  const x0 = Math.floor((o.x - r) / TS), x1 = Math.floor((o.x + r) / TS);
  const y0 = Math.floor((o.y - r) / TS), y1 = Math.floor((o.y + r) / TS);
  for (let ty = y0; ty <= y1; ty++) for (let tx = x0; tx <= x1; tx++) {
    if (!isSolid(tx, ty)) continue;
    const bx = tx * TS, by = ty * TS;
    const cx = clamp(o.x, bx, bx + TS), cy = clamp(o.y, by, by + TS);
    let dx = o.x - cx, dy = o.y - cy;
    const d2 = dx * dx + dy * dy;
    if (d2 >= r * r) continue;
    let nx, ny, pen;
    if (d2 < 1e-8) { // center inside tile: push out along shallowest axis
      const ox = o.x - (bx + TS / 2), oy = o.y - (by + TS / 2);
      if (Math.abs(ox) > Math.abs(oy)) { nx = Math.sign(ox) || 1; ny = 0; pen = TS / 2 - Math.abs(ox) + r; }
      else { nx = 0; ny = Math.sign(oy) || 1; pen = TS / 2 - Math.abs(oy) + r; }
    } else {
      const d = Math.sqrt(d2); nx = dx / d; ny = dy / d; pen = r - d;
    }
    o.x += nx * pen; o.y += ny * pen;
    const vn = o.vx * nx + o.vy * ny;
    if (vn < 0) {
      o.vx -= (1 + rest) * vn * nx; o.vy -= (1 + rest) * vn * ny;
      if (onHit && tx >= 0 && ty >= 0 && tx < MW && ty < MH) onHit(ty * MW + tx, -vn, cx, cy);
    }
  }
}

function damageSeg(id, dmg, x, y) {
  const s = segs[id];
  if (!s || s.broken || !segVisible(s)) return;
  s.hp -= dmg; s.flash = 0.1;
  if (x !== undefined && Math.random() < 0.35) addPart(x, y, rand(4, WALL_H), rand(-50, 50), rand(-50, 50), rand(20, 90), s.stair ? '#f0c040' : '#9aa0ad', 0.45, 2, 1);
  if (s.hp <= 0) breakSeg(s);
}

function breakSeg(s) {
  s.broken = true; s.hp = 0;
  for (const idx of s.tiles) {
    tiles[idx] = 0;
    const x = (idx % MW + 0.5) * TS, y = (Math.floor(idx / MW) + 0.5) * TS;
    for (let k = 0; k < 4; k++) addPart(x, y, rand(0, WALL_H), rand(-120, 120), rand(-120, 120), rand(80, 260), s.stair ? pick(['#f0c040', '#b8862a']) : pick(['#8a8f9c', '#5d626e', '#474b55']), rand(0.6, 1.1), rand(2, 4), 1);
  }
  visDirty = true;
  shake = Math.min(16, shake + 7);
  boom(0.35, 300);
  if (s.stair) { nextFloor(); return; }
  if (s.a >= 0) reveal(s.a);
  if (s.b >= 0) reveal(s.b);
}

function explode(b) {
  const R = (45 + b.size * 2.2) * (b.tnt ? 1.7 : 1);
  const dmg = (6 + b.size * 0.6) * scale() * (b.tnt ? 2.2 : 1);
  shake = Math.min(16, shake + 3 + b.size / 6 + (b.tnt ? 4 : 0));
  boom(b.tnt ? 0.5 : 0.3, b.tnt ? 500 : 800);
  rings.push({ x: b.x, y: b.y, r: 4, max: R, life: 0.35, t: 0.35 });
  const fire = ['#fff3b0', '#ffd257', '#ff9a3d', '#ff5a2b', '#c0392b'];
  const n = b.tnt ? 46 : 26;
  for (let i = 0; i < n; i++) {
    const a = rand(0, TAU), sp = rand(40, R * 3.2);
    addPart(b.x, b.y, rand(0, 10), Math.cos(a) * sp, Math.sin(a) * sp, rand(60, 240), pick(fire), rand(0.25, 0.6), rand(2, 5), 0.6);
  }
  for (let i = 0; i < 10; i++) addPart(b.x + rand(-R, R) * 0.3, b.y + rand(-R, R) * 0.3, rand(4, 16), rand(-20, 20), rand(-20, 20), rand(20, 60), 'rgba(80,80,90,0.7)', rand(0.6, 1.1), rand(5, 9), -0.05);

  // boxes
  for (const o of boxes) {
    if (o === b || o.fly || o.dead) continue;
    const dx = o.x - b.x, dy = o.y - b.y, d = Math.hypot(dx, dy) || 0.01;
    if (d > R + o.r) continue;
    const fall = 1 - 0.5 * d / (R + o.r);
    o.hp -= dmg * fall; o.flash = 0.12;
    const nx = dx / d, ny = dy / d;
    if (o.hp <= 0) launch(o, nx, ny, 0.8 + fall * 0.5);
    else { o.vx += nx * 160 * fall; o.vy += ny * 160 * fall; }
  }
  // circles (knockback only)
  for (const c of circles) {
    const dx = c.x - b.x, dy = c.y - b.y, d = Math.hypot(dx, dy) || 0.01;
    if (d > R) continue;
    const f = (1 - d / R) * 420;
    c.vx += dx / d * f; c.vy += dy / d * f;
  }
  // walls
  const hit = new Set();
  const tx0 = Math.floor((b.x - R) / TS), tx1 = Math.floor((b.x + R) / TS);
  const ty0 = Math.floor((b.y - R) / TS), ty1 = Math.floor((b.y + R) / TS);
  for (let ty = Math.max(0, ty0); ty <= Math.min(MH - 1, ty1); ty++)
    for (let tx = Math.max(0, tx0); tx <= Math.min(MW - 1, tx1); tx++) {
      const idx = ty * MW + tx;
      if (tiles[idx] !== 1) continue;
      const cx = (tx + 0.5) * TS, cy = (ty + 0.5) * TS;
      if ((cx - b.x) ** 2 + (cy - b.y) ** 2 < (R + TS * 0.5) ** 2) hit.add(segOf[idx]);
    }
  for (const id of hit) damageSeg(id, dmg);
}

// ============================================================
//  Promotion
// ============================================================
function promote(t) {
  if (t >= MAX_TIER) return false;
  const list = circles.filter(c => c.tier === t && !c.dead);
  if (list.length < 10) return false;
  const a = list[Math.floor(Math.random() * list.length)];
  list.sort((p, q) => ((p.x - a.x) ** 2 + (p.y - a.y) ** 2) - ((q.x - a.x) ** 2 + (q.y - a.y) ** 2));
  const g = list.slice(0, 10);
  for (const c of g) {
    c.dead = true;
    links.push({ x1: c.x, y1: c.y, x2: a.x, y2: a.y, life: 0.5, t: 0.5, col: TIERS[t - 1].c });
  }
  circles = circles.filter(c => !c.dead);
  const n = newCircle(t + 1, a.x, a.y);
  n.breed = 1.5;
  circles.push(n);
  rings.push({ x: a.x, y: a.y, r: 2, max: 40, life: 0.45, t: 0.45, col: TIERS[t].c });
  for (let i = 0; i < 18; i++) {
    const ang = rand(0, TAU), sp = rand(30, 140);
    addPart(a.x, a.y, rand(4, 16), Math.cos(ang) * sp, Math.sin(ang) * sp, rand(80, 200), TIERS[t].l, rand(0.4, 0.8), 2.5, 0.5);
  }
  chime([440 + t * 40, 660 + t * 40], 0.05);
  addText(a.x, a.y, 24, 'T' + (t + 1) + '!  공격 ' + fmt(DMG(t + 1)), TIERS[t].l, 14 + t);
  shake = Math.min(16, shake + 2 + t);
  return true;
}

// ============================================================
//  Simulation step
// ============================================================
const grid = new Map();
const CELL = 32;
function gkey(cx, cy) { return (cx + 1024) * 4096 + (cy + 1024); }

function step(dt) {
  T += dt;
  if (rally && (rally.life -= dt) <= 0) rally = null;
  // ---- circles: rat-like dash AI ----
  const buds = [];
  for (const c of circles) {
    c.breed -= dt; c.hitCd -= dt; c.wallCd -= dt; c.t -= dt;
    // solo budding: keeps tiny populations alive, and higher tiers bud more often
    if (c.breed <= 0 && circles.length + buds.length < CAP && Math.random() < BAL.budRate * c.tier * crowd(circles.length) * dt) {
      const bt = babyTier(), baby = newCircle(bt, c.x + rand(-3, 3), c.y + rand(-3, 3));
      baby.breed = rand(4, 6); buds.push(baby);
      c.breed = rand(3.5, 5.5);
      for (let k = 0; k < 5; k++) addPart(c.x, c.y, 6, rand(-50, 50), rand(-50, 50), rand(60, 140), '#ffb3d9', 0.45, 2, 0.8);
    }
    if (c.t <= 0) {
      if (c.state === 'dash') { c.state = 'rest'; c.t = rally ? rand(0.08, 0.25) : rand(0.3, 0.9); }
      else {
        c.state = 'dash';
        let a = rand(0, TAU), sp = rand(120, 200) * (1 + 0.04 * (c.tier - 1)), len = rand(30, 100);
        if (rally) {
          // rush toward the rally point with a little rat-like jitter
          const dx = rally.x - c.x, dy = rally.y - c.y, d = Math.hypot(dx, dy);
          if (d > 30) {
            a = Math.atan2(dy, dx) + rand(-0.45, 0.45);
            sp *= 1.4; len = Math.min(d + 20, rand(60, 140));
          }
        } else if (Math.random() < 0.3 && circles.length > 1) {
          // rats like company: sometimes scurry toward a nearby friend
          const o = circles[Math.floor(Math.random() * circles.length)];
          const dx = o.x - c.x, dy = o.y - c.y, d2 = dx * dx + dy * dy;
          if (o !== c && d2 < 260 * 260) a = Math.atan2(dy, dx) + rand(-0.6, 0.6);
        }
        c.vx = Math.cos(a) * sp; c.vy = Math.sin(a) * sp;
        c.t = len / sp;
      }
    }
    if (c.state === 'rest') { const f = Math.pow(0.0005, dt); c.vx *= f; c.vy *= f; }
    else c.phase += dt * 28;
    const sp2 = c.vx * c.vx + c.vy * c.vy;
    if (sp2 > 400) c.dir = Math.atan2(c.vy, c.vx);
    if (sp2 > 600 * 600) { const k = 600 / Math.sqrt(sp2); c.vx *= k; c.vy *= k; }
    c.x += c.vx * dt; c.y += c.vy * dt;
  }

  for (const b of buds) circles.push(b);

  // ---- spatial hash ----
  grid.clear();
  for (let i = 0; i < circles.length; i++) {
    const c = circles[i];
    const k = gkey(Math.floor(c.x / CELL), Math.floor(c.y / CELL));
    let cell = grid.get(k); if (!cell) { cell = []; grid.set(k, cell); } cell.push(i);
  }

  // ---- circle vs circle (bounce + breeding) ----
  const born = [];
  for (let i = 0; i < circles.length; i++) {
    const a = circles[i];
    const cx = Math.floor(a.x / CELL), cy = Math.floor(a.y / CELL);
    for (let oy = -1; oy <= 1; oy++) for (let ox = -1; ox <= 1; ox++) {
      const cell = grid.get(gkey(cx + ox, cy + oy)); if (!cell) continue;
      for (const j of cell) {
        if (j <= i) continue;
        const b = circles[j];
        const dx = b.x - a.x, dy = b.y - a.y, rr = a.r + b.r, d2 = dx * dx + dy * dy;
        if (d2 >= rr * rr || d2 < 1e-6) continue;
        const d = Math.sqrt(d2), nx = dx / d, ny = dy / d, pen = rr - d;
        const ma = a.r * a.r, mb = b.r * b.r, tot = ma + mb;
        a.x -= nx * pen * mb / tot; a.y -= ny * pen * mb / tot;
        b.x += nx * pen * ma / tot; b.y += ny * pen * ma / tot;
        const rv = (b.vx - a.vx) * nx + (b.vy - a.vy) * ny;
        if (rv < 0) {
          const jj = -1.8 * rv / (1 / ma + 1 / mb);
          a.vx -= jj * nx / ma; a.vy -= jj * ny / ma;
          b.vx += jj * nx / mb; b.vy += jj * ny / mb;
        }
        if (a.breed <= 0 && b.breed <= 0 && circles.length + born.length < CAP) {
          // every collision is a breeding *attempt*; failed attempts still cost a short cooldown
          if (Math.random() >= breedChance(a.tier, b.tier, circles.length + born.length)) {
            a.breed = rand(0.8, 1.4); b.breed = rand(0.8, 1.4);
            continue;
          }
          const mx = (a.x + b.x) / 2, my = (a.y + b.y) / 2;
          const bt = babyTier();
          const baby = newCircle(bt, mx + rand(-2, 2), my + rand(-2, 2));
          if (bt > 1) {
            rings.push({ x: mx, y: my, r: 2, max: 18 + bt * 6, life: 0.4, t: 0.4, col: TIERS[bt - 1].c });
            addText(mx, my, 14, 'T' + bt + ' 탄생!', TIERS[bt - 1].l, 12);
          }
          baby.breed = rand(4, 6);
          born.push(baby);
          a.breed = rand(3.5, 5.5); b.breed = rand(3.5, 5.5);
          for (let k = 0; k < 5; k++) addPart(mx, my, 6, rand(-50, 50), rand(-50, 50), rand(60, 140), '#ffb3d9', 0.45, 2, 0.8);
          blip(rand(900, 1300), 0.04, 0.025, 'sine');
        }
      }
    }
  }
  for (const b of born) circles.push(b);

  // ---- circle vs walls ----
  for (const c of circles) {
    collideTiles(c, 0.9, (idx, imp, hx, hy) => {
      if (tiles[idx] === 1 && c.wallCd <= 0) {
        damageSeg(segOf[idx], DMG(c.tier), hx, hy);
        hitFx(c, hx, hy, WALL_H * 0.6);
        c.wallCd = 0.12;
      }
    });
  }

  // ---- circle vs ground boxes ----
  for (const b of boxes) {
    if (b.fly || b.dead) continue;
    const reach = b.r + 18;
    const cx0 = Math.floor((b.x - reach) / CELL), cx1 = Math.floor((b.x + reach) / CELL);
    const cy0 = Math.floor((b.y - reach) / CELL), cy1 = Math.floor((b.y + reach) / CELL);
    for (let gy = cy0; gy <= cy1 && !b.fly; gy++) for (let gx = cx0; gx <= cx1 && !b.fly; gx++) {
      const cell = grid.get(gkey(gx, gy)); if (!cell) continue;
      for (const i of cell) {
        const c = circles[i]; if (!c) continue;
        const dx = b.x - c.x, dy = b.y - c.y, rr = b.r + c.r, d2 = dx * dx + dy * dy;
        if (d2 >= rr * rr || d2 < 1e-6) continue;
        const d = Math.sqrt(d2), nx = dx / d, ny = dy / d, pen = rr - d;
        c.x -= nx * pen * 0.85; c.y -= ny * pen * 0.85;
        b.x += nx * pen * 0.15; b.y += ny * pen * 0.15;
        const vn = c.vx * nx + c.vy * ny;
        if (vn > 0) {
          c.vx -= 1.8 * vn * nx; c.vy -= 1.8 * vn * ny;
          b.vx += nx * vn * 0.08 * c.r / 5; b.vy += ny * vn * 0.08 * c.r / 5;
        }
        if (c.hitCd <= 0) {
          c.hitCd = 0.15;
          b.hp -= DMG(c.tier); b.flash = 0.08;
          hitFx(c, b.x - nx * b.r, b.y - ny * b.r, b.size * 0.6);
          if (Math.random() < 0.3) addPart(b.x - nx * b.r, b.y - ny * b.r, rand(4, b.size), rand(-40, 40), rand(-40, 40), rand(30, 90), '#d9b47a', 0.35, 2, 1);
          if (b.hp <= 0) { launch(b, nx, ny, 1 + 0.15 * (c.tier - 1)); break; } // flies away from the hitter, harder for high tiers
        }
      }
    }
  }

  // ---- boxes ----
  for (const b of boxes) {
    if (b.dead) continue;
    b.flash -= dt; b.born += dt;
    if (b.fly) {
      const sub = 3;
      for (let s = 0; s < sub; s++) {
        b.x += b.vx * dt / sub; b.y += b.vy * dt / sub;
        collideTiles(b, 0.7, (idx, imp, hx, hy) => {
          if (tiles[idx] === 1) damageSeg(segOf[idx], (2 + b.size * 0.2) * scale(), hx, hy);
          blip(160, 0.05, 0.04, 'triangle');
        });
      }
      b.vz -= G * dt; b.z += b.vz * dt; b.rot += b.vrot * dt;
      if (b.z <= 0) { b.z = 0; b.dead = true; explode(b); }
    } else {
      const f = Math.pow(0.03, dt); b.vx *= f; b.vy *= f;
      b.x += b.vx * dt; b.y += b.vy * dt;
      collideTiles(b, 0.3);
    }
  }
  // ground box separation
  for (let i = 0; i < boxes.length; i++) {
    const a = boxes[i]; if (a.fly || a.dead) continue;
    for (let j = i + 1; j < boxes.length; j++) {
      const b = boxes[j]; if (b.fly || b.dead) continue;
      const dx = b.x - a.x, dy = b.y - a.y, rr = a.r + b.r, d2 = dx * dx + dy * dy;
      if (d2 >= rr * rr || d2 < 1e-6) continue;
      const d = Math.sqrt(d2), pen = (rr - d) / 2, nx = dx / d, ny = dy / d;
      a.x -= nx * pen; a.y -= ny * pen; b.x += nx * pen; b.y += ny * pen;
    }
  }
  if (boxes.some(b => b.dead)) boxes = boxes.filter(b => !b.dead);

  for (const s of segs) if (s.flash > 0) s.flash -= dt;

  // ---- box spawning ----
  boxTimer -= dt;
  if (boxTimer <= 0) {
    boxTimer = 1.6;
    const ex = rooms.map((r, k) => k).filter(k => rooms[k].explored);
    const ground = boxes.filter(b => !b.fly).length;
    if (ground < Math.min(90, ex.length * 7)) spawnBox(pick(ex));
  }

  // ---- auto promote ----
  if (autoPromote) {
    autoTimer -= dt;
    if (autoTimer <= 0) {
      autoTimer = 0.4;
      // keep a breeding reserve of 20 per tier (promoting ASAP starves breeding);
      // near the population cap, promote anything with 10+ to free space
      const cnt = new Array(MAX_TIER + 1).fill(0); for (const c of circles) cnt[c.tier]++;
      const need = circles.length >= CAP * 0.9 ? 10 : 30;
      for (let t = 1; t < MAX_TIER; t++) if (cnt[t] >= need && promote(t)) break;
    }
  }

  // ---- fx ----
  for (const p of parts) {
    p.life -= dt;
    p.x += p.vx * dt; p.y += p.vy * dt; p.z += p.vz * dt;
    p.vz -= 700 * p.g * dt;
    if (p.z < 0) { p.z = 0; p.vz *= -0.35; p.vx *= 0.6; p.vy *= 0.6; }
    if (p.g < 0) { p.vx *= 0.97; p.vy *= 0.97; }
  }
  if (parts.length) parts = parts.filter(p => p.life > 0);
  for (const r of rings) { r.life -= dt; }
  if (rings.length) rings = rings.filter(r => r.life > 0);
  for (const l of links) l.life -= dt;
  if (links.length) links = links.filter(l => l.life > 0);
  for (const t of texts) { t.life -= dt; t.z += t.vz * dt; t.vz *= Math.pow(0.1, dt); }
  if (texts.length) texts = texts.filter(t => t.life > 0);
}

// Per-hit feedback that scales with tier so promotions are visibly stronger.
function hitFx(c, x, y, z) {
  const t = c.tier, dmg = DMG(t);
  if (t >= 2) {
    rings.push({ x, y, r: 2, max: 6 + t * 5, life: 0.22, t: 0.22, col: TIERS[t - 1].l });
    for (let k = 0; k < t + 1; k++) addPart(x, y, z, rand(-1, 1) * 60 * t, rand(-1, 1) * 60 * t, rand(40, 120), TIERS[t - 1].l, 0.35, 1.5 + t * 0.4, 1);
    shake = Math.min(16, shake + 0.25 * (t - 1));
    blip(Math.max(70, 420 - t * 45), 0.07, 0.02 + 0.008 * t, 'square');
    addText(x, y, z + 6, fmt(dmg), TIERS[t - 1].l, 8 + t * 2);
  } else if (Math.random() < 0.12) {
    addText(x, y, z + 6, fmt(dmg), 'rgba(220,230,220,0.8)', 8);
  }
}
function addText(x, y, z, text, col, size) {
  if (texts.length > 120) texts.shift();
  texts.push({ x: x + rand(-4, 4), y: y + rand(-4, 4), z, vz: 60, text, col, size, life: 0.8, max: 0.8 });
}

function addPart(x, y, z, vx, vy, vz, col, life, s, g) {
  if (parts.length > 1800) return;
  parts.push({ x, y, z, vx, vy, vz, col, life, max: life, s, g });
}

// ============================================================
//  Floor transition
// ============================================================
function nextFloor() {
  if (trans) return;
  trans = { t: 0, done: false };
  chime([392, 523, 659, 784, 1046], 0.09);
}
function updateTrans(dt) {
  trans.t += dt;
  if (trans.t >= 0.8 && !trans.done) {
    trans.done = true;
    floorN++;
    boxes = []; parts = []; rings = []; links = []; texts = []; rally = null;
    genFloor();
    placeCircles();
    cam.auto = true; snapCamera();
    banner(floorN + '층');
  }
  if (trans.t >= 1.6) trans = null;
}
function placeCircles() {
  const b = roomBounds(startRoom);
  for (const c of circles) {
    c.x = rand(b.x0 + c.r + 4, b.x1 - c.r - 4);
    c.y = rand(b.y0 + c.r + 4, b.y1 - c.r - 4);
    c.vx = c.vy = 0; c.state = 'rest'; c.t = rand(0.2, 0.8);
  }
}

// ============================================================
//  Rendering
// ============================================================
function hexToRgb(h) { const n = parseInt(h.slice(1), 16); return [(n >> 16) & 255, (n >> 8) & 255, n & 255]; }
function mix(a, b, t) { return 'rgb(' + Math.round(a[0] + (b[0] - a[0]) * t) + ',' + Math.round(a[1] + (b[1] - a[1]) * t) + ',' + Math.round(a[2] + (b[2] - a[2]) * t) + ')'; }

const WALL = { top: hexToRgb('#9096a4'), left: hexToRgb('#646a77'), right: hexToRgb('#4b505b') };
const WALL_DMG = { top: hexToRgb('#5a3c34'), left: hexToRgb('#3d2824'), right: hexToRgb('#2e1e1b') };
const STAIR = { top: hexToRgb('#f3c845'), left: hexToRgb('#bb8a2a'), right: hexToRgb('#8f6620') };
const STAIR_DMG = { top: hexToRgb('#7a4e18'), left: hexToRgb('#553510'), right: hexToRgb('#40280c') };

function poly(pts) {
  ctx.beginPath(); ctx.moveTo(pts[0], pts[1]);
  for (let i = 2; i < pts.length; i += 2) ctx.lineTo(pts[i], pts[i + 1]);
  ctx.closePath();
}

// Generic square prism (box/wall) in iso. Corners rotated by rot around (cx,cy).
const _c = new Float64Array(8);
function prism(cx, cy, z0, half, rot, h, top, left, right, outline) {
  const rr = half * Math.SQRT2;
  for (let k = 0; k < 4; k++) {
    const a = rot + Math.PI / 4 + k * Math.PI / 2;
    _c[k * 2] = cx + Math.cos(a) * rr; _c[k * 2 + 1] = cy + Math.sin(a) * rr;
  }
  for (let k = 0; k < 4; k++) {
    const ax = _c[k * 2], ay = _c[k * 2 + 1], bx = _c[((k + 1) % 4) * 2], by = _c[((k + 1) % 4) * 2 + 1];
    const nx = (ax + bx) / 2 - cx, ny = (ay + by) / 2 - cy;
    if (nx + ny <= 0.001) continue;
    ctx.fillStyle = nx > ny ? right : left;
    poly([PX(ax, ay), PY(ax, ay, z0), PX(bx, by), PY(bx, by, z0), PX(bx, by), PY(bx, by, z0 + h), PX(ax, ay), PY(ax, ay, z0 + h)]);
    ctx.fill();
  }
  ctx.fillStyle = top;
  poly([PX(_c[0], _c[1]), PY(_c[0], _c[1], z0 + h), PX(_c[2], _c[3]), PY(_c[2], _c[3], z0 + h),
        PX(_c[4], _c[5]), PY(_c[4], _c[5], z0 + h), PX(_c[6], _c[7]), PY(_c[6], _c[7], z0 + h)]);
  ctx.fill();
  if (outline) { ctx.strokeStyle = outline; ctx.lineWidth = 1; ctx.stroke(); }
}

function rectDiamond(x0, y0, x1, y1, z) {
  poly([PX(x0, y0), PY(x0, y0, z), PX(x1, y0), PY(x1, y0, z), PX(x1, y1), PY(x1, y1, z), PX(x0, y1), PY(x0, y1, z)]);
}

function ellipse(x, y, z, r) {
  ctx.beginPath();
  ctx.ellipse(PX(x, y), PY(x, y, z), r * Math.SQRT2, r * Math.SQRT2 * 0.5, 0, 0, TAU);
}

function floorColors() {
  const hue = (210 + (floorN - 1) * 47) % 360;
  return {
    floor: `hsl(${hue},18%,24%)`, floor2: `hsl(${hue},18%,21%)`, line: `hsla(${hue},30%,70%,0.06)`,
    fog: `hsl(${hue},20%,9%)`, fogDisc: `hsl(${hue},16%,13%)`, bg: `hsl(${hue},25%,6%)`,
  };
}

function drawWall(w) {
  const t = tiles[w.idx];
  const x = (w.tx + 0.5) * TS, y = (w.ty + 0.5) * TS;
  if (t === 2) {
    prism(x, y, 0, TS / 2, 0, WALL_H + 4, '#5a6072', '#3c414f', '#2e323d');
    return;
  }
  const s = segs[segOf[w.idx]];
  const stair = s.stair && rooms[stairRoom].disc;
  const P1 = stair ? STAIR : WALL, P2 = stair ? STAIR_DMG : WALL_DMG;
  const k = 1 - s.hp / s.max;
  const topC = s.flash > 0 ? hexToRgb(stair ? '#fff0b8' : '#c8ccd6') : P1.top;
  prism(x, y, 0, TS / 2, 0, WALL_H, mix(topC, P2.top, k * 0.8), mix(P1.left, P2.left, k), mix(P1.right, P2.right, k));
  if (k > 0.35) { // cracks
    ctx.strokeStyle = 'rgba(0,0,0,0.45)'; ctx.lineWidth = 1;
    const sx = PX(x, y), sy = PY(x, y, WALL_H);
    const seed = (w.idx * 9301 + 49297) % 233280 / 233280;
    ctx.beginPath(); ctx.moveTo(sx - 6 + seed * 4, sy - 2); ctx.lineTo(sx, sy + 1); ctx.lineTo(sx + 5, sy - 1 + seed * 3);
    if (k > 0.65) { ctx.moveTo(sx, sy + 1); ctx.lineTo(sx - 1, sy + 5 + seed * 6); }
    ctx.stroke();
  }
}

function drawCircle(c) {
  const T0 = TIERS[c.tier - 1];
  const hop = c.state === 'dash' ? Math.abs(Math.sin(c.phase)) * (2 + c.r * 0.2) : 0;
  const sx = PX(c.x, c.y), gy = PY(c.x, c.y, 0), by = gy - c.r - hop;
  // shadow
  ctx.fillStyle = 'rgba(0,0,0,0.32)';
  ctx.beginPath(); ctx.ellipse(sx, gy, c.r * 1.05, c.r * 0.5, 0, 0, TAU); ctx.fill();
  // body
  ctx.fillStyle = T0.d;
  ctx.beginPath(); ctx.arc(sx, by, c.r, 0, TAU); ctx.fill();
  ctx.fillStyle = T0.c;
  ctx.beginPath(); ctx.arc(sx - c.r * 0.12, by - c.r * 0.12, c.r * 0.85, 0, TAU); ctx.fill();
  ctx.fillStyle = T0.l;
  ctx.beginPath(); ctx.arc(sx - c.r * 0.38, by - c.r * 0.4, c.r * 0.28, 0, TAU); ctx.fill();
  // eye looking in movement direction (projected)
  const ex = Math.cos(c.dir), ey = Math.sin(c.dir);
  const pdx = (ex - ey), pdy = (ex + ey) * 0.5;
  const pl = Math.hypot(pdx, pdy) || 1;
  ctx.fillStyle = c.tier === 10 ? '#ffd257' : '#15161c';
  ctx.beginPath(); ctx.arc(sx + pdx / pl * c.r * 0.55, by + pdy / pl * c.r * 0.45, Math.max(1.1, c.r * 0.17), 0, TAU); ctx.fill();
  if (c.tier >= 2) {
    ctx.strokeStyle = 'rgba(255,255,255,0.35)'; ctx.lineWidth = 1;
    ctx.beginPath(); ctx.arc(sx, by, c.r + 0.5, 0, TAU); ctx.stroke();
  }
}

function drawBox(b) {
  const half = b.size / 2;
  const top = b.flash > 0 ? '#ffffff' : b.tnt ? '#e8584a' : '#c9995a';
  const left = b.tnt ? '#a8322a' : '#8f6535';
  const right = b.tnt ? '#7d241e' : '#6e4c27';
  if (b.fly) {
    const sr = half * clamp(1 - b.z / 400, 0.4, 1);
    ctx.fillStyle = `rgba(0,0,0,${clamp(0.35 - b.z / 900, 0.1, 0.35)})`;
    ellipse(b.x, b.y, 0, sr); ctx.fill();
  } else {
    ctx.fillStyle = 'rgba(0,0,0,0.3)';
    ellipse(b.x + 2, b.y + 2, 0, half * 1.05); ctx.fill();
  }
  const pop = b.born < 0.25 ? b.born / 0.25 : 1;
  prism(b.x, b.y, b.z, half * pop, b.rot, b.size * 0.9 * pop, top, left, right, 'rgba(0,0,0,0.25)');
  if (!b.fly && pop === 1) {
    // crate cross / TNT mark on top
    const z = b.size * 0.9;
    ctx.strokeStyle = b.tnt ? 'rgba(255,230,120,0.8)' : 'rgba(90,60,25,0.6)'; ctx.lineWidth = 1.2;
    const k = half * 0.75, cr = Math.cos(b.rot), sr = Math.sin(b.rot);
    const pt = (u, v) => [b.x + u * cr - v * sr, b.y + u * sr + v * cr];
    const p1 = pt(-k, -k), p2 = pt(k, k), p3 = pt(k, -k), p4 = pt(-k, k);
    ctx.beginPath();
    ctx.moveTo(PX(p1[0], p1[1]), PY(p1[0], p1[1], z)); ctx.lineTo(PX(p2[0], p2[1]), PY(p2[0], p2[1], z));
    ctx.moveTo(PX(p3[0], p3[1]), PY(p3[0], p3[1], z)); ctx.lineTo(PX(p4[0], p4[1]), PY(p4[0], p4[1], z));
    ctx.stroke();
    if (b.hp < b.max) {
      const sx = PX(b.x, b.y), sy = PY(b.x, b.y, b.size * 0.9) - half - 6;
      ctx.fillStyle = 'rgba(0,0,0,0.6)'; ctx.fillRect(sx - 12, sy, 24, 3.5);
      ctx.fillStyle = b.tnt ? '#ff8a5b' : '#7ee07e'; ctx.fillRect(sx - 12, sy, 24 * Math.max(0, b.hp / b.max), 3.5);
    }
  }
}

function drawStairIcon(ri, glow) {
  const b = roomBounds(ri);
  const cx = (b.x0 + b.x1) / 2, cy = (b.y0 + b.y1) / 2;
  for (let k = 0; k < 4; k++) {
    const h = 6 + k * 8, off = (k - 1.5) * 18;
    prism(cx + off, cy - off * 0.0 + 0, 0, 14, 0, h, `rgba(243,200,69,${0.55 * glow})`, `rgba(187,138,42,${0.55 * glow})`, `rgba(143,102,32,${0.55 * glow})`);
  }
}

function render() {
  const C = floorColors();
  ctx.setTransform(DPR, 0, 0, DPR, 0, 0);
  ctx.fillStyle = C.bg; ctx.fillRect(0, 0, W, H);
  if (!tiles) return;
  if (visDirty) rebuildVis();

  const shx = shake > 0 ? rand(-shake, shake) : 0, shy = shake > 0 ? rand(-shake, shake) * 0.6 : 0;
  ctx.setTransform(DPR * cam.z, 0, 0, DPR * cam.z, DPR * (W / 2 - cam.x * cam.z + shx), DPR * (H / 2 - cam.y * cam.z + shy));

  // ---- floors ----
  for (let ri = 0; ri < rooms.length; ri++) {
    const R = rooms[ri], b = roomBounds(ri);
    if (R.explored) {
      ctx.fillStyle = C.floor; rectDiamond(b.x0, b.y0, b.x1, b.y1, 0); ctx.fill();
      // checker tiles
      ctx.fillStyle = C.floor2;
      ctx.beginPath();
      for (let ty = 0; ty < RI; ty++) for (let tx = (ty & 1); tx < RI; tx += 2) {
        const x0 = b.x0 + tx * TS, y0 = b.y0 + ty * TS, x1 = x0 + TS, y1 = y0 + TS;
        ctx.moveTo(PX(x0, y0), PY(x0, y0, 0)); ctx.lineTo(PX(x1, y0), PY(x1, y0, 0));
        ctx.lineTo(PX(x1, y1), PY(x1, y1, 0)); ctx.lineTo(PX(x0, y1), PY(x0, y1, 0)); ctx.closePath();
      }
      ctx.fill();
    } else if (R.disc) {
      ctx.fillStyle = ri === stairRoom ? '#2a2210' : C.fogDisc;
      rectDiamond(b.x0 - TS, b.y0 - TS, b.x1 + TS, b.y1 + TS, 0); ctx.fill();
      const cx = (b.x0 + b.x1) / 2, cy = (b.y0 + b.y1) / 2;
      if (ri === stairRoom) {
        const glow = 0.6 + 0.4 * Math.sin(T * 3);
        drawStairIcon(ri, glow);
        ctx.fillStyle = `rgba(255,210,87,${0.7 + 0.3 * glow})`;
        ctx.font = 'bold 16px system-ui, sans-serif'; ctx.textAlign = 'center';
        ctx.fillText('계단', PX(cx, cy), PY(cx, cy, 52));
      } else {
        ctx.fillStyle = 'rgba(255,255,255,0.12)';
        ctx.font = 'bold 34px system-ui, sans-serif'; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
        ctx.fillText('?', PX(cx, cy), PY(cx, cy, 0));
        ctx.textBaseline = 'alphabetic';
      }
    } else {
      ctx.fillStyle = C.fog; rectDiamond(b.x0 - TS, b.y0 - TS, b.x1 + TS, b.y1 + TS, 0); ctx.fill();
    }
  }
  // broken wall gaps -> floor
  ctx.fillStyle = C.floor;
  for (const idx of brokenTiles) {
    const tx = idx % MW, ty = Math.floor(idx / MW);
    rectDiamond(tx * TS - 0.5, ty * TS - 0.5, (tx + 1) * TS + 0.5, (ty + 1) * TS + 0.5, 0); ctx.fill();
  }

  // ---- explosion rings on ground ----
  for (const r of rings) {
    const k = 1 - r.life / r.t;
    const rad = r.r + (r.max - r.r) * Math.sqrt(k);
    ctx.strokeStyle = r.col || `rgba(255,190,90,${1 - k})`;
    ctx.globalAlpha = r.col ? 1 - k : 1;
    ctx.lineWidth = 3 * (1 - k) + 1;
    ellipse(r.x, r.y, 0, rad); ctx.stroke();
    if (!r.col) { ctx.fillStyle = `rgba(255,140,60,${0.25 * (1 - k)})`; ctx.fill(); }
    ctx.globalAlpha = 1;
  }

  // ---- rally marker ----
  if (rally) {
    const k = rally.life / rally.max, pulse = (T * 2.5) % 1;
    ctx.globalAlpha = Math.min(1, k * 2);
    ctx.strokeStyle = '#7fd7ff'; ctx.lineWidth = 2;
    ellipse(rally.x, rally.y, 0, 14); ctx.stroke();
    ctx.globalAlpha = Math.min(1, k * 2) * (1 - pulse);
    ellipse(rally.x, rally.y, 0, 14 + pulse * 26); ctx.stroke();
    ctx.globalAlpha = Math.min(1, k * 2);
    const sx = PX(rally.x, rally.y), sy = PY(rally.x, rally.y, 0);
    const bob = Math.sin(T * 8) * 3;
    ctx.fillStyle = '#7fd7ff';
    ctx.beginPath(); ctx.moveTo(sx, sy - 8 + bob); ctx.lineTo(sx - 7, sy - 20 + bob); ctx.lineTo(sx + 7, sy - 20 + bob); ctx.closePath(); ctx.fill();
    ctx.globalAlpha = 1;
  }

  // ---- depth-sorted: walls + entities ----
  const dyn = [];
  for (const b of boxes) dyn.push({ d: b.x + b.y + (b.fly ? 0 : b.r), o: b, k: 1 });
  for (const c of circles) dyn.push({ d: c.x + c.y, o: c, k: 0 });
  dyn.sort((a, b) => a.d - b.d);
  let wi = 0;
  for (const e of dyn) {
    while (wi < wallList.length && wallList[wi].d <= e.d) drawWall(wallList[wi++]);
    if (e.k === 0) drawCircle(e.o); else drawBox(e.o);
  }
  while (wi < wallList.length) drawWall(wallList[wi++]);

  // ---- wall HP bars ----
  for (const s of segs) {
    if (s.broken || s.hp >= s.max || !segVisible(s)) continue;
    const idx = s.tiles[Math.floor(s.tiles.length / 2)];
    const x = (idx % MW + 0.5) * TS, y = (Math.floor(idx / MW) + 0.5) * TS;
    const sx = PX(x, y), sy = PY(x, y, WALL_H + 12);
    ctx.fillStyle = 'rgba(0,0,0,0.65)'; ctx.fillRect(sx - 22, sy, 44, 5);
    ctx.fillStyle = s.stair ? '#ffd257' : '#ff6b5b';
    ctx.fillRect(sx - 22, sy, 44 * Math.max(0, s.hp / s.max), 5);
  }

  // ---- particles ----
  for (const p of parts) {
    const a = clamp(p.life / p.max, 0, 1);
    ctx.globalAlpha = a;
    ctx.fillStyle = p.col;
    const s = p.s * (p.g < 0 ? 2 - a : 1);
    ctx.fillRect(PX(p.x, p.y) - s / 2, PY(p.x, p.y, p.z) - s / 2, s, s);
  }
  ctx.globalAlpha = 1;

  // ---- damage numbers ----
  ctx.textAlign = 'center'; ctx.lineJoin = 'round';
  for (const t of texts) {
    ctx.globalAlpha = clamp(t.life / t.max * 1.6, 0, 1);
    ctx.font = `900 ${t.size}px system-ui, sans-serif`;
    const sx = PX(t.x, t.y), sy = PY(t.x, t.y, t.z);
    ctx.lineWidth = 3; ctx.strokeStyle = 'rgba(0,0,0,0.7)'; ctx.strokeText(t.text, sx, sy);
    ctx.fillStyle = t.col; ctx.fillText(t.text, sx, sy);
  }
  ctx.globalAlpha = 1;

  // ---- promotion links ----
  for (const l of links) {
    const k = l.life / l.t;
    ctx.strokeStyle = l.col; ctx.globalAlpha = k; ctx.lineWidth = 2;
    const mx = l.x2 + (l.x1 - l.x2) * k, my = l.y2 + (l.y1 - l.y2) * k;
    ctx.beginPath(); ctx.moveTo(PX(mx, my), PY(mx, my, 8)); ctx.lineTo(PX(l.x2, l.y2), PY(l.x2, l.y2, 8)); ctx.stroke();
  }
  ctx.globalAlpha = 1;

  // ---- transition fade ----
  if (trans) {
    ctx.setTransform(DPR, 0, 0, DPR, 0, 0);
    const a = trans.t < 0.8 ? trans.t / 0.8 : 1 - (trans.t - 0.8) / 0.8;
    ctx.fillStyle = `rgba(0,0,0,${clamp(a, 0, 1)})`; ctx.fillRect(0, 0, W, H);
  }
}

// ============================================================
//  Camera
// ============================================================
function cameraTarget() {
  let minX = 1e9, minY = 1e9, maxX = -1e9, maxY = -1e9;
  for (let ri = 0; ri < rooms.length; ri++) {
    if (!rooms[ri].explored && !(ri === stairRoom && rooms[ri].disc)) continue;
    const b = roomBounds(ri);
    for (const [x, y] of [[b.x0 - TS, b.y0 - TS], [b.x1 + TS, b.y0 - TS], [b.x1 + TS, b.y1 + TS], [b.x0 - TS, b.y1 + TS]]) {
      const sx = PX(x, y), sy = PY(x, y, 0);
      minX = Math.min(minX, sx); maxX = Math.max(maxX, sx);
      minY = Math.min(minY, sy - WALL_H - 20); maxY = Math.max(maxY, sy);
    }
  }
  const narrow = W < 640;
  const availW = narrow ? W - 24 : W - 260, availH = narrow ? H - 200 : H - 80;
  const z = clamp(Math.min(availW / (maxX - minX), availH / (maxY - minY)), 0.35, 2.6);
  const offX = narrow ? 0 : -110, offY = narrow ? -60 : 10;
  return { x: (minX + maxX) / 2 - offX / z, y: (minY + maxY) / 2 - offY / z, z };
}
function snapCamera() { const t = cameraTarget(); cam.x = t.x; cam.y = t.y; cam.z = t.z; }
function updateCamera(dt) {
  if (!cam.auto || !rooms) return;
  const t = cameraTarget(), k = 1 - Math.pow(0.02, dt);
  cam.x += (t.x - cam.x) * k; cam.y += (t.y - cam.y) * k; cam.z += (t.z - cam.z) * k;
}
function setCamAuto(v) { cam.auto = v; document.getElementById('camBtn').classList.toggle('on', v); }

// pointer: drag pan + pinch zoom
const pointers = new Map();
let pinchD = 0;
let tapStart = null; // click (no drag) => rally
cvs.addEventListener('pointerdown', e => {
  cvs.setPointerCapture(e.pointerId); pointers.set(e.pointerId, { x: e.clientX, y: e.clientY }); pinchD = 0;
  tapStart = pointers.size === 1 ? { x: e.clientX, y: e.clientY, moved: false } : null;
});
cvs.addEventListener('pointermove', e => {
  const p = pointers.get(e.pointerId); if (!p) return;
  if (pointers.size === 1) {
    if (tapStart && !tapStart.moved && Math.hypot(e.clientX - tapStart.x, e.clientY - tapStart.y) > 6) tapStart.moved = true;
    const dx = e.clientX - p.x, dy = e.clientY - p.y;
    if (tapStart && tapStart.moved) { cam.x -= dx / cam.z; cam.y -= dy / cam.z; setCamAuto(false); }
  }
  p.x = e.clientX; p.y = e.clientY;
  if (pointers.size === 2) {
    const [a, b] = [...pointers.values()];
    const d = Math.hypot(a.x - b.x, a.y - b.y);
    if (pinchD) zoomAt((a.x + b.x) / 2, (a.y + b.y) / 2, d / pinchD);
    pinchD = d;
  }
});
const endPtr = e => { pointers.delete(e.pointerId); pinchD = 0; };
cvs.addEventListener('pointerup', e => {
  if (tapStart && !tapStart.moved && pointers.size === 1) setRally(e.clientX, e.clientY);
  tapStart = null; endPtr(e);
});
cvs.addEventListener('pointercancel', e => { tapStart = null; endPtr(e); });

// screen -> world (ground plane, z = 0)
function screenToWorld(mx, my) {
  const sx = cam.x + (mx - W / 2) / cam.z, sy = cam.y + (my - H / 2) / cam.z;
  return { x: (sx + 2 * sy) / 2, y: (2 * sy - sx) / 2 };
}
function setRally(mx, my) {
  if (!started || trans || !tiles) return;
  const p = screenToWorld(mx, my);
  rally = { x: p.x, y: p.y, life: RALLY_TIME, max: RALLY_TIME };
  // everyone resting kicks off right away (staggered) instead of waiting out their pause
  for (const c of circles) if (c.state === 'rest') c.t = Math.min(c.t, rand(0, 0.12));
  blip(660, 0.08, 0.05, 'sine');
}
cvs.addEventListener('wheel', e => { e.preventDefault(); zoomAt(e.clientX, e.clientY, Math.exp(-e.deltaY * 0.0015)); }, { passive: false });
function zoomAt(mx, my, f) {
  setCamAuto(false);
  const wx = cam.x + (mx - W / 2) / cam.z, wy = cam.y + (my - H / 2) / cam.z;
  cam.z = clamp(cam.z * f, 0.25, 4);
  cam.x = wx - (mx - W / 2) / cam.z; cam.y = wy - (my - H / 2) / cam.z;
}

// ============================================================
//  Audio (tiny WebAudio synth)
// ============================================================
let AC = null, noiseBuf = null, lastBoom = 0, lastBlip = 0;
function initAudio() {
  try {
    AC = new (window.AudioContext || window.webkitAudioContext)();
    noiseBuf = AC.createBuffer(1, AC.sampleRate * 0.6, AC.sampleRate);
    const d = noiseBuf.getChannelData(0);
    for (let i = 0; i < d.length; i++) d[i] = (Math.random() * 2 - 1) * Math.pow(1 - i / d.length, 2);
  } catch (e) { AC = null; }
}
function boom(vol, freq) {
  if (!AC) return;
  const now = AC.currentTime; if (now - lastBoom < 0.05) return; lastBoom = now;
  const src = AC.createBufferSource(); src.buffer = noiseBuf;
  const f = AC.createBiquadFilter(); f.type = 'lowpass'; f.frequency.value = freq;
  const g = AC.createGain(); g.gain.setValueAtTime(vol * 0.6, now); g.gain.exponentialRampToValueAtTime(0.001, now + 0.5);
  src.connect(f); f.connect(g); g.connect(AC.destination); src.start(now);
}
function blip(freq, dur, vol, type) {
  if (!AC) return;
  const now = AC.currentTime; if (now - lastBlip < 0.03) return; lastBlip = now;
  const o = AC.createOscillator(), g = AC.createGain();
  o.type = type; o.frequency.setValueAtTime(freq, now); o.frequency.exponentialRampToValueAtTime(freq * 0.6, now + dur);
  g.gain.setValueAtTime(vol, now); g.gain.exponentialRampToValueAtTime(0.0001, now + dur);
  o.connect(g); g.connect(AC.destination); o.start(now); o.stop(now + dur + 0.02);
}
function chime(freqs, vol) {
  if (!AC) return;
  const now = AC.currentTime;
  freqs.forEach((fr, i) => {
    const o = AC.createOscillator(), g = AC.createGain(), t = now + i * 0.07;
    o.type = 'triangle'; o.frequency.value = fr;
    g.gain.setValueAtTime(0.0001, t); g.gain.exponentialRampToValueAtTime(vol, t + 0.01); g.gain.exponentialRampToValueAtTime(0.0001, t + 0.35);
    o.connect(g); g.connect(AC.destination); o.start(t); o.stop(t + 0.4);
  });
}

// ============================================================
//  UI
// ============================================================
const $ = id => document.getElementById(id);
const tierRows = [];
(function buildTiers() {
  const wrap = $('tiers');
  for (let t = 1; t <= MAX_TIER; t++) {
    const row = document.createElement('div'); row.className = 'tier';
    row.innerHTML = `<span class="dot" style="background:${TIERS[t - 1].c}"></span><span>T${t}</span>` +
      `<div><span class="cnt">0</span><span class="atk">공격 ${fmt(DMG(t))}</span><div class="bar" style="color:${TIERS[t - 1].c}"><i style="width:0"></i></div></div>` +
      `<button>${t === MAX_TIER ? '최대' : '승급'}</button>`;
    const btn = row.querySelector('button');
    btn.addEventListener('click', () => promote(t));
    wrap.appendChild(row);
    tierRows.push({ row, cnt: row.querySelector('.cnt'), bar: row.querySelector('.bar i'), btn });
  }
})();

let hudT = 0;
function hudTick(dt) {
  hudT -= dt; if (hudT > 0) return; hudT = 0.15;
  const counts = new Array(MAX_TIER + 1).fill(0);
  let top = 1;
  for (const c of circles) { counts[c.tier]++; top = Math.max(top, c.tier); }
  for (let t = 1; t <= MAX_TIER; t++) {
    const r = tierRows[t - 1];
    r.row.style.display = t <= Math.max(3, top + 1) ? '' : 'none';
    r.cnt.textContent = counts[t];
    r.bar.style.width = Math.min(100, counts[t] * 10) + '%';
    const ok = counts[t] >= 10 && t < MAX_TIER;
    r.btn.disabled = !ok; r.btn.classList.toggle('ready', ok);
  }
  $('hFloor').textContent = floorN;
  $('hCount').textContent = circles.length;
  $('hCap').textContent = '/' + CAP;
  const up = upChance(floorN);
  $('hUp').textContent = up > 0 ? Math.round(up * 100) + '%' : '0%';
  $('hBreed').textContent = circles.length >= CAP ? '최대' : Math.round(breedChance(1, 1, circles.length) * 100) + '%';
  $('hRooms').textContent = rooms ? rooms.filter(r => r.explored).length : 0;
  $('hRoomsTotal').textContent = '/' + (rooms ? rooms.length - 1 : 0);
  const st = $('hStair');
  st.textContent = stairFound ? '계단방: 발견! 금색 벽을 부수세요' : '계단방: 미발견';
  st.classList.toggle('found', !!stairFound);
}

function toast(msg) {
  const el = document.createElement('div'); el.textContent = msg;
  const box = $('toast'); box.appendChild(el);
  while (box.children.length > 3) box.removeChild(box.firstChild);
  setTimeout(() => { el.style.opacity = '0'; setTimeout(() => el.remove(), 400); }, 2200);
}
let bannerTimer = 0;
function banner(text) {
  const el = $('banner'); el.textContent = text; el.classList.add('show');
  clearTimeout(bannerTimer); bannerTimer = setTimeout(() => el.classList.remove('show'), 1600);
}

document.querySelectorAll('.spd').forEach(b => b.addEventListener('click', () => {
  speed = +b.dataset.speed;
  document.querySelectorAll('.spd').forEach(x => x.classList.toggle('on', x === b));
}));
function togglePause() { paused = !paused; $('pauseBtn').classList.toggle('on', paused); $('pauseBtn').textContent = paused ? '재개' : '일시정지'; }
$('pauseBtn').addEventListener('click', togglePause);
$('camBtn').addEventListener('click', () => setCamAuto(true));
$('autoPromote').addEventListener('change', e => { autoPromote = e.target.checked; });
addEventListener('keydown', e => {
  if (!started) return;
  if (e.code === 'Space') { e.preventDefault(); togglePause(); }
  const n = parseInt(e.key, 10);
  if (n >= 1 && n <= 9) promote(n);
});

$('startBtn').addEventListener('click', () => {
  initAudio();
  $('intro').style.display = 'none';
  started = true;
  banner('1층');
});

// ============================================================
//  Boot
// ============================================================
function newGame() {
  floorN = 1; circles = []; boxes = []; parts = []; rings = []; links = []; texts = [];
  genFloor();
  const b = roomBounds(startRoom);
  for (let i = 0; i < 3; i++) circles.push(newCircle(1, rand(b.x0 + 30, b.x1 - 30), rand(b.y0 + 30, b.y1 - 30)));
  snapCamera();
}
newGame();

let last = performance.now(), acc = 0;
const DT = 1 / 60;
function frame(now) {
  const rdt = Math.min(0.1, (now - last) / 1000); last = now;
  if (started && !paused && !trans) {
    acc += rdt * speed;
    let n = 0;
    while (acc >= DT && n < 12) { step(DT); acc -= DT; n++; }
    if (n >= 12) acc = 0;
  }
  if (trans) updateTrans(rdt);
  shake = Math.max(0, shake - rdt * 30);
  updateCamera(rdt);
  render();
  hudTick(rdt);
  requestAnimationFrame(frame);
}
requestAnimationFrame(frame);

// debug hook
window.__rat = {
  cam, BAL, setFloor(n) { floorN = n; }, get floor() { return floorN; }, get trans() { return trans; },
  get circles() { return circles; }, get boxes() { return boxes; }, get segs() { return segs; },
  setAuto(v) { autoPromote = v; }, promote, nextFloor, step, updateTrans, newGame,
  // headless balance sim: auto-promote, no clicks; returns seconds spent on each floor
  //   keep: how many circles of a tier the bot keeps before promoting (0 = promote ASAP)
  sim(floors = 5, limit = 900, keep = 0, bal = {}) {
    Object.assign(BAL, bal);
    newGame(); autoPromote = false; const out = [];
    let pt = 0;
    for (let f = 0; f < floors; f++) {
      const start = T, f0 = floorN;
      while (floorN === f0 && T - start < limit) {
        step(1 / 60);
        if ((pt += 1 / 60) > 0.4) {
          pt = 0;
          const cnt = new Array(MAX_TIER + 1).fill(0); for (const c of circles) cnt[c.tier]++;
          for (let t = 1; t < MAX_TIER; t++) if (cnt[t] >= 10 + keep && circles.length >= 14) { promote(t); break; }
        }
        if (trans) { trans.t = 0.8; updateTrans(0); trans = null; }
      }
      const tiers = {}; for (const c of circles) tiers[c.tier] = (tiers[c.tier] || 0) + 1;
      out.push({ floor: f0, sec: Math.round(T - start), n: circles.length, tiers: JSON.stringify(tiers) });
      if (floorN === f0) break;
    }
    return out;
  },
};
})();
