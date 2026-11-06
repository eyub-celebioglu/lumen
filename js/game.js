/* =========================================================
   LUMEN — puzzle de lumière
   Moteur : génération procédurale à solution unique,
   rendu pixel 1-bit tramé, sons 8-bit, progression locale.
   ========================================================= */
(() => {
'use strict';

const $ = (s, r = document) => r.querySelector(s);
const $$ = (s, r = document) => [...r.querySelectorAll(s)];

/* ---------------------------------------------------------
   Directions & masques  (U=1, R=2, D=4, L=8 — bit d = 1<<d)
   --------------------------------------------------------- */
const DIRS = [
  { b: 1, dx: 0, dy: -1, o: 4 },
  { b: 2, dx: 1, dy: 0, o: 8 },
  { b: 4, dx: 0, dy: 1, o: 1 },
  { b: 8, dx: -1, dy: 0, o: 2 },
];
const rot1 = m => ((m << 1) | (m >> 3)) & 15;
const rotN = (m, n) => { n = ((n % 4) + 4) % 4; while (n--) m = rot1(m); return m; };
const popc = m => (m & 1) + (m >> 1 & 1) + (m >> 2 & 1) + (m >> 3 & 1);

/* ---------------------------------------------------------
   Aléatoire déterministe
   --------------------------------------------------------- */
function mulberry32(a) {
  return function () {
    a |= 0; a = a + 0x6D2B79F5 | 0;
    let t = Math.imul(a ^ a >>> 15, 1 | a);
    t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t;
    return ((t ^ t >>> 14) >>> 0) / 4294967296;
  };
}
function hashStr(s) {
  let h = 2166136261;
  for (let i = 0; i < s.length; i++) { h ^= s.charCodeAt(i); h = Math.imul(h, 16777619); }
  return h >>> 0;
}

/* ---------------------------------------------------------
   Paliers de difficulté — [colonnes, lignes]
   --------------------------------------------------------- */
const TIERS = [
  { id: 'eveil', name: 'Éveil', diff: 'Facile', color: '#6EF6D6',
    desc: 'Premiers pas dans la lumière.',
    sizes: [[3,3],[3,3],[3,4],[4,4],[4,4],[4,5],[4,5],[5,5],[5,5],[5,5],[5,6],[5,6]] },
  { id: 'flux', name: 'Flux', diff: 'Moyen', color: '#5CC8FF',
    desc: 'Les réseaux s’étendent, les chemins se croisent.',
    sizes: [[5,6],[6,6],[6,6],[6,6],[6,7],[6,7],[7,7],[7,7],[7,7],[7,8],[7,8],[7,8]] },
  { id: 'prisme', name: 'Prisme', diff: 'Difficile', color: '#B98CFF',
    desc: 'Grandes grilles. Chaque coin compte.',
    sizes: [[7,8],[8,8],[8,8],[8,9],[8,9],[8,9],[9,9],[9,9],[9,10],[9,10],[9,11],[9,11]] },
  { id: 'nebuleuse', name: 'Nébuleuse', diff: 'Expert', color: '#FF7AD9', wrap: true,
    desc: 'Les bords se rejoignent : l’univers boucle sur lui-même.',
    sizes: [[5,5],[5,6],[6,6],[6,6],[6,7],[6,7],[7,7],[7,7],[7,8],[7,8],[8,8],[8,8]] },
  { id: 'singularite', name: 'Singularité', diff: 'Very high brain', color: '#FFC857', wrap: true, blind: true,
    desc: 'Bords infinis, lumière invisible jusqu’à la victoire. Pure logique.',
    sizes: [[5,5],[5,6],[6,6],[6,6],[6,7],[6,7],[7,7],[7,7],[7,8],[7,8],[8,8],[8,9]] },
];
const PER_TIER = 12;
const UNLOCK_NEXT = 8;
const MAX_STARS = TIERS.length * PER_TIER * 3;

/* ---------------------------------------------------------
   Grille
   --------------------------------------------------------- */
function makeGrid(W, H, wrap) {
  const N = W * H;
  const nb = new Int32Array(N * 4).fill(-1);
  const eid = new Int32Array(N * 4).fill(-1);
  for (let y = 0; y < H; y++) for (let x = 0; x < W; x++) {
    const i = y * W + x;
    for (let d = 0; d < 4; d++) {
      let nx = x + DIRS[d].dx, ny = y + DIRS[d].dy;
      if (wrap) { nx = (nx + W) % W; ny = (ny + H) % H; }
      else if (nx < 0 || ny < 0 || nx >= W || ny >= H) continue;
      const j = ny * W + nx;
      nb[i * 4 + d] = j;
      eid[i * 4 + d] = d === 1 ? i : d === 3 ? j : d === 2 ? N + i : N + j;
    }
  }
  return { W, H, N, wrap, nb, eid };
}

/* Arbre couvrant aléatoire (Prim randomisé) depuis la source */
function genTree(G, rng, src) {
  const { N, nb } = G;
  const sol = new Uint8Array(N);
  const inT = new Uint8Array(N);
  const fr = [];
  const push = i => { for (let d = 0; d < 4; d++) { const j = nb[i * 4 + d]; if (j >= 0 && !inT[j]) fr.push(i * 4 + d); } };
  inT[src] = 1; push(src);
  let count = 1;
  while (count < N && fr.length) {
    const k = Math.floor(rng() * fr.length);
    const f = fr[k]; fr[k] = fr[fr.length - 1]; fr.pop();
    const i = f >> 2, d = f & 3, j = nb[f];
    if (inT[j]) continue;
    sol[i] |= DIRS[d].b; sol[j] |= DIRS[d].o;
    inT[j] = 1; count++; push(j);
  }
  return sol;
}

/* Solveur par propagation de contraintes.
   Règles : cohérence des arêtes, pas de boucle, pas de
   composante fermée isolée. S'il résout tout, la solution
   est unique et atteignable sans deviner. */
function analyze(G, sol, fixed) {
  const { N, nb, eid } = G;
  const E = new Uint8Array(2 * N); // 0 inconnue, 1 oui, 2 non
  const cand = new Array(N);
  const deg = new Uint8Array(N);
  for (let i = 0; i < N; i++) {
    deg[i] = popc(sol[i]);
    if (fixed[i]) cand[i] = [sol[i]];
    else { const s = new Set(); for (let r = 0; r < 4; r++) s.add(rotN(sol[i], r)); cand[i] = [...s]; }
  }
  const par = new Int32Array(N);
  const need = new Int32Array(N), size = new Int32Array(N);
  const find = x => { while (par[x] !== x) { par[x] = par[par[x]]; x = par[x]; } return x; };
  let changed = true, guard = 0;
  while (changed && guard++ < 1000) {
    changed = false;
    for (let i = 0; i < N; i++) {
      let c = cand[i];
      const f = c.filter(m => {
        for (let d = 0; d < 4; d++) {
          const e = eid[i * 4 + d];
          const st = e < 0 ? 2 : E[e];
          const has = (m >> d) & 1;
          if (has && st === 2) return false;
          if (!has && st === 1) return false;
        }
        return true;
      });
      if (!f.length) return { ok: false, solved: false, cand };
      if (f.length !== c.length) { cand[i] = c = f; changed = true; }
      for (let d = 0; d < 4; d++) {
        const e = eid[i * 4 + d];
        if (e < 0 || E[e]) continue;
        let all = true, none = true;
        for (const m of c) { if ((m >> d) & 1) none = false; else all = false; }
        if (all) { E[e] = 1; changed = true; }
        else if (none) { E[e] = 2; changed = true; }
      }
    }
    for (let i = 0; i < N; i++) { par[i] = i; need[i] = 0; size[i] = 0; }
    for (let i = 0; i < N; i++) for (let d = 1; d <= 2; d++) {
      const e = eid[i * 4 + d];
      if (e >= 0 && E[e] === 1) { const a = find(i), b = find(nb[i * 4 + d]); if (a !== b) par[a] = b; }
    }
    for (let i = 0; i < N; i++) { const r = find(i); size[r]++; need[r] += deg[i]; }
    for (let i = 0; i < N; i++) for (let d = 1; d <= 2; d++) {
      const e = eid[i * 4 + d]; if (e >= 0 && E[e] === 1) need[find(i)] -= 2;
    }
    for (let i = 0; i < N; i++) for (let d = 1; d <= 2; d++) {
      const e = eid[i * 4 + d];
      if (e < 0 || E[e]) continue;
      const a = find(i), b = find(nb[i * 4 + d]);
      if (a === b || (need[a] + need[b] - 2 === 0 && size[a] + size[b] < N)) { E[e] = 2; changed = true; }
    }
  }
  let solved = true;
  for (let i = 0; i < N; i++) if (cand[i].length > 1) { solved = false; break; }
  return { ok: true, solved, cand };
}

/* Génère un niveau à solution unique (ancres ajoutées si besoin) */
function generate(cfg) {
  const G = makeGrid(cfg.W, cfg.H, cfg.wrap);
  const { N } = G;
  const rng = mulberry32(cfg.seed);
  const src = Math.floor(cfg.H / 2) * cfg.W + Math.floor(cfg.W / 2);
  let best = null;
  for (let a = 0; a < 8; a++) {
    const sol = genTree(G, rng, src);
    const fixed = new Uint8Array(N);
    let givens = 0;
    for (let k = 0; k < N; k++) {
      const res = analyze(G, sol, fixed);
      if (res.solved) break;
      const und = [];
      for (let i = 0; i < N; i++) if (res.cand[i].length > 1) und.push(i);
      fixed[und[Math.floor(rng() * und.length)]] = 1;
      givens++;
    }
    if (!best || givens < best.givens) best = { sol, fixed, givens };
    if (givens === 0) break;
  }
  const { sol, fixed } = best;
  const r = new Int8Array(N);
  for (let i = 0; i < N; i++) {
    if (fixed[i]) continue;
    r[i] = Math.floor(rng() * 4);
    // on limite les tuiles déjà bien orientées
    if (rotN(sol[i], r[i]) === sol[i] && rotN(sol[i], 1) !== sol[i] && rng() < 0.7) r[i] = (r[i] + 1) % 4;
  }
  return { G, src, sol, fixed, r, givens: best.givens };
}

/* ---------------------------------------------------------
   Sauvegarde
   --------------------------------------------------------- */
const store = {
  d: {},
  load() {
    try { this.d = JSON.parse(localStorage.getItem('lumen.v1')) || {}; } catch (e) { this.d = {}; }
    this.d.lv = this.d.lv || {};
    this.d.cur = this.d.cur || {};
    this.d.st = Object.assign({ sound: true, vibe: true, free: false, pal: 'gravure' }, this.d.st || {});
  },
  save() { try { localStorage.setItem('lumen.v1', JSON.stringify(this.d)); } catch (e) { /* stockage indisponible */ } },
};

const TOTAL = TIERS.length * PER_TIER;
const levelKey = (ti, li) => `${TIERS[ti].id}-${li}`;
const fromG = g => [Math.floor(g / PER_TIER), g % PER_TIER];
const isDone = (ti, li) => !!store.d.lv[levelKey(ti, li)];
const tierDone = ti => { let n = 0; for (let i = 0; i < PER_TIER; i++) if (isDone(ti, i)) n++; return n; };
const levelUnlocked = (ti, li) => {
  const g = ti * PER_TIER + li;
  return store.d.st.free || g === 0 || isDone(...fromG(g - 1)) || isDone(ti, li);
};
const tierUnlocked = ti => levelUnlocked(ti, 0);
const totalStars = () => Object.values(store.d.lv).reduce((s, v) => s + (v.s || 0), 0);

function nextLevel() {
  for (let g = 0; g < TOTAL; g++) { const [t, l] = fromG(g); if (!isDone(t, l) && levelUnlocked(t, l)) return [t, l]; }
  return null;
}

function levelCfg(ti, li) {
  const T = TIERS[ti];
  const [W, H] = T.sizes[li];
  return {
    key: levelKey(ti, li), ti, li, g: ti * PER_TIER + li, W, H,
    wrap: !!T.wrap, blind: !!T.blind,
    seed: hashStr(`lumen:${T.id}:${li}:v1`),
    title: `Niveau ${li + 1}`, sub: `${T.name} · ${T.diff}`,
  };
}

/* ---------------------------------------------------------
   Palettes 1-bit & trames
   --------------------------------------------------------- */
const PALETTES = [
  { id: 'gravure', name: 'Gravure', bg: '#1e1d18', ink: '#e6dfc8' },
  { id: 'mac', name: 'Mac', bg: '#333319', ink: '#e5ffff' },
  { id: 'ambre', name: 'Ambre', bg: '#1c1100', ink: '#ffb000' },
  { id: 'phosphore', name: 'Phosphore', bg: '#06140a', ink: '#3dff74' },
  { id: 'papier', name: 'Papier', bg: '#ebe4d0', ink: '#24201a' },
];
let pal = PALETTES[0];
const BAYER = [0, 8, 2, 10, 12, 4, 14, 6, 3, 11, 1, 9, 15, 7, 13, 5];
const hexRgb = h => { const n = parseInt(h.slice(1), 16); return [n >> 16 & 255, n >> 8 & 255, n & 255]; };

function ditherTile(level, color) {
  const c = document.createElement('canvas'); c.width = c.height = 4;
  const x = c.getContext('2d'); x.fillStyle = color;
  for (let k = 0; k < 16; k++) if (BAYER[k] < level) x.fillRect(k % 4, (k / 4) | 0, 1, 1);
  return c;
}
function makePats(context, color) {
  const a = [];
  for (let l = 0; l <= 16; l++) a.push(l >= 16 ? color : context.createPattern(ditherTile(l, color), 'repeat'));
  return a;
}

function applyPalette(id) {
  pal = PALETTES.find(p => p.id === id) || PALETTES[0];
  const r = document.documentElement.style;
  r.setProperty('--bg', pal.bg);
  r.setProperty('--ink', pal.ink);
  r.setProperty('--d2', `url(${ditherTile(2, pal.ink).toDataURL()})`);
  r.setProperty('--d4', `url(${ditherTile(4, pal.ink).toDataURL()})`);
  r.setProperty('--d8', `url(${ditherTile(8, pal.ink).toDataURL()})`);
  r.setProperty('--dim', `url(${ditherTile(11, pal.bg).toDataURL()})`);
  $('meta[name="theme-color"]').setAttribute('content', pal.bg);
  P.main = makePats(ctx, pal.ink);
  P.spr = makePats(sctx, pal.ink);
  P.logo = makePats(lctx, pal.ink);
  haloKey = '';
  paintSky();
  drawLogo();
  if (S) draw(performance.now());
}

/* ---------------------------------------------------------
   Icônes pixel
   --------------------------------------------------------- */
const ICONS = {
  back: ['...#...', '..#....', '.#.....', '#######', '.#.....', '..#....', '...#...'],
  play: ['#......', '###....', '#####..', '#######', '#####..', '###....', '#......'],
  grid: ['##.##.##', '##.##.##', '........', '##.##.##', '##.##.##', '........', '##.##.##', '##.##.##'],
  help: ['.#####.', '#.....#', '......#', '....##.', '...#...', '.......', '...#...'],
  gear: ['...#...', '.#####.', '.##.##.', '###.###', '.##.##.', '.#####.', '...#...'],
  star: ['...#...', '...#...', '#######', '.#####.', '..###..', '.##.##.', '.#...#.'],
  star0: ['...#...', '...#...', '###.###', '.#...#.', '..#.#..', '.##.##.', '.#...#.'],
  turn: ['.####.#', '#....##', '#...###', '#......', '#.....#', '#.....#', '.#####.'],
  clock: ['.#####.', '#..#..#', '#..#..#', '#..##.#', '#.....#', '#.....#', '.#####.'],
  undo: ['..#......', '.##......', '#######..', '.##....#.', '..#.....#', '........#', '........#', '.......#.', '..#####..'],
  lock: ['..#####..', '.#.....#.', '.#.....#.', '#########', '#########', '####.####', '####.####', '#########', '#########'],
  hint: ['..#####..', '.#.....#.', '#.......#', '#...#...#', '#..###..#', '.#..#..#.', '..#####..', '..#####..', '...###...'],
  reset: ['..####.#.', '.#....##.', '#....###.', '#........', '#.......#', '#.......#', '.#.....#.', '..#####..', '.........'],
};
function iconSvg(name, cell = 2) {
  const rows = ICONS[name]; if (!rows) return '';
  const h = rows.length, w = rows[0].length;
  let d = '';
  rows.forEach((r, y) => { for (let x = 0; x < w; x++) if (r[x] === '#') d += `M${x} ${y}h1v1h-1z`; });
  return `<svg viewBox="0 0 ${w} ${h}" width="${w * cell}" height="${h * cell}" aria-hidden="true"><path d="${d}"/></svg>`;
}
function hydrateIcons(root = document) { $$('i[data-ic]', root).forEach(el => { el.innerHTML = iconSvg(el.dataset.ic, +(el.dataset.cell || 2)); }); }
const starsHtml = (n, cell) => [0, 1, 2].map(k => `<i>${iconSvg(k < n ? 'star' : 'star0', cell)}</i>`).join('');

/* ---------------------------------------------------------
   Audio synthétisé (esprit 8-bit)
   --------------------------------------------------------- */
const Sound = {
  ctx: null, out: null,
  init() {
    if (!this.ctx) {
      try {
        const C = window.AudioContext || window.webkitAudioContext;
        this.ctx = new C();
        const master = this.ctx.createGain(); master.gain.value = 0.8;
        const delay = this.ctx.createDelay(); delay.delayTime.value = 0.16;
        const fb = this.ctx.createGain(); fb.gain.value = 0.25;
        const lp = this.ctx.createBiquadFilter(); lp.type = 'lowpass'; lp.frequency.value = 1800;
        master.connect(this.ctx.destination);
        master.connect(delay); delay.connect(lp); lp.connect(fb); fb.connect(delay); lp.connect(this.ctx.destination);
        this.out = master;
      } catch (e) { this.ctx = null; }
    }
    if (this.ctx && this.ctx.state === 'suspended') this.ctx.resume();
  },
  tone(f, dur, type = 'square', vol = 0.03, delay = 0) {
    if (!store.d.st.sound || !this.ctx) return;
    const c = this.ctx, t = c.currentTime + delay;
    const o = c.createOscillator(), g = c.createGain();
    o.type = type; o.frequency.setValueAtTime(f, t);
    g.gain.setValueAtTime(0.0001, t);
    g.gain.exponentialRampToValueAtTime(vol, t + 0.006);
    g.gain.exponentialRampToValueAtTime(0.0001, t + dur);
    o.connect(g); g.connect(this.out);
    o.start(t); o.stop(t + dur + 0.05);
  },
  note: s => 330 * Math.pow(2, s / 12),
  rotate() { this.tone(220 + Math.random() * 30, 0.045, 'square', 0.022); },
  lock(on) { this.tone(on ? 440 : 330, 0.06, 'square', 0.02); this.tone(on ? 660 : 247, 0.08, 'square', 0.018, 0.05); },
  deny() { this.tone(110, 0.12, 'square', 0.025); },
  chime(n) {
    const P = [0, 3, 5, 7, 10, 12, 15, 17, 19, 22, 24, 27, 29];
    const f = this.note(P[n % P.length]);
    this.tone(f, 0.35, 'triangle', 0.07); this.tone(f * 2, 0.12, 'square', 0.012);
  },
  hint() { this.tone(this.note(12), 0.12, 'square', 0.02); this.tone(this.note(19), 0.25, 'triangle', 0.06, 0.08); },
  win() {
    [0, 3, 7, 10, 12, 15, 19, 24].forEach((s, k) => {
      this.tone(this.note(s), 0.5, 'triangle', 0.07, k * 0.07);
      this.tone(this.note(s) * 2, 0.08, 'square', 0.012, k * 0.07);
    });
  },
  ui() { this.tone(660, 0.03, 'square', 0.015); },
};
const vibe = p => { if (store.d.st.vibe && navigator.vibrate) try { navigator.vibrate(p); } catch (e) {} };

/* ---------------------------------------------------------
   Rendu pixel : tuiles
   --------------------------------------------------------- */
const cv = $('#cv'), ctx = cv.getContext('2d');
const spr = document.createElement('canvas'), sctx = spr.getContext('2d');
const logo = $('#logo'), lctx = logo.getContext('2d');
const P = { main: [], spr: [], logo: [] };

function arm(c2, ox, oy, T, PW, d, ins) {
  const c = T / 2, h = PW / 2, a = c - h + ins, w = PW - 2 * ins;
  if (d === 0) c2.fillRect(ox + a, oy, w, c + h - ins);
  else if (d === 2) c2.fillRect(ox + a, oy + c - h + ins, w, T - (c - h + ins));
  else if (d === 3) c2.fillRect(ox, oy + a, c + h - ins, w);
  else c2.fillRect(ox + c - h + ins, oy + a, T - (c - h + ins), w);
}
function disc(c2, cx, cy, r) {
  for (let j = 0; j < 2 * r; j++) {
    const dy = j - r + 0.5;
    const hw = Math.floor(Math.sqrt(Math.max(0, r * r - dy * dy)) + 0.5);
    if (hw > 0) c2.fillRect(cx - hw, cy - r + j, 2 * hw, 1);
  }
}
function diamond(c2, cx, cy, r) {
  for (let j = 0; j < 2 * r; j++) {
    const hw = Math.round(r - Math.abs(j - r + 0.5));
    if (hw > 0) c2.fillRect(cx - hw, cy - r + j, 2 * hw, 1);
  }
}

/* Dessine une tuile (conduits creux qui se remplissent de lumière tramée) */
function drawTile(c2, pats, ox, oy, T, PW, mask, p, kind) {
  const c = T / 2;
  const lvl = Math.round(p * 16);
  c2.fillStyle = pal.ink;
  for (let d = 0; d < 4; d++) if (mask & (1 << d)) arm(c2, ox, oy, T, PW, d, 0);
  c2.fillStyle = pal.bg;
  for (let d = 0; d < 4; d++) if (mask & (1 << d)) arm(c2, ox, oy, T, PW, d, 1);
  if (lvl > 0) {
    c2.fillStyle = pats[lvl];
    for (let d = 0; d < 4; d++) if (mask & (1 << d)) arm(c2, ox, oy, T, PW, d, 1);
  }
  const cx = ox + c, cy = oy + c;
  if (kind === 'src') {
    const r = Math.max(4, Math.round(T * 0.3));
    c2.fillStyle = pal.ink; disc(c2, cx, cy, r);
    c2.fillStyle = pal.bg; disc(c2, cx, cy, r - 1);
    c2.fillStyle = pal.ink; disc(c2, cx, cy, Math.max(2, r - 3));
  } else if (kind === 'gem') {
    const r = Math.max(3, Math.round(T * 0.24));
    c2.fillStyle = pal.ink; diamond(c2, cx, cy, r);
    c2.fillStyle = pal.bg; diamond(c2, cx, cy, r - 1);
    if (lvl > 0) {
      c2.fillStyle = pats[lvl]; diamond(c2, cx, cy, r - 1);
      if (lvl >= 16) {
        c2.fillStyle = pal.bg; c2.fillRect(cx - 1, cy - 2, 1, 1); c2.fillRect(cx - 2, cy - 1, 1, 1);
        if (T >= 16) { // éclats
          c2.fillStyle = pal.ink;
          const e = r + 1;
          c2.fillRect(cx - e - 1, cy - e - 1, 1, 1); c2.fillRect(cx + e, cy - e - 1, 1, 1);
          c2.fillRect(cx - e - 1, cy + e, 1, 1); c2.fillRect(cx + e, cy + e, 1, 1);
        }
      }
    }
  }
}

/* Halo tramé autour de la source */
const halo = document.createElement('canvas'), hctx = halo.getContext('2d');
let haloKey = '';
function drawHalo(c2, w, h, sx, sy, R, wrapW, wrapH, strength = 0.42) {
  const key = [w, h, sx, sy, Math.round(R), wrapW, wrapH, strength, pal.id].join(',');
  if (key !== haloKey) {
    haloKey = key;
    halo.width = w; halo.height = h;
    const img = hctx.createImageData(w, h), D = img.data;
    const [r, g, b] = hexRgb(pal.ink);
    for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
      let dx = Math.abs(x + 0.5 - sx), dy = Math.abs(y + 0.5 - sy);
      if (wrapW) dx = Math.min(dx, wrapW - dx);
      if (wrapH) dy = Math.min(dy, wrapH - dy);
      const dd = Math.sqrt(dx * dx + dy * dy);
      if (dd >= R) continue;
      const v = strength * Math.pow(1 - dd / R, 2);
      if (v * 16 > BAYER[(y & 3) * 4 + (x & 3)] + 0.5) {
        const o = (y * w + x) * 4; D[o] = r; D[o + 1] = g; D[o + 2] = b; D[o + 3] = 255;
      }
    }
    hctx.putImageData(img, 0, 0);
  }
  c2.drawImage(halo, 0, 0);
}

/* ---------------------------------------------------------
   Ciel tramé & logo
   --------------------------------------------------------- */
function paintSky() {
  const c = $('#sky'), s = 3;
  const w = Math.ceil(innerWidth / s), h = Math.ceil(innerHeight / s);
  c.width = w; c.height = h;
  const x = c.getContext('2d');
  x.fillStyle = pal.bg; x.fillRect(0, 0, w, h);
  const img = x.getImageData(0, 0, w, h), D = img.data;
  const [r, g, b] = hexRgb(pal.ink);
  const rng = mulberry32(11);
  for (let y = 0; y < h; y++) {
    const fy = y / h;
    const base = 0.13 * Math.pow(Math.max(0, (fy - 0.7) / 0.3), 1.8);
    for (let xx = 0; xx < w; xx++) {
      let v = base;
      if (fy < 0.6 && rng() < 0.0022) v = 1;
      if (v * 16 > BAYER[(y & 3) * 4 + (xx & 3)] + 0.5) {
        const o = (y * w + xx) * 4; D[o] = r; D[o + 1] = g; D[o + 2] = b;
      }
    }
  }
  x.putImageData(img, 0, 0);
}

const LOGO = [2, 14, 8, 4, 7, 12, 3, 9, 1];
const LOGO_DIST = [2, 1, 2, 3, 0, 1, 2, 1, 2];
let logoPhase = 6;
function drawLogo() {
  if (!lctx || !P.logo.length) return;
  const T = 16, PW = 4;
  lctx.fillStyle = pal.bg; lctx.fillRect(0, 0, 48, 48);
  drawHalo(lctx, 48, 48, 24, 24, 20 + (logoPhase % 2), 0, 0, 0.5);
  haloKey = '';
  LOGO.forEach((m, i) => {
    const lit = logoPhase >= 4 ? 1 : (LOGO_DIST[i] <= logoPhase ? 1 : 0);
    drawTile(lctx, P.logo, (i % 3) * T, ((i / 3) | 0) * T, T, PW, m, i === 4 ? 1 : lit, i === 4 ? 'src' : popc(m) === 1 ? 'gem' : 'pipe');
  });
}
setInterval(() => { if (current === 'home' && !document.hidden) { logoPhase = (logoPhase + 1) % 9; drawLogo(); } }, 420);

/* ---------------------------------------------------------
   Interface
   --------------------------------------------------------- */
let current = 'home';
let gameFrom = 'home';
function render(id) {
  if (id === current) return;
  if (current === 'game') { pauseGame(); clearAdvance(); }
  $$('.screen').forEach(s => s.classList.toggle('active', s.id === id));
  current = id;
  if (id === 'home') refreshHome();
  if (id === 'levels') buildLevels();
  if (id === 'game') { layout(); requestAnimationFrame(layout); }
}
function nav(id) {
  if (id === current) return;
  history.pushState({ s: id }, '');
  render(id);
}
function back() {
  if (history.state && history.state.s !== 'home') history.back();
  else render('home');
}
window.addEventListener('popstate', e => { closeModals(); render((e.state && e.state.s) || 'home'); });

let toastT = 0;
function toast(msg, ms = 2000) {
  const t = $('#toast');
  t.innerHTML = msg; t.classList.remove('show'); void t.offsetWidth; t.classList.add('show');
  clearTimeout(toastT); toastT = setTimeout(() => t.classList.remove('show'), ms);
}
function openModal(id) { $('#' + id).classList.add('open'); }
function closeModals() { $$('.modal.open').forEach(m => m.classList.remove('open')); }
$$('[data-close]').forEach(b => b.addEventListener('click', () => { Sound.ui(); closeModals(); }));
$$('.modal').forEach(m => m.addEventListener('click', e => { if (e.target === m) closeModals(); }));

const fmtTime = s => { s = Math.floor(s); return `${Math.floor(s / 60)}:${String(s % 60).padStart(2, '0')}`; };
const ROMAN = ['I', 'II', 'III', 'IV', 'V'];

function refreshHome() {
  const nx = nextLevel();
  $('#play-sub').textContent = nx ? `${TIERS[nx[0]].name} · niveau ${nx[1] + 1}` : 'Tout est lumière';
  $('#stars-total').textContent = totalStars();
  $('#stars-max').textContent = TOTAL * 3;
  drawLogo();
}

function buildLevels() {
  const wrap = $('#tiers');
  wrap.innerHTML = '';
  $('#lv-stars').textContent = `${totalStars()}/${TOTAL * 3}`;
  const nx = nextLevel();
  TIERS.forEach((T, ti) => {
    const open = tierUnlocked(ti);
    const done = tierDone(ti);
    const el = document.createElement('article');
    el.className = 'tier' + (open ? '' : ' locked') + (ti >= 3 ? ' hard' : '');
    let meter = '';
    for (let i = 0; i < PER_TIER; i++) meter += `<i class="cell${isDone(ti, i) ? ' on' : ''}"></i>`;
    let html = `
      <div class="tier-head">
        <div class="tier-roman">${ROMAN[ti]}</div>
        <div><div class="tier-name">${T.name}</div><div class="tier-desc">${T.desc}</div></div>
        <span class="tier-diff">${T.diff}</span>
      </div>
      <div class="tier-meter">${meter}<span>${done}/${PER_TIER}</span></div>
      <div class="lv-grid">`;
    for (let li = 0; li < PER_TIER; li++) {
      const rec = store.d.lv[levelKey(ti, li)];
      const un = levelUnlocked(ti, li);
      const cur = nx && nx[0] === ti && nx[1] === li;
      html += `<button class="lv${rec ? ' done' : ''}${un ? '' : ' locked'}${cur ? ' current' : ''}" data-t="${ti}" data-l="${li}" aria-label="${T.name} niveau ${li + 1}${un ? '' : ' (verrouillé)'}">
        <span class="num">${li + 1}</span>${un ? '' : iconSvg('lock', 2)}<span class="ls">${starsHtml(rec ? rec.s : 0, 1)}</span></button>`;
    }
    html += '</div>';
    el.innerHTML = html;
    wrap.appendChild(el);
  });
  const c = $('.lv.current', wrap);
  if (c) setTimeout(() => c.scrollIntoView({ block: 'center', behavior: 'auto' }), 0);
}
$('#tiers').addEventListener('click', e => {
  const b = e.target.closest('.lv'); if (!b) return;
  Sound.init();
  const ti = +b.dataset.t, li = +b.dataset.l;
  if (!levelUnlocked(ti, li)) { Sound.deny(); toast('Termine le niveau précédent d’abord', 1500); return; }
  Sound.ui();
  gameFrom = 'levels';
  startLevel(levelCfg(ti, li));
  nav('game');
});

/* ---------------------------------------------------------
   Partie
   --------------------------------------------------------- */
let S = null;
let raf = 0, last = 0, advT = 0;
const particles = [];

function startLevel(cfg) {
  clearAdvance();
  const L = generate(cfg);
  const now = performance.now();
  const { G, src } = L;
  const sx = src % cfg.W, sy = (src / cfg.W) | 0;
  const tiles = [];
  for (let i = 0; i < G.N; i++) {
    const x = i % cfg.W, y = (i / cfg.W) | 0;
    let dx = Math.abs(x - sx), dy = Math.abs(y - sy);
    if (cfg.wrap) { dx = Math.min(dx, cfg.W - dx); dy = Math.min(dy, cfg.H - dy); }
    tiles.push({
      sol: L.sol[i], deg: popc(L.sol[i]),
      r: L.r[i], a: L.r[i], r0: L.r[i],
      p: 0, locked: !!L.fixed[i], fixed: !!L.fixed[i],
      t0: now + 60 + (dx + dy) * 40, shown: false, flash: 0, shake: 0,
    });
  }
  let par = 0;
  tiles.forEach(t => { let k = 0; while (rotN(t.sol, t.r + k) !== t.sol) k++; par += k; });

  S = {
    cfg, G, src, tiles, par, givens: L.givens,
    moves: 0, time: 0, started: false, solved: false,
    hints: 0, undo: [], lockMode: false,
    powered: new Uint8Array(G.N), lit: 0,
    T: 16, k: 2, PW: 4, haloR: 0,
  };

  const saved = store.d.cur[cfg.key];
  if (saved && saved.r && saved.r.length === G.N) {
    tiles.forEach((t, i) => { t.r = saved.r[i]; t.a = t.r; if (!t.fixed) t.locked = saved.lk.includes(i); });
    S.moves = saved.m || 0; S.time = saved.t || 0; S.hints = saved.h || 0; S.started = S.moves > 0;
  }

  $('#g-title').textContent = cfg.title;
  $('#g-sub').textContent = cfg.sub;
  const tags = [`<span class="tag">${cfg.W} × ${cfg.H}</span>`];
  if (cfg.wrap) tags.push('<span class="tag hot">∞ bords liés</span>');
  if (cfg.blind) tags.push('<span class="tag hot">lumière cachée</span>');
  if (S.givens) tags.push(`<span class="tag">${S.givens} ancre${S.givens > 1 ? 's' : ''}</span>`);
  $('#g-tags').innerHTML = tags.join('');
  $('#board').classList.toggle('wrap', cfg.wrap);
  $('#board').classList.remove('solved');
  $('#banner').classList.remove('show');
  particles.length = 0;
  setLockMode(false);
  computePower(true);
  updateHud();
  layout();
  kick();

  if (!store.d.seenHelp) { store.d.seenHelp = true; store.save(); setTimeout(() => openModal('m-help'), 400); }
  else if (cfg.li === 0 && !saved) {
    if (cfg.ti === 3) toast('Nébuleuse — les bords se rejoignent : ce qui sort à droite revient à gauche.', 4200);
    if (cfg.ti === 4) toast('Singularité — la lumière reste cachée jusqu’à la victoire. Verrouille ce dont tu es sûr.', 4800);
  }
}

const curMask = i => { const t = S.tiles[i]; return rotN(t.sol, t.r); };

function computePower(silent) {
  const { G, src } = S;
  const pw = S.powered; pw.fill(0);
  const q = [src]; pw[src] = 1;
  while (q.length) {
    const i = q.pop(), m = curMask(i);
    for (let d = 0; d < 4; d++) {
      if (!(m & DIRS[d].b)) continue;
      const j = G.nb[i * 4 + d];
      if (j < 0 || pw[j] || !(curMask(j) & DIRS[d].o)) continue;
      pw[j] = 1; q.push(j);
    }
  }
  let lit = 0;
  S.tiles.forEach((t, i) => { if (t.deg === 1 && i !== src && pw[i]) lit++; });
  if (!silent && !S.cfg.blind && lit > S.lit) Sound.chime(lit);
  S.lit = lit;
}

function isSolved() {
  const { G } = S;
  for (let i = 0; i < G.N; i++) if (!S.powered[i]) return false;
  for (let i = 0; i < G.N; i++) {
    const m = curMask(i);
    for (let d = 0; d < 4; d++) {
      if (!(m & DIRS[d].b)) continue;
      const j = G.nb[i * 4 + d];
      if (j < 0 || !(curMask(j) & DIRS[d].o)) return false;
    }
  }
  return true;
}

function afterChange(silent) {
  computePower(silent);
  updateHud();
  if (isSolved()) win();
  else saveCurrent();
  kick();
}

function rotate(i, dir) {
  const t = S.tiles[i];
  if (t.locked) {
    t.shake = 1; Sound.deny(); vibe(12); kick();
    if (!S.lockMode) toast(t.fixed ? 'Ancre fixe — déjà bien placée' : 'Tuile verrouillée — appui long pour libérer', 1500);
    return;
  }
  t.r += dir;
  S.moves++; S.started = true;
  S.undo.push({ k: 'r', i, d: dir });
  Sound.rotate(); vibe(5);
  afterChange();
}

function toggleLock(i) {
  const t = S.tiles[i];
  if (t.fixed) { toast('Ancre fixe', 1100); Sound.deny(); return; }
  t.locked = !t.locked; t.flash = 0.5;
  S.undo.push({ k: 'l', i });
  Sound.lock(t.locked); vibe(14);
  updateHud(); saveCurrent(); kick();
}

function undo() {
  if (!S || S.solved) return;
  const u = S.undo.pop();
  if (!u) return;
  const t = S.tiles[u.i];
  if (u.k === 'r') { t.r -= u.d; S.moves = Math.max(0, S.moves - 1); Sound.rotate(); }
  else { t.locked = !t.locked; Sound.lock(t.locked); }
  t.flash = 0.4;
  afterChange(true);
}

function resetLevel() {
  if (!S) return;
  if (S.solved) { startLevel(S.cfg); return; } // rejouer après victoire
  if (!S.moves && !S.hints && !S.tiles.some(t => t.locked && !t.fixed)) return;
  const now = performance.now();
  S.tiles.forEach(t => { t.r = t.r0; t.a = t.r; if (!t.fixed) t.locked = false; t.t0 = now + Math.random() * 180; t.shown = false; });
  S.moves = 0; S.time = 0; S.hints = 0; S.undo = []; S.started = false;
  delete store.d.cur[S.cfg.key]; store.save();
  Sound.hint();
  afterChange(true);
}

function hint() {
  if (!S || S.solved) return;
  const wrong = i => rotN(S.tiles[i].sol, S.tiles[i].r) !== S.tiles[i].sol;
  const all = S.tiles.map((t, i) => i);
  let pool = all.filter(i => S.tiles[i].locked && !S.tiles[i].fixed && wrong(i));
  if (!pool.length) {
    pool = all.filter(i => !S.tiles[i].locked && wrong(i));
    const near = pool.filter(i => [0, 1, 2, 3].some(d => { const j = S.G.nb[i * 4 + d]; return j >= 0 && (S.tiles[j].locked || (!S.cfg.blind && S.powered[j])); }));
    if (near.length) pool = near;
  }
  if (!pool.length) pool = all.filter(i => !S.tiles[i].locked);
  if (!pool.length) return;
  const i = pool[Math.floor(Math.random() * pool.length)];
  const t = S.tiles[i];
  let k = 0; while (rotN(t.sol, t.r + k) !== t.sol) k++;
  t.r += k; t.locked = true; t.flash = 1.2;
  S.hints++; S.started = true;
  S.undo = S.undo.filter(u => u.i !== i);
  Sound.hint(); vibe([10, 30, 10]);
  afterChange(true);
}

function setLockMode(on) {
  if (S) S.lockMode = on;
  $('#t-lock').classList.toggle('on', on);
}

function updateHud() {
  $('#g-moves').textContent = S.moves;
  $('#g-time').textContent = fmtTime(S.time);
  $('#t-undo').disabled = !S.undo.length || S.solved;
  $('#t-hint').disabled = S.solved;
  $('#t-lock').disabled = S.solved;
  const hb = $('#t-hint');
  let badge = $('.badge', hb);
  if (S.hints) {
    if (!badge) { badge = document.createElement('span'); badge.className = 'badge'; hb.appendChild(badge); }
    badge.textContent = S.hints;
  } else if (badge) badge.remove();
}

function snapshot() {
  return {
    r: S.tiles.map(t => t.r),
    lk: S.tiles.map((t, i) => (t.locked && !t.fixed ? i : -1)).filter(i => i >= 0),
    m: S.moves, t: Math.floor(S.time), h: S.hints,
  };
}
const worthSaving = () => S && !S.solved && (S.started || S.tiles.some(t => t.locked && !t.fixed));
let saveT = 0;
function saveCurrent() {
  clearTimeout(saveT);
  saveT = setTimeout(() => { if (worthSaving()) { store.d.cur[S.cfg.key] = snapshot(); store.save(); } }, 250);
}
function pauseGame() { clearTimeout(saveT); if (worthSaving()) { store.d.cur[S.cfg.key] = snapshot(); store.save(); } }

let lastTick = performance.now();
setInterval(() => {
  const now = performance.now();
  const dt = (now - lastTick) / 1000; lastTick = now;
  if (S && S.started && !S.solved && current === 'game' && !document.hidden && !$('.modal.open')) {
    S.time += Math.min(dt, 1);
    $('#g-time').textContent = fmtTime(S.time);
  }
}, 250);
document.addEventListener('visibilitychange', () => { if (document.hidden) pauseGame(); });

/* ---------- victoire & enchaînement ---------- */
function win() {
  S.solved = true;
  setLockMode(false);
  const now = performance.now();
  const { G, src, cfg } = S;
  const dist = new Int32Array(G.N).fill(-1); dist[src] = 0;
  const q = [src];
  for (let h = 0; h < q.length; h++) {
    const i = q[h], m = curMask(i);
    for (let d = 0; d < 4; d++) {
      if (!(m & DIRS[d].b)) continue;
      const j = G.nb[i * 4 + d];
      if (j >= 0 && dist[j] < 0) { dist[j] = dist[i] + 1; q.push(j); }
    }
  }
  const maxD = Math.max(...dist);
  const step = Math.min(55, 700 / Math.max(1, maxD));
  S.tiles.forEach((t, i) => { t.wave = now + 120 + dist[i] * step; });
  S.winAt = now;
  S.waveEnd = now + 120 + maxD * step;
  $('#board').classList.add('solved');

  const extra = Math.max(2, Math.ceil(S.par * 0.25));
  let stars = S.moves <= S.par + extra ? 3 : S.moves <= S.par * 2 + 4 ? 2 : 1;
  stars = Math.max(1, stars - S.hints);
  S.stars = stars;

  delete store.d.cur[cfg.key];
  const old = store.d.lv[cfg.key];
  store.d.lv[cfg.key] = {
    s: Math.max(stars, old ? old.s : 0),
    m: old ? Math.min(old.m, S.moves) : S.moves,
    t: old ? Math.min(old.t, Math.floor(S.time)) : Math.floor(S.time),
  };
  store.save();
  S.newRecord = !!old && Math.floor(S.time) < old.t;

  Sound.win(); vibe([20, 50, 30]);
  updateHud();
  kick();
  advT = setTimeout(showBanner, S.waveEnd - now + 280);
}

function showBanner() {
  if (!S || !S.solved || current !== 'game') return;
  const { cfg } = S;
  const last = cfg.g === TOTAL - 1;
  $('#b-eyebrow').textContent = `${TIERS[cfg.ti].name} · niveau ${cfg.li + 1}`;
  $('#b-title').textContent = S.stars === 3 ? 'Lumière' : S.stars === 2 ? 'Résolu' : 'Résolu';
  $('#b-stars').innerHTML = starsHtml(S.stars, 4);
  $('#b-stats').textContent = `${S.moves} coups · ${fmtTime(S.time)}${S.newRecord ? ' · record' : ''}`;
  let nextLabel = 'Niveau suivant';
  if (!last && cfg.li === PER_TIER - 1) nextLabel = `Palier ${ROMAN[cfg.ti + 1]} — ${TIERS[cfg.ti + 1].name}`;
  if (last) nextLabel = 'Fin du voyage';
  $('#b-next').innerHTML = `${nextLabel}<span class="caret">▮</span><span class="bar-fill" id="b-fill"></span>`;
  $('#banner').classList.add('show');
  const fill = $('#b-fill');
  fill.animate([{ transform: 'scaleX(0)' }, { transform: 'scaleX(1)' }], { duration: 1700, easing: 'steps(12)', fill: 'forwards' });
  advT = setTimeout(goNext, 1750);
}

function clearAdvance() { clearTimeout(advT); advT = 0; }

function goNext() {
  clearAdvance();
  if (!S || !S.solved) return;
  $('#banner').classList.remove('show');
  const g = S.cfg.g + 1;
  if (g >= TOTAL) {
    let left = 0;
    for (let k = 0; k < TOTAL; k++) if (!isDone(...fromG(k))) left++;
    $('#e-text').innerHTML = left
      ? `Le dernier niveau est vaincu. Il te reste <b>${left}</b> niveau${left > 1 ? 'x' : ''} à éclairer.`
      : `Les ${TOTAL} niveaux sont résolus. Total : <b>${totalStars()}</b> étoiles sur ${TOTAL * 3}. Rejoue les niveaux pour toutes les décrocher.`;
    openModal('m-end'); return;
  }
  startLevel(levelCfg(...fromG(g)));
}
$('#banner').addEventListener('click', () => { Sound.ui(); goNext(); });
$('#e-levels').addEventListener('click', () => {
  closeModals();
  if (gameFrom === 'levels') back();
  else { history.replaceState({ s: 'levels' }, ''); render('levels'); }
});

function burst(x, y, n, speed = 1) {
  for (let k = 0; k < n; k++) {
    const a = Math.random() * Math.PI * 2, v = (12 + Math.random() * 40) * speed;
    particles.push({ x, y, vx: Math.cos(a) * v, vy: Math.sin(a) * v, life: 0, max: 0.5 + Math.random() * 0.7, s: Math.random() < 0.3 ? 2 : 1 });
  }
}

/* ---------------------------------------------------------
   Mise en page & boucle de rendu
   --------------------------------------------------------- */
function layout() {
  if (!S) return;
  const wrap = $('#board-wrap');
  const aw = wrap.clientWidth - 26, ah = wrap.clientHeight - 30;
  if (aw <= 0 || ah <= 0) return;
  const { W, H } = S.cfg;
  let k = Math.min(aw, ah) < 520 ? 2 : 3;
  let T = Math.floor(Math.min(aw / (W * k), ah / (H * k)));
  if (T < 14 && k > 2) { k = 2; T = Math.floor(Math.min(aw / (W * k), ah / (H * k))); }
  T = Math.max(10, Math.min(40, T - (T % 2)));
  S.T = T; S.k = k; S.PW = Math.max(4, 2 * Math.round(T * 0.14));
  cv.width = W * T; cv.height = H * T;
  cv.style.width = W * T * k + 'px'; cv.style.height = H * T * k + 'px';
  spr.width = spr.height = T;
  ctx.imageSmoothingEnabled = false; sctx.imageSmoothingEnabled = false;
  const pulse = $('#pulse');
  const sx = S.src % W, sy = (S.src / W) | 0;
  pulse.style.left = (sx + 0.5) * T * k + 'px'; pulse.style.top = (sy + 0.5) * T * k + 'px';
  pulse.style.width = pulse.style.height = T * k * 1.1 + 'px';
  draw(performance.now());
}
new ResizeObserver(() => { if (current === 'game') layout(); }).observe($('#board-wrap'));
let skyT = 0;
window.addEventListener('resize', () => { clearTimeout(skyT); skyT = setTimeout(paintSky, 120); });

function kick() { if (!raf) { last = performance.now(); raf = requestAnimationFrame(frame); } }

function frame(now) {
  raf = 0;
  if (!S) return;
  const dt = Math.min(0.05, (now - last) / 1000); last = now;
  let busy = false;
  const { W } = S.cfg, T = S.T;
  const blindHide = S.cfg.blind && !S.solved;
  S.tiles.forEach((t, i) => {
    if (!t.shown) { if (now >= t.t0) { t.shown = true; t.flash = Math.max(t.flash, 0.7); } busy = true; }
    const da = t.r - t.a;
    if (Math.abs(da) > 0.01) { t.a += Math.sign(da) * Math.min(Math.abs(da), dt * 7); busy = true; } else t.a = t.r;
    let target = blindHide ? (i === S.src ? 1 : 0) : (S.powered[i] ? 1 : 0);
    if (S.solved) target = now >= t.wave ? 1 : (S.cfg.blind ? 0 : target);
    if (Math.abs(target - t.p) > 0.01) { t.p += Math.sign(target - t.p) * Math.min(Math.abs(target - t.p), dt * (target > t.p ? 5 : 4)); busy = true; } else t.p = target;
    if (S.solved && !t.waved) {
      busy = true;
      if (now >= t.wave) {
        t.waved = true; t.flash = 1;
        const px = ((i % W) + 0.5) * T, py = (((i / W) | 0) + 0.5) * T;
        if (t.deg === 1 && i !== S.src) burst(px, py, 10);
        if (i === S.src) burst(px, py, 24, 1.6);
      }
    }
    if (t.flash > 0) { t.flash = Math.max(0, t.flash - dt * 2.6); busy = true; }
    if (t.shake > 0) { t.shake = Math.max(0, t.shake - dt * 4); busy = true; }
  });
  // halo : s'étend sur tout le plateau à la victoire
  const baseR = T * 1.7;
  const fullR = Math.hypot(S.cfg.W, S.cfg.H) * T * 0.62;
  const targetR = S.solved ? fullR : baseR;
  if (!S.haloR) S.haloR = baseR;
  if (Math.abs(targetR - S.haloR) > 1) { S.haloR += (targetR - S.haloR) * Math.min(1, dt * 2.2); busy = true; } else S.haloR = targetR;
  for (let k = particles.length - 1; k >= 0; k--) {
    const p = particles[k];
    p.life += dt;
    if (p.life >= p.max) { particles.splice(k, 1); continue; }
    p.x += p.vx * dt; p.y += p.vy * dt; p.vx *= 1 - dt * 2.5; p.vy *= 1 - dt * 2.5; p.vy += 14 * dt;
  }
  if (particles.length) busy = true;
  draw(now);
  if (busy) raf = requestAnimationFrame(frame);
}

function draw(now) {
  if (!S || !P.main.length) return;
  const { W, H, wrap } = S.cfg, T = S.T, PW = S.PW;
  const w = W * T, h = H * T;
  ctx.fillStyle = pal.bg; ctx.fillRect(0, 0, w, h);

  const sx = S.src % W, sy = (S.src / W) | 0;
  drawHalo(ctx, w, h, (sx + 0.5) * T, (sy + 0.5) * T, Math.round(S.haloR || T * 1.7), wrap ? w : 0, wrap ? h : 0, S.solved ? 0.34 : 0.42);

  // trame des tuiles verrouillées
  for (let i = 0; i < S.tiles.length; i++) {
    const t = S.tiles[i];
    if (!t.shown || !t.locked) continue;
    const x = (i % W) * T, y = ((i / W) | 0) * T;
    ctx.fillStyle = pal.bg; ctx.fillRect(x + 1, y + 1, T - 2, T - 2);
    ctx.fillStyle = P.main[t.fixed ? 6 : 4]; ctx.fillRect(x + 1, y + 1, T - 2, T - 2);
    if (t.fixed) { ctx.fillStyle = pal.ink; ctx.fillRect(x + 2, y + 2, 3, 3); }
  }

  // repères de grille
  ctx.fillStyle = pal.ink;
  for (let gy = wrap ? 0 : 1; gy < H; gy++) for (let gx = wrap ? 0 : 1; gx < W; gx++) ctx.fillRect(gx * T - 1, gy * T - 1, 2, 2);

  // conduits
  for (let i = 0; i < S.tiles.length; i++) {
    const t = S.tiles[i];
    if (!t.shown) continue;
    let x = (i % W) * T;
    const y = ((i / W) | 0) * T;
    if (t.shake > 0) x += Math.round(Math.sin(t.shake * 26) * 2 * t.shake);
    const kind = i === S.src ? 'src' : t.deg === 1 ? 'gem' : 'pipe';
    if (t.a === t.r) {
      drawTile(ctx, P.main, x, y, T, PW, rotN(t.sol, t.r), t.p, kind);
    } else {
      sctx.clearRect(0, 0, T, T);
      drawTile(sctx, P.spr, 0, 0, T, PW, t.sol, t.p, kind);
      const ang = Math.round(t.a * 4) / 4 * Math.PI / 2; // rotation par paliers de 22,5°
      ctx.save();
      ctx.translate(x + T / 2, y + T / 2);
      ctx.rotate(ang);
      ctx.drawImage(spr, -T / 2, -T / 2);
      ctx.restore();
    }
    if (t.flash > 0) { ctx.fillStyle = P.main[Math.min(16, Math.ceil(t.flash * 7))]; ctx.fillRect(x, y, T, T); }
  }

  // étincelles
  ctx.fillStyle = pal.ink;
  for (const p of particles) ctx.fillRect(Math.round(p.x), Math.round(p.y), p.s, p.s);
}

/* ---------------------------------------------------------
   Entrées
   --------------------------------------------------------- */
let press = null, pressT = 0;
function cellAt(e) {
  const r = cv.getBoundingClientRect();
  const s = r.width / S.cfg.W;
  const x = Math.floor((e.clientX - r.left) / s), y = Math.floor((e.clientY - r.top) / s);
  if (x < 0 || y < 0 || x >= S.cfg.W || y >= S.cfg.H) return -1;
  return y * S.cfg.W + x;
}
cv.addEventListener('pointerdown', e => {
  Sound.init();
  if (!S) return;
  if (S.solved) { e.preventDefault(); goNext(); return; }
  const i = cellAt(e); if (i < 0) return;
  e.preventDefault();
  clearTimeout(pressT);
  press = { i, x: e.clientX, y: e.clientY, long: false, shift: e.shiftKey };
  if (e.button === 2) { press.long = true; toggleLock(i); return; }
  if (e.button !== 0) { press = null; return; }
  pressT = setTimeout(() => { if (press) { press.long = true; toggleLock(press.i); } }, 420);
});
cv.addEventListener('pointermove', e => {
  if (press && !press.long && Math.hypot(e.clientX - press.x, e.clientY - press.y) > 12) { clearTimeout(pressT); press = null; }
});
cv.addEventListener('pointerup', () => {
  clearTimeout(pressT);
  if (!press) return;
  const p = press; press = null;
  if (p.long || !S || S.solved) return;
  if (S.lockMode) toggleLock(p.i);
  else rotate(p.i, p.shift ? -1 : 1);
});
cv.addEventListener('pointercancel', () => { clearTimeout(pressT); press = null; });
cv.addEventListener('contextmenu', e => e.preventDefault());

$('#t-undo').addEventListener('click', () => { Sound.init(); undo(); });
$('#t-hint').addEventListener('click', () => { Sound.init(); hint(); });
$('#t-reset').addEventListener('click', () => { Sound.init(); resetLevel(); });
$('#t-lock').addEventListener('click', () => {
  Sound.init(); Sound.ui();
  setLockMode(!S.lockMode);
  toast(S.lockMode ? 'Mode verrou — touche une tuile pour la verrouiller' : 'Mode rotation', 1500);
});

document.addEventListener('keydown', e => {
  if (e.key === 'Escape') {
    if ($('.modal.open')) { closeModals(); return; }
    if (current !== 'home') back();
    return;
  }
  if (current !== 'game' || !S || $('.modal.open')) return;
  const k = e.key.toLowerCase();
  if (S.solved && (k === ' ' || k === 'enter')) { e.preventDefault(); goNext(); }
  else if (k === 'z') { e.preventDefault(); undo(); }
  else if (k === 'h') hint();
  else if (k === 'l' && !S.solved) $('#t-lock').click();
  else if (k === 'r' && !e.ctrlKey && !e.metaKey) resetLevel();
});

/* ---------- menus ---------- */
$$('[data-back]').forEach(b => b.addEventListener('click', () => { Sound.init(); Sound.ui(); back(); }));
$('#btn-play').addEventListener('click', () => {
  Sound.init(); Sound.ui();
  const nx = nextLevel() || [TIERS.length - 1, PER_TIER - 1];
  gameFrom = 'home';
  startLevel(levelCfg(nx[0], nx[1]));
  nav('game');
});
$('#btn-levels').addEventListener('click', () => { Sound.init(); Sound.ui(); nav('levels'); });
$('#btn-help').addEventListener('click', () => { Sound.init(); Sound.ui(); openModal('m-help'); });
$('#btn-settings').addEventListener('click', () => {
  Sound.init(); Sound.ui();
  $('#s-sound').checked = store.d.st.sound;
  $('#s-vibe').checked = store.d.st.vibe;
  $('#s-free').checked = store.d.st.free;
  $('#s-reset').classList.remove('armed');
  $('.btn-main', $('#s-reset')).textContent = 'Effacer ma progression';
  buildPalettes();
  openModal('m-settings');
});
function buildPalettes() {
  $('#palettes').innerHTML = PALETTES.map(p => `
    <button class="pal" role="radio" aria-checked="${p.id === pal.id}" data-p="${p.id}">
      <span class="sw" style="background:linear-gradient(135deg, ${p.bg} 50%, ${p.ink} 50%)"></span>${p.name}
    </button>`).join('');
}
$('#palettes').addEventListener('click', e => {
  const b = e.target.closest('.pal'); if (!b) return;
  store.d.st.pal = b.dataset.p; store.save();
  applyPalette(b.dataset.p); buildPalettes(); Sound.ui();
});
['sound', 'vibe', 'free'].forEach(k => $('#s-' + k).addEventListener('change', e => {
  store.d.st[k] = e.target.checked; store.save(); Sound.ui(); refreshHome();
}));
$('#s-reset').addEventListener('click', e => {
  const b = e.currentTarget, lab = $('.btn-main', b);
  if (!b.classList.contains('armed')) { b.classList.add('armed'); lab.textContent = 'Sûr ? Touche encore'; return; }
  store.d = { st: store.d.st, seenHelp: true, lv: {}, cur: {} }; store.save();
  b.classList.remove('armed'); lab.textContent = 'Progression effacée';
  refreshHome();
});

/* ---------------------------------------------------------
   Démarrage
   --------------------------------------------------------- */
store.load();
hydrateIcons();
applyPalette(store.d.st.pal);
history.replaceState({ s: 'home' }, '');
refreshHome();
if (document.fonts) document.fonts.ready.then(() => { if (S && current === 'game') layout(); });

if ('serviceWorker' in navigator && location.protocol.startsWith('http')) {
  window.addEventListener('load', () => navigator.serviceWorker.register('sw.js').catch(() => {}));
}

window.Lumen = { generate, analyze, makeGrid, TIERS, levelCfg, get state() { return S; } };
})();
