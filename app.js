'use strict';
/* =========================================================
   Potències i operacions combinades · 1r ESO
   - Motor d'expressions (arbre), jerarquia i passos
   - Generadors aleatoris (sempre amb nombres naturals)
   - Interfície: teoria + pràctica
   ========================================================= */

/* ---------------- Utilitats ---------------- */
const $ = (s, el = document) => el.querySelector(s);
const $$ = (s, el = document) => [...el.querySelectorAll(s)];
const rnd = (a, b) => a + Math.floor(Math.random() * (b - a + 1));
const pick = arr => arr[Math.floor(Math.random() * arr.length)];
const chance = p => Math.random() < p;
const range = (a, b) => Array.from({ length: b - a + 1 }, (_, i) => a + i);
const fmt = n => (n >= 1000 ? String(n).replace(/\B(?=(\d{3})+(?!\d))/g, '.') : String(n));
const P = (b, e) => `${b}<sup>${e}</sup>`;
function parseNat(s) {
  s = String(s ?? '').trim().replace(/\s+/g, '');
  if (/^\d+$/.test(s)) return parseInt(s, 10);
  if (/^\d{1,3}(\.\d{3})+$/.test(s)) return parseInt(s.replace(/\./g, ''), 10);
  return null;
}
function divisors(n) { const d = []; for (let i = 2; i < n; i++) if (n % i === 0) d.push(i); return d; }
const store = {
  get(k, d) { try { const v = localStorage.getItem(k); return v === null ? d : JSON.parse(v); } catch (e) { return d; } },
  set(k, v) { try { localStorage.setItem(k, JSON.stringify(v)); } catch (e) { /* sense emmagatzematge */ } },
};

/* ---------------- Arbre d'expressions ---------------- */
let _id = 0;
const num = v => ({ t: 'num', v, id: ++_id });
const bin = (op, l, r) => ({ t: 'bin', op, l, r, id: ++_id });
const pow = (b, e) => ({ t: 'pow', b, e, id: ++_id });
const sqrt = a => ({ t: 'sqrt', a, id: ++_id });
const par = e => ({ t: 'par', e, id: ++_id });

const kids = n => n.t === 'bin' ? [n.l, n.r] : n.t === 'pow' ? [n.b] : n.t === 'sqrt' ? [n.a] : n.t === 'par' ? [n.e] : [];
const isOp = n => n.t === 'bin' || n.t === 'pow' || n.t === 'sqrt';
const prio = n => n.t === 'bin' ? (n.op === '+' || n.op === '-' ? 1 : 2) : 3;
const ready = n => n.t === 'bin' ? n.l.t === 'num' && n.r.t === 'num'
  : n.t === 'pow' ? n.b.t === 'num'
  : n.t === 'sqrt' ? n.a.t === 'num' : false;

// Valor d'un subarbre (NaN si en algun moment no és natural)
function val(n) {
  switch (n.t) {
    case 'num': return n.v;
    case 'par': return val(n.e);
    case 'pow': return val(n.b) ** n.e;
    case 'sqrt': { const a = val(n.a), r = Math.round(Math.sqrt(a)); return r * r === a ? r : NaN; }
    case 'bin': {
      const a = val(n.l), b = val(n.r);
      switch (n.op) {
        case '+': return a + b;
        case '-': return a >= b ? a - b : NaN;
        case '·': return a * b;
        case ':': return b > 0 && a % b === 0 ? a / b : NaN;
      }
    }
  }
  return NaN;
}
// Calcula una operació que ja té els operands calculats
function compute(n) {
  if (n.t === 'pow') { const v = n.b.v ** n.e; return v > 1e12 ? { err: 'El nombre és massa gran.' } : { v }; }
  if (n.t === 'sqrt') {
    const r = Math.round(Math.sqrt(n.a.v));
    return r * r === n.a.v ? { v: r } : { err: `√${fmt(n.a.v)} no és un nombre natural (${fmt(n.a.v)} no és un quadrat perfecte).` };
  }
  const a = n.l.v, b = n.r.v;
  switch (n.op) {
    case '+': return { v: a + b };
    case '-': return a >= b ? { v: a - b } : { err: `${fmt(a)} − ${fmt(b)} no es pot fer amb nombres naturals.` };
    case '·': return a * b > 1e12 ? { err: 'El nombre és massa gran.' } : { v: a * b };
    case ':': return b !== 0 && a % b === 0 ? { v: a / b } : { err: `${fmt(a)} : ${fmt(b)} no és una divisió exacta.` };
  }
}
function findNode(n, id) {
  if (n.id === id) return n;
  for (const k of kids(n)) { const f = findNode(k, id); if (f) return f; }
  return null;
}
function inorder(n, out = []) {
  if (n.t === 'bin') { inorder(n.l, out); out.push(n.id); inorder(n.r, out); }
  else { if (isOp(n)) out.push(n.id); kids(n).forEach(k => inorder(k, out)); }
  return out;
}
// Substitueix nodes pel seu valor; treu els parèntesis que ja només tenen un nombre
function replaceNodes(n, map, created) {
  if (map.has(n.id)) { const m = num(map.get(n.id)); created.add(m.id); return m; }
  switch (n.t) {
    case 'num': return n;
    case 'par': { const e = replaceNodes(n.e, map, created); return e.t === 'num' ? e : { ...n, e }; }
    case 'bin': return { ...n, l: replaceNodes(n.l, map, created), r: replaceNodes(n.r, map, created) };
    case 'pow': return { ...n, b: replaceNodes(n.b, map, created) };
    case 'sqrt': return { ...n, a: replaceNodes(n.a, map, created) };
  }
}
const normalize = t => replaceNodes(t, new Map(), new Set());

/* Jerarquia:
   Cada parèntesi (i l'interior de cada arrel) és un "tram".
   En un tram, mentre quedin potències, arrels, multiplicacions o divisions,
   només es poden fer aquestes (si ja tenen els operands calculats).
   Quan no en queden, es fan les sumes i restes (d'esquerra a dreta). */
function contexts(root) {
  const ctxs = [], ctxOf = new Map();
  const walk = (n, ctx) => {
    if (n.t === 'num') return;
    if (n.t === 'par') { const c = { ops: [], owner: 'par' }; ctxs.push(c); walk(n.e, c); return; }
    ctx.ops.push(n); ctxOf.set(n.id, ctx);
    if (n.t === 'bin') { walk(n.l, ctx); walk(n.r, ctx); }
    else if (n.t === 'pow') walk(n.b, ctx);
    else { const c = { ops: [], owner: 'sqrt' }; ctxs.push(c); walk(n.a, c); }
  };
  const top = { ops: [], owner: null };
  ctxs.push(top);
  walk(root, top);
  return { ctxs, ctxOf };
}
function analyse(root) {
  const { ctxs, ctxOf } = contexts(root);
  const allowed = new Set();
  for (const c of ctxs) {
    const high = c.ops.some(o => prio(o) >= 2);
    for (const o of c.ops) if (ready(o) && (!high || prio(o) >= 2)) allowed.add(o.id);
  }
  return { allowed, ctxOf };
}

const KIND = {
  pow: ['potència', 'potències', 'una potència'],
  sqrt: ['arrel', 'arrels', 'una arrel'],
  '·': ['multiplicació', 'multiplicacions', 'una multiplicació'],
  ':': ['divisió', 'divisions', 'una divisió'],
  '+': ['suma', 'sumes', 'una suma'],
  '-': ['resta', 'restes', 'una resta'],
};
const KIND_ORDER = ['pow', 'sqrt', '·', ':', '+', '-'];
const kindKey = n => (n.t === 'bin' ? n.op : n.t);
function joinCat(parts) { return parts.length > 1 ? parts.slice(0, -1).join(', ') + ' i ' + parts[parts.length - 1] : parts[0] || ''; }
function labelFor(counts, allInner) {
  const parts = KIND_ORDER.filter(k => counts.get(k)).map(k => KIND[k][counts.get(k) > 1 ? 1 : 0]);
  let s = joinCat(parts);
  s = s.charAt(0).toUpperCase() + s.slice(1);
  return allInner ? s + ' (dins del parèntesi)' : s;
}

// Resolució agrupada (com a l'examen): a cada pas es fan totes les operacions que ja es poden fer
function solveSteps(root) {
  let tree = normalize(root);
  const steps = [{ tree, created: new Set(), label: '' }];
  let guard = 0;
  while (tree.t !== 'num' && guard++ < 60) {
    const { allowed, ctxOf } = analyse(tree);
    const map = new Map(), counts = new Map();
    let allInner = true;
    for (const id of allowed) {
      const n = findNode(tree, id);
      const r = compute(n);
      if (r.err) return { steps, error: r.err };
      map.set(id, r.v);
      const k = kindKey(n);
      counts.set(k, (counts.get(k) || 0) + 1);
      if (ctxOf.get(id).owner !== 'par') allInner = false;
    }
    const created = new Set();
    tree = replaceNodes(tree, map, created);
    steps.push({ tree, created, label: labelFor(counts, allInner) });
  }
  return { steps, value: tree.v };
}

/* Resolució per fases, en l'ordre estricte de la jerarquia (per a "Resol la teva operació"):
   1 tot el que hi ha dins dels parèntesis (i dins de les arrels), de dins cap a fora;
   2 totes les potències i arrels; 3 totes les multiplicacions i divisions; 4 totes les sumes i restes.
   Dins dels parèntesis també es fa per ordre: potències, després · i :, després + i −. */
const opClass = n => (n.t === 'pow' || n.t === 'sqrt') ? 1 : (n.op === '·' || n.op === ':') ? 2 : 3;
const PHASES = [
  { title: 'Parèntesis', tex: ['(\\ )', '[\\ ]'], none: 'No hi ha parèntesis.' },
  { title: 'Potències i arrels', tex: ['a^{n}', '\\sqrt{\\ }'], none: 'No hi ha potències ni arrels.', done: 'Ja no en queda cap.' },
  { title: 'Multiplicacions i divisions', tex: ['\\Large\\cdot', ':'], none: 'No hi ha multiplicacions ni divisions.', done: 'Ja no en queda cap.' },
  { title: 'Sumes i restes', tex: ['+', '-'], none: 'No hi ha sumes ni restes.', done: 'Ja no en queda cap.' },
];
function solvePhased(root) {
  let tree = normalize(root);
  const start = tree;
  const phases = PHASES.map((p, i) => ({ n: i + 1, ...p, steps: [] }));
  // operacions de la classe L que es poden fer als trams triats (sense res de classe inferior pendent al tram)
  const pickOps = (inner, L) => {
    const { ctxs, ctxOf } = contexts(tree);
    const ids = [];
    for (const c of ctxs) {
      if (!!c.owner !== inner || c.ops.some(o => opClass(o) < L)) continue;
      for (const o of c.ops) if (opClass(o) === L && ready(o)) ids.push(o.id);
    }
    return { ids, ctxOf };
  };
  const apply = (phase, ids, ctxOf, inner) => {
    const map = new Map(), counts = new Map(), owners = new Set(), cs = new Set();
    for (const id of ids) {
      const n = findNode(tree, id);
      const r = compute(n);
      if (r.err) return r.err;
      map.set(id, r.v);
      counts.set(kindKey(n), (counts.get(kindKey(n)) || 0) + 1);
      owners.add(ctxOf.get(id).owner); cs.add(ctxOf.get(id));
    }
    let label = labelFor(counts, false);
    if (inner) {
      const pl = cs.size > 1;
      label += owners.size > 1 ? ' (dins dels parèntesis i de les arrels)'
        : owners.has('sqrt') ? (pl ? ' (dins de les arrels)' : ' (dins de l\'arrel)')
        : (pl ? ' (dins dels parèntesis)' : ' (dins del parèntesi)');
    }
    const created = new Set();
    tree = replaceNodes(tree, map, created);
    phase.steps.push({ tree, created, label });
    return null;
  };
  const had = [false, false, false, false];
  contexts(start).ctxs.forEach(c => c.ops.forEach(o => { had[opClass(o)] = true; if (c.owner) had[0] = true; }));
  phases.forEach((p, i) => { p.had = had[i]; });
  let guard = 0;
  // fase 1: dins dels parèntesis i de les arrels
  while (guard++ < 60) {
    let did = false;
    for (let L = 1; L <= 3 && !did; L++) {
      const { ids, ctxOf } = pickOps(true, L);
      if (ids.length) {
        const err = apply(phases[0], ids, ctxOf, true);
        if (err) return { start, phases, error: err, stop: 0 };
        did = true;
      }
    }
    if (!did) break;
  }
  // fases 2, 3 i 4: fora dels parèntesis
  for (let L = 1; L <= 3; L++) {
    while (guard++ < 120) {
      const { ids, ctxOf } = pickOps(false, L);
      if (!ids.length) break;
      const err = apply(phases[L], ids, ctxOf, false);
      if (err) return { start, phases, error: err, stop: L };
    }
  }
  return { start, phases, value: tree.v };
}

/* ---------------- Dibuix d'expressions ---------------- */
function parDepth(n) {
  if (n.t === 'num') return 0;
  const d = Math.max(0, ...kids(n).map(parDepth));
  return n.t === 'par' ? d + 1 : d;
}
/* ---- Format LaTeX amb KaTeX (si no carrega, es fa servir l'HTML propi) ---- */
const KX = () => typeof katex !== 'undefined';
// o.sel pot ser un id o un conjunt d'ids (diverses operacions seleccionades)
const isSel = (o, id) => o.sel instanceof Set ? o.sel.has(id) : o.sel === id;
const KOPTS = { throwOnError: false, strict: 'ignore', trust: c => c.command === '\\htmlData' || c.command === '\\htmlClass' };
function texToHtml(t) {
  return t.replace(/\\htmlData\{[^}]*\}/g, '').replace(/\\htmlClass\{[^}]*\}/g, '')
    .replace(/\\left|\\right|\\mathbin|\\mathbf|\\,/g, '').replace(/\\cdot/g, '·').replace(/\\dots/g, '…')
    .replace(/\\sqrt/g, '√').replace(/\\\{/g, '⦃').replace(/\\\}/g, '⦄')
    .replace(/\^\{([^{}]*)\}/g, '<sup>$1</sup>').replace(/\^(\d)/g, '<sup>$1</sup>')
    .replace(/-/g, '−').replace(/[{}]/g, '').replace(/⦃/g, '{').replace(/⦄/g, '}');
}
function M(tex, cls = '') {
  if (KX()) { try { return `<span class="tex ${cls}">${katex.renderToString(tex, KOPTS)}</span>`; } catch (e) { /* cau a HTML */ } }
  return `<span class="m ${cls}">${texToHtml(tex)}</span>`;
}
const TEXOP = { '+': '+', '-': '-', '·': '\\cdot', ':': ':' };
const KEYN = { '+': 'suma', '-': 'resta', '·': 'mul', ':': 'div', pow: 'pow', sqrt: 'sqrt' };
const KNAME = { suma: 'suma', resta: 'resta', mul: 'multiplicació', div: 'divisió', pow: 'potència', sqrt: 'arrel' };
// o.kinds: afegeix classes per tipus (per a la jerarquia interactiva de la teoria)
function texTree(n, o = {}) {
  const T = x => texTree(x, o);
  const wrap = (id, s) => (isSel(o, id) || o.hint === id)
    ? `\\htmlClass{node${isSel(o, id) ? ' sel' : ''}${o.hint === id ? ' hint' : ''}}{${s}}` : s;
  const clk = (id, k, s) => o.clickable ? `\\htmlData{id=${id}, k=${k}}{${s}}` : s;
  const kc = (k, s) => o.kinds ? `\\htmlClass{k-${k}}{${s}}` : s;
  switch (n.t) {
    case 'num': return o.created && o.created.has(n.id) ? `\\htmlClass{num new}{${fmt(n.v)}}` : `{${fmt(n.v)}}`;
    case 'par': {
      const d = parDepth(n);
      const [a, b] = d >= 3 ? ['\\{', '\\}'] : d === 2 ? ['[', ']'] : ['(', ')'];
      const inner = `\\left${a} ${T(n.e)} \\right${b}`;
      return o.kinds ? `\\htmlClass{k-par}{${inner}}` : inner;
    }
    case 'bin': {
      const k = KEYN[n.op];
      const kind = n.op === '+' || n.op === '-' ? 'sum' : 'mul';
      return wrap(n.id, `${T(n.l)} \\mathbin{${clk(n.id, k, kc(kind, `\\htmlClass{op}{${TEXOP[n.op]}}`))}} ${T(n.r)}`);
    }
    case 'pow': return wrap(n.id, clk(n.id, 'pow', kc('pow', `{${T(n.b)}}^{${n.e}}`)));
    case 'sqrt': return wrap(n.id, clk(n.id, 'sqrt', kc('pow', `\\sqrt{${T(n.a)}}`)));
  }
  return '';
}
// Expressió en format LaTeX (o HTML si KaTeX no és disponible)
function exprHTML(n, o = {}) { return KX() ? M(texTree(n, o)) : renderTree(n, o); }
// Accessibilitat per als elements clicables generats per KaTeX
function decorate(root) {
  $$('[data-id]', root).forEach(el => {
    if (el.closest('.katex-mathml')) return;
    el.tabIndex = 0; el.setAttribute('role', 'button');
    if (el.dataset.k) el.setAttribute('aria-label', KNAME[el.dataset.k] || 'operació');
  });
}

// Signe d'arrel dibuixat: s'estira amb el que hi ha a dins i s'uneix amb la ratlla de dalt
const RAD = '<svg class="rad" viewBox="0 0 10 20" preserveAspectRatio="none" aria-hidden="true"><path d="M0.6 12.2 L2.6 11 L5.2 19.2 L10 0.5"/></svg>';
function upgradeRoots(root = document) {
  $$('.sq', root).forEach(el => { if (!el.querySelector('svg.rad')) el.insertAdjacentHTML('afterbegin', RAD); });
}
const OP_NAMES ={ '+': 'suma', '-': 'resta', '·': 'multiplicació', ':': 'divisió' };
function renderTree(n, o = {}) {
  const R = x => renderTree(x, o);
  const extra = id => (isSel(o, id) ? ' sel' : '') + (o.hint === id ? ' hint' : '');
  const click = (id, name) => (o.clickable ? ` data-id="${id}" tabindex="0" role="button" aria-label="${name}"` : '');
  switch (n.t) {
    case 'num': return `<span class="num${o.created && o.created.has(n.id) ? ' new' : ''}">${fmt(n.v)}</span>`;
    case 'par': {
      const d = parDepth(n);
      const [a, b] = d >= 3 ? ['{', '}'] : d === 2 ? ['[', ']'] : ['(', ')'];
      return `<span class="paren">${a}</span>${R(n.e)}<span class="paren">${b}</span>`;
    }
    case 'bin': {
      const sym = n.op === '-' ? '−' : n.op;
      return `<span class="node${extra(n.id)}" data-node="${n.id}">${R(n.l)}<span class="op"${click(n.id, OP_NAMES[n.op])}>${sym}</span><wbr>${R(n.r)}</span>`;
    }
    case 'pow': return `<span class="node pw${extra(n.id)}" data-node="${n.id}"${click(n.id, 'potència')}>${R(n.b)}<sup>${n.e}</sup></span>`;
    case 'sqrt': return `<span class="node sq${extra(n.id)}" data-node="${n.id}"${click(n.id, 'arrel')}>${RAD}<span class="radicand">${R(n.a)}</span></span>`;
  }
  return '';
}
function toText(n) {
  switch (n.t) {
    case 'num': return String(n.v);
    case 'par': return '(' + toText(n.e) + ')';
    case 'bin': return toText(n.l) + n.op + toText(n.r);
    case 'pow': return toText(n.b) + '^' + n.e;
    case 'sqrt': return '√(' + toText(n.a) + ')';
  }
}
function stepsHTML(steps, upto, withFirst) {
  let h = '<div class="steps">';
  steps.forEach((st, i) => {
    if (i > upto || (i === 0 && !withFirst)) return;
    h += `<div class="step"><span class="eq">${i === 0 ? '' : '='}</span><span class="expr">${exprHTML(st.tree, { created: st.created })}</span><span class="step-label">${st.label || ''}</span></div>`;
  });
  return h + '</div>';
}
// Resolució per fases: l'operació inicial i, a sota, les 4 fases de la jerarquia
// upto: quantes línies es mostren (per anar pas a pas); les fases buides surten quan s'hi arriba
const phasedCount = sol => sol.phases.reduce((s, p) => s + p.steps.length, 0);
function phasedHTML(sol, upto = Infinity) {
  const line = st => `<div class="step"><span class="eq">=</span><span class="expr">${exprHTML(st.tree, { created: st.created })}</span><span class="step-label">${st.label}</span></div>`;
  let h = `<div class="steps"><div class="step"><span class="eq"></span><span class="expr">${exprHTML(sol.start, {})}</span><span class="step-label"></span></div></div>`;
  const last = sol.error ? sol.stop : 3;
  let cum = 0;
  sol.phases.slice(0, last + 1).forEach((p, i) => {
    const before = cum; cum += p.steps.length;
    if (p.steps.length ? upto <= before : upto < before) return;
    p = { ...p, steps: p.steps.slice(0, upto - before) };
    const empty = !p.steps.length && !(sol.error && i === last);
    h += `<div class="phase${empty ? ' empty' : ''}">
      <div class="phase-h"><span class="phase-n">${p.n}</span><b>${p.title}</b>${p.tex.map(t => `<span class="sym">${M(t)}</span>`).join('')}${empty ? `<small>${p.had && p.done ? p.done : p.none}</small>` : ''}</div>
      ${p.steps.length ? `<div class="steps">${p.steps.map(line).join('')}</div>` : ''}
    </div>`;
  });
  return h;
}

/* ---------------- Lector d'expressions (per "Resol la teva operació") ---------------- */
// Substitueix una ordre LaTeX amb n arguments entre claus: \sqrt{81} -> fn('81')
function replaceTexCmd(t, cmd, n, fn) {
  let i, guard = 0;
  while ((i = t.indexOf(cmd)) !== -1 && guard++ < 100) {
    let j = i + cmd.length;
    const args = [];
    for (let k = 0; k < n; k++) {
      while (t[j] === ' ') j++;
      if (t[j] === '[') { while (j < t.length && t[j] !== ']') j++; j++; }   // \sqrt[n]{..}: s'ignora l'índex
      if (t[j] !== '{') { args.push(t[j] || ''); j++; continue; }
      let d = 0; const s = j;
      for (; j < t.length; j++) { if (t[j] === '{') d++; else if (t[j] === '}' && --d === 0) { j++; break; } }
      args.push(t.slice(s + 1, j - 1));
    }
    t = t.slice(0, i) + fn(...args) + t.slice(j);
  }
  return t;
}
// LaTeX de l'editor visual (MathLive) -> text que entén parseExpr
function latexToPlain(tex) {
  let t = String(tex || '')
    .replace(/\\left|\\right|\\mleft|\\mright|\\bigl|\\bigr|\\Bigl|\\Bigr/g, '')
    .replace(/\\cdot|\\times|\\ast/g, '·').replace(/\\div|\\colon/g, ':')
    .replace(/\\lbrack/g, '[').replace(/\\rbrack/g, ']').replace(/\\lbrace/g, '(').replace(/\\rbrace/g, ')')
    .replace(/\\placeholder\{[^}]*\}/g, '')
    .replace(/\\(,|;|!|quad|qquad| )/g, ' ');
  t = replaceTexCmd(t, '\\frac', 2, (a, b) => `(${a}):(${b})`);
  t = replaceTexCmd(t, '\\sqrt', 1, a => `√(${a})`);
  t = t.replace(/\^\{\s*(\d+)\s*\}/g, '^$1').replace(/[{}]/g, '');
  return t;
}
function parseExpr(str) {
  const SUP = { '⁰': '0', '¹': '1', '²': '2', '³': '3', '⁴': '4', '⁵': '5', '⁶': '6', '⁷': '7', '⁸': '8', '⁹': '9' };
  let s = String(str)
    .replace(/[⁰¹²³⁴⁵⁶⁷⁸⁹]+/g, m => '^' + [...m].map(c => SUP[c]).join(''))
    .replace(/sqrt|arrel/gi, '√').replace(/r\s*\(/gi, '√(')
    .replace(/\s+/g, '')
    .replace(/[x×*·]/gi, '·').replace(/[÷/]/g, ':')
    .replace(/[−–—]/g, '-')
    .replace(/[[{]/g, '(').replace(/[\]}]/g, ')')
    .replace(/(\d)\.(?=\d{3}(\D|$))/g, '$1');
  let i = 0;
  const fail = () => { throw new Error('sintaxi'); };
  const intLit = () => { const m = /^\d+/.exec(s.slice(i)); if (!m) fail(); i += m[0].length; return parseInt(m[0], 10); };
  function expr() { let n = term(); while (s[i] === '+' || s[i] === '-') { const op = s[i++]; n = bin(op, n, term()); } return n; }
  function term() { let n = factor(); while (s[i] === '·' || s[i] === ':') { const op = s[i++]; n = bin(op, n, factor()); } return n; }
  function factor() {
    const b = atom();
    if (s[i] === '^') { i++; const e = intLit(); if (e > 30) fail(); return pow(b, e); }
    return b;
  }
  function atom() {
    if (s[i] === '(') { i++; const e = expr(); if (s[i] !== ')') fail(); i++; return par(e); }
    if (s[i] === '√') { i++; const a = atom(); return sqrt(a.t === 'par' ? a.e : a); }
    return num(intLit());
  }
  if (!s) fail();
  const t = expr();
  if (i !== s.length) fail();
  return t;
}

/* ================= GENERADOR 1: operacions combinades ================= */
const COMB = {
  1: { n: [2, 10], ops: [3, 4], max: 120, pows: [[2, 2], [3, 2], [4, 2], [5, 2], [2, 3], [3, 3], [10, 2]], roots: [2, 10],
       parP: 0.3, depth: 1, divP: 0.25, terms: [2, 3], factors: [1, 2], prP: 0.35 },
  2: { n: [2, 15], ops: [5, 7], max: 400, pows: [...range(2, 10).map(b => [b, 2]), ...range(2, 5).map(b => [b, 3]), [2, 4], [2, 5], [3, 4]], roots: [2, 12],
       parP: 0.35, depth: 1, divP: 0.35, terms: [2, 3], factors: [1, 3], prP: 0.35 },
  3: { n: [2, 20], ops: [7, 11], max: 1000, pows: [...range(2, 12).map(b => [b, 2]), ...range(2, 6).map(b => [b, 3]), [2, 4], [2, 5], [2, 6], [3, 4], [10, 3]], roots: [2, 15],
       parP: 0.3, depth: 2, divP: 0.35, terms: [2, 4], factors: [1, 3], prP: 0.35, sqrtExprP: 0.35, powParP: 0.3 },
};

function valueNode(L, d) {
  const opts = [num(d)];
  for (const [b, e] of L.pows) if (b ** e === d) opts.push(pow(num(b), e));
  if (d >= L.roots[0] && d <= L.roots[1]) opts.push(sqrt(num(d * d)));
  return chance(0.55) ? opts[0] : pick(opts);
}
function gPowPar() {
  const b = rnd(2, 5), e = b <= 3 && chance(0.4) ? 3 : 2;
  let inner;
  switch (rnd(0, 2)) {
    case 0: { const x = rnd(1, b - 1); inner = bin('+', num(x), num(b - x)); break; }
    case 1: { const y = rnd(1, 9); inner = bin('-', num(b + y), num(y)); break; }
    default: { const y = rnd(2, 5); inner = bin(':', num(b * y), num(y)); }
  }
  return pow(par(inner), e);
}
function gSqrtExpr() {
  const opt = rnd(0, 3);
  if (opt === 0) {
    const [a, b] = pick([[3, 4], [4, 3], [6, 8], [8, 6], [5, 12]]);
    return sqrt(bin('+', pow(num(a), 2), pow(num(b), 2)));
  }
  const r = rnd(3, 10), N = r * r;
  if (opt === 1) { const x = rnd(Math.ceil(N / 4), N - 1); return sqrt(bin('+', num(x), num(N - x))); }
  if (opt === 2) { const y = rnd(2, 20); return sqrt(bin('-', num(N + y), num(y))); }
  const ds = divisors(N).filter(d => d < r);
  if (!ds.length) return sqrt(num(N));
  const d = pick(ds);
  return sqrt(bin('·', num(d), num(N / d)));
}
function gAtom(L, depth, F) {
  const pp = F.noPar ? 0 : depth === 0 ? L.parP * (F.morePar ? 1.6 : 1) : L.parP * 0.5;
  const r = Math.random();
  if (depth < L.depth && r < pp) {
    if (L.powParP && chance(L.powParP)) return gPowPar();
    return par(gExpr(L, depth + 1, depth + 1 < L.depth && chance(0.3) ? 3 : 2, F));
  }
  if (r < pp + L.prP) {
    if (chance(0.55)) { const [b, e] = pick(L.pows); return pow(num(b), e); }
    if (L.sqrtExprP && !F.noPar && chance(L.sqrtExprP)) return gSqrtExpr();
    const k = rnd(L.roots[0], L.roots[1]);
    return sqrt(num(k * k));
  }
  return num(rnd(L.n[0], L.n[1]));
}
function gTerm(L, depth, nF, F) {
  let node, forceDiv = false;
  if (nF >= 2 && chance(L.divP)) { node = num(rnd(2, L.n[1] > 10 ? 9 : 5) * rnd(2, depth ? 5 : 9)); forceDiv = true; }
  else node = gAtom(L, depth, F);
  let v = val(node);
  if (!Number.isFinite(v)) return node;
  for (let k = 1; k < nF; k++) {
    if ((k === 1 && forceDiv) || chance(L.divP * 0.6)) {
      const ds = divisors(v);
      if (ds.length) { const d = pick(ds); node = bin(':', node, valueNode(L, d)); v /= d; continue; }
    }
    let ok = false;
    for (let t = 0; t < 15 && !ok; t++) {
      const a = gAtom(L, depth, F), w = val(a);
      if (w > 1 && v * w <= L.max) { node = bin('·', node, a); v *= w; ok = true; }
    }
    if (!ok) break;
  }
  return node;
}
function gExpr(L, depth, nT, F) {
  const nf = () => rnd(L.factors[0], depth > 0 ? Math.min(2, L.factors[1]) : L.factors[1]);
  let node = gTerm(L, depth, nf(), F), v = val(node);
  for (let k = 1; k < nT; k++) {
    if (v > 1 && chance(0.5)) {
      let ok = false;
      for (let t = 0; t < 25 && !ok; t++) {
        const tm = gTerm(L, depth, nf(), F), w = val(tm);
        if (w >= 1 && w < v) { node = bin('-', node, tm); v -= w; ok = true; }
      }
      if (ok) continue;
    }
    for (let t = 0; t < 25; t++) {
      const tm = gTerm(L, depth, nf(), F), w = val(tm);
      if (Number.isFinite(w) && v + w <= L.max) { node = bin('+', node, tm); v += w; break; }
    }
  }
  return node;
}
function treeStats(n, s = { ops: 0, pr: false, p1: false, p2: false, par: 0 }) {
  if (n.t === 'par') s.par++;
  if (isOp(n)) { s.ops++; const p = prio(n); if (p === 3) s.pr = true; else if (p === 2) s.p2 = true; else s.p1 = true; }
  kids(n).forEach(k => treeStats(k, s));
  return s;
}
const maxNum = n => (n.t === 'num' ? n.v : Math.max(...kids(n).map(maxNum)));
// Parèntesis que no canvien res: (a+b)+c, a+(b+c), (a+b)−c o tota l'expressió entre parèntesis
function uselessPar(n, parent = null, side = null) {
  if (n.t === 'par') {
    if (!parent) return true;
    if (parent.t === 'bin' && (parent.op === '+' || (parent.op === '-' && side === 'l'))) return true;
  }
  if (n.t === 'bin') return uselessPar(n.l, n, 'l') || uselessPar(n.r, n, 'r');
  return kids(n).some(k => uselessPar(k, n, null));
}
const RESULT_MAX = 50; // resultat màxim de les operacions combinades de pràctica
const FALLBACK = { 1: '3^2+4·5', 2: '2^2·5-14:7·3^2', 3: '[20-(3+1)^2]·√9+12:2^2' };

// sub: 'all' | 'nopar' | 'par'
function genCombined(level, sub = 'all') {
  const L = COMB[level];
  const F = { noPar: sub === 'nopar', morePar: sub === 'par' };
  for (let tries = 0; tries < 6000; tries++) {
    const tree = normalize(gExpr(L, 0, rnd(L.terms[0], L.terms[1]), F));
    const v = val(tree);
    // resultat final entre 0 i 50 (el 0 surt de tant en tant)
    if (!Number.isFinite(v) || v < 0 || v > RESULT_MAX) continue;
    if (v === 0 && chance(0.75)) continue;
    const st = treeStats(tree);
    if (st.ops < L.ops[0] || st.ops > L.ops[1]) continue;
    if (!st.pr || !st.p1 || !st.p2) continue;
    if (sub === 'par' && !st.par) continue;
    if (sub === 'nopar' && st.par) continue;
    if (st.par && uselessPar(tree)) continue;
    if (level === 3 && sub === 'all' && !st.par && chance(0.7)) continue;
    const sol = solveSteps(tree);
    if (sol.error || sol.steps.some(x => maxNum(x.tree) > L.max)) continue;
    if (level === 3 && sol.steps.length < 4) continue;
    return tree;
  }
  return normalize(parseExpr(sub === 'nopar' ? '2^2·5-14:7·3^2' : FALLBACK[level]));
}

/* ================= GENERADOR 2: propietats de les potències ================= */
const PROP = {
  1: { bases: [2, 3, 5, 10], maxE: { 2: 8, 3: 5, 5: 4, 10: 5 }, eMax: 6 },
  2: { bases: [2, 3, 4, 5, 10], maxE: { 2: 10, 3: 6, 4: 5, 5: 5, 10: 6 }, eMax: 9 },
  3: { bases: [2, 3, 4, 5, 6, 7, 10], maxE: { 2: 12, 3: 7, 4: 6, 5: 5, 6: 4, 7: 4, 10: 7 }, eMax: 12 },
};
// Quines formes surten segons el subtipus i el nivell
const PFORMS = {
  mul: { 1: ['mul2'], 2: ['mul3'], 3: ['mul4'] },
  div: { 1: ['div2'], 2: ['div3'], 3: ['div4'] },
  pp: { 1: ['pp'], 2: ['pp', 'ppbig'], 3: ['pp3'] },
  comb: { 1: ['muldiv', 'divmul'], 2: ['ppmul', 'gdiv', 'muldiv'], 3: ['gdiv', 'gmul', 'mulpp', 'ppdiv'] },
};
// "Totes barrejades": cada vegada surt a l'atzar un dels quatre subtipus anteriors
const pickForm = (sub, level) => pick(PFORMS[sub === 'all' ? pick(['mul', 'div', 'pp', 'comb']) : sub][level]);

const RULES = {
  mul: `<b>Producte</b> de potències de la mateixa base: es deixa la base i se <b>sumen</b> els exponents (<span class="m">a<sup>m</sup> · a<sup>n</sup> = a<sup>m+n</sup></span>).`,
  div: `<b>Quocient</b> de potències de la mateixa base: es deixa la base i es <b>resten</b> els exponents (<span class="m">a<sup>m</sup> : a<sup>n</sup> = a<sup>m−n</sup></span>).`,
  pp: `<b>Potència d'una potència</b>: es deixa la base i es <b>multipliquen</b> els exponents (<span class="m">(a<sup>m</sup>)<sup>n</sup> = a<sup>m·n</sup></span>).`,
  group: `Comença pel que hi ha <b>dins del parèntesi</b>.`,
};

/* Arbre de potències de la mateixa base:
   p  = potència a^e          g = (x)^n (potència d'un parèntesi)
   op = x · y  o  x : y (sempre amb la mateixa base) */
let _pid = 0;
const pl = (b, e) => ({ t: 'p', b, e, id: ++_pid });
const pop = (op, l, r) => ({ t: 'op', op, l, r, id: ++_pid });
const pg = (x, n) => ({ t: 'g', x, n, id: ++_pid });
const pkids = n => n.t === 'op' ? [n.l, n.r] : n.t === 'g' ? [n.x] : [];
// cadena d'esquerra a dreta: pch(x0, '·', x1, ':', x2 ...)
function pch(...a) { let n = a[0]; for (let i = 1; i < a.length; i += 2) n = pop(a[i], n, a[i + 1]); return n; }
// exponent final (NaN si en algun moment quedaria un exponent < 1)
function pExp(n) {
  if (n.t === 'p') return n.e;
  if (n.t === 'g') return pExp(n.x) * n.n;
  const a = pExp(n.l), b = pExp(n.r), r = n.op === '·' ? a + b : a - b;
  return r >= 1 ? r : NaN;
}
const pReady = n => n.t === 'g' ? n.x.t === 'p' : n.t === 'op' ? n.l.t === 'p' && n.r.t === 'p' : false;
function pCompute(n) {
  if (n.t === 'g') return { e: n.x.e * n.n, expr: `${n.x.e}\\cdot ${n.n}`, rule: 'pp' };
  return n.op === '·'
    ? { e: n.l.e + n.r.e, expr: `${n.l.e}+${n.r.e}`, rule: 'mul' }
    : { e: n.l.e - n.r.e, expr: `${n.l.e}-${n.r.e}`, rule: 'div' };
}
function pBase(n) { return n.t === 'p' ? n.b : pBase(pkids(n)[0]); }
function pFind(n, id) { if (n.id === id) return n; for (const k of pkids(n)) { const f = pFind(k, id); if (f) return f; } return null; }
function pInorder(n, out = []) {
  if (n.t === 'op') { pInorder(n.l, out); out.push(n.id); pInorder(n.r, out); }
  else if (n.t === 'g') { pInorder(n.x, out); out.push(n.id); }
  return out;
}
// substitueix nodes per la potència resultant; exprs guarda l'expressió de l'exponent (3+4)
function pReplace(n, map, created, exprs) {
  if (map.has(n.id)) {
    const c = pCompute(n), m = pl(pBase(n), c.e);
    created.add(m.id); if (exprs) exprs.set(m.id, c.expr);
    return m;
  }
  if (n.t === 'op') return { ...n, l: pReplace(n.l, map, created, exprs), r: pReplace(n.r, map, created, exprs) };
  if (n.t === 'g') return { ...n, x: pReplace(n.x, map, created, exprs) };
  return n;
}
const isFlatChain = n => n.t === 'p' || (n.t === 'op' && isFlatChain(n.l) && isFlatChain(n.r));
// LaTeX de l'arbre (o.clickable, o.sel, o.hint, o.created, o.exprs)
function pTex(n, o = {}) {
  const R = x => pTex(x, o);
  const wrap = (id, s) => (isSel(o, id) || o.hint === id)
    ? `\\htmlClass{node${isSel(o, id) ? ' sel' : ''}${o.hint === id ? ' hint' : ''}}{${s}}` : s;
  const clk = (id, k, s) => o.clickable ? `\\htmlData{id=${id}, k=${k}}{${s}}` : s;
  switch (n.t) {
    case 'p': {
      const e = o.exprs && o.exprs.has(n.id) ? o.exprs.get(n.id) : n.e;
      const s = `{${n.b}}^{${e}}`;
      return o.created && o.created.has(n.id) ? `\\htmlClass{num new}{${s}}` : s;
    }
    case 'g': return wrap(n.id, clk(n.id, 'pp', `\\left(${R(n.x)}\\right)^{${n.n}}`));
    case 'op': return wrap(n.id, `${R(n.l)} \\mathbin{${clk(n.id, n.op === '·' ? 'mul' : 'div', `\\htmlClass{op}{${n.op === '·' ? '\\cdot' : ':'}}`)}} ${R(n.r)}`);
  }
  return '';
}
// Passos de la solució (com a l'examen): 2^{3+4} = 2^7
function pSolve(root) {
  const a = pBase(root), steps = [];
  let t = root, guard = 0;
  while (t.t !== 'p' && guard++ < 20) {
    if (isFlatChain(t)) {
      let ex = '', first = true;
      (function walk(n, sign) {
        if (n.t === 'p') { ex += (first ? '' : sign) + n.e; first = false; return; }
        walk(n.l, sign); walk(n.r, n.op === '·' ? '+' : '-');
      })(t, '+');
      steps.push(`{${a}}^{${ex}}`);
      t = pl(a, pExp(t));
      steps.push(pTex(t));
      break;
    }
    const map = new Map();
    (function walk(n) { if (pReady(n)) map.set(n.id, true); else pkids(n).forEach(walk); })(t);
    const exprs = new Map(), created = new Set();
    const next = pReplace(t, map, created, exprs);
    if (next.t === 'p') steps.push(pTex(next, { exprs }));
    steps.push(pTex(next));
    t = next;
  }
  return steps;
}

function genProp(level, sub = 'all') {
  const L = PROP[level];
  // primer es tria el tipus d'exercici i després es busquen nombres que hi encaixin
  // (així tots els tipus surten amb la mateixa freqüència)
  for (let round = 0; round < 6; round++) {
  const f = pickForm(sub, level);
  for (let t = 0; t < 4000; t++) {
    const a = pick(L.bases);
    const E = () => rnd(2, L.eMax), sm = () => rnd(2, 4), X = e => pl(a, e);
    let tree, rules;
    switch (f) {
      case 'mul2': tree = pch(X(E()), '·', X(E())); rules = ['mul']; break;
      case 'mul3': tree = pch(X(E()), '·', X(E()), '·', X(E())); rules = ['mul']; break;
      case 'mul4': tree = pch(X(E() - 1), '·', X(E() - 1), '·', X(E() - 1), '·', X(E() - 1)); rules = ['mul']; break;
      case 'div2': tree = pch(X(E()), ':', X(E())); rules = ['div']; break;
      case 'div3': tree = pch(X(rnd(6, 15)), ':', X(E()), ':', X(E())); rules = ['div']; break;
      case 'div4': tree = pch(X(rnd(10, 20)), ':', X(E()), ':', X(E()), ':', X(E())); rules = ['div']; break;
      case 'pp': tree = pg(X(sm()), sm()); rules = ['pp']; break;
      case 'ppbig': tree = pg(X(rnd(2, 5)), rnd(2, 3)); rules = ['pp']; break;
      case 'pp3': tree = pg(pg(X(rnd(1, 3)), 2), rnd(2, 3)); rules = ['pp']; break;
      case 'muldiv': tree = pch(X(E()), '·', X(E()), ':', X(E())); rules = ['mul', 'div']; break;
      case 'divmul': tree = pch(X(E()), ':', X(E()), '·', X(E())); rules = ['div', 'mul']; break;
      case 'ppmul': tree = pch(pg(X(sm()), sm()), '·', X(E())); rules = ['pp', 'mul']; break;
      case 'gdiv': tree = pch(pg(pch(X(E()), ':', X(E())), sm()), '·', X(E())); rules = ['group', 'div', 'pp', 'mul']; break;
      case 'gmul': tree = pch(pg(pch(X(E()), '·', X(E())), sm()), ':', X(E())); rules = ['group', 'mul', 'pp', 'div']; break;
      case 'mulpp': tree = pch(X(E()), '·', pg(X(sm()), sm()), ':', X(E())); rules = ['pp', 'mul', 'div']; break;
      case 'ppdiv': tree = pch(pg(X(sm()), sm()), ':', pg(X(sm()), sm())); rules = ['pp', 'div']; break;
      default: continue;
    }
    const s = pExp(tree);
    if (!(s >= 2 && s <= L.maxE[a])) continue;
    // evitem passos intermedis que donin exponent 1 (2^1 queda estrany)
    let tt = tree, ones = false, gg = 0;
    while (tt.t !== 'p' && gg++ < 30) {
      const id = pInorder(tt).find(x => pReady(pFind(tt, x)));
      if (pCompute(pFind(tt, id)).e === 1) { ones = true; break; }
      tt = pReplace(tt, new Map([[id, true]]), new Set());
    }
    if (ones) continue;
    const q = pTex(tree);
    return { a, s, v: a ** s, tree, q, steps: pSolve(tree), rules, key: f + '|' + q };
  }
  }
  const tree = pch(pl(2, 3), '·', pl(2, 4));
  return { a: 2, s: 7, v: 128, tree, q: pTex(tree), steps: pSolve(tree), rules: ['mul'], key: 'fallback' };
}

/* ================= INTERFÍCIE ================= */
if (typeof document !== 'undefined') document.addEventListener('DOMContentLoaded', init);

const LEVEL_NAMES = { 1: 'Bàsic', 2: 'Mitjà', 3: 'Avançat' };
const LEVEL_HELP = {
  comb: {
    1: 'Expressions curtes (3 o 4 operacions) amb nombres petits.',
    2: 'Com a l\'examen: 5 a 7 operacions amb potències, arrels, divisions i parèntesis.',
    3: 'Expressions llargues: claudàtors, potències de parèntesis i arrels amb operacions a dins.',
  },
  prop: {
    1: 'Una sola propietat cada vegada, amb exponents petits.',
    2: 'Com a l\'examen: tres potències o dues propietats seguides.',
    3: 'Diverses propietats encadenades i parèntesis, com l\'apartat e) de l\'examen.',
  },
};
const TYPE_NAMES = { comb: 'Operacions combinades', prop: 'Propietats de les potències' };

const S = {
  type: 'comb', subComb: 'all', subProp: 'all', level: 2, mode: 'guiat',
  stats: { ok: 0, total: 0, streak: 0, best: 0 },
  ex: null, lastKey: '',
};

function init() {
  // preferències guardades (només comoditat)
  const pref = store.get('pot-pref', {});
  Object.assign(S, {
    type: ['comb', 'prop', 'mix'].includes(pref.type) ? pref.type : S.type,
    subComb: pref.subComb || S.subComb, subProp: pref.subProp || S.subProp,
    level: [1, 2, 3].includes(pref.level) ? pref.level : S.level,
    mode: pref.mode === 'final' ? 'final' : 'guiat',
  });
  S.stats.best = store.get('pot-best', 0);

  // pestanyes
  $$('.tabs button').forEach(b => b.addEventListener('click', () => showTab(b.dataset.tab, true)));
  $$('[data-goto]').forEach(b => b.addEventListener('click', () => showTab(b.dataset.goto, true)));
  showTab(location.hash === '#practica' ? 'practica' : 'apren', false);

  renderStaticTex();
  upgradeRoots();
  initTheory();
  initPractice();
}

function showTab(tab, push) {
  $$('.tabs button').forEach(b => b.setAttribute('aria-selected', String(b.dataset.tab === tab)));
  $('#apren').hidden = tab !== 'apren';
  $('#practica').hidden = tab !== 'practica';
  if (push) { history.replaceState(null, '', tab === 'practica' ? '#practica' : '#'); window.scrollTo({ top: 0 }); }
}

/* ---------------- Teoria ---------------- */
// Converteix a LaTeX tots els elements amb data-tex
function renderStaticTex() {
  if (!KX()) return;
  $$('[data-tex]').forEach(el => { el.innerHTML = M(el.dataset.tex); el.classList.remove('m'); });
}
function initHierarchy() {
  const box = $('#hier-ex');
  if (!box) return;
  box.innerHTML = exprHTML(normalize(parseExpr('5^2-√25·2-(7-3·2)')), { kinds: true });
  const items = $$('#hier li');
  const select = li => {
    const on = li.getAttribute('aria-pressed') !== 'true';
    items.forEach(x => x.setAttribute('aria-pressed', 'false'));
    box.className = 'expr hier-ex';
    if (on) { li.setAttribute('aria-pressed', 'true'); box.classList.add('show-' + li.dataset.k); }
  };
  items.forEach(li => {
    li.addEventListener('click', () => select(li));
    li.addEventListener('keydown', e => { if (e.key === 'Enter' || e.key === ' ') { e.preventDefault(); select(li); } });
  });
}
function initTheory() {
  initHierarchy();
  // explorador de potències
  const PX = { b: 3, e: 4 };
  const drawPX = () => {
    $('#px-b').textContent = PX.b; $('#px-e').textContent = PX.e;
    const lhs = `${PX.b}^{${PX.e}} = `;
    let h;
    if (PX.e === 0) h = M(lhs + '1') + ' <span class="note">(qualsevol nombre diferent de 0 elevat a 0 dona 1)</span>';
    else if (PX.e === 1) h = M(lhs + PX.b) + ' <span class="note">(un sol factor)</span>';
    else h = M(`${lhs}${Array(PX.e).fill(PX.b).join(' \\cdot ')} = \\mathbf{${fmt(PX.b ** PX.e)}}`);
    $('#px-out').innerHTML = h;
  };
  $$('[data-px]').forEach(b => b.addEventListener('click', () => {
    const [k, d] = [b.dataset.px[0], b.dataset.px.slice(1)];
    const lim = k === 'b' ? [1, 12] : [0, 8];
    PX[k] = Math.min(lim[1], Math.max(lim[0], PX[k] + parseInt(d, 10)));
    drawPX();
  }));
  drawPX();

  // quadrats perfectes
  $('#squares').innerHTML = range(1, 14).map(n =>
    `<div class="sqcard">${M(`${n}^2 = ${n * n}`)}<span class="sqarrow" aria-hidden="true">↓</span>${M(`\\sqrt{${n * n}} = ${n}`)}</div>`).join('');

  // exemples pas a pas
  const EX = [
    { name: 'Exemple 1', src: '2^2·5-14:7·3^2' },
    { name: 'Exemple 2', src: '2·(3+2^3)-√81' },
    { name: 'Exemple 3', src: '5^2-√25·2-(7-3·2)' },
    { name: 'Exemple 4', src: '[20-(3+1)^2]·√9+12:2^2' },
    { name: '🎲 Aleatori · nivell 1', lvl: 1 },
    { name: '🎲 Aleatori · nivell 2', lvl: 2 },
    { name: '🎲 Aleatori · nivell 3', lvl: 3 },
  ];
  const ST = { sol: null, total: 0, shown: 0 };
  const drawST = () => {
    const done = ST.shown >= ST.total;
    $('#stepper-out').innerHTML = phasedHTML(ST.sol, ST.shown) +
      (done ? `<p class="result-line">Resultat: ${fmt(ST.sol.value)}</p>` : '');
    $('#st-next').disabled = done;
    $('#st-all').disabled = done;
  };
  const load = (i) => {
    const e = EX[i];
    const tree = e.lvl ? genCombined(e.lvl) : parseExpr(e.src);
    ST.sol = solvePhased(tree); ST.total = phasedCount(ST.sol); ST.shown = 0;
    $$('#ex-chips button').forEach((b, j) => b.setAttribute('aria-pressed', String(j === i)));
    drawST();
  };
  $('#ex-chips').innerHTML = EX.map((e, i) => `<button data-i="${i}" aria-pressed="false">${e.name}</button>`).join('');
  $('#ex-chips').addEventListener('click', ev => { const b = ev.target.closest('button'); if (b) load(+b.dataset.i); });
  $('#st-next').addEventListener('click', () => { ST.shown++; drawST(); });
  $('#st-all').addEventListener('click', () => { ST.shown = ST.total; drawST(); });
  $('#st-reset').addEventListener('click', () => { ST.shown = 0; drawST(); });
  load(0);

  // resol la teva operació
  // Si MathLive carrega, l'alumne escriu en un editor visual (2², √81, parèntesis...);
  // si no, es fa servir la casella de text de sempre.
  const inp = $('#try-in'), mf = $('#try-mf');
  let visual = false;
  const enableVisual = () => {
    if (visual || !window.MathfieldElement) return;
    visual = true;
    try { MathfieldElement.soundsDirectory = null; MathfieldElement.keypressSound = null; MathfieldElement.plonkSound = null; } catch (e) { /* opcional */ }
    $('#try-mf-wrap').hidden = false;
    inp.hidden = true;
    mf.smartFence = true;
    setupKeyboard();
    // com a la llibreta: * o x -> punt de multiplicar (·) i / -> dos punts (:)
    const SUBST = { '*': '\\cdot', 'x': '\\cdot', 'X': '\\cdot', '×': '\\cdot', '/': ':', '÷': ':' };
    mf.addEventListener('beforeinput', e => {
      if (e.inputType === 'insertText' && SUBST[e.data]) {
        e.preventDefault();
        mf.executeCommand(['insert', SUBST[e.data]]);
      }
    });
    mf.addEventListener('keydown', e => { if (e.key === 'Enter') { e.preventDefault(); go(); } });
  };
  if (window.customElements) customElements.whenDefined('math-field').then(enableVisual);
  $('#try-keys').addEventListener('click', ev => {
    const b = ev.target.closest('button'); if (!b) return;
    if (visual) {
      if (b.dataset.cmd === 'back') mf.executeCommand('deleteBackward');
      else if (b.dataset.cmd === 'clear') mf.value = '';
      else mf.executeCommand(['insert', b.dataset.ins, { focus: true, selectionMode: 'placeholder' }]);
      mf.focus();
      return;
    }
    if (b.dataset.cmd === 'back') { inp.value = inp.value.slice(0, -1); inp.focus(); return; }
    if (b.dataset.cmd === 'clear') { inp.value = ''; inp.focus(); return; }
    const k = b.dataset.k, a = inp.selectionStart ?? inp.value.length, z = inp.selectionEnd ?? a;
    inp.value = inp.value.slice(0, a) + k + inp.value.slice(z);
    inp.focus(); inp.setSelectionRange(a + k.length, a + k.length);
  });
  const go = () => {
    const out = $('#try-out');
    let tree;
    const src = visual ? latexToPlain(mf.value) : inp.value;
    try { tree = parseExpr(src); }
    catch (e) {
      const open = (src.match(/[([]/g) || []).length, close = (src.match(/[)\]]/g) || []).length;
      const why = open > close ? 'Falta <b>tancar un parèntesi</b>: escriu <b>)</b> on s\'acaba.'
        : open < close ? 'Hi ha un parèntesi tancat que <b>no s\'ha obert</b>.'
        : /\d\s*[([√]|[)\]]\s*[\d([√]/.test(src) ? 'Falta un <b>signe d\'operació</b>: escriu 2·(3+1), no 2(3+1).'
        : 'Revisa els símbols: hi ha alguna operació que no està completa.';
      out.innerHTML = `<p class="err-msg">No entenc l'operació. ${why}</p>`;
      return;
    }
    const sol = solvePhased(tree);
    let h = `<div class="notebook phased" style="margin-top:12px">${phasedHTML(sol)}</div>`;
    if (sol.error) h += `<p class="err-msg">Aquí ens aturem: ${sol.error} Amb nombres naturals no es pot continuar.</p>`;
    else h += `<p class="result-line">Resultat: ${fmt(sol.value)}</p>`;
    out.innerHTML = h;
  };
  $('#try-go').addEventListener('click', go);
  inp.addEventListener('keydown', e => { if (e.key === 'Enter') go(); });
}

// Teclat virtual de MathLive simplificat: només el que cal a 1r d'ESO
function setupKeyboard() {
  const kb = window.mathVirtualKeyboard;
  if (!kb) return;
  const op = (latex, label) => ({ latex, label: label || undefined, class: 'kb-op' });
  try {
    kb.layouts = [{
      label: 'Operacions',
      tooltip: 'Operacions combinades',
      rows: [
        ['7', '8', '9', '[separator-5]', op('+'), op('-', '−'), '[separator-5]',
          { label: '<span>x<sup>2</sup></span>', insert: '^{2}', class: 'kb-pow', tooltip: 'Al quadrat' },
          { label: '<span>x<sup>3</sup></span>', insert: '^{3}', class: 'kb-pow', tooltip: 'Al cub' }],
        ['4', '5', '6', '[separator-5]', op('\\cdot', '·'), op(':'), '[separator-5]',
          { label: '<span>x<sup>n</sup></span>', insert: '^{#?}', class: 'kb-pow', tooltip: 'Potència' },
          { latex: '\\sqrt{#0}', insert: '\\sqrt{#?}', class: 'kb-pow', tooltip: 'Arrel quadrada' }],
        ['1', '2', '3', '[separator-5]', op('('), op(')'), '[separator-5]', op('['), op(']')],
        ['[separator-5]', '0', '[separator-5]', '[separator-5]', '[left]', '[right]', '[separator-5]', '[backspace]', '[hide-keyboard]'],
      ],
    }];
    kb.editToolbar = 'none';
  } catch (e) { /* si l'API canvia, queda el teclat per defecte */ }
}

/* ---------------- Pràctica: controls ---------------- */
function setPressed(group, v) { $$(`#${group} button`).forEach(b => b.setAttribute('aria-pressed', String(b.dataset.v === String(v)))); }
function savePref() { store.set('pot-pref', { type: S.type, subComb: S.subComb, subProp: S.subProp, level: S.level, mode: S.mode }); }
function syncControls() {
  setPressed('seg-type', S.type);
  setPressed('seg-sub-comb', S.subComb);
  setPressed('seg-sub-prop', S.subProp);
  setPressed('seg-level', S.level);
  setPressed('seg-mode', S.mode);
  $('#sub-comb').hidden = S.type !== 'comb';
  $('#sub-prop').hidden = S.type !== 'prop';
  const help = S.type === 'mix'
    ? `Operacions combinades: ${LEVEL_HELP.comb[S.level].toLowerCase()} Propietats: ${LEVEL_HELP.prop[S.level].toLowerCase()}`
    : LEVEL_HELP[S.type][S.level];
  $('#level-help').textContent = help;
  const SUBHELP = {
    all: 'Surten exercicis de tots els tipus barrejats: de producte, de quocient, de potència d\'una potència i de propietats combinades.',
    mul: 'Només multiplicacions de potències de la mateixa base: se sumen els exponents.',
    div: 'Només divisions de potències de la mateixa base: es resten els exponents.',
    pp: 'Només potències d\'una potència: es multipliquen els exponents.',
    comb: 'En cada exercici has d\'aplicar dues o més propietats diferents, com a l\'apartat e) de l\'examen.',
  };
  $('#sub-prop-help').textContent = SUBHELP[S.subProp] || '';
  $('#mode-help').textContent = S.mode === 'guiat'
    ? 'Tries les operacions i l\'app et corregeix cada línia.'
    : 'Ho fas a la llibreta i només escrius el resultat final.';
  // els exemples de la dreta només canvien si canvia el tipus, la variant o el nivell
  const pkey = `${S.type}|${S.subComb}|${S.subProp}|${S.level}`;
  if (pkey !== S.previewKey) { S.previewKey = pkey; drawPreview(); }
}
// Panell d'exemples: mostra exercicis reals (generats a l'atzar) del tipus i nivell triats
function drawPreview() {
  const box = $('#preview');
  if (!box) return;
  const sample = t => t === 'comb'
    ? exprHTML(genCombined(S.level, S.type === 'mix' ? 'all' : S.subComb), {})
    : M(genProp(S.level, S.type === 'mix' ? 'all' : S.subProp).q);
  const list = S.type === 'mix' ? ['comb', 'prop'] : [S.type, S.type];
  let h = `<div class="pv-h">Exemples · ${'🏀'.repeat(S.level)} ${LEVEL_NAMES[S.level]}</div>`;
  list.forEach(t => {
    h += `<div class="pv-ex">${S.type === 'mix' ? `<span class="pv-t">${TYPE_NAMES[t]}</span>` : ''}<span class="expr">${sample(t)}</span></div>`;
  });
  h += '<button class="btn sm ghost pv-more" type="button">🎲 Altres exemples</button>';
  box.innerHTML = h;
}
// Resum de l'entrenament (barra de dalt mentre es practica)
function drawSummary() {
  const SUBN = { comb: { all: '', nopar: 'Sense parèntesis', par: 'Amb parèntesis' },
                 prop: { all: '', mul: 'Producte', div: 'Quocient', pp: 'Potència d\'una potència', comb: 'Propietats combinades' } };
  const typeName = S.type === 'mix' ? '🎲 Barreja' : TYPE_NAMES[S.type];
  const sub = S.type === 'comb' ? SUBN.comb[S.subComb] : S.type === 'prop' ? SUBN.prop[S.subProp] : '';
  const chips = [typeName, sub, `${'🏀'.repeat(S.level)} ${LEVEL_NAMES[S.level]}`, S.mode === 'guiat' ? '👣 Pas a pas' : '🎯 Només el resultat'].filter(Boolean);
  $('#summary').innerHTML = chips.map((c, i) => `<span class="chip${i ? '' : ' main'}">${c}</span>`).join('');
}
function startTraining() {
  $('#setup').hidden = true;
  $('#training').hidden = false;
  drawSummary();
  newExercise();
  window.scrollTo({ top: 0 });
}
function initPractice() {
  const bindSeg = (id, fn) => $(`#${id}`).addEventListener('click', e => {
    const b = e.target.closest('button'); if (!b) return;
    fn(b.dataset.v); savePref(); syncControls();
  });
  $('#btn-start').addEventListener('click', startTraining);
  $('#preview').addEventListener('click', e => { if (e.target.closest('.pv-more')) drawPreview(); });
  $('#btn-change').addEventListener('click', () => {
    $('#training').hidden = true;
    $('#setup').hidden = false;
    window.scrollTo({ top: 0 });
  });
  bindSeg('seg-type', v => { S.type = v; });
  bindSeg('seg-sub-comb', v => { S.subComb = v; });
  bindSeg('seg-sub-prop', v => { S.subProp = v; });
  bindSeg('seg-level', v => { S.level = +v; });
  bindSeg('seg-mode', v => { S.mode = v; });
  syncControls();
  drawScore();
  $('#sc-reset').addEventListener('click', () => { S.stats.ok = 0; S.stats.total = 0; S.stats.streak = 0; drawScore(); });

  const ex = $('#exercise');
  ex.addEventListener('click', e => {
    const op = e.target.closest('[data-id]');
    if (op && S.ex) { clickOp(+op.dataset.id); return; }
    const b = e.target.closest('[data-act]');
    if (b) ACT[b.dataset.act]();
  });
  ex.addEventListener('keydown', e => {
    if (e.key !== 'Enter' && e.key !== ' ') return;
    const op = e.target.closest('[data-id]');
    if (op && S.ex) { e.preventDefault(); clickOp(+op.dataset.id); return; }
    if (e.key === 'Enter' && e.target.matches('input.ans')) {
      e.preventDefault();
      // amb diverses caselles, Enter passa a la següent buida; a l'última, comprova
      const all = $$('#exercise input[data-for]');
      const next = all.slice(all.indexOf(e.target) + 1).find(i => !i.value);
      if (e.target.dataset.for && next) next.focus(); else ACT.check();
    }
  });
}
function clickOp(id) { if (S.ex.type === 'comb') onOpClick(id); else if (S.ex.mode === 'guiat') onPropClick(id); }
function drawScore(bump) {
  const s = S.stats;
  $('#sc-ok').textContent = s.ok; $('#sc-tot').textContent = s.total;
  $('#sc-streak').textContent = s.streak; $('#sc-best').textContent = s.best;
  const badge = $('#sc-badge');
  const msg = s.streak >= 10 ? 'Ets l\'MVP! 🏆' : s.streak >= 7 ? 'Imparable! 🔥' : s.streak >= 5 ? 'En ratxa! 🔥'
    : s.streak >= 3 ? 'Bona ratxa! 🏀' : s.total === 0 ? 'A escalfar! 🏀' : s.streak === 0 ? 'Torna-hi! 💪' : 'Endavant! 🏀';
  badge.textContent = msg;
  badge.classList.toggle('hot', s.streak >= 5);
  if (bump) {
    const el = bump === 'ok' ? $('#sc-ok').parentElement : $('#sc-streak');
    el.classList.remove('bump'); void el.offsetWidth; el.classList.add('bump');
  }
}
function finish(clean) {
  const E = S.ex;
  if (E.counted) return;
  E.counted = true;
  S.stats.total++;
  if (clean) { S.stats.ok++; S.stats.streak++; if (S.stats.streak > S.stats.best) { S.stats.best = S.stats.streak; store.set('pot-best', S.stats.best); } }
  else S.stats.streak = 0;
  drawScore(clean ? 'ok' : 'streak');
}
const ACT = {
  check() { if (!S.ex) return; S.ex.type === 'comb' ? (S.ex.mode === 'guiat' ? checkGuided() : checkFinal()) : checkProp(); },
  hint() { if (!S.ex) return; S.ex.type === 'comb' ? hintComb() : hintProp(); },
  sol() { if (!S.ex) return; S.ex.type === 'comb' ? solComb() : solProp(); },
  next() { newExercise(); },
};
function newExercise() {
  const type = S.type === 'mix' ? pick(['comb', 'prop']) : S.type;
  if (type === 'comb') startComb(); else startProp();
  const first = $('#exercise input.ans');
  if (first && S.ex.mode !== 'guiat' && window.matchMedia('(pointer: fine)').matches) first.focus({ preventScroll: true });
}
function head(type, instr) {
  // el tipus i el nivell ja surten a la barra resum; només a la barreja cal dir quin tipus ha sortit
  const tag = S.type === 'mix' ? `<div class="ex-head"><span class="tag">${TYPE_NAMES[type]}</span></div>` : '';
  return `${tag}<p class="ex-instr">${instr}</p>`;
}
function fbHTML(fb) { return fb ? `<div class="${fb.k}">${fb.h}</div>` : ''; }
function actionsHTML(done) {
  return `<div class="actions">
    ${done ? '' : '<button class="btn" data-act="hint">Pista</button><button class="btn" data-act="sol">Veure la solució</button>'}
    <button class="btn ${done ? 'primary' : 'ghost'}" data-act="next">${done ? 'Següent exercici ▸' : 'Un altre exercici'}</button>
  </div>`;
}
const PRAISE = ['Cistella! 🏀', 'Triple! 🏀', 'Molt bé!', 'Perfecte!', 'Així es fa!', 'Esmaixada! 🏀'];

/* ---------------- Exercici 1: operacions combinades ---------------- */
/* ============ Mode guiat comú: diverses operacions per línia ============
   L'alumne pot seleccionar totes les operacions que es poden fer alhora
   (p. ex. dues multiplicacions separades per una suma) i escriure'n els
   resultats en una sola línia, com a la llibreta. */
function newGuided(tree) {
  return { cur: tree, lines: [{ tree, created: new Set() }], sels: [], vals: new Map(), marks: new Map(),
           fails: new Map(), hint: null, errors: 0, hints: 0, done: false, showSol: false, fb: null, counted: false };
}
// Adaptadors: com es calcula i s'aplica una operació a cada tipus d'exercici
const ADAPT = {
  comb: {
    find: (t, id) => findNode(t, id),
    order: t => inorder(t),
    allowed: t => analyse(t).allowed,
    answer: n => compute(n).v,
    apply: (t, ids, created) => replaceNodes(t, new Map(ids.map(id => [id, compute(findNode(t, id)).v])), created),
    row: (n, id, val, mark) => `<div class="ask-row"><span class="expr">${exprHTML(n, {})}</span><span class="eq">=</span><input class="ans${mark ? ' ' + mark : ''}" data-for="${id}" value="${val}" inputmode="numeric" autocomplete="off" aria-label="Resultat de l'operació"></div>`,
    hint: n => opHint(n),
    why: n => whyNot(n),
    draw: () => drawComb(),
  },
  prop: {
    find: (t, id) => pFind(t, id),
    order: t => pInorder(t),
    allowed: t => new Set(pInorder(t).filter(id => pReady(pFind(t, id)))),
    answer: n => pCompute(n).e,
    apply: (t, ids, created) => pReplace(t, new Map(ids.map(id => [id, true])), created),
    row: (n, id, val, mark) => `<div class="ask-row"><span class="ask-eq"><span class="expr">${M(pTex(n) + ' = ')}</span><span class="powin"><span class="expr">${M(String(pBase(n)))}</span><input class="ans xs exp${mark ? ' ' + mark : ''}" data-for="${id}" value="${val}" inputmode="numeric" autocomplete="off" aria-label="Nou exponent"></span></span></div>`,
    hint: n => propRuleHint(n),
    why: n => whyNotProp(n),
    draw: () => drawPropGuided(),
  },
};
function saveVals() {
  const E = S.ex;
  if (!E || !E.vals) return;
  $$('#exercise input[data-for]').forEach(i => E.vals.set(+i.dataset.for, i.value));
}
function askHTML(E, A) {
  if (!E.sels.length || E.done) return '';
  let h = '<div class="ask multi"><div class="ask-title">' + (E.sels.length > 1
    ? `Has triat <b>${E.sels.length} operacions</b> per fer en aquesta línia:`
    : 'Quant fa? <span class="ask-tip">(Si hi ha altres operacions que es poden fer alhora, també les pots seleccionar.)</span>') + '</div>';
  h += '<div class="ask-grid">';
  for (const id of E.sels) h += A.row(A.find(E.cur, id), id, E.vals.get(id) || '', E.marks.get(id));
  return h + `</div><div class="row"><button class="btn primary" data-act="check">${E.sels.length > 1 ? 'Comprova la línia' : 'Comprova'}</button></div></div>`;
}
function guidedClick(type, id) {
  const E = S.ex, A = ADAPT[type];
  if (!E || E.done) return;
  const node = A.find(E.cur, id);
  if (!node) return;
  saveVals();
  E.hint = null;
  if (A.allowed(E.cur).has(id)) {
    if (E.sels.includes(id)) { E.sels = E.sels.filter(x => x !== id); E.vals.delete(id); E.marks.delete(id); E.fb = null; }
    else {
      E.sels.push(id);
      const ord = A.order(E.cur);
      E.sels.sort((a, b) => ord.indexOf(a) - ord.indexOf(b));
      E.fb = null; E.focus = id;
    }
  } else { E.errors++; E.fb = { k: 'bad', h: A.why(node) }; }
  A.draw();
}
// Comprova totes les caselles de la línia. Retorna true si s'ha aplicat la línia.
function guidedCheck(type) {
  const E = S.ex, A = ADAPT[type];
  if (!E.sels.length) return false;
  saveVals();
  let wrong = [], auto = [], empty = false;
  for (const id of E.sels) {
    const n = A.find(E.cur, id), r = A.answer(n), v = parseNat(E.vals.get(id));
    if (v === null) { empty = true; continue; }
    if (v === r) { E.marks.set(id, 'ok'); continue; }
    const f = (E.fails.get(id) || 0) + 1;
    E.fails.set(id, f); E.errors++;
    if (f >= 3) { E.vals.set(id, String(r)); E.marks.set(id, 'ok'); auto.push(n); }
    else { E.marks.set(id, 'bad'); wrong.push({ n, f }); }
  }
  if (empty) { E.fb = { k: 'warn', h: E.sels.length > 1 ? 'Omple totes les caselles de la línia.' : 'Escriu un nombre natural.' }; A.draw(); return false; }
  if (wrong.length) {
    const w = wrong[0];
    E.fb = { k: 'bad', h: (wrong.length > 1 ? `Hi ha ${wrong.length} resultats que no són correctes (en vermell). ` : 'El resultat en vermell no és correcte. ')
      + (w.f >= 2 ? A.hint(w.n) : 'Torna-ho a provar.') };
    A.draw(); return false;
  }
  const n = E.sels.length;
  const rules = E.sels.map(id => type === 'prop' ? pCompute(A.find(E.cur, id)).rule : null);
  const created = new Set();
  E.cur = A.apply(E.cur, E.sels, created);
  E.lines.push({ tree: E.cur, created });
  E.sels = []; E.vals = new Map(); E.marks = new Map(); E.fails = new Map();
  E.lastLine = { n, rules, auto: auto.length };
  return true;
}
function lineMsg(E) {
  const L = E.lastLine;
  if (L.auto) return `Alguns resultats els he posat jo. Continua amb la línia següent.`;
  return `${pick(PRAISE)} ${L.n > 1 ? `Has fet ${L.n} operacions en una sola línia.` : ''}`;
}
function focusGuided() {
  const E = S.ex;
  const inp = (E.focus && $(`#exercise input[data-for="${E.focus}"]`)) || $$('#exercise input.ans').find(i => !i.value);
  E.focus = null;
  if (inp && E.lines.length + E.sels.length > 1) inp.focus({ preventScroll: true });
}

/* ---------------- Exercici 1: operacions combinades ---------------- */
function startComb() {
  let tree, k = 0;
  do { tree = genCombined(S.level, S.type === 'mix' ? 'all' : S.subComb); } while (toText(tree) === S.lastKey && k++ < 5);
  S.lastKey = toText(tree);
  const sol = solveSteps(tree);
  const t0 = sol.steps[0].tree;
  S.ex = Object.assign(newGuided(t0), { type: 'comb', mode: S.mode, orig: t0, sol, shown: 0 });
  drawComb();
}
function drawComb() {
  const E = S.ex;
  const guided = E.mode === 'guiat';
  let h = head('comb', guided
    ? 'Fes clic a l\'operació que toca fer i escriu-ne el resultat. Si n\'hi ha <b>diverses que es poden fer alhora</b> (per exemple, dues multiplicacions separades per una suma), selecciona-les totes i fes-les en la mateixa línia.'
    : 'Calcula el resultat. Escriu tots els passos a la llibreta i després posa aquí el resultat final.');
  if (guided) {
    const sel = new Set(E.sels);
    h += '<div class="notebook">';
    E.lines.forEach((ln, i) => {
      const last = i === E.lines.length - 1;
      const live = last && !E.done;
      h += `<div class="line${last ? '' : ' past'}"><span class="eq">${i ? '=' : ''}</span><span class="expr${live ? ' clickable' : ''}">${exprHTML(ln.tree, { clickable: live, created: ln.created, sel: live ? sel : null, hint: live ? E.hint : null })}</span></div>`;
    });
    h += '</div>';
    h += askHTML(E, ADAPT.comb);
  } else {
    h += `<div class="notebook"><div class="line"><span class="expr">${exprHTML(E.orig, {})}</span><span class="eq">=</span>${E.done
      ? `<span class="final-v">${fmt(E.sol.value)}</span>`
      : '<input id="ans" class="ans" inputmode="numeric" autocomplete="off" aria-label="Resultat final"><button class="btn primary" data-act="check">Comprova</button>'}</div></div>`;
    if (E.shown > 0) h += `<div class="solbox"><h4>${E.shown >= E.sol.steps.length - 1 ? 'Solució' : 'Pistes: primers passos'}</h4>${stepsHTML(E.sol.steps, E.shown, false)}</div>`;
  }
  if (guided && E.showSol) h += `<div class="solbox"><h4>Solució completa</h4>${stepsHTML(E.sol.steps, 99, true)}</div>`;
  h += `<div class="fb">${fbHTML(E.fb)}</div>`;
  h += actionsHTML(E.done);
  $('#exercise').innerHTML = h;
  decorate($('#exercise'));
  if (guided) focusGuided();
  else { const a = $('#ans'); if (a && window.matchMedia('(pointer: fine)').matches) a.focus({ preventScroll: true }); }
}
function whyNot(n) {
  if (ready(n)) return 'Encara no! En aquesta part queden <b>potències, arrels, multiplicacions o divisions</b>. Les sumes i les restes es fan al final.';
  if (n.t === 'sqrt') return 'Primer has de calcular el que hi ha <b>dins de l\'arrel</b>.';
  for (const k of kids(n)) {
    if (k.t === 'par') return 'Primer has de resoldre el que hi ha <b>dins del parèntesi</b>.';
    if (k.t === 'pow') return 'Abans cal calcular la <b>potència</b>.';
    if (k.t === 'sqrt') return 'Abans cal calcular l\'<b>arrel</b>.';
  }
  for (const k of kids(n)) {
    if (k.t === 'bin') return prio(k) > prio(n)
      ? 'Abans cal fer la <b>multiplicació o divisió</b>.'
      : 'Les operacions del mateix nivell es fan <b>d\'esquerra a dreta</b>.';
  }
  return 'Aquesta operació encara no es pot fer.';
}
function opHint(n) {
  if (n.t === 'pow') return M(`${n.b.v}^{${n.e}} = ${Array(n.e).fill(n.b.v).join(' \\cdot ')}`);
  if (n.t === 'sqrt') return `Quin nombre multiplicat per ell mateix dona ${fmt(n.a.v)}?`;
  const a = n.l.v, b = n.r.v;
  if (n.op === ':') return `Pensa: quin nombre multiplicat per ${b} dona ${fmt(a)}?`;
  if (n.op === '·' && b > 10 && a < 10) return `Fes-ho per parts: ${a} · ${b} = ${a} · ${b - (b % 10)} + ${a} · ${b % 10}`;
  if (n.op === '·' && a > 10 && b < 10) return `Fes-ho per parts: ${a} · ${b} = ${a - (a % 10)} · ${b} + ${a % 10} · ${b}`;
  return 'Fes-ho amb calma (pots fer servir la llibreta).';
}
function onOpClick(id) { if (S.ex.mode === 'guiat') guidedClick('comb', id); }
function checkGuided() {
  const E = S.ex;
  if (!guidedCheck('comb')) return;
  if (E.cur.t === 'num') {
    E.done = true;
    const clean = E.errors === 0 && E.hints === 0 && !E.showSol;
    finish(clean);
    E.fb = { k: 'ok', h: `<b>${pick(PRAISE)}</b> El resultat és <b>${fmt(E.cur.v)}</b>.` + (clean ? '' : ` Has acabat amb ${E.errors} ${E.errors === 1 ? 'errada' : 'errades'}${E.hints ? ' i alguna pista' : ''}; el proper el faràs sense!`) };
  } else E.fb = { k: E.lastLine.auto ? 'warn' : 'ok', h: lineMsg(E) + ' Tria les operacions de la línia següent.' };
  drawComb();
}
function checkFinal() {
  const E = S.ex;
  const v = parseNat($('#ans').value);
  if (v === null) { E.fb = { k: 'warn', h: 'Escriu el resultat amb un nombre natural.' }; drawComb(); return; }
  if (v === E.sol.value) {
    E.done = true;
    const clean = E.errors === 0 && E.hints === 0;
    finish(clean);
    E.shown = E.sol.steps.length - 1;
    E.fb = { k: 'ok', h: `<b>${pick(PRAISE)}</b> El resultat és <b>${fmt(v)}</b>. Compara els teus passos amb la solució.` + (clean ? '' : ' (Aquest no suma a la ratxa perquè has necessitat més d\'un intent o alguna pista.)') };
  } else {
    E.errors++;
    E.fb = { k: 'bad', h: 'No és correcte. Revisa l\'<b>ordre de les operacions</b> i els càlculs. Pots demanar una pista: et mostraré el primer pas.' };
  }
  drawComb();
  const a = $('#ans'); if (a && !E.done) { a.value = String(v); a.select(); }
}
function hintComb() {
  const E = S.ex;
  if (E.done) return;
  E.hints++;
  if (E.mode === 'guiat') {
    saveVals();
    const { allowed, ctxOf } = analyse(E.cur);
    const ids = inorder(E.cur).filter(x => allowed.has(x));
    const id = ids.find(x => !E.sels.includes(x)) || ids[0];
    const n = findNode(E.cur, id);
    const owner = ctxOf.get(id).owner;
    E.hint = id;
    const also = ids.length > 1 ? ` En aquesta línia es poden fer <b>${ids.length} operacions</b> alhora.` : '';
    E.fb = { k: 'info', h: `Pista: ${owner === 'par' ? 'dins del parèntesi, ' : owner === 'sqrt' ? 'dins de l\'arrel, ' : ''}ara pots fer <b>${KIND[kindKey(n)][2]}</b>. L'he marcada en blau: fes-hi clic.${also}` };
  } else {
    E.shown = Math.min(E.shown + 1, E.sol.steps.length - 2);
    if (E.shown < 1) E.shown = 1;
    E.fb = { k: 'info', h: 'Pista: mira el pas següent i continua tu.' };
  }
  drawComb();
}
function solComb() {
  const E = S.ex;
  saveVals();
  if (E.mode === 'guiat') { E.showSol = true; }
  else { E.shown = E.sol.steps.length - 1; E.done = true; }
  finish(false);
  E.fb = { k: 'info', h: `La solució és <b>${fmt(E.sol.value)}</b>. Mira bé l'ordre dels passos i prova'n un altre.` };
  if (E.mode === 'guiat') E.fb.h += ' També pots acabar-lo tu fent clic a les operacions.';
  drawComb();
}

/* ---------------- Exercici 2: propietats de les potències ---------------- */
function startProp() {
  const sub = S.type === 'mix' ? 'all' : S.subProp;
  let p, k = 0;
  do { p = genProp(S.level, sub); } while (p.key === S.lastKey && k++ < 5);
  S.lastKey = p.key;
  const guided = S.mode === 'guiat' && KX();
  S.ex = Object.assign(newGuided(p.tree), { type: 'prop', mode: guided ? 'guiat' : 'final', p });
  if (guided) { drawPropGuided(); return; }
  const h = head('prop', 'Expressa-ho com <b>una sola potència</b> de la mateixa base aplicant les propietats i, després, <b>calcula</b> el resultat.') +
    `<div class="notebook"><div class="line" style="flex-wrap:wrap">
      <span class="expr">${M(p.q)}</span><span class="eq">=</span>
      <span class="powin"><input id="pb" class="ans sm" inputmode="numeric" autocomplete="off" aria-label="Base"><input id="pe" class="ans xs" inputmode="numeric" autocomplete="off" aria-label="Exponent"></span>
      <span class="eq">=</span>
      <input id="pv" class="ans" inputmode="numeric" autocomplete="off" aria-label="Valor de la potència">
    </div></div>
    <p class="ctrl-help">Escriu la base a la casella gran, l'exponent a la petita (a dalt) i el valor al final. Pots escriure 1024 o 1.024.</p>
    <div class="row"><button class="btn primary" data-act="check">Comprova</button></div>
    <div id="prop-extra"></div>
    <div class="fb" id="fb"></div>
    <div id="acts">${actionsHTML(false)}</div>`;
  $('#exercise').innerHTML = h;
}

/* --- Mode guiat: l'alumne tria les propietats que aplica i escriu els nous exponents --- */
const PROP_DONE = {
  mul: 'has <b>sumat</b> els exponents',
  div: 'has <b>restat</b> els exponents',
  pp: 'has <b>multiplicat</b> els exponents',
};
function drawPropGuided() {
  const E = S.ex, p = E.p;
  let h = head('prop', 'Fes clic a l\'operació que vols fer (<b>·</b>, <b>:</b> o l\'exponent d\'un parèntesi) i escriu el <b>nou exponent</b>. Si n\'hi ha diverses que es poden fer alhora, selecciona-les totes. Quan quedi una sola potència, calcula\'n el valor.');
  const sel = new Set(E.sels);
  h += '<div class="notebook">';
  E.lines.forEach((ln, i) => {
    const last = i === E.lines.length - 1, live = last && !E.done && E.cur.t !== 'p';
    h += `<div class="line${last ? '' : ' past'}"><span class="eq">${i ? '=' : ''}</span><span class="expr${live ? ' clickable' : ''}">${M(pTex(ln.tree, { clickable: live, created: ln.created, sel: live ? sel : null, hint: live ? E.hint : null }))}</span></div>`;
  });
  if (E.done) h += `<div class="line"><span class="eq">=</span><span class="final-v">${fmt(p.v)}</span></div>`;
  h += '</div>';
  if (!E.done) {
    if (E.cur.t === 'p') {
      h += `<div class="ask"><label for="ans">Ara calcula el valor:</label><span class="expr">${M(pTex(E.cur))}</span><span class="eq">=</span><input id="ans" class="ans" inputmode="numeric" autocomplete="off" aria-label="Valor de la potència"><button class="btn primary" data-act="check">Comprova</button></div>`;
    } else h += askHTML(E, ADAPT.prop);
  }
  if (E.showSol) h += `<div class="solbox"><h4>Solució completa</h4><div class="chain">${solChainProp(p)}</div></div>`;
  h += `<div class="fb">${fbHTML(E.fb)}</div>`;
  h += actionsHTML(E.done);
  $('#exercise').innerHTML = h;
  decorate($('#exercise'));
  if (E.cur.t === 'p' && !E.done && E.lines.length > 1) { const a = $('#ans'); if (a) a.focus({ preventScroll: true }); }
  else focusGuided();
}
function whyNotProp(n) {
  if (n.t === 'g') return 'Primer has de resoldre el que hi ha <b>dins del parèntesi</b>. Després podràs aplicar la potència d\'una potència.';
  for (const k of pkids(n)) if (k.t === 'g') return 'Abans has de treure el <b>parèntesi</b>: fes la potència d\'una potència (o el que hi ha a dins).';
  return 'Les multiplicacions i divisions es fan <b>d\'esquerra a dreta</b>.';
}
function onPropClick(id) { if (S.ex.cur.t !== 'p') guidedClick('prop', id); }
function propRuleHint(node) {
  const c = pCompute(node);
  if (c.rule === 'mul') return `Producte de la mateixa base: se <b>sumen</b> els exponents. ${M(c.expr.replace('+', ' + ') + ' = \\ ?')}`;
  if (c.rule === 'div') return `Quocient de la mateixa base: es <b>resten</b> els exponents. ${M(c.expr.replace('-', ' - ') + ' = \\ ?')}`;
  return `Potència d'una potència: es <b>multipliquen</b> els exponents. ${M(c.expr + ' = \\ ?')}`;
}
function checkPropGuided() {
  const E = S.ex, p = E.p;
  if (E.done) return;
  if (E.cur.t === 'p') {                     // últim pas: el valor
    const v = parseNat($('#ans') && $('#ans').value);
    if (v === null) { E.fb = { k: 'warn', h: 'Escriu un nombre natural.' }; drawPropGuided(); return; }
    if (v === p.v) {
      E.done = true;
      const clean = E.errors === 0 && E.hints === 0 && !E.showSol;
      finish(clean);
      E.fb = { k: 'ok', h: `<b>${pick(PRAISE)}</b> ${solChainProp(p)}` + (clean ? '' : `<br>Has acabat amb ${E.errors} ${E.errors === 1 ? 'errada' : 'errades'}${E.hints ? ' i alguna pista' : ''}; el proper el faràs sense!`) };
    } else {
      E.errors++;
      E.fb = { k: 'bad', h: 'El valor no és correcte. ' + (p.s <= 10 ? M(`${p.a}^{${p.s}} = ${Array(p.s).fill(p.a).join(' \\cdot ')}`) : 'Calcula-ho amb calma.') };
    }
    drawPropGuided(); return;
  }
  if (!guidedCheck('prop')) return;
  const L = E.lastLine;
  const done = [...new Set(L.rules)].map(r => PROP_DONE[r]);
  E.fb = { k: L.auto ? 'warn' : 'ok', h: L.auto ? lineMsg(E)
    : `${pick(PRAISE)} ${done.length ? 'En aquesta línia ' + joinCat(done) + '.' : ''}` + (E.cur.t === 'p' ? ' Ja tens una sola potència: ara calcula\'n el valor.' : ' Tria la següent operació.') };
  drawPropGuided();
}

function setFb(k, html) { $('#fb').innerHTML = fbHTML({ k, h: html }); }
function solChainProp(p) { return M(`${p.q} = ${p.steps.join(' = ')} = ${fmt(p.v)}`); }
function checkProp() {
  const E = S.ex, p = E.p;
  if (E.mode === 'guiat') { checkPropGuided(); return; }
  if (E.done) return;
  const ib = $('#pb'), ie = $('#pe'), iv = $('#pv');
  const b = parseNat(ib.value), e = parseNat(ie.value), v = parseNat(iv.value);
  if (b === null || e === null || v === null) { setFb('warn', 'Omple les tres caselles: base, exponent i valor.'); return; }
  const okB = b === p.a, okE = okB && e === p.s, okV = v === p.v;
  ib.classList.toggle('ok', okB); ib.classList.toggle('bad', !okB);
  ie.classList.toggle('ok', okE); ie.classList.toggle('bad', !okE);
  iv.classList.toggle('ok', okV); iv.classList.toggle('bad', !okV);
  if (okB && okE && okV) {
    E.done = true;
    const clean = E.errors === 0 && E.hints === 0;
    finish(clean);
    setFb('ok', `<b>${pick(PRAISE)}</b> ${solChainProp(p)}` + (clean ? '' : '<br>(Aquest no suma a la ratxa perquè has necessitat més d\'un intent o alguna pista.)'));
    $('#acts').innerHTML = actionsHTML(true);
    $$('#exercise input').forEach(i => { i.readOnly = true; });
    return;
  }
  E.errors++;
  let msg;
  if (!okB) msg = `La <b>base no canvia</b>: totes les potències tenen base ${p.a}, i el resultat també.`;
  else if (!okE) msg = 'L\'<b>exponent</b> no és correcte. Revisa quina propietat has d\'aplicar a cada operació (pots demanar una pista o fer-lo <b>pas a pas</b>).';
  else msg = `La forma de potència és correcta! Però el valor no: calcula ${M(`${p.a}^{${p.s}}`)} amb calma.`;
  if (okB && okE && !okV && p.s <= 10) msg += ` ${M(`${p.a}^{${p.s}} = ${Array(p.s).fill(p.a).join(' \\cdot ')}`)}`;
  setFb('bad', msg);
}
function hintProp() {
  const E = S.ex; if (E.done) return;
  E.hints++;
  const p = E.p;
  if (E.mode === 'guiat') {
    if (E.cur.t === 'p') {
      E.fb = { k: 'info', h: `Pista: ${p.s <= 10 ? M(`${p.a}^{${p.s}} = ${Array(p.s).fill(p.a).join(' \\cdot ')}`) : 'multiplica la base per ella mateixa tantes vegades com diu l\'exponent.'}` };
    } else {
      const id = pInorder(E.cur).find(x => pReady(pFind(E.cur, x)));
      const n = pFind(E.cur, id);
      saveVals(); E.hint = id;
      E.fb = { k: 'info', h: `Pista: ara pots fer l'operació marcada en blau. ${propRuleHint(n)}` };
    }
    drawPropGuided(); return;
  }
  const lines = p.rules.map(r => `<li>${RULES[r]}</li>`).join('');
  const first = p.steps.length > 1 ? `<p>Primer pas: ${M(`${p.q} = ${p.steps[0]} = \\dots`)}</p>` : '';
  $('#prop-extra').innerHTML = `<div class="solbox"><h4>Pista</h4><ul style="margin:4px 0 4px 18px;padding:0">${lines}</ul>${first}</div>`;
}
function solProp() {
  const E = S.ex; if (E.done) return;
  if (E.mode === 'guiat') {
    E.showSol = true; finish(false);
    E.fb = { k: 'info', h: 'Mira la solució. També pots acabar-lo tu fent clic a les operacions.' };
    drawPropGuided(); return;
  }
  E.done = true;
  finish(false);
  $('#prop-extra').innerHTML = `<div class="solbox"><h4>Solució</h4><div class="chain">${solChainProp(E.p)}</div></div>`;
  $('#acts').innerHTML = actionsHTML(true);
  setFb('info', 'Fixa\'t en com es mantenen la base i com canvien els exponents. Prova\'n un altre!');
}

if (typeof module !== 'undefined') module.exports = { genCombined, genProp, solveSteps, parseExpr, val, toText, treeStats, maxNum, COMB };
