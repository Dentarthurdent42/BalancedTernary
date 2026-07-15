// CI check: extract the inline text/babel script from each HTML page, compile
// it with the same Babel the pages load from the CDN, then execute it in a
// sandbox with React/ReactDOM stubbed so the pure arithmetic functions can be
// pulled out and tested directly. This exercises the shipped code, not a copy.
import { readFileSync } from 'node:fs';
import vm from 'node:vm';
import { createRequire } from 'node:module';

const require = createRequire(import.meta.url);
const Babel = require('@babel/standalone');

let failures = 0;
function assert(cond, msg) {
  if (!cond) { failures++; console.error('FAIL:', msg); }
}

function extractBabelScript(file) {
  const html = readFileSync(file, 'utf8');
  const m = html.match(/<script type="text\/babel">([\s\S]*?)<\/script>/);
  if (!m) throw new Error(`${file}: no text/babel script found`);
  return m[1];
}

// Run a page's script with UI machinery stubbed; `capture` names the
// top-level functions to hand back for testing.
function loadPage(file, capture) {
  const src = extractBabelScript(file)
    + `\n;__capture({ ${capture.join(', ')} });`;
  const { code } = Babel.transform(src, { presets: ['react'], filename: file });
  let captured = null;
  const sandbox = {
    __capture: (fns) => { captured = fns; },
    React: {
      useState: (v) => [v, () => {}],
      useEffect: () => {},
      useRef: (v) => ({ current: v }),
      createElement: () => ({}),
    },
    ReactDOM: { createRoot: () => ({ render: () => {} }) },
    document: { getElementById: () => ({}) },
    performance, console,
    requestAnimationFrame: () => 0,
    cancelAnimationFrame: () => {},
    setTimeout, clearTimeout, setInterval, clearInterval,
  };
  vm.runInNewContext(code, sandbox, { filename: file });
  if (!captured) throw new Error(`${file}: capture hook never ran`);
  return captured;
}

// Load the *kinematics* half of a `type="module"` page. Strips the bare ES
// imports and keeps only the code up to the GEOMETRY divider (the Geneva
// transfer functions are pure — Math only — and self-contained), then captures
// the named functions. Exercises the shipped sim code, not a copy.
function loadModuleKinematics(file, capture) {
  const html = readFileSync(file, 'utf8');
  const m = html.match(/<script type="module">([\s\S]*?)<\/script>/);
  if (!m) throw new Error(`${file}: no module script found`);
  let src = m[1].replace(/^\s*import\s.*$/gm, '');     // drop ES imports
  const cut = src.indexOf('//  GEOMETRY');
  if (cut === -1) throw new Error(`${file}: GEOMETRY divider not found`);
  src = src.slice(0, cut) + `\n;__capture({ ${capture.join(', ')} });`;
  let captured = null;
  vm.runInNewContext(src, { __capture: (f) => { captured = f; }, Math, console },
    { filename: file });
  if (!captured) throw new Error(`${file}: capture hook never ran`);
  return captured;
}

// ---------- counter3d.html : the Geneva kinematic chain ----------
{
  const { geneva, rotToTrit, solveWheels } = loadModuleKinematics('counter3d.html',
    ['geneva', 'rotToTrit', 'solveWheels']);

  // single 6-slot Geneva transfer: 60° index per 360° driver, dwell otherwise
  assert(geneva(0) === 0, `geneva(0) = ${geneva(0)}`);
  assert(Math.abs(geneva(360) - 60) < 1e-9, `geneva(360) = ${geneva(360)}`);
  assert(geneva(60) === 0 && geneva(110) === 0, 'geneva dwells before engagement');
  assert(Math.abs(geneva(300) - 60) < 1e-9, 'geneva settled after engagement');

  // THE EMERGENT PROPERTY: cranking T turns must reconstruct the integer T,
  // with carries produced only by the linkage (solveWheels), across full range.
  const N = 7, MAX = (3 ** N - 1) / 2;
  let okAll = true;
  for (let T = -MAX; T <= MAX; T++) {
    const th = solveWheels(360 * T, N);
    let V = 0;
    for (let k = 0; k < N; k++) V += rotToTrit(th[k]) * 3 ** k;
    if (V !== T) { okAll = false; assert(false, `crank ${T} turns → emergent ${V}`); break; }
  }
  assert(okAll, 'emergent count tracks crank turns');

  // higher wheels dwell between carries: W1 holds while W0 has not yet stepped
  const a = solveWheels(360 * 1.0, N)[1], b = solveWheels(360 * 1.2, N)[1];
  assert(Math.abs(a - b) < 1e-9, `W1 should dwell across counts 1.0→1.2 (${a}, ${b})`);

  console.log(`counter3d.html: Geneva chain — emergent count over full ±${MAX} range ok`);
}

// ---------- index.html : the adder ----------
{
  const { addTrits, tritsToDecimal, rotToTrit } = loadPage('index.html',
    ['addTrits', 'tritsToDecimal', 'rotToTrit']);

  // rotToTrit cycle: 0°→0, 60°→+1, 120°→−1, repeating both directions
  const cycle = [[0, 0], [60, 1], [120, -1], [180, 0], [240, 1], [300, -1],
                 [-60, -1], [-120, 1], [-180, 0], [720, 0]];
  for (const [deg, t] of cycle) {
    assert(rotToTrit(deg) === t, `rotToTrit(${deg}) = ${rotToTrit(deg)}, want ${t}`);
  }

  // addTrits: exhaustive over all pairs of 4-trit numbers (81 × 81)
  const n = 4;
  const all = [[]];
  for (let i = 0; i < n; i++) {
    const next = [];
    for (const a of all) for (const d of [-1, 0, 1]) next.push([...a, d]);
    all.length = 0; all.push(...next);
  }
  for (const a of all) for (const b of all) {
    const { result, carry } = addTrits(a, b);
    const lhs = tritsToDecimal(result) + carry * 3 ** n;
    const rhs = tritsToDecimal(a) + tritsToDecimal(b);
    assert(lhs === rhs, `addTrits([${a}],[${b}]) → ${lhs}, want ${rhs}`);
    assert([-1, 0, 1].includes(carry), `carry out of range for [${a}]+[${b}]`);
    assert(result.every(t => [-1, 0, 1].includes(t)), `result trit out of range for [${a}]+[${b}]`);
  }
  console.log(`index.html: rotToTrit + addTrits exhaustive (${all.length}²) ok`);
}

// ---------- counter.html : the Geneva counter ----------
{
  const { decompose, rotToTrit } = loadPage('counter.html', ['decompose', 'rotToTrit']);

  const N = 7, MAX = (3 ** N - 1) / 2; // 1093
  for (let V = -MAX; V <= MAX; V++) {
    const { trits, counts } = decompose(V, N);
    let s = 0;
    for (let k = 0; k < N; k++) s += trits[k] * 3 ** k;
    assert(s === V, `decompose(${V}) reconstructs to ${s}`);
    assert(counts[0] === V, `counts[0] for ${V}`);
    assert(trits.every(t => [-1, 0, 1].includes(t)), `trit out of range for ${V}`);
    assert(counts.every(Number.isInteger), `non-integer index count for ${V}`);
    // wheel angle/trit agreement: the bar must read the digit the math says
    for (let k = 0; k < N; k++) {
      assert(rotToTrit(counts[k] * 60) === trits[k],
        `wheel ${k} at V=${V}: angle says ${rotToTrit(counts[k] * 60)}, trit is ${trits[k]}`);
    }
  }
  // carry cadence: stage k indexes once per 3^k counts → 3 times over 3^(k+1)
  for (let k = 1; k < N; k++) {
    let changes = 0;
    for (let V = 0; V < 3 ** (k + 1); V++) {
      if (decompose(V + 1, N).counts[k] !== decompose(V, N).counts[k]) changes++;
    }
    assert(changes === 3,
      `stage ${k} indexed ${changes}× over ${3 ** (k + 1)} counts, want 3`);
  }
  console.log(`counter.html: decompose full ±${MAX} range + carry cadence ok`);
}

// ---------- imaginary.html : complex-base positional systems ----------
{
  const { gnorm, gmul, gdivExact, gdivmod, isCRS, encode, evalDigits, minimalDepths,
    digitsFromParents } =
    loadPage('imaginary.html', ['gnorm', 'gmul', 'gdivExact', 'gdivmod', 'isCRS',
      'encode', 'evalDigits', 'minimalDepths', 'digitsFromParents']);

  const key = (z) => z[0] + ',' + z[1];
  const eq = (a, b) => a[0] === b[0] && a[1] === b[1];

  // complete-residue-system detection. Note 2i: N(2i) = 4 but rational
  // integers only occupy two residue classes mod 2i (2 ≡ 0), so quater-
  // imaginary's {0,1,2,3} is NOT a CRS — expansions need search, not greedy.
  assert(isCRS([-1, 1], [0, 1]) === true, 'i−1 with {0,1} is a CRS');
  assert(isCRS([0, 2], [0, 1, 2, 3]) === false, '2i with {0,1,2,3}: 2 ≡ 0 mod 2i, not a CRS');
  assert(isCRS([1, 1], [0, 1]) === true, '1+i with {0,1} is a CRS');
  assert(isCRS([-1, 1], [0, 2]) === false, 'i−1 with {0,2}: 2 ≡ 0 mod (i−1), not a CRS');
  assert(isCRS([3, 0], [-1, 0, 1]) === false, 'base 3 with 3 digits: N(3)=9, not a CRS');

  // THE THEOREM, computationally: in base i−1 with digits {0,1} every
  // Gaussian integer in a big box has an expansion, and it reconstructs.
  const B = [-1, 1], D01 = [0, 1], BOX = 40;
  for (let a = -BOX; a <= BOX; a++) {
    for (let b = -BOX; b <= BOX; b++) {
      const enc = encode([a, b], B, D01);
      assert(enc !== null, `no base i−1 expansion for ${a}+${b}i`);
      if (!enc) continue;
      assert(enc.digits.every((d) => d === 0 || d === 1),
        `digit out of {0,1} for ${a}+${b}i`);
      assert(eq(evalDigits(enc.digits, B), [a, b]),
        `base i−1 round-trip failed for ${a}+${b}i`);
    }
  }

  // uniqueness, computationally: distinct digit strings (no leading zero)
  // must evaluate to distinct Gaussian integers — exhaustive to 16 digits.
  {
    const seen = new Map([['0,0', '0']]);
    let strings = [[1]]; // every canonical nonzero string ends (MSD) in 1
    for (let len = 1; len <= 16; len++) {
      for (const ds of strings) {
        const v = key(evalDigits(ds, B));
        assert(!seen.has(v) || seen.get(v) === ds.join(''),
          `two expansions hit ${v}: ${seen.get(v)} and ${ds.join('')}`);
        seen.set(v, ds.join(''));
      }
      strings = strings.flatMap((ds) => [[0, ...ds], [1, ...ds]]);
    }
    console.log(`imaginary.html: base i−1 uniqueness exhaustive to 16 digits (${seen.size} values) ok`);
  }

  // the viz's forward search agrees with the division algorithm: minimal
  // depth = canonical digit count (unique representation ⇒ they coincide)
  {
    const { depth } = minimalDepths(B, D01, 24, 40);
    for (let a = -15; a <= 15; a++) {
      for (let b = -15; b <= 15; b++) {
        const enc = encode([a, b], B, D01);
        assert(depth.get(key([a, b])) === enc.digits.length,
          `depth(${a}+${b}i) = ${depth.get(key([a, b]))} ≠ ${enc.digits.length} digits`);
      }
    }
  }

  // quater-imaginary (Knuth): base 2i, digits {0,1,2,3}. Integer digit
  // strings Σ dₖ(2i)ᵏ always have even imaginary part, so exactly the
  // even-imaginary half of ℤ[i] is representable (i itself needs the
  // radix-point digit of Knuth's full system). Non-CRS ⇒ test via the
  // forward search, the same path the page uses.
  {
    const B2 = [0, 2], D4 = [0, 1, 2, 3];
    const { depth, parent } = minimalDepths(B2, D4, 60, 24);
    for (let a = -BOX; a <= BOX; a++) {
      for (let b = -BOX; b <= BOX; b++) {
        const dep = depth.get(key([a, b]));
        if (b % 2 !== 0) {
          assert(dep === undefined, `quater-imaginary should miss ${a}+${b}i (odd im)`);
          continue;
        }
        assert(dep !== undefined, `quater-imaginary missing ${a}+${b}i`);
        const ds = digitsFromParents(parent, [a, b]);
        assert(ds !== null && ds.length === dep && ds.every((d) => D4.includes(d)),
          `quater-imaginary digits invalid for ${a}+${b}i`);
        assert(eq(evalDigits(ds, B2), [a, b]),
          `quater-imaginary round-trip failed for ${a}+${b}i`);
      }
    }
  }

  // negabinary: base −2 on the real line matches n.toString via known values
  for (let v = -100; v <= 100; v++) {
    const enc = encode([v, 0], [-2, 0], [0, 1]);
    assert(enc !== null && eq(evalDigits(enc.digits, [-2, 0]), [v, 0]),
      `negabinary round-trip failed for ${v}`);
  }

  // negative control: base 1+i with {0,1} is a CRS but does NOT span ℤ[i] —
  // i cycles under the division algorithm and has no finite expansion
  assert(encode([0, 1], [1, 1], [0, 1]) === null, '1+i: i must have no expansion');
  assert(gdivmod([0, 1], [1, 1], [0, 1]).q.join() === '0,1',
    '1+i: (i−1)/(1+i) = i, the fixed point behind the gap');
  {
    const { depth } = minimalDepths([1, 1], [0, 1], 20, 40);
    let gaps = 0, total = 0;
    for (let a = -10; a <= 10; a++) {
      for (let b = -10; b <= 10; b++) {
        total++;
        if (!depth.has(key([a, b]))) gaps++;
      }
    }
    assert(gaps > 0, '1+i with {0,1} should leave gaps');
    assert(gaps < total, '1+i with {0,1} should still reach some values');
  }

  // spot algebra
  assert(gnorm([-1, 1]) === 2 && gnorm([0, 2]) === 4, 'gnorm');
  assert(eq(gmul([-1, 1], [-1, 1]), [0, -2]), '(i−1)² = −2i');
  assert(gdivExact([2, 0], [-1, 1]).join() === '-1,-1', '2/(i−1) = −1−i');
  assert(gdivExact([1, 0], [-1, 1]) === null, '(i−1) ∤ 1');

  console.log(`imaginary.html: base i−1 / 2i / −2 round-trips over ±${BOX} box + 1+i gaps ok`);
}

if (failures) { console.error(`${failures} assertion(s) failed`); process.exit(1); }
console.log('all checks passed');
