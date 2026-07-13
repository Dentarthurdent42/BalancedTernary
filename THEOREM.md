# The Imaginary-Base Theorem

> **Theorem (Khmelnik 1964 · Penney 1965).**
> Every Gaussian integer has exactly one finite representation in base
> `β = i − 1` with digits `{0, 1}`:
> for every `z ∈ ℤ[i]` there is exactly one digit string
> `d_{n−1} … d_1 d_0` with `d_k ∈ {0,1}`, `d_{n−1} = 1` (or the empty string
> for `z = 0`), such that
>
> ```
> z = Σ_{k<n} d_k · (i−1)^k .
> ```

One unsigned bit string per complex integer — no sign, no separate real and
imaginary parts. This file is the paper proof. The same statement is
machine-checked in Lean 4 in [`theorem/`](./theorem/), verified computationally
by [`scripts/ci-check.mjs`](./scripts/ci-check.mjs), and drawn interactively by
[`imaginary.html`](./imaginary.html), where growing the digit budget `n` traces
this proof's descent in reverse until the twindragon fills the plane.

Throughout, `z = a + bi` with `a, b ∈ ℤ`, and `N(z) = a² + b²` is the norm.
`N` is multiplicative, `N(β) = 2`.

---

## 1. The residue step: one digit always fits, and only one

**Lemma 1.** For every `z ∈ ℤ[i]` exactly one of `z`, `z − 1` is divisible by
`β = i − 1`, namely the one matching the parity of `a + b`:
`β | z ⇔ a + b` is even.

*Proof.* Compute the candidate quotient exactly:

```
z / β = z·β̄ / N(β) = (a + bi)(−1 − i) / 2 = ( (b − a) + (−a − b)i ) / 2 .
```

Both `b − a` and `−a − b` are even precisely when `a + b` is even (they differ
from `a + b` by even numbers), so the quotient is a Gaussian integer iff
`a + b` is even. Replacing `z` by `z − 1` flips the parity of `a + b`. ∎

So `ℤ[i]/(β) ≅ ℤ/2ℤ`, the digit set `{0, 1}` is a complete residue system
mod `β`, and the **division algorithm** is deterministic: define

```
d(z) = (a + b) mod 2 ∈ {0, 1},          T(z) = (z − d(z)) / β .
```

Any expansion `z = Σ d_k β^k` must use `d_0 ≡ z (mod β)`, i.e. `d_0 = d(z)`,
and then `d_1 d_2 …` is an expansion of `T(z)`. Both halves of the theorem
now reduce to properties of the single map `T`.

## 2. Uniqueness

**Lemma 2.** If `Σ_{k<n} d_k β^k = Σ_{k<m} e_k β^k` with all digits in
`{0,1}` and no leading zeros (`d_{n−1} = e_{m−1} = 1` when the strings are
nonempty), then `n = m` and `d_k = e_k` for all `k`.

*Proof.* Induction on `n + m`.

*Base.* If both strings are empty there is nothing to prove. If exactly one is
empty, the other evaluates to `0`; take the least `k` with `d_k = 1`, then
`β^k (1 + β·w) = 0` for some `w ∈ ℤ[i]`, so `β | 1`, impossible since
`N(β) = 2 ∤ 1 = N(1)`. (In particular a nonempty leading-`1` string never
represents `0`.)

*Step.* Both nonempty. By Lemma 1 the value's residue determines the last
digit: `d_0 ≡ Σ d_k β^k ≡ Σ e_k β^k ≡ e_0 (mod β)`, and `0 ≢ 1`, so
`d_0 = e_0`. Subtract and cancel one factor of `β` (valid: `ℤ[i]` is an
integral domain and `β ≠ 0`) to get two shorter equal expansions; apply the
induction hypothesis. ∎

## 3. Existence, by descent

Iterating `T` from `z` and collecting digits `d(z), d(T z), d(T² z), …`
produces the expansion — *provided the orbit reaches `0`*. The engine is:

**Lemma 3 (descent).** `2·N(T(z)) = N(z − d(z))`; consequently

- if `d(z) = 0`:  `N(T z) = N(z)/2 < N(z)` for every `z ≠ 0`;
- if `d(z) = 1`:  `2·N(T z) = N(z) − 2a + 1`, so `N(T z) < N(z)` **unless**
  `(a+1)² + b² ≤ 2`.

*Proof.* `N(T z) = N(z − d)/N(β) = N(z − d)/2` by multiplicativity. For
`d = 1`, `N(z − 1) = (a−1)² + b² = N(z) − 2a + 1`, and
`(N(z) − 2a + 1)/2 < N(z) ⇔ 1 − 2a < N(z) ⇔ (a+1)² + b² > 2`. ∎

The integer points with `(a+1)² + b² ≤ 2` **and** `a + b` odd (so that
`d = 1` actually applies) are just five:

```
E = { −1,  i,  −i,  −2+i,  −2−i } .
```

**Lemma 4 (the exceptional orbits).** Each point of `E` reaches `0` under
iteration of `T`. Explicitly:

```
−1  → 1+i → −i → i → 1 → 0        so  −1   = 11101₍β₎
 i  → 1 → 0                        so   i   = 11₍β₎
−i  → i → 1 → 0                    so  −i   = 111₍β₎
−2+i → 2+i → −i → i → 1 → 0        so  −2+i = 11111₍β₎
−2−i → 1+2i → 1−i → −1 → …         so  −2−i = 11101011₍β₎
```

*Proof.* Direct computation (each arrow is one application of `T`; each listed
digit string evaluates back to its point — checked by machine in both
[`theorem/`](./theorem/) and CI). Note the orbits are *not* norm-monotone —
`N(−1) = 1` but `N(T(−1)) = N(1+i) = 2` — which is exactly why these five
points must be handled separately. ∎

**Theorem (existence).** Every `z ∈ ℤ[i]` has a finite expansion.

*Proof.* Strong induction on `N(z)`. If `z = 0`, take the empty string. If
`z ∈ E`, Lemma 4 exhibits an expansion outright. Otherwise Lemma 3 gives
`N(T z) < N(z)`; by the induction hypothesis `T z` has an expansion
`e_{m−1} … e_0`, and `z = β·T(z) + d(z)` makes `e_{m−1} … e_0 d(z)` an
expansion of `z`. ∎

Together with Lemma 2 (after discarding leading zeros) this proves the
theorem. ∎

The descent also bounds the digit count: away from a ball around the origin
each step halves the norm, so `z` needs about `log₂ N(z) = 2·log₂ |z|`
digits — the twindragon in `imaginary.html` gains one "ring" each time the
norm budget doubles.

## 4. Why the base matters: near misses

The proof used three separate properties of `(β, D) = (i−1, {0,1})`, and each
can fail individually — the explorer has a preset for each failure mode.

**`1 + i` with `{0,1}` — the division algorithm cycles.** `{0,1}` is again a
complete residue system (`N(1+i) = 2`), Lemma 1 and Lemma 2 go through
verbatim, but existence fails: for `z = i`,

```
T(i) = (i − 1)/(1 + i) = i ,
```

a fixed point that never reaches `0`. So `i` has *no* finite expansion, and
the set that is representable is a fractal proper subset of `ℤ[i]` (the
hatched gaps in the explorer). Uniqueness without existence.

**`2i` with `{0,1,2,3}` (Knuth's quater-imaginary) — not a residue system on
`ℤ[i]`.** `N(2i) = 4` but rational-integer digits occupy only two classes mod
`2i` (`2 ≡ 0`, `3 ≡ 1`), so Lemma 1 fails and greedy division is not
well-defined. Integer digit strings `Σ d_k (2i)^k` have even imaginary part,
so exactly half of `ℤ[i]` is reachable: `i` itself needs Knuth's radix-point
digit (`i = 10.2₍₂ᵢ₎`). Quater-imaginary is a perfectly good system for
ℂ-with-a-radix-point, but not for finite integer strings.

**The full classification (Kátai–Szabó 1975).** `(b, {0, 1, …, N(b)−1})`
represents every Gaussian integer uniquely **iff** `b = −n ± i` for some
integer `n ≥ 1`. Base `i − 1 = −1 + i` is the `n = 1` case — the only one
with binary digits, and the reason the twindragon tiles the plane by halves.

## 5. The algorithm, as shipped

[`imaginary.html`](./imaginary.html) implements the proof directly:

- `gdivmod(z, b, D)` is Lemma 1's residue step for any `(b, D)`;
- `encode(z, b, D)` iterates it — the descent of §3 — with cycle detection,
  so a `1+i`-style orbit that never reaches `0` is reported as
  "no expansion" instead of looping forever;
- `evalDigits(digits, b)` is the Horner reconstruction used to state the
  theorem, and every clicked cell shows the `z → (z − d)/b` trace;
- the canvas colors each Gaussian integer by its minimal digit count, computed
  by the forward search `S₀ = {0}`, `Sₙ₊₁ = b·Sₙ + D` (for unique-representation
  systems the minimal count is *the* count, and CI asserts both computations
  agree).

CI ([`scripts/ci-check.mjs`](./scripts/ci-check.mjs)) re-derives the theorem's
content computationally on every push: exhaustive round-trips over the
`|a|, |b| ≤ 40` box, exhaustive uniqueness over all canonical strings up to 16
digits, and the `1+i` / `2i` failure modes above as negative controls.

The Lean 4 development in [`theorem/`](./theorem/) machine-checks §§1–3 —
`Penney.exists_rep`, `Penney.eval_inj`, and the packaged `Penney.penney`
(∃! stated unfolded: an expansion exists, is canonical, and every canonical
expansion equals it) — with no `sorry` and no axioms beyond Lean's kernel.

## References

- S. I. Khmelnik, *Specialized digital computer for operations with complex
  numbers* (in Russian), Questions of Radio Electronics 12 (1964).
- W. F. Penney, *A "binary" system for complex numbers*, JACM 12 (1965)
  247–248.
- D. E. Knuth, *An imaginary number system*, CACM 3 (1960) 245–247.
- I. Kátai, J. Szabó, *Canonical number systems for complex integers*,
  Acta Sci. Math. (Szeged) 37 (1975) 255–260.
- D. E. Knuth, *The Art of Computer Programming*, Vol. 2, §4.1 —
  positional number systems with unusual radices; the twindragon.
