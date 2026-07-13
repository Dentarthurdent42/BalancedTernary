# Machine-checked proof

A Lean 4 formalization of the Penney–Khmelnik theorem stated and proved on
paper in [`../THEOREM.md`](../THEOREM.md):

> every Gaussian integer has exactly one canonical representation in base
> `β = i − 1` with digits `{0, 1}`.

- [`Penney.lean`](./Penney.lean) — the whole development. Core Lean only,
  no mathlib: Gaussian integers as a two-field structure, the division
  algorithm `T z = (z − digit z)/β`, existence by strong induction on the
  norm (the five exceptional orbits are discharged by `decide` on explicit
  digit strings), uniqueness by parity and cancellation of β, and the
  packaged `Penney.penney : ∀ z, ∃! ds, Canonical ds ∧ eval ds = z`.
- No `sorry`, no extra axioms (`decide` only — nothing uses `Classical.choice`
  beyond what `by_cases` on decidable propositions needs).

## Building

```bash
cd theorem
lake build        # requires the pinned toolchain in ./lean-toolchain (elan fetches it)
```

CI builds this on every push alongside the JavaScript checks.
