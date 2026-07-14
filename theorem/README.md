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
  packaged `Penney.penney` — for every `z` a canonical digit string exists,
  evaluates to `z`, and is the only canonical one that does (`∃!`, stated
  unfolded since core Lean has no `ExistsUnique`).
- Proof toolkit: structural induction, `omega` (linear integer arithmetic),
  `decide` (the five exceptional orbits and other closed facts), `simp` with
  explicit lemma lists, and `rcases`/`by_cases` — all core tactics. No `sorry`,
  no mathlib, no axioms beyond the ones Lean's kernel-checked core itself uses.

## Building

```bash
cd theorem
lake build        # requires the pinned toolchain in ./lean-toolchain (elan fetches it)
```

CI builds this on every push alongside the JavaScript checks.
