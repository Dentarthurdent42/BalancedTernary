/-
The Penney–Khmelnik theorem, machine-checked:

  every Gaussian integer has exactly one canonical representation
  in base β = i − 1 with digits {0, 1}.

Self-contained — core Lean 4 only, no mathlib. The development mirrors
../THEOREM.md: the residue step (`digit`, `T`), descent on the norm with
five exceptional orbits handled by explicit digit strings, and uniqueness
by parity plus cancellation of β.

Digit strings are `List Bool`, least-significant digit first. `Canonical`
forbids a trailing `false` (a leading zero in the usual MSD-first reading),
so `0` is represented by `[]` and every value by exactly one string.
-/

namespace Penney

/-- A Gaussian integer, as a pair of integers. -/
structure GInt where
  re : Int
  im : Int
deriving DecidableEq, Repr

theorem GInt.ext {p q : GInt} (hre : p.re = q.re) (him : p.im = q.im) : p = q := by
  cases p; cases q; cases hre; cases him; rfl

@[simp] theorem mk_re (a b : Int) : (GInt.mk a b).re = a := rfl
@[simp] theorem mk_im (a b : Int) : (GInt.mk a b).im = b := rfl

instance : OfNat GInt 0 := ⟨⟨0, 0⟩⟩

@[simp] theorem zero_re : (0 : GInt).re = 0 := rfl
@[simp] theorem zero_im : (0 : GInt).im = 0 := rfl

/-- Multiplication by the base β = i − 1:  β·(x + yi) = (−x − y) + (x − y)i. -/
def bmul (w : GInt) : GInt := ⟨-w.re - w.im, w.re - w.im⟩

/-- The numeric value of one binary digit. -/
def digitVal : Bool → Int
  | true => 1
  | false => 0

/-- Value of a digit string, least-significant digit first: Σ dₖ βᵏ. -/
def eval : List Bool → GInt
  | [] => 0
  | d :: ds => ⟨(bmul (eval ds)).re + digitVal d, (bmul (eval ds)).im⟩

@[simp] theorem eval_nil_re : (eval []).re = 0 := rfl
@[simp] theorem eval_nil_im : (eval []).im = 0 := rfl

/-- Component form of `eval` on a cons cell. The right-hand side mentions
`eval ds` only behind projections, so rewriting with these never recurses. -/
theorem eval_cons_re (d : Bool) (ds : List Bool) :
    (eval (d :: ds)).re = -(eval ds).re - (eval ds).im + digitVal d := rfl

theorem eval_cons_im (d : Bool) (ds : List Bool) :
    (eval (d :: ds)).im = (eval ds).re - (eval ds).im := rfl

/-- The digit forced by the residue of `z` mod β: the parity of re + im. -/
def digit (z : GInt) : Int := (z.re + z.im) % 2

theorem digit_def (z : GInt) : digit z = (z.re + z.im) % 2 := rfl

def digitB (z : GInt) : Bool := decide (digit z = 1)

/-- One step of the division algorithm, `T z = (z − digit z) / β`, computed
without division by β: with `m = (re + im) / 2`, `T z = (im − m) − m·i`. -/
def T (z : GInt) : GInt := ⟨z.im - (z.re + z.im) / 2, -((z.re + z.im) / 2)⟩

theorem T_re (z : GInt) : (T z).re = z.im - (z.re + z.im) / 2 := rfl
theorem T_im (z : GInt) : (T z).im = -((z.re + z.im) / 2) := rfl

/-- The norm `a² + b²`. -/
def norm (z : GInt) : Int := z.re * z.re + z.im * z.im

theorem norm_def (z : GInt) : norm z = z.re * z.re + z.im * z.im := rfl

/-! ### Small integer facts (kept name-lean: omega does the arithmetic) -/

theorem sq_nonneg' (a : Int) : 0 ≤ a * a := by
  have h := Int.natAbs_mul_self (a := a)
  omega

theorem sq_pos (a : Int) (h : a ≠ 0) : 0 < a * a := by
  have hn := Int.natAbs_mul_self (a := a)
  have h0 : a.natAbs ≠ 0 := by omega
  have h1 : 0 < a.natAbs * a.natAbs :=
    Nat.mul_pos (Nat.pos_of_ne_zero h0) (Nat.pos_of_ne_zero h0)
  omega

theorem natAbs_le_one_of_sq_le_two (x : Int) (h : x * x ≤ 2) : x.natAbs ≤ 1 := by
  have hn := Int.natAbs_mul_self (a := x)
  by_cases hc : x.natAbs ≤ 1
  · exact hc
  · have h2 : 2 ≤ x.natAbs := by omega
    have h3 : 2 * 2 ≤ x.natAbs * x.natAbs := Nat.mul_le_mul h2 h2
    omega

theorem norm_pos (z : GInt) (h : z ≠ 0) : 0 < norm z := by
  have h1 := sq_nonneg' z.re
  have h2 := sq_nonneg' z.im
  rw [norm_def]
  by_cases hre : z.re = 0
  · by_cases him : z.im = 0
    · exact absurd (GInt.ext (by rw [hre]; rfl) (by rw [him]; rfl)) h
    · have := sq_pos z.im him
      omega
  · have := sq_pos z.re hre
    omega

theorem norm_nonneg (z : GInt) : 0 ≤ norm z := by
  have h1 := sq_nonneg' z.re
  have h2 := sq_nonneg' z.im
  rw [norm_def]
  omega

/-! ### The reconstruction step: β · T z + digit z = z -/

theorem digitVal_digitB (z : GInt) : digitVal (digitB z) = digit z := by
  have h : digit z = 0 ∨ digit z = 1 := by rw [digit_def]; omega
  unfold digitB
  rcases h with h | h <;> rw [h] <;> decide

theorem eval_step (z : GInt) (ds : List Bool) (h : eval ds = T z) :
    eval (digitB z :: ds) = z := by
  apply GInt.ext
  · rw [eval_cons_re, h, digitVal_digitB, T_re, T_im, digit_def]
    omega
  · rw [eval_cons_im, h, T_re, T_im]
    omega

/-! ### The descent: the norm drops outside five exceptional points -/

/-- The quadratic identity behind `2·N(T z) = N(z − d)`, in the two variables
that survive eliminating `z.re` via `2m = re + im − d`. -/
theorem quad_id (b m : Int) :
    2 * ((b - m) * (b - m) + -(m) * -(m)) = (m + m - b) * (m + m - b) + b * b := by
  have h1 : b - m = b + -(m) := by omega
  have h2 : m + m - b = m + m + -(b) := by omega
  rw [h1, h2]
  simp only [Int.mul_add, Int.add_mul, Int.mul_neg, Int.neg_mul, Int.neg_neg]
  simp only [Int.mul_comm m b]
  generalize b * b = B
  generalize b * m = P
  generalize m * m = M
  omega

theorem two_norm_T (z : GInt) :
    2 * norm (T z) = (z.re - digit z) * (z.re - digit z) + z.im * z.im := by
  rw [norm_def, T_re, T_im, digit_def]
  have ha : z.re - (z.re + z.im) % 2
      = (z.re + z.im) / 2 + (z.re + z.im) / 2 - z.im := by omega
  rw [ha]
  exact quad_id z.im ((z.re + z.im) / 2)

theorem sq_sub_one (a : Int) : (a - 1) * (a - 1) = a * a - a - a + 1 := by
  have h1 : a - 1 = a + -(1 : Int) := by omega
  rw [h1]
  simp only [Int.mul_add, Int.add_mul, Int.mul_neg, Int.neg_mul, Int.neg_neg,
    Int.mul_one, Int.one_mul]
  generalize a * a = A
  omega

theorem sq_add_one (a : Int) : (a + 1) * (a + 1) = a * a + a + a + 1 := by
  simp only [Int.mul_add, Int.add_mul, Int.mul_one, Int.one_mul]
  generalize a * a = A
  omega

/-- The five points where the `d = 1` step does not shrink the norm.
An `abbrev`, so `rcases`/`decide` see the disjunction directly. -/
abbrev Exceptional (z : GInt) : Prop :=
  z = ⟨-1, 0⟩ ∨ z = ⟨0, 1⟩ ∨ z = ⟨0, -1⟩ ∨ z = ⟨-2, 1⟩ ∨ z = ⟨-2, -1⟩

/-- Outside the exceptional set, an odd-parity point sits outside the
closed disk `(a+1)² + b² ≤ 2` that breaks the descent. -/
theorem not_small (a b : Int) (hd : (a + b) % 2 = 1)
    (hE : ¬Exceptional ⟨a, b⟩) : 2 < (a + 1) * (a + 1) + b * b := by
  by_cases hc : 2 < (a + 1) * (a + 1) + b * b
  · exact hc
  · exfalso
    have s1 := sq_nonneg' (a + 1)
    have s2 := sq_nonneg' b
    have b1 := natAbs_le_one_of_sq_le_two (a + 1) (by omega)
    have b2 := natAbs_le_one_of_sq_le_two b (by omega)
    have hre : a = -2 ∨ a = -1 ∨ a = 0 := by omega
    have him : b = -1 ∨ b = 0 ∨ b = 1 := by omega
    rcases hre with rfl | rfl | rfl <;> rcases him with rfl | rfl | rfl <;>
      first
        | omega
        | exact hE (by decide)

theorem norm_T_lt (z : GInt) (h0 : z ≠ 0) (hE : ¬Exceptional z) :
    norm (T z) < norm z := by
  obtain ⟨a, b⟩ := z
  have key := two_norm_T ⟨a, b⟩
  simp only [mk_re, mk_im] at key
  have hnz : 0 < norm (⟨a, b⟩ : GInt) := norm_pos _ h0
  have hnm : norm (⟨a, b⟩ : GInt) = a * a + b * b := rfl
  have hd : digit ⟨a, b⟩ = 0 ∨ digit ⟨a, b⟩ = 1 := by rw [digit_def]; omega
  rcases hd with hd | hd
  · -- d = 0: 2·N(T z) = N(z), and N(z) > 0
    rw [hd] at key
    have e0 : a - 0 = a := by omega
    rw [e0] at key
    omega
  · -- d = 1: 2·N(T z) = N(z) − 2a + 1 < 2·N(z) since (a+1)² + b² ≥ 3
    rw [hd] at key
    have hd' : (a + b) % 2 = 1 := hd
    have hB := not_small a b hd' hE
    have e1 := sq_sub_one a
    have e2 := sq_add_one a
    omega

/-! ### Existence -/

theorem exists_rep_bounded :
    ∀ (n : Nat) (z : GInt), (norm z).toNat ≤ n → ∃ ds : List Bool, eval ds = z := by
  intro n
  induction n with
  | zero =>
      intro z hz
      by_cases h0 : z = 0
      · exact ⟨[], by subst h0; rfl⟩
      · have h1 := norm_pos z h0
        exact absurd hz (by omega)
  | succ n ih =>
      intro z hz
      by_cases h0 : z = 0
      · exact ⟨[], by subst h0; rfl⟩
      by_cases hE : Exceptional z
      · rcases hE with rfl | rfl | rfl | rfl | rfl
        · exact ⟨[true, false, true, true, true], by decide⟩
        · exact ⟨[true, true], by decide⟩
        · exact ⟨[true, true, true], by decide⟩
        · exact ⟨[true, true, true, true, true], by decide⟩
        · exact ⟨[true, true, false, true, false, true, true, true], by decide⟩
      · have hlt := norm_T_lt z h0 hE
        have h1 := norm_nonneg (T z)
        have h2 := norm_nonneg z
        obtain ⟨ds, hds⟩ := ih (T z) (by omega)
        exact ⟨digitB z :: ds, eval_step z ds hds⟩

/-- **Existence**: every Gaussian integer has a base-(i−1) expansion. -/
theorem exists_rep (z : GInt) : ∃ ds : List Bool, eval ds = z :=
  exists_rep_bounded (norm z).toNat z (Nat.le_refl _)

/-! ### Uniqueness -/

/-- The parity of re + im of a value determines its last digit:
β·w has even re + im, so the digit alone decides the parity. -/
theorem eval_parity (d : Bool) (ds : List Bool) :
    ((eval (d :: ds)).re + (eval (d :: ds)).im) % 2 = digitVal d := by
  rw [eval_cons_re, eval_cons_im]
  cases d <;> simp only [digitVal] <;> omega

/-- No trailing `false` (no leading zero, reading most-significant first). -/
def Canonical : List Bool → Prop
  | [] => True
  | [d] => d = true
  | _ :: ds => Canonical ds

/-- A canonical nonempty string never represents 0
(so a leading 1 is never redundant). -/
theorem eval_ne_zero : ∀ (ds : List Bool), Canonical ds → ds ≠ [] → eval ds ≠ 0 := by
  intro ds
  induction ds with
  | nil => intro _ hne; exact absurd rfl hne
  | cons d t ih =>
      intro hc _
      cases t with
      | nil =>
          have hd : d = true := hc
          subst hd
          decide
      | cons x xs =>
          intro h0
          have hp := eval_parity d (x :: xs)
          rw [h0] at hp
          simp only [zero_re, zero_im] at hp
          have hd : d = false := by
            cases d
            · rfl
            · exfalso; simp only [digitVal] at hp; omega
          subst hd
          have h1 : (eval (false :: x :: xs)).re = (0 : GInt).re := by rw [h0]
          have h2 : (eval (false :: x :: xs)).im = (0 : GInt).im := by rw [h0]
          rw [eval_cons_re] at h1
          rw [eval_cons_im] at h2
          simp only [digitVal, zero_re, zero_im] at h1 h2
          have hz : eval (x :: xs) = 0 := by
            apply GInt.ext
            · rw [zero_re]; omega
            · rw [zero_im]; omega
          exact ih hc (by intro h; cases h) hz

/-- **Uniqueness**: canonical digit strings with equal values are equal. -/
theorem eval_inj : ∀ (ds : List Bool), Canonical ds →
    ∀ (es : List Bool), Canonical es → eval ds = eval es → ds = es := by
  intro ds
  induction ds with
  | nil =>
      intro _ es he h
      cases es with
      | nil => rfl
      | cons e u =>
          exact absurd h.symm (eval_ne_zero (e :: u) he (by intro h'; cases h'))
  | cons d t ih =>
      intro hd es he h
      cases es with
      | nil => exact absurd h (eval_ne_zero (d :: t) hd (by intro h'; cases h'))
      | cons e u =>
          have hp1 := eval_parity d t
          have hp2 := eval_parity e u
          rw [h] at hp1
          have hde : d = e := by
            cases d <;> cases e <;> simp only [digitVal] at hp1 hp2 <;>
              first | rfl | (exfalso; omega)
          subst hde
          have h1 : (eval (d :: t)).re = (eval (d :: u)).re := by rw [h]
          have h2 : (eval (d :: t)).im = (eval (d :: u)).im := by rw [h]
          simp only [eval_cons_re, eval_cons_im] at h1 h2
          have ht : eval t = eval u := GInt.ext (by omega) (by omega)
          cases t with
          | nil =>
              cases u with
              | nil => rfl
              | cons x xs =>
                  exact absurd ht.symm
                    (eval_ne_zero (x :: xs) he (by intro h'; cases h'))
          | cons y ys =>
              cases u with
              | nil =>
                  exact absurd ht (eval_ne_zero (y :: ys) hd (by intro h'; cases h'))
              | cons x xs =>
                  have htails : (y :: ys) = (x :: xs) := ih hd (x :: xs) he ht
                  rw [htails]

/-! ### Canonicalization: strip leading zeros -/

def trimCons (d : Bool) : List Bool → List Bool
  | [] => cond d [true] []
  | x :: xs => d :: x :: xs

def trim : List Bool → List Bool
  | [] => []
  | d :: t => trimCons d (trim t)

theorem eval_trim (ds : List Bool) : eval (trim ds) = eval ds := by
  induction ds with
  | nil => rfl
  | cons d t ih =>
      show eval (trimCons d (trim t)) = eval (d :: t)
      cases htr : trim t with
      | nil =>
          have h0 : eval t = 0 := by rw [← ih, htr]; rfl
          have h0re : (eval t).re = 0 := by rw [h0]; rfl
          have h0im : (eval t).im = 0 := by rw [h0]; rfl
          cases d
          · show eval [] = eval (false :: t)
            apply GInt.ext
            · have e1 := eval_cons_re false t
              have e2 : digitVal false = 0 := rfl
              rw [eval_nil_re]
              omega
            · have e1 := eval_cons_im false t
              rw [eval_nil_im]
              omega
          · show eval [true] = eval (true :: t)
            apply GInt.ext
            · have e1 := eval_cons_re true t
              have e2 := eval_cons_re true ([] : List Bool)
              have e3 : (eval ([] : List Bool)).re = 0 := rfl
              have e4 : (eval ([] : List Bool)).im = 0 := rfl
              omega
            · have e1 := eval_cons_im true t
              have e2 := eval_cons_im true ([] : List Bool)
              have e3 : (eval ([] : List Bool)).re = 0 := rfl
              have e4 : (eval ([] : List Bool)).im = 0 := rfl
              omega
      | cons x xs =>
          rw [htr] at ih
          have hre : (eval (x :: xs)).re = (eval t).re := by rw [ih]
          have him : (eval (x :: xs)).im = (eval t).im := by rw [ih]
          show eval (d :: x :: xs) = eval (d :: t)
          apply GInt.ext
          · have e1 := eval_cons_re d (x :: xs)
            have e2 := eval_cons_re d t
            omega
          · have e1 := eval_cons_im d (x :: xs)
            have e2 := eval_cons_im d t
            omega

theorem canonical_trim (ds : List Bool) : Canonical (trim ds) := by
  induction ds with
  | nil => exact trivial
  | cons d t ih =>
      show Canonical (trimCons d (trim t))
      cases htr : trim t with
      | nil =>
          cases d
          · exact trivial
          · exact rfl
      | cons x xs =>
          rw [htr] at ih
          exact ih

/-! ### The theorem -/

/-- **Penney–Khmelnik.** Every Gaussian integer has exactly one canonical
representation in base i − 1 with digits {0, 1}. (The statement is `∃!`
unfolded — core Lean has no `ExistsUnique`.) -/
theorem penney (z : GInt) :
    ∃ ds : List Bool, (Canonical ds ∧ eval ds = z) ∧
      ∀ es : List Bool, Canonical es → eval es = z → es = ds := by
  obtain ⟨ds₀, h₀⟩ := exists_rep z
  refine ⟨trim ds₀, ⟨canonical_trim ds₀, ?_⟩, ?_⟩
  · rw [eval_trim, h₀]
  · intro es hc he
    exact eval_inj es hc (trim ds₀) (canonical_trim ds₀)
      (by rw [he, eval_trim, h₀])

/-! ### Spot checks: the exceptional orbits of THEOREM.md §3, and values
that also appear in the interactive explorer and the JS test suite. -/

example : eval [true, true] = ⟨0, 1⟩ := by decide                 -- i   = 11
example : eval [true, true, true] = ⟨0, -1⟩ := by decide          -- −i  = 111
example : eval [true, false, true, true, true] = ⟨-1, 0⟩ := by decide  -- −1 = 11101
example : eval [true, true, true, true, true] = ⟨-2, 1⟩ := by decide
example : eval [true, true, false, true, false, true, true, true] = ⟨-2, -1⟩ := by decide
example : eval [false, true] = ⟨-1, 1⟩ := by decide               -- β itself = 10
example : digitB ⟨0, 1⟩ = true := by decide
example : T ⟨0, 1⟩ = ⟨1, 0⟩ := by decide                          -- i → 1 → 0
example : T ⟨1, 0⟩ = 0 := by decide

end Penney
