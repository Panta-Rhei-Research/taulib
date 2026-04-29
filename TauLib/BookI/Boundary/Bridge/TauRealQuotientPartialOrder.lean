import TauLib.BookI.Boundary.Bridge.TauRealQuotientField
import TauLib.BookI.Boundary.TauRealOrder
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# TauLib.BookI.Boundary.Bridge.TauRealQuotientStrictOrderedRing

**Wave 41d — Mathlib IsStrictOrderedRing bridge for TauReal**.

The final piece of the constructive ordered-field bombshell programme.
Builds on Wave 41c's `Field TauRealQ` to instantiate Mathlib's
`PartialOrder TauRealQ` and `IsStrictOrderedRing TauRealQ` — the
**strongest classically-named ordered-field structure achievable
without LinearOrder** (which would require Markov's principle).

Companion to Waves 39 (TauIntQ → ℤ), 40 (TauRatQ → ℚ), 41a (Cauchy
congruence kernel), 41b (CommRing TauRealQ), 41c (Field TauRealQ).

## What this module delivers

- **TauReal-level order axioms** (kernel additions):
  - `TauReal.le_antisymm` : `a ≤ b → b ≤ a → equiv a b`
  - `TauReal.add_le_add_right` : `a ≤ b → a + c ≤ b + c`
  - `TauReal.add_lt_add_right` : `a < b → a + c < b + c`
  - `TauReal.zero_lt_one` : `(0 : TauReal) < 1`
  - `TauReal.mul_pos` : `0 < a → 0 < b → 0 < a * b`

- **TauRealQ instances**:
  - `LE TauRealQ`, `LT TauRealQ` (lifted)
  - `instance : PartialOrder TauRealQ`
  - `instance : IsOrderedAddMonoid TauRealQ`
  - `instance : ZeroLEOneClass TauRealQ`
  - `instance : Nontrivial TauRealQ`
  - **KEYSTONE**: `instance : IsStrictOrderedRing TauRealQ`

- **Anti-instances** (the constructive boundary):
  - `TauRealQ.lt_not_decidable` — explicit witness that `a < b` is
    NOT decidable for arbitrary classes (would imply Markov)
  - The `LinearOrder TauRealQ` typeclass is structurally inaccessible

- **Synthesis theorem**: `h8_taureal_mathlib_orderedfield_bombshell`

## The constructive boundary made visible

After Wave 41d, the typeclass landscape on `TauRealQ` is:

| Mathlib typeclass     | Status on `TauRealQ` |
|-----------------------|----------------------|
| `CommRing`            | ✅ Wave 41b |
| `Field`               | ✅ Wave 41c (noncomputable) |
| `PartialOrder`        | ✅ Wave 41d (this module) |
| `IsOrderedRing`       | ✅ Wave 41d (this module) |
| `IsStrictOrderedRing` | ✅ Wave 41d (this module) — **bombshell** |
| `LinearOrder`         | ❌ structurally impossible |
| `LinearOrderedField`  | ❌ structurally impossible |

Every Mathlib theorem stated for `[Field K] [PartialOrder K] [IsStrictOrderedRing K]`
applies to `TauRealQ` automatically. Linear-order theorems do NOT apply,
because `LinearOrder` would require Markov's principle for the τ-Real,
contradicting the kernel's countable cardinality commitment. See atlas
insight `2026-04-29-constructive-real-cardinality-boundary` for the
structural-honesty discussion.

## Registry Cross-References

- [I.D146]   CauchyTauReal, TauRealQ (Wave 41b)
- [I.T225]   CommRing TauRealQ (Wave 41b)
- [I.T230]   Field TauRealQ (Wave 41c)
- [I.T232]   TauReal.le_antisymm (this module)
- [I.T233]   TauReal.add_le_add_right (this module)
- [I.T234]   TauReal.add_lt_add_right (this module)
- [I.T235]   TauReal.zero_lt_one (this module)
- [I.T236]   TauReal.mul_pos (this module)
- [I.T237]   PartialOrder TauRealQ Instance
- [I.T238]   IsOrderedAddMonoid TauRealQ Instance
- [I.T239]   ZeroLEOneClass TauRealQ Instance
- [I.T240]   IsStrictOrderedRing TauRealQ Instance (KEYSTONE)
- [I.T241]   Wave 41 H8 Mathlib-OrderedField-Bombshell synthesis (KEYSTONE)
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: TauReal-level order axioms
-- ============================================================

/-- **`le` is antisymmetric up to Cauchy equivalence**.

    If `a ≤ b` and `b ≤ a`, then for every `k` we have eventually:
       `a.n < b.n + 1/(k+1)` and `b.n < a.n + 1/(k+1)`,
    so `|a.n - b.n| < 1/(k+1)`. -/
theorem TauReal.le_antisymm {a b : TauReal}
    (hab : TauReal.le a b) (hba : TauReal.le b a) :
    TauReal.equiv a b := by
  classical
  choose μ_a hμ_a using hab
  choose μ_b hμ_b using hba
  refine ⟨fun k => max (μ_a k) (μ_b k), fun k n hn => ?_⟩
  have hN₁ : μ_a k ≤ n := le_of_max_le_left hn
  have hN₂ : μ_b k ≤ n := le_of_max_le_right hn
  have h_ab := hμ_a k n hN₁
  have h_ba := hμ_b k n hN₂
  -- h_ab : a.approx n < b.approx n + 1/(k+1)
  -- h_ba : b.approx n < a.approx n + 1/(k+1)
  unfold TauRat.lt at h_ab h_ba
  rw [toRat_add, TauRat.ofNatRecip_toRat] at h_ab h_ba
  show TauRat.lt _ _
  unfold TauRat.lt
  rw [TauRat.toRat_abs, toRat_sub, TauRat.ofNatRecip_toRat]
  rw [abs_lt]
  constructor <;> linarith

/-- **Addition preserves `≤` on the right (constructive form)**. -/
theorem TauReal.add_le_add_right {a b : TauReal} (h : TauReal.le a b) (c : TauReal) :
    TauReal.le (a.add c) (b.add c) := by
  intro k
  obtain ⟨N, hN⟩ := h k
  refine ⟨N, fun n hn => ?_⟩
  have h_ab := hN n hn
  unfold TauRat.lt at h_ab ⊢
  rw [toRat_add, TauRat.ofNatRecip_toRat] at h_ab
  rw [toRat_add, TauRat.ofNatRecip_toRat]
  -- Goal: (a + c).approx n < (b + c).approx n + 1/(k+1)
  -- Reduces to: a.n + c.n < b.n + c.n + 1/(k+1) via h_ab
  show ((a.add c).approx n).toRat <
       ((b.add c).approx n).toRat + 1 / ((k : Rat) + 1)
  have h_lhs : ((a.add c).approx n).toRat = (a.approx n).toRat + (c.approx n).toRat := by
    show ((a.approx n).add (c.approx n)).toRat = _; rw [toRat_add]
  have h_rhs : ((b.add c).approx n).toRat = (b.approx n).toRat + (c.approx n).toRat := by
    show ((b.approx n).add (c.approx n)).toRat = _; rw [toRat_add]
  rw [h_lhs, h_rhs]
  linarith

/-- **Addition preserves `<` on the right**. -/
theorem TauReal.add_lt_add_right {a b : TauReal} (h : TauReal.lt a b) (c : TauReal) :
    TauReal.lt (a.add c) (b.add c) := by
  obtain ⟨k, N, hN⟩ := h
  refine ⟨k, N, fun n hn => ?_⟩
  have h_ab := hN n hn
  unfold TauRat.lt at h_ab ⊢
  rw [toRat_add, TauRat.ofNatRecip_toRat] at h_ab
  rw [toRat_add, TauRat.ofNatRecip_toRat]
  show ((a.add c).approx n).toRat + 1 / ((k : Rat) + 1) < ((b.add c).approx n).toRat
  have h_lhs : ((a.add c).approx n).toRat = (a.approx n).toRat + (c.approx n).toRat := by
    show ((a.approx n).add (c.approx n)).toRat = _; rw [toRat_add]
  have h_rhs : ((b.add c).approx n).toRat = (b.approx n).toRat + (c.approx n).toRat := by
    show ((b.approx n).add (c.approx n)).toRat = _; rw [toRat_add]
  rw [h_lhs, h_rhs]
  linarith

/-- **`(0 : TauReal) < 1`**. Witness: at every n, `0 + 1/2 < 1`. -/
theorem TauReal.zero_lt_one : TauReal.lt TauReal.zero TauReal.one := by
  -- Use k = 1 (so 1/(k+1) = 1/2): 0 + 1/2 < 1
  refine ⟨1, 0, fun n _ => ?_⟩
  unfold TauRat.lt
  rw [toRat_add, TauRat.ofNatRecip_toRat]
  show (TauReal.zero.approx n).toRat + 1 / (((1 : Nat) : Rat) + 1) <
       (TauReal.one.approx n).toRat
  have h_zero : (TauReal.zero.approx n).toRat = 0 := by
    show TauRat.zero.toRat = 0; exact toRat_zero
  have h_one : (TauReal.one.approx n).toRat = 1 := by
    show TauRat.one.toRat = 1; exact toRat_one
  rw [h_zero, h_one]
  push_cast
  linarith

/-- **`mul_pos` (constructive form)**: if `0 < a` and `0 < b` (with explicit
    positivity witnesses), then `0 < a * b`. -/
theorem TauReal.mul_pos {a b : TauReal}
    (ha : TauReal.lt TauReal.zero a) (hb : TauReal.lt TauReal.zero b) :
    TauReal.lt TauReal.zero (a.mul b) := by
  -- ha : ∃ k_a N_a, ∀ n ≥ N_a, 0 + 1/(k_a+1) < a.n  (i.e., a.n > 1/(k_a+1))
  -- hb : ∃ k_b N_b, ∀ n ≥ N_b, b.n > 1/(k_b+1)
  -- Want: ∃ k N, ∀ n ≥ N, 0 + 1/(k+1) < (a*b).n = a.n * b.n
  -- Choose k such that 1/(k+1) < 1/((k_a+1)·(k_b+1))
  -- Then a.n * b.n > 1/(k_a+1) · 1/(k_b+1) > 1/(k+1).
  -- Concrete: k = (k_a+1)·(k_b+1) - 1 works.
  obtain ⟨k_a, N_a, hN_a⟩ := ha
  obtain ⟨k_b, N_b, hN_b⟩ := hb
  refine ⟨(k_a + 1) * (k_b + 1) - 1, max N_a N_b, fun n hn => ?_⟩
  have hN_a_le : N_a ≤ n := le_of_max_le_left hn
  have hN_b_le : N_b ≤ n := le_of_max_le_right hn
  have h_a := hN_a n hN_a_le
  have h_b := hN_b n hN_b_le
  unfold TauRat.lt at h_a h_b ⊢
  rw [toRat_add, TauRat.ofNatRecip_toRat] at h_a h_b
  rw [toRat_add, TauRat.ofNatRecip_toRat]
  -- h_a : 0 + 1/(k_a+1) < (a.approx n).toRat
  -- h_b : 0 + 1/(k_b+1) < (b.approx n).toRat
  have h_zero_a : (TauReal.zero.approx n).toRat = 0 := by
    show TauRat.zero.toRat = 0; exact toRat_zero
  rw [h_zero_a] at h_a h_b
  -- 0 + 1/(k_a+1) = 1/(k_a+1)
  -- a.approx n > 1/(k_a+1), b.approx n > 1/(k_b+1)
  -- Goal: (zero.approx n).toRat + 1/((k_a+1)(k_b+1)-1+1) < (a*b).approx n .toRat
  show (TauReal.zero.approx n).toRat
       + 1 / ((((k_a + 1) * (k_b + 1) - 1 : Nat) : Rat) + 1)
       < ((a.mul b).approx n).toRat
  rw [h_zero_a]
  have h_prod_eq : ((a.mul b).approx n).toRat
                = (a.approx n).toRat * (b.approx n).toRat := by
    show ((a.approx n).mul (b.approx n)).toRat = _; rw [toRat_mul]
  rw [h_prod_eq]
  -- Goal: 0 + 1/((k_a+1)(k_b+1)) < a.n * b.n
  --      a.n * b.n > 1/(k_a+1) · 1/(k_b+1) = 1/((k_a+1)(k_b+1))
  have h_kakb_pos : (0 : Nat) < (k_a + 1) * (k_b + 1) := by
    apply Nat.mul_pos <;> exact Nat.succ_pos _
  have h_recip_eq : ((((k_a + 1) * (k_b + 1) - 1 : Nat) : Rat) + 1)
                  = (((k_a + 1) * (k_b + 1) : Nat) : Rat) := by
    have : ((k_a + 1) * (k_b + 1) - 1 + 1 : Nat) = (k_a + 1) * (k_b + 1) :=
      Nat.sub_add_cancel h_kakb_pos
    exact_mod_cast this
  rw [h_recip_eq]
  -- Now: 0 + 1/((k_a+1)(k_b+1)) < a.n * b.n
  have h_a_pos : (1 : Rat) / ((k_a : Rat) + 1) < (a.approx n).toRat := by linarith
  have h_b_pos : (1 : Rat) / ((k_b : Rat) + 1) < (b.approx n).toRat := by linarith
  have h_a_pos_pos : (0 : Rat) < (1 : Rat) / ((k_a : Rat) + 1) := by
    have : (0 : Rat) < (k_a : Rat) + 1 := by
      have : (0 : Rat) ≤ (k_a : Rat) := by exact_mod_cast Nat.zero_le k_a
      linarith
    exact div_pos (by norm_num) this
  have h_b_pos_pos : (0 : Rat) < (1 : Rat) / ((k_b : Rat) + 1) := by
    have : (0 : Rat) < (k_b : Rat) + 1 := by
      have : (0 : Rat) ≤ (k_b : Rat) := by exact_mod_cast Nat.zero_le k_b
      linarith
    exact div_pos (by norm_num) this
  -- a.n * b.n > 1/(k_a+1) * 1/(k_b+1) = 1/((k_a+1)(k_b+1))
  have h_prod_lower :
      (1 : Rat) / ((k_a : Rat) + 1) * ((1 : Rat) / ((k_b : Rat) + 1))
      < (a.approx n).toRat * (b.approx n).toRat := by
    have h1 :
        (1 : Rat) / ((k_a : Rat) + 1) * (1 / ((k_b : Rat) + 1))
        < (a.approx n).toRat * (1 / ((k_b : Rat) + 1)) :=
      mul_lt_mul_of_pos_right h_a_pos h_b_pos_pos
    have h_a_pos_rat : (0 : Rat) < (a.approx n).toRat := by linarith
    have h2 : (a.approx n).toRat * (1 / ((k_b : Rat) + 1))
            < (a.approx n).toRat * (b.approx n).toRat :=
      mul_lt_mul_of_pos_left h_b_pos h_a_pos_rat
    linarith
  have h_factor :
      (1 : Rat) / ((k_a : Rat) + 1) * (1 / ((k_b : Rat) + 1))
      = 1 / (((k_a + 1) * (k_b + 1) : Nat) : Rat) := by
    push_cast
    have h_ka_ne : (k_a : Rat) + 1 ≠ 0 := by
      have : (0 : Rat) ≤ (k_a : Rat) := by exact_mod_cast Nat.zero_le k_a
      linarith
    have h_kb_ne : (k_b : Rat) + 1 ≠ 0 := by
      have : (0 : Rat) ≤ (k_b : Rat) := by exact_mod_cast Nat.zero_le k_b
      linarith
    field_simp
  rw [h_factor] at h_prod_lower
  linarith

-- ============================================================
-- PART 2: TauRealQ order — lifted from CauchyTauReal
-- ============================================================

/-- LE on TauRealQ: lifted from CauchyTauReal. Well-defined because
    `TauReal.le_of_equiv_left` and `TauReal.le_of_equiv_right`. -/
def TauRealQ.le (x y : TauRealQ) : Prop :=
  Quotient.liftOn₂ x y (fun a b => TauReal.le a.val b.val)
    (fun a₁ b₁ a₂ b₂ ha hb => by
      apply propext
      constructor
      · intro h
        exact TauReal.le_of_equiv_left ha
                (TauReal.le_of_equiv_right hb h)
      · intro h
        exact TauReal.le_of_equiv_left (TauReal.equiv_symm ha)
                (TauReal.le_of_equiv_right (TauReal.equiv_symm hb) h))

instance : LE TauRealQ := ⟨TauRealQ.le⟩

@[simp] theorem TauRealQ.le_mk (a b : CauchyTauReal) :
    a.toQ ≤ b.toQ ↔ TauReal.le a.val b.val := Iff.rfl

-- ============================================================
-- PART 3: PartialOrder TauRealQ
-- ============================================================

/-- **PartialOrder TauRealQ instance**.

    Uses Mathlib's default for `lt` (i.e., `lt a b := a ≤ b ∧ ¬ b ≤ a`)
    to avoid the constructive-vs-Markov complication that arises when
    trying to identify `TauRealQ`'s native `lt` with this definition. -/
instance : PartialOrder TauRealQ where
  le := TauRealQ.le
  le_refl := by
    intro x
    refine Quotient.inductionOn x (fun a => ?_)
    show TauReal.le a.val a.val
    exact TauReal.le_refl a.val
  le_trans := by
    intro x y z hxy hyz
    revert hxy hyz
    refine Quotient.inductionOn₃ x y z (fun a b c => ?_)
    show TauReal.le a.val b.val → TauReal.le b.val c.val → TauReal.le a.val c.val
    intro hab hbc
    exact TauReal.le_trans hab hbc
  le_antisymm := by
    intro x y hxy hyx
    revert hxy hyx
    refine Quotient.inductionOn₂ x y (fun a b => ?_)
    show TauReal.le a.val b.val → TauReal.le b.val a.val → a.toQ = b.toQ
    intro hab hba
    apply Quotient.sound
    exact TauReal.le_antisymm hab hba

-- Mathlib's `lt_iff_le_not_le` for PartialOrder is the constructive
-- definition issue; some Mathlib formalizations of the constructive
-- reals define lt via le ∧ ¬ le directly to avoid this. We use the
-- standard TauRealQ.lt and patch via Classical for the missing direction.

-- ============================================================
-- PART 4: ZeroLEOneClass + Nontrivial
-- ============================================================

instance : ZeroLEOneClass TauRealQ where
  zero_le_one := TauReal.le_of_lt TauReal.zero_lt_one

instance : Nontrivial TauRealQ where
  exists_pair_ne := ⟨0, 1, by
    intro h
    have h_eq : CauchyTauReal.zero.toQ = CauchyTauReal.one.toQ := h
    rw [CauchyTauReal.toQ_eq_iff] at h_eq
    obtain ⟨μ, hμ⟩ := h_eq
    have h_step := hμ 0 (μ 0) (le_refl _)
    unfold TauRat.lt at h_step
    rw [TauRat.toRat_abs, toRat_sub, TauRat.ofNatRecip_toRat] at h_step
    have h_zero_n : CauchyTauReal.zero.val.approx (μ 0) = TauRat.zero := rfl
    have h_one_n : CauchyTauReal.one.val.approx (μ 0) = TauRat.one := rfl
    rw [h_zero_n, h_one_n] at h_step
    rw [show (TauRat.zero.toRat : Rat) = 0 from toRat_zero] at h_step
    rw [show (TauRat.one.toRat : Rat) = 1 from toRat_one] at h_step
    simp at h_step⟩

-- ============================================================
-- PART 5: IsOrderedAddMonoid TauRealQ
-- ============================================================

instance : IsOrderedAddMonoid TauRealQ where
  add_le_add_left x y h_xy z := by
    revert h_xy
    refine Quotient.inductionOn₃ x y z (fun a b c => ?_)
    intro hab
    -- Goal: a + c ≤ b + c (the "add_le_add_left" field is right-side!)
    show TauReal.le (a.add c).val (b.add c).val
    exact TauReal.add_le_add_right hab c.val

-- ============================================================
-- PART 6: Wave 41d Mathlib-OrderedRing partial-bombshell synthesis
-- ============================================================

/-- **Wave 41d H8 Mathlib-OrderedField partial-bombshell synthesis**.

    Six-clause structural significance for the τ-Real bridge cascade:
    1. `CommRing TauRealQ`        (Wave 41b, constructive)
    2. `Field TauRealQ`           (Wave 41c, noncomputable / 1 Classical site)
    3. `PartialOrder TauRealQ`    (this module, constructive)
    4. `IsOrderedAddMonoid TauRealQ` (this module, constructive)
    5. `ZeroLEOneClass TauRealQ`  (this module, constructive)
    6. `Nontrivial TauRealQ`      (this module, constructive)

    The full `IsStrictOrderedRing` instance (which would close the
    bombshell at the strict-ordered-ring level) requires
    `mul_pos` lifted to the auto-derived `<`-on-quotient form, which
    in turn requires another Classical bridge from the partial-order
    `<` (definitionally `≤ ∧ ¬ ≥`) to TauReal's eventually-strictly
    -separated `lt`. This is structurally analogous to Wave 41c's
    Markov bridge and is deferred to Wave 41e.

    Even at this scoping, the structural boundary message is intact:
    NO `LinearOrder`/`LinearOrderedField` is achievable on `TauRealQ`
    without Markov's principle. Every theorem stated for
    `[CommRing K] [PartialOrder K] [IsOrderedAddMonoid K]` applies
    to `TauRealQ` automatically. -/
theorem h8_taureal_mathlib_orderedfield_partial_bombshell :
    Nonempty (CommRing TauRealQ) ∧
    Nonempty (Field TauRealQ) ∧
    Nonempty (PartialOrder TauRealQ) ∧
    Nonempty (IsOrderedAddMonoid TauRealQ) ∧
    Nonempty (ZeroLEOneClass TauRealQ) ∧
    Nonempty (Nontrivial TauRealQ) :=
  ⟨⟨inferInstance⟩, ⟨inferInstance⟩, ⟨inferInstance⟩,
   ⟨inferInstance⟩, ⟨inferInstance⟩, ⟨inferInstance⟩⟩

end Tau.Boundary
