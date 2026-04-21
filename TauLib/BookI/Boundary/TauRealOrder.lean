import TauLib.BookI.Boundary.ConstructiveReals
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp

/-!
# TauLib.BookI.Boundary.TauRealOrder

Ordering on `TauReal`: strict less-than (`lt`) and less-than-or-equal
(`le`), both defined via the Cauchy approximation sequences.

## Registry Cross-References

- [I.D84] TauReal — the Cauchy completion of TauRat
- [I.D112] TauReal.equiv — the Cauchy equivalence relation on TauReal
  (from `ConstructiveReals.lean`, Wave 2a)

New declarations in this module are not yet registered (pending the
Wave 2 registry-bookkeeping commit): `TauReal.lt`, `TauReal.le`,
`LT TauReal` / `LE TauReal` instances, and the basic order lemmas.

## Mathematical Content

**Wave 2b** of the TauReal infrastructure (see `ROADMAP-3-HINGES.md`).

### Constructive ordering

Classical trichotomy on the reals is not constructive — given a
specific Cauchy sequence, we cannot always decide whether its limit is
positive, negative, or zero.  TauReal therefore carries two
independent constructive relations:

- `TauReal.lt a b` — **eventually strictly separated**:
  `∃ k N, ∀ n ≥ N, a.approx n + 1/(k+1) < b.approx n`.
  Witnesses a *definite* positive gap between `a` and `b`.

- `TauReal.le a b` — **never exceeded by a positive tolerance**:
  `∀ k, ∃ N, ∀ n ≥ N, a.approx n < b.approx n + 1/(k+1)`.
  Says `a` is not detectably greater than `b`.

Note that `le` is classically equivalent to `¬ lt b a` but not
constructively — `le` is the stronger positive-content formulation and
matches the Bishop-style constructive ordering.

### Wiring into Lean core

The `LT TauReal` and `LE TauReal` instances make the usual `a < b` and
`a ≤ b` notation work on `TauReal`, following the same pattern as
Wave 1b's `LT TauRat` / `LE TauRat` alignment.

### Scope of this module

- Definitions: `TauReal.lt`, `TauReal.le`, instances.
- Reflexivity, transitivity of `le`.
- Irreflexivity, asymmetry of `lt`.
- Bridge: `lt` implies `le`.
- Equiv-preservation:  `lt` / `le` are well-defined modulo `equiv`.

Constructive trichotomy (requires apartness) is **out of scope** for
Wave 2b and deferred to a later wave — the Wave 3/4 roadmap only needs
the above basic order properties.
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: STRICT LESS-THAN  (eventually strictly separated)
-- ============================================================

/-- Strict less-than on `TauReal`: `a < b` witnesses a *definite*
    positive gap — there's a tolerance `1/(k+1)` such that eventually
    `a.approx n + 1/(k+1) < b.approx n`. -/
def TauReal.lt (a b : TauReal) : Prop :=
  ∃ k N : Nat, ∀ n : Nat, N ≤ n →
    TauRat.lt ((a.approx n).add (TauRat.ofNatRecip k)) (b.approx n)

/-- `lt` is irreflexive. -/
theorem TauReal.lt_irrefl (a : TauReal) : ¬ TauReal.lt a a := by
  intro ⟨k, N, h⟩
  have hN := h N (_root_.le_refl _)
  -- hN : (a.approx N + 1/(k+1)) < a.approx N  — contradicts 1/(k+1) > 0
  unfold TauRat.lt at hN
  rw [toRat_add, TauRat.ofNatRecip_toRat] at hN
  have h_pos : (0 : Rat) < 1 / ((k : Rat) + 1) := by
    have : (0 : Rat) < (k : Rat) + 1 := by
      have : (0 : Rat) ≤ (k : Rat) := by exact_mod_cast Nat.zero_le k
      linarith
    exact div_pos (by norm_num) this
  linarith

-- ============================================================
-- PART 2: LESS-THAN-OR-EQUAL  (never exceeded by a positive tolerance)
-- ============================================================

/-- Less-than-or-equal on `TauReal`: `a ≤ b` says that for every
    tolerance `1/(k+1)`, eventually `a.approx n < b.approx n + 1/(k+1)`.
    Equivalent to saying: `a − b` is ≤ any positive rational. -/
def TauReal.le (a b : TauReal) : Prop :=
  ∀ k : Nat, ∃ N : Nat, ∀ n : Nat, N ≤ n →
    TauRat.lt (a.approx n) ((b.approx n).add (TauRat.ofNatRecip k))

/-- `le` is reflexive. -/
theorem TauReal.le_refl (a : TauReal) : TauReal.le a a := by
  intro k
  refine ⟨0, fun n _ => ?_⟩
  unfold TauRat.lt
  rw [toRat_add, TauRat.ofNatRecip_toRat]
  -- Goal: (a.approx n).toRat < (a.approx n).toRat + 1 / (k + 1)
  have h_pos : (0 : Rat) < 1 / ((k : Rat) + 1) := by
    have : (0 : Rat) < (k : Rat) + 1 := by
      have : (0 : Rat) ≤ (k : Rat) := by exact_mod_cast Nat.zero_le k
      linarith
    exact div_pos (by norm_num) this
  linarith

-- ============================================================
-- PART 3: lt → le BRIDGE
-- ============================================================

/-- `lt` implies `le`. -/
theorem TauReal.le_of_lt {a b : TauReal} (h : TauReal.lt a b) : TauReal.le a b := by
  obtain ⟨k₀, N₀, h_lt⟩ := h
  -- At any tolerance level k, past index N₀ we have
  --   a + 1/(k₀+1) < b
  -- which gives the weaker  a < b + 1/(k+1)  for any k (since 1/(k₀+1) > 0).
  intro k
  refine ⟨N₀, fun n hn => ?_⟩
  have h0 := h_lt n hn
  unfold TauRat.lt at h0 ⊢
  rw [toRat_add, TauRat.ofNatRecip_toRat] at h0
  rw [toRat_add, TauRat.ofNatRecip_toRat]
  -- h0 : (a.approx n).toRat + 1/(k₀+1) < (b.approx n).toRat
  -- Goal: (a.approx n).toRat < (b.approx n).toRat + 1/(k+1)
  have h_pos_k : (0 : Rat) < 1 / ((k : Rat) + 1) := by
    have : (0 : Rat) < (k : Rat) + 1 := by
      have : (0 : Rat) ≤ (k : Rat) := by exact_mod_cast Nat.zero_le k
      linarith
    exact div_pos (by norm_num) this
  have h_pos_k0 : (0 : Rat) < 1 / ((k₀ : Rat) + 1) := by
    have : (0 : Rat) < (k₀ : Rat) + 1 := by
      have : (0 : Rat) ≤ (k₀ : Rat) := by exact_mod_cast Nat.zero_le k₀
      linarith
    exact div_pos (by norm_num) this
  linarith

-- ============================================================
-- PART 4: le TRANSITIVITY
-- ============================================================

/-- `le` is transitive.

    Strategy: at tolerance level `k`, split the budget — use tolerance
    `2k+1` for each half (giving `1/(2k+2)` each), sum to `1/(k+1)`. -/
theorem TauReal.le_trans {a b c : TauReal}
    (hab : TauReal.le a b) (hbc : TauReal.le b c) : TauReal.le a c := by
  intro k
  obtain ⟨N₁, h₁⟩ := hab (2 * k + 1)
  obtain ⟨N₂, h₂⟩ := hbc (2 * k + 1)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have hn₁ : N₁ ≤ n := le_of_max_le_left hn
  have hn₂ : N₂ ≤ n := le_of_max_le_right hn
  have h_ab := h₁ n hn₁
  have h_bc := h₂ n hn₂
  unfold TauRat.lt at h_ab h_bc ⊢
  rw [toRat_add, TauRat.ofNatRecip_toRat] at h_ab h_bc
  rw [toRat_add, TauRat.ofNatRecip_toRat]
  -- h_ab : a.approx n .toRat < b.approx n .toRat + 1/(2k+2)
  -- h_bc : b.approx n .toRat < c.approx n .toRat + 1/(2k+2)
  -- Goal : a.approx n .toRat < c.approx n .toRat + 1/(k+1)
  -- Since 1/(2k+2) + 1/(2k+2) = 1/(k+1), the two half-tolerances sum cleanly.
  have h_eq : (1 : Rat) / ((2 * k + 1 : Nat) + 1) + 1 / ((2 * k + 1 : Nat) + 1)
              = 1 / ((k : Rat) + 1) := by
    push_cast; field_simp; ring
  linarith

-- ============================================================
-- PART 5: lt TRANSITIVITY AND ASYMMETRY
-- ============================================================

/-- `lt` is transitive.

    Strategy: chain the two witnessed gaps.  Take `k = k₁` (we only need
    the first gap, since `b < c` implies `b < b + 1/(k₂+1) + something`). -/
theorem TauReal.lt_trans {a b c : TauReal}
    (hab : TauReal.lt a b) (hbc : TauReal.lt b c) : TauReal.lt a c := by
  obtain ⟨k₁, N₁, h₁⟩ := hab
  obtain ⟨k₂, N₂, h₂⟩ := hbc
  refine ⟨k₁, max N₁ N₂, fun n hn => ?_⟩
  have hn₁ : N₁ ≤ n := le_of_max_le_left hn
  have hn₂ : N₂ ≤ n := le_of_max_le_right hn
  have h_ab := h₁ n hn₁
  have h_bc := h₂ n hn₂
  unfold TauRat.lt at h_ab h_bc ⊢
  rw [toRat_add, TauRat.ofNatRecip_toRat] at h_ab h_bc
  rw [toRat_add, TauRat.ofNatRecip_toRat]
  -- h_ab : a + 1/(k₁+1) < b
  -- h_bc : b + 1/(k₂+1) < c
  -- Goal : a + 1/(k₁+1) < c.  Chain:
  --        a + 1/(k₁+1) < b < b + 1/(k₂+1) < c.
  have h_pos_k₂ : (0 : Rat) < 1 / ((k₂ : Rat) + 1) := by
    have : (0 : Rat) < (k₂ : Rat) + 1 := by
      have : (0 : Rat) ≤ (k₂ : Rat) := by exact_mod_cast Nat.zero_le k₂
      linarith
    exact div_pos (by norm_num) this
  linarith

/-- `lt` is asymmetric. -/
theorem TauReal.lt_asymm {a b : TauReal}
    (hab : TauReal.lt a b) : ¬ TauReal.lt b a :=
  fun hba => TauReal.lt_irrefl a (TauReal.lt_trans hab hba)

-- ============================================================
-- PART 6: EQUIV-PRESERVATION (well-definedness)
-- ============================================================

/-- `lt` is preserved by `equiv` on the left. -/
theorem TauReal.lt_of_equiv_left {a a' b : TauReal}
    (h_equiv : TauReal.equiv a a') (h_lt : TauReal.lt a b) : TauReal.lt a' b := by
  obtain ⟨k, N, h_gap⟩ := h_lt
  obtain ⟨μ, h_mod⟩ := h_equiv
  -- Pick a half-tolerance at level `2k+1` on the equiv side, so the
  -- difference |a - a'| is below `1/(2k+2)`.  Combined with the `1/(k+1)`
  -- gap  a + 1/(k+1) < b, we keep a strictly positive gap from `a'`
  -- at a refined tolerance.
  refine ⟨2 * k + 1, max N (μ (2 * k + 1)), fun n hn => ?_⟩
  have hn_N : N ≤ n := le_of_max_le_left hn
  have hn_μ : μ (2 * k + 1) ≤ n := le_of_max_le_right hn
  have h_g := h_gap n hn_N
  have h_e := h_mod (2 * k + 1) n hn_μ
  unfold TauRat.lt at h_g h_e ⊢
  rw [toRat_add, TauRat.ofNatRecip_toRat] at h_g
  rw [TauRat.toRat_abs, toRat_sub, TauRat.ofNatRecip_toRat] at h_e
  rw [toRat_add, TauRat.ofNatRecip_toRat]
  -- h_g : a.toRat + 1/(k+1) < b.toRat
  -- h_e : |a.toRat - a'.toRat| < 1/(2k+2)
  -- Goal: a'.toRat + 1/(2k+2) < b.toRat
  -- From h_e:  a.toRat - 1/(2k+2) < a'.toRat < a.toRat + 1/(2k+2)
  --   ⇒  a'.toRat - 1/(2k+2) < a.toRat, so a'.toRat < a.toRat + 1/(2k+2)
  -- Then a'.toRat + 1/(2k+2) < a.toRat + 2/(2k+2) = a.toRat + 1/(k+1) < b.toRat
  have h_abs : ((a.approx n).toRat - (a'.approx n).toRat) < 1 / ((2 * k + 1 : Nat) + 1) ∧
               -((a.approx n).toRat - (a'.approx n).toRat) < 1 / ((2 * k + 1 : Nat) + 1) := by
    constructor
    · have := abs_lt.mp h_e
      linarith [this.2]
    · have := abs_lt.mp h_e
      linarith [this.1]
  have h_sum : (1 : Rat) / ((2 * k + 1 : Nat) + 1) + 1 / ((2 * k + 1 : Nat) + 1)
               = 1 / ((k : Rat) + 1) := by
    push_cast; field_simp; ring
  linarith

/-- `lt` is preserved by `equiv` on the right. -/
theorem TauReal.lt_of_equiv_right {a b b' : TauReal}
    (h_equiv : TauReal.equiv b b') (h_lt : TauReal.lt a b) : TauReal.lt a b' := by
  obtain ⟨k, N, h_gap⟩ := h_lt
  obtain ⟨μ, h_mod⟩ := h_equiv
  refine ⟨2 * k + 1, max N (μ (2 * k + 1)), fun n hn => ?_⟩
  have hn_N : N ≤ n := le_of_max_le_left hn
  have hn_μ : μ (2 * k + 1) ≤ n := le_of_max_le_right hn
  have h_g := h_gap n hn_N
  have h_e := h_mod (2 * k + 1) n hn_μ
  unfold TauRat.lt at h_g h_e ⊢
  rw [toRat_add, TauRat.ofNatRecip_toRat] at h_g
  rw [TauRat.toRat_abs, toRat_sub, TauRat.ofNatRecip_toRat] at h_e
  rw [toRat_add, TauRat.ofNatRecip_toRat]
  have h_abs : ((b.approx n).toRat - (b'.approx n).toRat) < 1 / ((2 * k + 1 : Nat) + 1) ∧
               -((b.approx n).toRat - (b'.approx n).toRat) < 1 / ((2 * k + 1 : Nat) + 1) := by
    constructor
    · have := abs_lt.mp h_e
      linarith [this.2]
    · have := abs_lt.mp h_e
      linarith [this.1]
  have h_sum : (1 : Rat) / ((2 * k + 1 : Nat) + 1) + 1 / ((2 * k + 1 : Nat) + 1)
               = 1 / ((k : Rat) + 1) := by
    push_cast; field_simp; ring
  linarith

/-- `le` is preserved by `equiv` on the left. -/
theorem TauReal.le_of_equiv_left {a a' b : TauReal}
    (h_equiv : TauReal.equiv a a') (h_le : TauReal.le a b) : TauReal.le a' b := by
  intro k
  obtain ⟨μ, h_mod⟩ := h_equiv
  obtain ⟨N, h_le_inst⟩ := h_le (2 * k + 1)
  refine ⟨max N (μ (2 * k + 1)), fun n hn => ?_⟩
  have hn_N : N ≤ n := le_of_max_le_left hn
  have hn_μ : μ (2 * k + 1) ≤ n := le_of_max_le_right hn
  have h_L := h_le_inst n hn_N
  have h_e := h_mod (2 * k + 1) n hn_μ
  unfold TauRat.lt at h_L h_e ⊢
  rw [toRat_add, TauRat.ofNatRecip_toRat] at h_L
  rw [TauRat.toRat_abs, toRat_sub, TauRat.ofNatRecip_toRat] at h_e
  rw [toRat_add, TauRat.ofNatRecip_toRat]
  have h_abs : ((a.approx n).toRat - (a'.approx n).toRat) < 1 / ((2 * k + 1 : Nat) + 1) ∧
               -((a.approx n).toRat - (a'.approx n).toRat) < 1 / ((2 * k + 1 : Nat) + 1) := by
    constructor
    · have := abs_lt.mp h_e
      linarith [this.2]
    · have := abs_lt.mp h_e
      linarith [this.1]
  have h_sum : (1 : Rat) / ((2 * k + 1 : Nat) + 1) + 1 / ((2 * k + 1 : Nat) + 1)
               = 1 / ((k : Rat) + 1) := by
    push_cast; field_simp; ring
  linarith

/-- `le` is preserved by `equiv` on the right. -/
theorem TauReal.le_of_equiv_right {a b b' : TauReal}
    (h_equiv : TauReal.equiv b b') (h_le : TauReal.le a b) : TauReal.le a b' := by
  intro k
  obtain ⟨μ, h_mod⟩ := h_equiv
  obtain ⟨N, h_le_inst⟩ := h_le (2 * k + 1)
  refine ⟨max N (μ (2 * k + 1)), fun n hn => ?_⟩
  have hn_N : N ≤ n := le_of_max_le_left hn
  have hn_μ : μ (2 * k + 1) ≤ n := le_of_max_le_right hn
  have h_L := h_le_inst n hn_N
  have h_e := h_mod (2 * k + 1) n hn_μ
  unfold TauRat.lt at h_L h_e ⊢
  rw [toRat_add, TauRat.ofNatRecip_toRat] at h_L
  rw [TauRat.toRat_abs, toRat_sub, TauRat.ofNatRecip_toRat] at h_e
  rw [toRat_add, TauRat.ofNatRecip_toRat]
  have h_abs : ((b.approx n).toRat - (b'.approx n).toRat) < 1 / ((2 * k + 1 : Nat) + 1) ∧
               -((b.approx n).toRat - (b'.approx n).toRat) < 1 / ((2 * k + 1 : Nat) + 1) := by
    constructor
    · have := abs_lt.mp h_e
      linarith [this.2]
    · have := abs_lt.mp h_e
      linarith [this.1]
  have h_sum : (1 : Rat) / ((2 * k + 1 : Nat) + 1) + 1 / ((2 * k + 1 : Nat) + 1)
               = 1 / ((k : Rat) + 1) := by
    push_cast; field_simp; ring
  linarith

-- ============================================================
-- PART 7: LEAN CORE LT / LE HIERARCHY ALIGNMENT
-- ============================================================

/-!
Wire `TauReal.lt` and `TauReal.le` into Lean core's `LT` / `LE` type-class
hierarchy, matching the Wave 1b alignment for `TauRat`.  Downstream
consumers can use `a < b` and `a ≤ b` on `TauReal` values.
-/

instance : LT TauReal := ⟨TauReal.lt⟩

instance : LE TauReal := ⟨TauReal.le⟩

/-- `a < b` on `TauReal` unfolds to `TauReal.lt a b` by definition. -/
@[simp] theorem TauReal.lt_iff (a b : TauReal) : a < b ↔ TauReal.lt a b := Iff.rfl

/-- `a ≤ b` on `TauReal` unfolds to `TauReal.le a b` by definition. -/
@[simp] theorem TauReal.le_iff (a b : TauReal) : a ≤ b ↔ TauReal.le a b := Iff.rfl

end Tau.Boundary
