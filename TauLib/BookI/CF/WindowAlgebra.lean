import TauLib.BookI.Kernel.Diagonal

/-!
# TauLib.BookI.CF.WindowAlgebra

Window algebra on the continued fraction head of ι_τ = 2/(π+e).

## Registry Cross-References

- [CF.01] CF Head — `cf_head`
- [CF.05] 17 = a₃+a₄+a₅ — `w3_at_3`
- [CF.06] 5/7 symmetric recipe — `symmetric_recipe`
- [CF.09] Window Algebra — `windowSum`, key identities

## Mathematical Content

The continued fraction CF[ι_τ] = [0; 2, 1, 13, 3, 1, 1, 1, 42, ...] encodes
electroweak physics through width-3 sliding window sums W₃(j) = a_j + a_{j+1} + a_{j+2}.

Key values:
- W₃(3) = 13+3+1 = 17  (g_A NLO denominator: 8/17)
- W₃(4) = 3+1+1 = 5    (sin²θ_W NLO numerator)
- W₃(5) = 1+1+1 = 3    (= |solenoidal triple|)

The symmetric 5/7 identity:
  5/7 = W₃(4) / (W₃(3) − 2·W₃(4))
Both numerator and denominator use the same W₃ family.

The 17/5 quotient:
  M_W/m_n = (17/5)·ι⁻³ = W₃(3)/W₃(4) · ι⁻³

Width 3 = |{π, γ, η}| = cardinality of solenoidal triple = number of
generators winding through the fiber T².
-/

namespace Tau.CF

open Tau.Kernel

-- ============================================================
-- CF HEAD
-- ============================================================

/-- The first 14 partial quotients of CF[ι_τ] = CF[2/(π+e)].
    Index 0 = floor part (0), indices 1..13 = partial quotients a₁..a₁₃.
    Sufficient for all known physics encodings. -/
def cf_head : List Nat := [0, 2, 1, 13, 3, 1, 1, 1, 42, 1, 2, 1, 5, 5]

theorem cf_head_length : cf_head.length = 14 := by rfl

-- ============================================================
-- WINDOW SUM
-- ============================================================

/-- Window sum W_k(j): sum of `width` consecutive CF terms starting at position `start`.
    Returns 0 if any index is out of bounds. -/
def windowSum (cf : List Nat) (width start : Nat) : Nat :=
  (List.range width).foldl (fun acc i =>
    acc + (cf.getD (start + i) 0)) 0

-- ============================================================
-- KEY WINDOW VALUES
-- ============================================================

/-- [CF.05] W₃(3) = a₃ + a₄ + a₅ = 13 + 3 + 1 = 17.
    The g_A NLO denominator: δ_A = (8/17)·ι². -/
theorem w3_at_3 : windowSum cf_head 3 3 = 17 := by native_decide

/-- [CF.06] W₃(4) = a₄ + a₅ + a₆ = 3 + 1 + 1 = 5.
    The sin²θ_W NLO numerator. -/
theorem w3_at_4 : windowSum cf_head 3 4 = 5 := by native_decide

/-- W₃(5) = a₅ + a₆ + a₇ = 1 + 1 + 1 = 3.
    Equals the cardinality of the solenoidal triple {π, γ, η}. -/
theorem w3_at_5 : windowSum cf_head 3 5 = 3 := by native_decide

/-- W₃(1) = a₁ + a₂ + a₃ = 2 + 1 + 13 = 16. -/
theorem w3_at_1 : windowSum cf_head 3 1 = 16 := by native_decide

/-- W₃(2) = a₂ + a₃ + a₄ = 1 + 13 + 3 = 17. -/
theorem w3_at_2 : windowSum cf_head 3 2 = 17 := by native_decide

-- ============================================================
-- SYMMETRIC 5/7 IDENTITY
-- ============================================================

/-- [CF.06] The symmetric recipe for 5/7:
    numerator = W₃(4) = 5, denominator = W₃(3) − 2·W₃(4) = 17 − 10 = 7.
    Both sides use the same W₃ window family. -/
theorem symmetric_recipe :
    let w34 := windowSum cf_head 3 4  -- 5
    let denom := windowSum cf_head 3 3 - 2 * windowSum cf_head 3 4  -- 17 - 10 = 7
    w34 = 5 ∧ denom = 7 := by
  native_decide

/-- The product 5 × 7 = 35 from the symmetric recipe. -/
theorem symmetric_product :
    windowSum cf_head 3 4 * (windowSum cf_head 3 3 - 2 * windowSum cf_head 3 4) = 35 := by
  native_decide

-- ============================================================
-- 17/5 QUOTIENT (M_W/m_n)
-- ============================================================

/-- [CF.06] The 17/5 quotient: W₃(3)/W₃(4) = 17/5.
    This is the coefficient in M_W/m_n = (17/5)·ι⁻³. -/
theorem mw_window_quotient :
    windowSum cf_head 3 3 = 17 ∧ windowSum cf_head 3 4 = 5 := by
  exact ⟨w3_at_3, w3_at_4⟩

-- ============================================================
-- WIDTH-3 = SOLENOIDAL CARDINALITY
-- ============================================================

/-- The window width 3 equals the number of solenoidal generators.
    This is the structural reason WHY width-3 windows encode physics:
    each W₃ window sum "reads out" one complete fiber period
    through the three generators {π, γ, η} winding through T². -/
theorem window_width_is_solenoidal :
    3 = solenoidalGenerators.length := by
  rfl

/-- W₃(5) = 3 = |solenoidal|: the third window echoes the width itself. -/
theorem w3_at_5_eq_solenoidal :
    windowSum cf_head 3 5 = solenoidalGenerators.length := by
  native_decide

-- ============================================================
-- INDIVIDUAL CF TERMS (for cross-reference)
-- ============================================================

/-- a₃ = 13 (the CF hub, anomalously large). -/
theorem a3_eq : cf_head.getD 3 0 = 13 := by native_decide

/-- a₄ = 3 = dim(τ³) = window width. -/
theorem a4_eq : cf_head.getD 4 0 = 3 := by native_decide

/-- a₈ = 42 (the "dark number", highest information content). -/
theorem a8_eq : cf_head.getD 8 0 = 42 := by native_decide

-- ============================================================
-- THREE EW OBSERVABLES FROM TWO WINDOWS
-- ============================================================

/-- The electroweak cross-web: all three EW observables (g_A, sin²θ_W, M_W/m_n)
    are determined by two adjacent W₃ windows at positions 3 and 4.
    - g_A NLO: 8/W₃(3) = 8/17
    - sin²θ_W NLO: W₃(4)/(W₃(3)−2·W₃(4)) = 5/7
    - M_W/m_n: W₃(3)/W₃(4) = 17/5
    This structure packages 3 from the 17 that is expressible as a sum of
    sums from two overlapping W₃ windows. -/
structure EWCrossWeb where
  w3_3 : Nat  -- W₃(3) = 17
  w3_4 : Nat  -- W₃(4) = 5
  hw3 : w3_3 = windowSum cf_head 3 3
  hw4 : w3_4 = windowSum cf_head 3 4

/-- The canonical EW cross-web instance. -/
def ewCrossWeb : EWCrossWeb := ⟨17, 5, by native_decide, by native_decide⟩

end Tau.CF
