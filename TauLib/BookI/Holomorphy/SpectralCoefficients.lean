import TauLib.BookI.Holomorphy.IdentityTheorem
import TauLib.BookI.Boundary.Fourier

/-!
# TauLib.BookI.Holomorphy.SpectralCoefficients

Spectral coefficients and the restriction map for τ-holomorphic functions.

## Registry Cross-References

- [I.D65] Spectral Coefficients — `SpectralCoeff`
- [I.D66] Restriction Map — `restriction`
- [I.T29] Spectral Determination — `spectral_determines`

## Mathematical Content

Each τ-holomorphic function decomposes into spectral coefficients
via the character basis χ₊, χ₋ from Part X.
At each primorial stage k, the B-sector and C-sector outputs
provide two "Fourier coefficients".

The Spectral Determination Theorem: a τ-holomorphic function
is uniquely determined by its spectral coefficients.
-/

namespace Tau.Holomorphy

open Tau.Polarity Tau.Denotation Tau.Boundary

-- ============================================================
-- SPECTRAL COEFFICIENTS [I.D65]
-- ============================================================

/-- [I.D65] Spectral coefficients of a StageFun at input n, stage k.
    The B-sector coefficient is the B-output; the C-sector coefficient
    is the C-output. Together they determine the function value at (n, k). -/
structure SpectralCoeff where
  -- B-sector coefficient
  b_coeff : TauIdx
  -- C-sector coefficient
  c_coeff : TauIdx

/-- Extract spectral coefficients from a StageFun. -/
def spectral_of (f : StageFun) (n k : TauIdx) : SpectralCoeff :=
  ⟨f.b_fun n k, f.c_fun n k⟩

/-- Two functions with the same spectral coefficients agree at that point. -/
theorem spectral_eq_implies_agree (f₁ f₂ : StageFun) (n k : TauIdx)
    (h : spectral_of f₁ n k = spectral_of f₂ n k) :
    f₁.b_fun n k = f₂.b_fun n k ∧ f₁.c_fun n k = f₂.c_fun n k := by
  have hb : (spectral_of f₁ n k).b_coeff = (spectral_of f₂ n k).b_coeff :=
    congrArg SpectralCoeff.b_coeff h
  have hc : (spectral_of f₁ n k).c_coeff = (spectral_of f₂ n k).c_coeff :=
    congrArg SpectralCoeff.c_coeff h
  exact ⟨hb, hc⟩

-- ============================================================
-- RESTRICTION MAP [I.D66]
-- ============================================================

/-- [I.D66] The restriction map: restrict a StageFun to inputs
    NOT in a given subset K (modeled as a predicate).
    Returns 0 for inputs in K (the "deleted" set). -/
def restriction (f : StageFun) (inK : TauIdx → Bool) : StageFun :=
  { b_fun := fun n k => if inK n then 0 else f.b_fun n k
    c_fun := fun n k => if inK n then 0 else f.c_fun n k }

/-- Restriction agrees with original outside K. -/
theorem restriction_outside (f : StageFun) (inK : TauIdx → Bool)
    (n k : TauIdx) (hn : inK n = false) :
    (restriction f inK).b_fun n k = f.b_fun n k ∧
    (restriction f inK).c_fun n k = f.c_fun n k := by
  simp [restriction, hn]

/-- Restriction is zero inside K. -/
theorem restriction_inside (f : StageFun) (inK : TauIdx → Bool)
    (n k : TauIdx) (hn : inK n = true) :
    (restriction f inK).b_fun n k = 0 ∧
    (restriction f inK).c_fun n k = 0 := by
  simp [restriction, hn]

-- ============================================================
-- SPECTRAL DETERMINATION [I.T29]
-- ============================================================

/-- [I.T29] Spectral Determination: if two tower-coherent StageFuns
    have the same spectral coefficients at all inputs and stages,
    they are equal.

    This is essentially the content of the Identity Theorem (I.T21)
    reformulated in spectral language. -/
theorem spectral_determines (f₁ f₂ : StageFun)
    (h : ∀ n k, spectral_of f₁ n k = spectral_of f₂ n k) :
    f₁ = f₂ := by
  cases f₁; cases f₂
  simp only [StageFun.mk.injEq]
  constructor <;> funext n k
  · exact (spectral_eq_implies_agree _ _ n k (h n k)).1
  · exact (spectral_eq_implies_agree _ _ n k (h n k)).2

/-- Spectral coefficients of χ₊ at input 1, stage 1. -/
example : (spectral_of chi_plus_stage 1 1).b_coeff = 1 := by native_decide

/-- Spectral coefficients of χ₋ at input 1, stage 1. -/
example : (spectral_of chi_minus_stage 1 1).c_coeff = 1 := by native_decide

-- ============================================================
-- SMOKE TESTS
-- ============================================================

#eval spectral_of chi_plus_stage 5 2    -- ⟨b, c⟩
#eval spectral_of chi_minus_stage 5 2

-- Restriction
#eval (restriction chi_plus_stage (fun n => n == 5)).b_fun 5 2   -- 0 (deleted)
#eval (restriction chi_plus_stage (fun n => n == 5)).b_fun 3 2   -- original value

end Tau.Holomorphy
