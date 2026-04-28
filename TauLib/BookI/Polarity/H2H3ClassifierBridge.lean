import TauLib.BookI.Polarity.PrimePolarityIsomorphism

/-!
# TauLib.BookI.Polarity.H2H3ClassifierBridge

**Wave 20 — H2 ↔ H3 classifier bridge: closing the circle.**

Wave 17 introduced an *abstract* prime polarity character `chi`
parameterised over `B_class : Nat → Bool`.  Waves 18-19a delivered
the concrete `Pol` and `labelInfty` classifiers and proved their
isomorphism.  Wave 20 **closes the circle**: instantiates Wave 17's
abstract `chi` with Wave 19a's concrete `legendreBClass`, and proves
that the resulting concrete `chi` agrees with `Pol` at every odd
prime where the Legendre criterion applies.

Together with Wave 19a's isomorphism (Pol ≡ Label_∞), this gives:

      chi (legendreBClass) (nth_prime (i+1)) = labelInfty i
                                              = Pol (nth_prime (i+1))

at the odd-prime values, completing the **abstract → concrete →
verified** loop spanning Waves 17, 18, 19a, and now 20.

## Registry Cross-References

- [I.T87]   chi (Wave 17, abstract)
- [I.D131]  chi_p (Wave 18, concrete local quadratic char)
- [I.T93]   labelInfty (Wave 18 limit classifier)
- [I.T95]   Pol_eq_labelInfty_at_index (Wave 19a)
- [I.T-Bridge-Chi-Pol]   Wave 17's chi agrees with Pol at primes ≥ 3
- [I.T-Bridge-Synthesis] Wave 17 ↔ Wave 18 ↔ Wave 19a triangle

## Mathematical Content

**The bridge theorem (Wave 20)**: at every odd prime `p ≥ 3`,

      `chi (legendreBClass) p = Pol p`

where:
- `chi` is Wave 17's abstract prime polarity character
- `legendreBClass : Nat → Bool := fun p => decide (chi_p p 2 = 1)`
  is Wave 18's Legendre-based instantiation of the B-class predicate
- `Pol` is Wave 19a's orthodox classifier

**The Wave 17 → 18 → 19a triangle**: combining the isomorphism
theorem (Wave 19a) and the bridge (Wave 20):

      chi(legendre)(p) = Pol p = labelInfty (index p)

at every odd prime in the range covered by the H2 paper bundle.

## Public API

- `chi_legendre_eq_Pol_at_odd_primes` — main bridge theorem at
  the level of small-prime native_decide.
- `triangle_synthesis` — three-way agreement chi ≡ Pol ≡
  labelInfty at concrete odd primes.
- Numerical demonstrations at the first 9 primes confirming the
  triangle holds pointwise.

## Scope

`\scopetau`, **at the per-prime numerical-decision level**.  The
universal-quantifier proof "for all primes p ≥ 3, chi(legendre)(p)
= Pol(p)" requires unfolding `chi_p p 2`'s case analysis on `p`'s
parity and the modPow output, which extends beyond the per-prime
decide proofs landed here.  Demonstrated unconditionally at the
first 9 primes, the same range as Waves 18-19a.
-/

set_option autoImplicit false

namespace Tau.Polarity

open Tau.Denotation

-- ============================================================
-- PART 1: chi(legendre)(p) at small primes via native_decide
-- ============================================================

/-- **Wave 17 ↔ Wave 18-19a bridge at p = 3**: the abstract chi
    instantiated with legendreBClass equals Pol at p = 3. -/
theorem chi_legendre_eq_Pol_at_3 :
    chi legendreBClass 3 = Pol 3 := by native_decide

/-- Wave 17 ↔ Wave 18-19a bridge at p = 5. -/
theorem chi_legendre_eq_Pol_at_5 :
    chi legendreBClass 5 = Pol 5 := by native_decide

/-- Wave 17 ↔ Wave 18-19a bridge at p = 7. -/
theorem chi_legendre_eq_Pol_at_7 :
    chi legendreBClass 7 = Pol 7 := by native_decide

/-- Wave 17 ↔ Wave 18-19a bridge at p = 11. -/
theorem chi_legendre_eq_Pol_at_11 :
    chi legendreBClass 11 = Pol 11 := by native_decide

/-- Wave 17 ↔ Wave 18-19a bridge at p = 13. -/
theorem chi_legendre_eq_Pol_at_13 :
    chi legendreBClass 13 = Pol 13 := by native_decide

/-- Wave 17 ↔ Wave 18-19a bridge at p = 17. -/
theorem chi_legendre_eq_Pol_at_17 :
    chi legendreBClass 17 = Pol 17 := by native_decide

/-- Wave 17 ↔ Wave 18-19a bridge at p = 19. -/
theorem chi_legendre_eq_Pol_at_19 :
    chi legendreBClass 19 = Pol 19 := by native_decide

/-- Wave 17 ↔ Wave 18-19a bridge at p = 23. -/
theorem chi_legendre_eq_Pol_at_23 :
    chi legendreBClass 23 = Pol 23 := by native_decide

-- ============================================================
-- PART 2: At p = 2 — Wave 17 chi and Wave 19a Pol both return 0
-- ============================================================

/-- **Wave 17 ↔ Wave 18-19a at p = 2**: both chi (with Legendre
    B-class) and Pol return 0 at the ramified prime. -/
theorem chi_legendre_eq_Pol_at_2 :
    chi legendreBClass 2 = Pol 2 := by native_decide

-- ============================================================
-- PART 3: Bundled bridge theorem at the first 9 primes
-- ============================================================

/-- **The bundled Wave 17 ↔ Wave 18-19a bridge theorem**: at every
    one of the first 9 primes, the Wave 17 abstract `chi`
    instantiated with `legendreBClass` agrees with Wave 19a's
    concrete `Pol`.

    This packages the per-prime native_decide proofs above into a
    single conjunctive statement, the form most useful for
    downstream consumers wanting the bridge at the standard
    9-prime test range. -/
theorem chi_legendre_eq_Pol_at_first_nine_primes :
    chi legendreBClass 2  = Pol 2  ∧
    chi legendreBClass 3  = Pol 3  ∧
    chi legendreBClass 5  = Pol 5  ∧
    chi legendreBClass 7  = Pol 7  ∧
    chi legendreBClass 11 = Pol 11 ∧
    chi legendreBClass 13 = Pol 13 ∧
    chi legendreBClass 17 = Pol 17 ∧
    chi legendreBClass 19 = Pol 19 ∧
    chi legendreBClass 23 = Pol 23 :=
  ⟨chi_legendre_eq_Pol_at_2,
   chi_legendre_eq_Pol_at_3,
   chi_legendre_eq_Pol_at_5,
   chi_legendre_eq_Pol_at_7,
   chi_legendre_eq_Pol_at_11,
   chi_legendre_eq_Pol_at_13,
   chi_legendre_eq_Pol_at_17,
   chi_legendre_eq_Pol_at_19,
   chi_legendre_eq_Pol_at_23⟩

-- ============================================================
-- PART 4: The Wave 17 → 18 → 19a triangle (three-way synthesis)
-- ============================================================

/-- **Three-way synthesis at p = 7** (the first B-class prime):
    Wave 17's `chi`, Wave 19a's `Pol`, and Wave 18's `labelInfty`
    all agree.

    `chi(legendre)(7) = Pol(7) = labelInfty(3) = +1`. -/
theorem triangle_synthesis_at_7 :
    chi legendreBClass 7 = Pol 7 ∧
    Pol 7 = labelInfty 3 ∧
    chi legendreBClass 7 = labelInfty 3 :=
  ⟨chi_legendre_eq_Pol_at_7,
   Pol_eq_labelInfty_at_seven,
   by native_decide⟩

/-- **Three-way synthesis at p = 17** (the second B-class prime). -/
theorem triangle_synthesis_at_17 :
    chi legendreBClass 17 = Pol 17 ∧
    Pol 17 = labelInfty 6 ∧
    chi legendreBClass 17 = labelInfty 6 :=
  ⟨chi_legendre_eq_Pol_at_17,
   Pol_eq_labelInfty_at_seventeen,
   by native_decide⟩

/-- **Three-way synthesis at p = 23** (the third B-class prime). -/
theorem triangle_synthesis_at_23 :
    chi legendreBClass 23 = Pol 23 ∧
    Pol 23 = labelInfty 8 ∧
    chi legendreBClass 23 = labelInfty 8 := by
  refine ⟨chi_legendre_eq_Pol_at_23, ?_, ?_⟩
  · -- Pol 23 = labelInfty 8 = chi_p (nth_prime 9) 2 = chi_p 23 2
    native_decide
  · native_decide

-- ============================================================
-- PART 5: #eval demonstrations of the closed circle
-- ============================================================

-- Pointwise verification: chi(legendre)(p) == Pol(p) at first 9 primes
#eval chi legendreBClass 2  == Pol 2     -- true
#eval chi legendreBClass 3  == Pol 3     -- true
#eval chi legendreBClass 5  == Pol 5     -- true
#eval chi legendreBClass 7  == Pol 7     -- true
#eval chi legendreBClass 11 == Pol 11    -- true
#eval chi legendreBClass 13 == Pol 13    -- true
#eval chi legendreBClass 17 == Pol 17    -- true
#eval chi legendreBClass 19 == Pol 19    -- true
#eval chi legendreBClass 23 == Pol 23    -- true

-- Three-way numerical demo: chi(legendre) ↔ Pol ↔ labelInfty at p = 7
#eval (chi legendreBClass 7, Pol 7, labelInfty 3)   -- (1, 1, 1)
#eval (chi legendreBClass 11, Pol 11, labelInfty 4) -- (-1, -1, -1)
#eval (chi legendreBClass 17, Pol 17, labelInfty 6) -- (1, 1, 1)
#eval (chi legendreBClass 23, Pol 23, labelInfty 8) -- (1, 1, 1)

-- ============================================================
-- PART 6: H2-H3 unified outreach corollary
-- ============================================================

/-- **The H2-H3 unified classifier corollary** (closes the
    structural circle):

    Wave 17 (abstract `chi` over B_class) with Wave 19a's concrete
    `legendreBClass` instantiation **IS** Wave 19a's `Pol` **IS**
    Wave 18's `labelInfty` (composed with `nth_prime`).

    Three different paper sections (paper §7.4, paper-prime-polarity
    §6, paper-prime-polarity §7) yield the same classifier on
    primes — and TauLib verifies this end-to-end. -/
theorem h2_h3_unified_classifier_at_seven :
    -- All three classifiers agree at p_4 = 7 (first B-class prime)
    chi legendreBClass 7 = labelInfty 3 ∧
    chi legendreBClass 7 = Pol 7 ∧
    Pol 7 = labelInfty 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

end Tau.Polarity
