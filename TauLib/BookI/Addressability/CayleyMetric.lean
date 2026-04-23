import TauLib.BookI.Denotation.ProgramMonoid

/-!
# TauLib.BookI.Addressability.CayleyMetric

The **Cayley word metric** on the program monoid's normal forms:
Hinge 7 `thm:main-cayley` from `papers/address-resolution/main.tex`.

## Registry Cross-References

- [I.D14] Instruction / Program
- [I.L02] NF Confluence (`Tau.Denotation.rho_count_compose`)
- [I.T-H7-Cayley] Cayley Word Metric (this module)

## Mathematical Content

**Hinge 7 Wave 5a**.  The address space `AddrTau` is the set of
NF-equivalence classes of programs.  Each class has a unique
representative `NormalForm = { seedMap, rhoCount }`.

This module defines and proves the metric axioms of the **Cayley
word metric** on the ρ-count component:

  `CayleyDist nf₁ nf₂ := natAbsDiff nf₁.rhoCount nf₂.rhoCount`

This is a **pseudometric** on `NormalForm` (NFs with the same ρ-count
but distinct seed-maps are at distance 0).  The full ultrametric on
the address space combines this with the seed-map component using a
max-combinator (Wave 5b, `OnticUltrametric.lean`).

We prove the four metric axioms:

- Non-negativity (trivial — `Nat`-valued).
- Symmetry: `CayleyDist nf₁ nf₂ = CayleyDist nf₂ nf₁`.
- `CayleyDist nf nf = 0`.
- Triangle inequality: `CayleyDist a c ≤ CayleyDist a b + CayleyDist b c`.

This is the simplest working Cayley metric that compiles cleanly under
TauLib's tactics-only Mathlib budget; the seed-map refinement layers
on cleanly in the ultrametric module above.
-/

set_option autoImplicit false

namespace Tau.Addressability

open Tau.Kernel
open Tau.Denotation

-- ============================================================
-- PART 1: Symmetric Nat absolute-difference (self-contained)
-- ============================================================

/-- Symmetric absolute difference between two `Nat` values:
    `|a - b|` realised as `(a - b) + (b - a)` since one term is zero. -/
def natAbsDiff (a b : Nat) : Nat := (a - b) + (b - a)

@[simp] theorem natAbsDiff_self (a : Nat) : natAbsDiff a a = 0 := by
  unfold natAbsDiff; omega

theorem natAbsDiff_comm (a b : Nat) : natAbsDiff a b = natAbsDiff b a := by
  unfold natAbsDiff; omega

theorem natAbsDiff_eq_zero_iff (a b : Nat) :
    natAbsDiff a b = 0 ↔ a = b := by
  unfold natAbsDiff
  constructor
  · intro h; omega
  · intro h; subst h; simp

theorem natAbsDiff_triangle (a b c : Nat) :
    natAbsDiff a c ≤ natAbsDiff a b + natAbsDiff b c := by
  unfold natAbsDiff; omega

-- ============================================================
-- PART 2: Cayley word (pseudo)metric on NormalForm
-- ============================================================

/-- The **Cayley word metric** on normal forms: absolute ρ-count drift. -/
def CayleyDist (nf₁ nf₂ : NormalForm) : Nat :=
  natAbsDiff nf₁.rhoCount nf₂.rhoCount

@[simp] theorem CayleyDist_self (nf : NormalForm) : CayleyDist nf nf = 0 := by
  unfold CayleyDist; simp

theorem CayleyDist_symm (nf₁ nf₂ : NormalForm) :
    CayleyDist nf₁ nf₂ = CayleyDist nf₂ nf₁ := by
  unfold CayleyDist
  exact natAbsDiff_comm _ _

/-- Identity-of-indiscernibles for the Cayley pseudometric:
    `CayleyDist = 0` ⇔ same ρ-count.  (NFs with same ρ-count but
    different seed maps have distance 0, capturing the pseudometric
    nature; the strictly-metric refinement layers on in 5b.) -/
theorem CayleyDist_eq_zero_iff_rhoCount (nf₁ nf₂ : NormalForm) :
    CayleyDist nf₁ nf₂ = 0 ↔ nf₁.rhoCount = nf₂.rhoCount := by
  unfold CayleyDist
  exact natAbsDiff_eq_zero_iff _ _

/-- Triangle inequality. -/
theorem CayleyDist_triangle (nf₁ nf₂ nf₃ : NormalForm) :
    CayleyDist nf₁ nf₃ ≤ CayleyDist nf₁ nf₂ + CayleyDist nf₂ nf₃ := by
  unfold CayleyDist
  exact natAbsDiff_triangle _ _ _

-- ============================================================
-- PART 3: Connection to NF infrastructure
-- ============================================================

/-- `CayleyDist` is preserved by NF composition with a third NF on
    the right: composing a fixed NF on both sides keeps the relative
    ρ-count distance unchanged. -/
theorem CayleyDist_compose_right (a b c : NormalForm) :
    CayleyDist (a.compose c) (b.compose c)
      = CayleyDist a b := by
  unfold CayleyDist NormalForm.compose
  unfold natAbsDiff
  simp; omega

/-- Symmetric: composition on the left preserves distance. -/
theorem CayleyDist_compose_left (a b c : NormalForm) :
    CayleyDist (c.compose a) (c.compose b)
      = CayleyDist a b := by
  unfold CayleyDist NormalForm.compose
  unfold natAbsDiff
  simp; omega

end Tau.Addressability
