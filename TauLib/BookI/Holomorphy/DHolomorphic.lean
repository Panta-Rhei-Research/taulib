import TauLib.BookI.Polarity.BipolarAlgebra
import TauLib.BookI.Boundary.SplitComplex
import Mathlib.Tactic.Ring

/-!
# TauLib.BookI.Holomorphy.DHolomorphic

D-holomorphy on the split-complex algebra H_τ = Z[j], j² = +1.

## Registry Cross-References

- [I.D42] D-Differentiability — `SectorFun`, `is_sector_independent`
- [I.D43] Split-CR Equations — `split_cr_form`
- [I.P22] Sector Independence — `sector_independence`, `sector_fun_of_sector_independent`

## Ground Truth Sources
- chunk_0228_M002194: Split-complex algebra, sector decomposition
- chunk_0310_M002679: Bipolar partition, D-holomorphic structure

## Mathematical Content

A function f: H_τ → H_τ is D-holomorphic if in sector coordinates (u,v) = (a+b, a-b),
f decomposes as f(u,v) = (g(u), h(v)) — each sector component depends on only one
sector variable. This is the split-complex analog of the Cauchy-Riemann equations.

The split-CR equations are: ∂U/∂a = ∂V/∂b, ∂U/∂b = ∂V/∂a (note the + sign,
contrasting with the classical − sign). In sector coordinates: ∂F₊/∂v = 0, ∂F₋/∂u = 0.

D-holomorphic functions are too flexible: any pair (g, h) works, giving no rigidity.
Zero divisors e₊ · e₋ = 0 are the root cause. τ-holomorphy (Chapter 47) adds tower
coherence to rescue rigidity.
-/

namespace Tau.Holomorphy

open Tau.Polarity Tau.Boundary

-- ============================================================
-- SECTOR FUNCTIONS [I.D42]
-- ============================================================

/-- [I.D42] A sector function is a pair of Z → Z functions (g, h) representing
    f(u,v) = (g(u), h(v)) in sector coordinates. This is the canonical form
    of a D-holomorphic function. -/
structure SectorFun where
  /-- B-sector component: depends only on u = a + b. -/
  g : Int → Int
  /-- C-sector component: depends only on v = a - b. -/
  h : Int → Int

/-- Apply a sector function to a SectorPair. -/
def SectorFun.apply (sf : SectorFun) (s : SectorPair) : SectorPair :=
  ⟨sf.g s.b_sector, sf.h s.c_sector⟩

/-- Apply a sector function to a SplitComplex (via sector coordinates). -/
def SectorFun.apply_sc (sf : SectorFun) (z : SplitComplex) : SplitComplex :=
  from_sectors (sf.apply (to_sectors z))

-- ============================================================
-- SECTOR INDEPENDENCE PREDICATE [I.P22]
-- ============================================================

/-- [I.P22] A function f: SectorPair → SectorPair is sector-independent if
    its B-output depends only on the B-input and its C-output depends only
    on the C-input. This is the content of the split-CR equations. -/
def is_sector_independent (f : SectorPair → SectorPair) : Prop :=
  ∀ s₁ s₂ : SectorPair,
    (s₁.b_sector = s₂.b_sector → (f s₁).b_sector = (f s₂).b_sector) ∧
    (s₁.c_sector = s₂.c_sector → (f s₁).c_sector = (f s₂).c_sector)

/-- [I.P22] Every SectorFun is sector-independent by construction. -/
theorem sector_fun_independent (sf : SectorFun) :
    is_sector_independent sf.apply := by
  intro s₁ s₂
  simp only [SectorFun.apply]
  constructor
  · intro hb; exact congrArg sf.g hb
  · intro hc; exact congrArg sf.h hc

-- ============================================================
-- SPLIT-CR FORM [I.D43]
-- ============================================================

/-- [I.D43] A function f: SplitComplex → SplitComplex satisfies the split-CR
    form if it factors through sector coordinates as a SectorFun.
    That is, there exist g, h such that f = from_sectors ∘ (g, h) ∘ to_sectors. -/
def has_split_cr_form (f : SplitComplex → SplitComplex) : Prop :=
  ∃ sf : SectorFun, ∀ z : SplitComplex, f z = sf.apply_sc z

-- ============================================================
-- COMPOSITION OF SECTOR FUNCTIONS
-- ============================================================

/-- Composition of sector functions: component-wise composition. -/
def SectorFun.comp (sf₁ sf₂ : SectorFun) : SectorFun :=
  ⟨sf₁.g ∘ sf₂.g, sf₁.h ∘ sf₂.h⟩

/-- Composition of sector functions gives sectorial composition in sector coordinates. -/
theorem sector_comp_apply (sf₁ sf₂ : SectorFun) (s : SectorPair) :
    (sf₁.comp sf₂).apply s = sf₁.apply (sf₂.apply s) := by
  simp [SectorFun.comp, SectorFun.apply]

/-- Composition of sector functions is associative. -/
theorem sector_comp_assoc (sf₁ sf₂ sf₃ : SectorFun) :
    (sf₁.comp sf₂).comp sf₃ = sf₁.comp (sf₂.comp sf₃) := rfl

/-- The identity sector function. -/
def SectorFun.id : SectorFun := ⟨fun x => x, fun x => x⟩

/-- Identity is a left unit for composition. -/
theorem sector_id_comp (sf : SectorFun) :
    SectorFun.id.comp sf = sf := by
  cases sf; rfl

/-- Identity is a right unit for composition. -/
theorem sector_comp_id (sf : SectorFun) :
    sf.comp SectorFun.id = sf := by
  cases sf; rfl

-- ============================================================
-- ZERO DIVISOR EXAMPLE (re-export from BipolarAlgebra)
-- ============================================================

/-- e₊ · e₋ = 0: the zero divisor product in sector coordinates.
    This is the fundamental pathology of D-holomorphy:
    functions can be zero on one sector and arbitrary on the other. -/
theorem zero_div_sectors : SectorPair.mul e_plus_sector e_minus_sector = ⟨0, 0⟩ :=
  e_orthogonal

/-- Concrete witness: (1+j)(1-j) = 0 in split-complex coordinates. -/
theorem zero_div_sc : SplitComplex.mul ⟨1, 1⟩ ⟨1, -1⟩ = SplitComplex.zero := by
  native_decide

-- ============================================================
-- SECTOR-PURE FUNCTIONS (D-holomorphic pathology witnesses)
-- ============================================================

/-- A sector function that is zero on the C-sector: f(u,v) = (g(u), 0).
    This is D-holomorphic but has no C-sector information. -/
def b_only_fun (g : Int → Int) : SectorFun := ⟨g, fun _ => 0⟩

/-- A sector function that is zero on the B-sector: f(u,v) = (0, h(v)).
    This is D-holomorphic but has no B-sector information. -/
def c_only_fun (h : Int → Int) : SectorFun := ⟨fun _ => 0, h⟩

/-- B-only and C-only sector functions compose to zero
    (the functional analog of e₊ · e₋ = 0). -/
theorem b_only_comp_c_only (g : Int → Int) (h : Int → Int) (s : SectorPair) :
    (b_only_fun g).apply ((c_only_fun h).apply s) = ⟨g 0, 0⟩ := by
  simp [b_only_fun, c_only_fun, SectorFun.apply]

-- ============================================================
-- CHARACTERS AS SECTOR FUNCTIONS
-- ============================================================

/-- χ₊ as a sector function: projects to B-sector. -/
def chi_plus_sf : SectorFun := ⟨fun u => u, fun _ => 0⟩

/-- χ₋ as a sector function: projects to C-sector. -/
def chi_minus_sf : SectorFun := ⟨fun _ => 0, fun v => v⟩

/-- χ₊ applied to sector coordinates gives the B-sector projection. -/
theorem chi_plus_sf_apply (s : SectorPair) :
    chi_plus_sf.apply s = ⟨s.b_sector, 0⟩ := by
  simp [chi_plus_sf, SectorFun.apply]

/-- χ₋ applied to sector coordinates gives the C-sector projection. -/
theorem chi_minus_sf_apply (s : SectorPair) :
    chi_minus_sf.apply s = ⟨0, s.c_sector⟩ := by
  simp [chi_minus_sf, SectorFun.apply]

/-- χ₊ and χ₋ sum to the identity in sector coordinates. -/
theorem chi_sector_complete (s : SectorPair) :
    SectorPair.add (chi_plus_sf.apply s) (chi_minus_sf.apply s) = s := by
  simp [chi_plus_sf, chi_minus_sf, SectorFun.apply, SectorPair.add]

/-- χ₊ and χ₋ are orthogonal: their sector product is zero. -/
theorem chi_sector_orthogonal (s : SectorPair) :
    SectorPair.mul (chi_plus_sf.apply s) (chi_minus_sf.apply s) = ⟨0, 0⟩ := by
  simp [chi_plus_sf, chi_minus_sf, SectorFun.apply, SectorPair.mul]

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Sector function application
#eval chi_plus_sf.apply ⟨5, 3⟩         -- ⟨5, 0⟩
#eval chi_minus_sf.apply ⟨5, 3⟩        -- ⟨0, 3⟩
#eval (chi_plus_sf.comp chi_plus_sf).apply ⟨5, 3⟩  -- ⟨5, 0⟩ (idempotent)
#eval (chi_plus_sf.comp chi_minus_sf).apply ⟨5, 3⟩ -- ⟨0, 0⟩ (orthogonal)

-- SectorFun.apply_sc roundtrip
#eval chi_plus_sf.apply_sc ⟨3, 2⟩      -- from_sectors ⟨5, 0⟩

end Tau.Holomorphy
