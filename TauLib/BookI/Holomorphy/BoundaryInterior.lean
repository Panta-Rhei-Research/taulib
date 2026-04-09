import TauLib.BookI.Holomorphy.GlobalHartogs
import TauLib.BookI.Topos.InternalHom

/-!
# TauLib.BookI.Holomorphy.BoundaryInterior

The boundary-interior passage: boundary determines interior.

## Registry Cross-References

- [I.D68] Earned Interior Point — `EarnedInteriorPoint`
- [I.C02] Interior from Boundary — `interior_from_boundary`
- [I.P29] Passage to Book II — `passage_to_book_ii`

## Mathematical Content

The Global Hartogs Extension Theorem (I.T31) implies that
the boundary L = S¹ ∨ S¹ determines the interior of τ³.
Every interior point can be reconstructed from boundary data
via tower-coherent extension.

This chapter bridges Book I to Book II:
the Central Theorem O(τ³) ≅ A_spec(L) makes this determination precise.

## Book I Summary

Starting from:
- 5 generators: α, π, γ, η, ω
- 6+3 axioms: K1-K6 + diagonal discipline + solenoidality + finite saturation
- 1 operator: ρ (primorial reduction)

Through 60 chapters we earned:
- The τ-index set and program monoid (Part III-V)
- The ABCD chart and normal form (Part V)
- Prime polarity and the algebraic lemniscate (Part VI-VII)
- Internal set theory and boundary ring (Part VIII-IX)
- Characters and spectral decomposition (Part X)
- Four-valued logic (Part XI)
- Holomorphic transformers and the Identity Theorem (Part XII)
- The earned category and topos (Part XIII)
- Bi-monoidal structure (Part XIV)
- The Global Hartogs Extension Theorem (Part XV)
-/

namespace Tau.Holomorphy

open Tau.Polarity Tau.Denotation Tau.Topos

-- ============================================================
-- EARNED INTERIOR POINT [I.D68]
-- ============================================================

/-- [I.D68] An earned interior point: a value obtained by
    extending boundary data via the Hartogs extension.
    The extension is uniquely determined by tower coherence
    and the Identity Theorem. -/
structure EarnedInteriorPoint where
  -- The boundary function (tower-coherent StageFun)
  boundary_fun : StageFun
  -- Tower coherence
  coherent : TowerCoherent boundary_fun
  -- The interior value at input n, stage k
  value_at : TauIdx → TauIdx → TauIdx := boundary_fun.b_fun

/-- An earned interior point from the identity StageFun. -/
def earned_id : EarnedInteriorPoint where
  boundary_fun := id_stage
  coherent := id_coherent

/-- Interior values are self-consistent: output at stage k is reduced. -/
theorem earned_interior_reduced (p : EarnedInteriorPoint) (n k : TauIdx) :
    reduce (p.boundary_fun.b_fun n k) k = p.boundary_fun.b_fun n k :=
  output_reduced p.boundary_fun p.coherent n k

-- ============================================================
-- INTERIOR FROM BOUNDARY [I.C02]
-- ============================================================

/-- [I.C02] Corollary: the interior is determined by the boundary.
    Two tower-coherent functions with the same boundary data
    (i.e., agreement at a reference depth) have the same interior values. -/
theorem interior_from_boundary (f₁ f₂ : StageFun)
    (hcoh1 : TowerCoherent f₁) (hcoh2 : TowerCoherent f₂)
    (d₀ : TauIdx) (hbdry : ∀ n, agree_at f₁ f₂ n d₀) :
    ∀ n k, k ≤ d₀ → f₁.b_fun n k = f₂.b_fun n k :=
  fun n k hk => (tau_identity_nat f₁ f₂ hcoh1 hcoh2 d₀ hbdry n k hk).1

/-- The interior-boundary principle for C-sector. -/
theorem interior_from_boundary_c (f₁ f₂ : StageFun)
    (hcoh1 : TowerCoherent f₁) (hcoh2 : TowerCoherent f₂)
    (d₀ : TauIdx) (hbdry : ∀ n, agree_at f₁ f₂ n d₀) :
    ∀ n k, k ≤ d₀ → f₁.c_fun n k = f₂.c_fun n k :=
  fun n k hk => (tau_identity_nat f₁ f₂ hcoh1 hcoh2 d₀ hbdry n k hk).2

-- ============================================================
-- PASSAGE TO BOOK II [I.P29]
-- ============================================================

/-- [I.P29] Passage to Book II: the earned import list.
    Book I has earned all the tools needed for the Central Theorem.

    The canonical data structure that Book II receives: -/
structure BookIExport where
  -- The earned category
  category : Tau.Topos.CatTau
  -- The earned topos
  topos : Tau.Topos.EarnedTopos
  -- The holomorphic function space Hol(L)
  hol_space : Type := HolFun
  -- The identity theorem provides uniqueness
  identity : ∀ f₁ f₂ : StageFun,
    TowerCoherent f₁ → TowerCoherent f₂ →
    ∀ d₀, (∀ n, agree_at f₁ f₂ n d₀) →
    ∀ n k, k ≤ d₀ → agree_at f₁ f₂ n k
  -- The subobject classifier is Truth4
  classifier_four : ∀ v : Tau.Logic.Omega_tau,
    v = Tau.Logic.Truth4.T ∨ v = Tau.Logic.Truth4.F ∨
    v = Tau.Logic.Truth4.B ∨ v = Tau.Logic.Truth4.N

/-- The canonical Book I export. -/
def book_i_export : BookIExport where
  category := Tau.Topos.cat_tau
  topos := Tau.Topos.earned_topos
  identity := tau_identity_nat
  classifier_four := Tau.Topos.omega_tau_classifier

-- ============================================================
-- BOOK I EARNED INFRASTRUCTURE COUNT
-- ============================================================

/-- Book I summary: 5 generators (α, π, γ, η, ω). -/
theorem five_generators :
    [Tau.Kernel.Generator.alpha, .pi, .gamma, .eta, .omega].length = 5 := rfl

/-- Book I summary: the program monoid is associative. -/
theorem monoid_assoc :
    ∀ f₁ f₂ f₃ : StageFun,
    StageFun.comp (StageFun.comp f₁ f₂) f₃ =
    StageFun.comp f₁ (StageFun.comp f₂ f₃) :=
  stagefun_comp_assoc

/-- Book I summary: the topos is non-Boolean. -/
theorem non_boolean : Tau.Logic.Truth4.impl Tau.Logic.Truth4.B Tau.Logic.Truth4.F ≠ Tau.Logic.Truth4.T :=
  Tau.Logic.explosion_barrier

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Earned interior
#eval earned_id.value_at 7 2     -- reduce(7, 2) via id_stage
#eval earned_id.value_at 42 3    -- reduce(42, 3) via id_stage

-- Book I export exists
#check book_i_export

end Tau.Holomorphy
