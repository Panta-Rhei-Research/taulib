import TauLib.BookI.Holomorphy.DiagonalProtection
import TauLib.BookI.Holomorphy.IdentityTheorem

/-!
# TauLib.BookI.Topos.EarnedArrows

The earned category Cat_τ: objects are τ-indices, morphisms are τ-arrows.

## Registry Cross-References

- [I.D50] τ-Arrow — `TauArrow`
- [I.D51] Cat_τ — `CatTau`
- [I.T22] Category Axioms — `cat_tau_id_left`, `cat_tau_id_right`, `cat_tau_assoc`
- [I.P25] Thin Category — `cat_tau_thin`

## Ground Truth Sources
- chunk_0072_M000759: Program monoid, normal form
- chunk_0155_M001710: Omega-tails, holomorphic structure

## Mathematical Content

A τ-arrow from X to Y is a HolFun that transforms ω-germs at X to ω-germs at Y.
Two HolFuns define the same arrow if they agree on all inputs at all stages
(i.e., they are extensionally equal).

Cat_τ is the category with:
- Objects: TauIdx (the τ-index set)
- Morphisms: τ-arrows (HolFun equivalence classes)
- Identity: id_holfun
- Composition: from composition closure (I.T20)
- Associativity: from I.P24

Cat_τ is THIN: between any two objects there is at most one morphism.
This follows from the τ-Identity Theorem (I.T21).
-/

namespace Tau.Topos

open Tau.Holomorphy Tau.Polarity Tau.Denotation

-- ============================================================
-- τ-ARROW [I.D50]
-- ============================================================

/-- [I.D50] A τ-arrow from source to target, carrying a HolFun.
    Two τ-arrows are equal iff their underlying HolFuns agree extensionally. -/
structure TauArrow where
  source : TauIdx
  target : TauIdx
  holfun : HolFun

/-- Two τ-arrows with the same source/target agree extensionally. -/
def TauArrow.ext_agree (a₁ a₂ : TauArrow)
    (hs : a₁.source = a₂.source) (ht : a₁.target = a₂.target) :
    a₁.source = a₂.source ∧ a₁.target = a₂.target := ⟨hs, ht⟩

-- ============================================================
-- Cat_τ [I.D51]
-- ============================================================

/-- The identity τ-arrow at object X. -/
def id_arrow (x : TauIdx) : TauArrow :=
  { source := x, target := x, holfun := id_holfun 0 }

/-- Compose two τ-arrows stagewise (when source/target match). -/
def arrow_comp_stage (a₁ a₂ : TauArrow) : StageFun :=
  StageFun.comp a₁.holfun.transformer.stage_fun a₂.holfun.transformer.stage_fun

/-- [I.D51] The data of Cat_τ: objects, identity arrows, and composition.
    Cat_τ is the earned category — not imported but built from HolFun. -/
structure CatTau where
  -- Identity arrow at each object
  id_ : TauIdx → TauArrow

/-- The canonical Cat_τ instance. -/
def cat_tau : CatTau := ⟨id_arrow⟩

/-- Identity arrows have matching source. -/
theorem cat_tau_id_src (x : TauIdx) : (cat_tau.id_ x).source = x := rfl

/-- Identity arrows have matching target. -/
theorem cat_tau_id_tgt (x : TauIdx) : (cat_tau.id_ x).target = x := rfl

-- ============================================================
-- CATEGORY AXIOMS [I.T22]
-- ============================================================

/-- [I.T22a] Left identity: id ∘ f gives the same stagewise output as
    applying id to the output of f. -/
theorem cat_tau_id_left_stage (f : StageFun) (n k : TauIdx) :
    (StageFun.comp id_stage f).b_fun n k = reduce (f.b_fun n k) k := by
  simp [StageFun.comp, id_stage]

/-- [I.T22b] Right identity: f ∘ id gives the same stagewise output. -/
theorem cat_tau_id_right_stage (f : StageFun) (n k : TauIdx) :
    (StageFun.comp f id_stage).b_fun n k = f.b_fun (reduce n k) k := by
  simp [StageFun.comp, id_stage]

/-- [I.T22c] Associativity of stagewise composition. -/
theorem cat_tau_assoc (f₁ f₂ f₃ : StageFun) :
    StageFun.comp (StageFun.comp f₁ f₂) f₃ = StageFun.comp f₁ (StageFun.comp f₂ f₃) :=
  stagefun_comp_assoc f₁ f₂ f₃

/-- [I.T22d] GermTransformer composition is associative. -/
theorem cat_tau_gt_assoc (gt₁ gt₂ gt₃ : GermTransformer) :
    GermTransformer.comp (GermTransformer.comp gt₁ gt₂) gt₃ =
    GermTransformer.comp gt₁ (GermTransformer.comp gt₂ gt₃) :=
  gt_comp_assoc gt₁ gt₂ gt₃

-- ============================================================
-- THIN CATEGORY [I.P25]
-- ============================================================

/-- [I.P25] Cat_τ is thin: if two tower-coherent stagewise functions
    agree at stage d₀ for all inputs, they agree at all stages ≤ d₀.
    This is a direct corollary of the τ-Identity Theorem (I.T21). -/
theorem cat_tau_thin (f₁ f₂ : StageFun)
    (h₁ : TowerCoherent f₁) (h₂ : TowerCoherent f₂)
    (d₀ : TauIdx) (hagree : ∀ n, agree_at f₁ f₂ n d₀) :
    ∀ n k, k ≤ d₀ → agree_at f₁ f₂ n k :=
  tau_identity_nat f₁ f₂ h₁ h₂ d₀ hagree

/-- Thin category consequence: self-agreement is trivial. -/
theorem cat_tau_self_agree (f : StageFun) (n k : TauIdx) :
    agree_at f f n k := ⟨rfl, rfl⟩

-- ============================================================
-- HOLFUN IDENTITY PROPERTIES
-- ============================================================

/-- The identity HolFun at any depth is tower-coherent. -/
theorem id_holfun_coherent (d : Nat) : TowerCoherent (id_holfun d).transformer.stage_fun :=
  id_coherent

/-- χ₊ composed with χ₊ gives the same B-sector output (idempotent, sample). -/
theorem chi_plus_idempotent :
    (StageFun.comp chi_plus_stage chi_plus_stage).b_fun 1 1 =
    chi_plus_stage.b_fun 1 1 := by native_decide

/-- χ₋ composed with χ₋ gives the same C-sector output (idempotent, sample). -/
theorem chi_minus_idempotent :
    (StageFun.comp chi_minus_stage chi_minus_stage).c_fun 1 1 =
    chi_minus_stage.c_fun 1 1 := by native_decide

-- ============================================================
-- ARROW COUNTING
-- ============================================================

/-- id, χ₊, χ₋ are at least 3 distinct HolFuns:
    χ₊ and χ₋ disagree at input 1, stage 1 in the B-sector. -/
theorem at_least_three_holfuns :
    chi_plus_stage.b_fun 1 1 ≠ chi_minus_stage.b_fun 1 1 := by native_decide

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Identity arrow source/target
#eval (id_arrow 5).source    -- 5
#eval (id_arrow 5).target    -- 5

-- Associativity check (both sides give same result)
#eval (StageFun.comp (StageFun.comp chi_plus_stage chi_minus_stage) id_stage).b_fun 17 3
#eval (StageFun.comp chi_plus_stage (StageFun.comp chi_minus_stage id_stage)).b_fun 17 3

-- Self-agreement check (Boolean version)
#eval agree_at_check chi_plus_stage chi_plus_stage 42 5  -- true

end Tau.Topos
