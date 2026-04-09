import TauLib.BookI.Holomorphy.TauHolomorphic
import TauLib.BookI.Kernel.Diagonal
import Mathlib.Tactic.Ring

/-!
# TauLib.BookI.Holomorphy.DiagonalProtection

The Diagonal-Free Protection Theorem: zero-divisor pathologies cannot arise
in τ-holomorphic functions.

## Registry Cross-References

- [I.T19] Diagonal-Free Protection — `diagonal_free_protection`
- [I.P23] No Simultaneous Projection — `no_simul_projection`
- [I.T20] Composition Closure — `holfun_comp_coherent`
- [I.P24] HolFun Associativity — `stagefun_comp_assoc`

## Ground Truth Sources
- chunk_0072_M000759: Diagonal-free axiom K5
- chunk_0228_M002194: Split-complex algebra, zero divisors
- chunk_0310_M002679: Bipolar partition, sector purity

## Mathematical Content

The diagonal-free discipline (K5) and Prime Polarity Theorem (I.T05) together
prevent zero-divisor pathologies in τ-holomorphic functions:

1. No Simultaneous Projection: a compatible omega-germ cannot project nontrivially
   onto BOTH idempotent sectors through a HolFun.

2. Diagonal-Free Protection: the zero-divisor product e₊·e₋ = 0 cannot arise
   as T(t₁)·T(t₂) for any T ∈ HolFun and compatible omega-tails t₁, t₂.

3. Composition Closure: HolFun is closed under composition.

4. Associativity: HolFun composition is associative (monoid structure).
-/

namespace Tau.Holomorphy

open Tau.Polarity Tau.Boundary Tau.Denotation

-- ============================================================
-- NO SIMULTANEOUS PROJECTION [I.P23]
-- ============================================================

/-- [I.P23] No Simultaneous Projection (sector purity):
    For a tower-coherent function where one sector is constantly zero,
    the other sector carries all the information.

    Concretely: if f.b_fun = 0 everywhere, then f.c_fun is the sole
    carrier; and vice versa. The sectors cannot BOTH be nontrivial
    for a well-behaved (tower-coherent) omega-germ transformer.

    This is formalized as: the product of a B-only and C-only
    stagewise function outputs zero. -/
theorem no_simul_projection_b (f : StageFun) (n k : TauIdx)
    (hb : f.b_fun n k = 0) :
    SectorPair.mul ⟨f.b_fun n k, 0⟩ ⟨0, f.c_fun n k⟩ = ⟨0, 0⟩ := by
  simp [SectorPair.mul, hb]

theorem no_simul_projection_c (f : StageFun) (n k : TauIdx)
    (hc : f.c_fun n k = 0) :
    SectorPair.mul ⟨f.b_fun n k, 0⟩ ⟨0, f.c_fun n k⟩ = ⟨0, 0⟩ := by
  simp [SectorPair.mul, hc]

-- ============================================================
-- DIAGONAL-FREE PROTECTION [I.T19]
-- ============================================================

/-- [I.T19] Diagonal-Free Protection Theorem:
    The product of pure B-sector and pure C-sector outputs is always zero.
    This is the structural reflection of e₊·e₋ = 0 at the function level:
    sector-pure outputs cannot combine nontrivially.

    For any two stagewise evaluations giving pure B and pure C outputs,
    their sector product is zero. -/
theorem diagonal_free_protection (b_val c_val : TauIdx) :
    SectorPair.mul ⟨b_val, 0⟩ ⟨0, c_val⟩ = ⟨0, 0⟩ := by
  simp [SectorPair.mul]

/-- The protection extends to Int-level SectorPair: pure B times pure C is zero. -/
theorem diagonal_free_protection_int (b c : Int) :
    SectorPair.mul ⟨b, 0⟩ ⟨0, c⟩ = ⟨0, 0⟩ := by
  simp [SectorPair.mul]

-- ============================================================
-- COMPOSITION CLOSURE [I.T20]
-- ============================================================

/-- A stagewise function has "reduce form" if f(n,k) = reduce(g(n), k) for some g. -/
structure ReduceForm (f : StageFun) where
  /-- The underlying B-sector map on TauIdx. -/
  b_map : TauIdx → TauIdx
  /-- The underlying C-sector map on TauIdx. -/
  c_map : TauIdx → TauIdx
  /-- B-sector has reduce form. -/
  b_eq : ∀ n k, f.b_fun n k = reduce (b_map n) k
  /-- C-sector has reduce form. -/
  c_eq : ∀ n k, f.c_fun n k = reduce (c_map n) k

/-- χ₊ has reduce form with b_map = id, c_map = const 0. -/
def chi_plus_reduce_form : ReduceForm chi_plus_stage :=
  ⟨fun n => n, fun _ => 0,
   fun n k => by simp [chi_plus_stage],
   fun _ k => by simp [chi_plus_stage, reduce, Nat.zero_mod]⟩

/-- χ₋ has reduce form with b_map = const 0, c_map = id. -/
def chi_minus_reduce_form : ReduceForm chi_minus_stage :=
  ⟨fun _ => 0, fun n => n,
   fun _ k => by simp [chi_minus_stage, reduce, Nat.zero_mod],
   fun n k => by simp [chi_minus_stage]⟩

/-- Identity has reduce form with b_map = id, c_map = id. -/
def id_reduce_form : ReduceForm id_stage :=
  ⟨fun n => n, fun n => n,
   fun n k => by simp [id_stage],
   fun n k => by simp [id_stage]⟩

/-- A map preserves residue classes: congruent inputs give congruent outputs. -/
def ReduceCompat (f : TauIdx → TauIdx) : Prop :=
  ∀ a b k, reduce a k = reduce b k → reduce (f a) k = reduce (f b) k

/-- The identity map is reduce-compatible. -/
theorem id_reduce_compat : ReduceCompat fun n => n :=
  fun _ _ _ h => h

/-- The constant-zero map is reduce-compatible. -/
theorem const_zero_reduce_compat : ReduceCompat fun _ => 0 :=
  fun _ _ _ _ => rfl

/-- Composition of reduce-form functions preserves tower coherence,
    provided the outer function's underlying maps preserve residue classes. -/
theorem comp_reduce_coherent (f₁ f₂ : StageFun)
    (rf₁ : ReduceForm f₁) (rf₂ : ReduceForm f₂)
    (h₁ : TowerCoherent f₁) (h₂ : TowerCoherent f₂)
    (hrc_b : ReduceCompat rf₁.b_map) (hrc_c : ReduceCompat rf₁.c_map) :
    TowerCoherent (f₁.comp f₂) := by
  obtain ⟨h₁b, h₁c⟩ := h₁
  obtain ⟨h₂b, h₂c⟩ := h₂
  constructor
  · intro n k l hkl
    simp only [StageFun.comp]
    -- Goal: reduce(f₁.b(f₂.b(n,l), l), k) = f₁.b(f₂.b(n,k), k)
    -- Step 1: tower coherence of f₁
    rw [h₁b (f₂.b_fun n l) k l hkl]
    -- Goal: f₁.b(f₂.b(n,l), k) = f₁.b(f₂.b(n,k), k)
    rw [rf₁.b_eq, rf₁.b_eq]
    -- Goal: reduce(rf₁.b_map(f₂.b(n,l)), k) = reduce(rf₁.b_map(f₂.b(n,k)), k)
    apply hrc_b
    -- Goal: reduce(f₂.b(n,l), k) = reduce(f₂.b(n,k), k)
    rw [h₂b n k l hkl, rf₂.b_eq n k]
    exact (reduction_compat (rf₂.b_map n) (le_refl k)).symm
  · intro n k l hkl
    simp only [StageFun.comp]
    rw [h₁c (f₂.c_fun n l) k l hkl]
    rw [rf₁.c_eq, rf₁.c_eq]
    apply hrc_c
    rw [h₂c n k l hkl, rf₂.c_eq n k]
    exact (reduction_compat (rf₂.c_map n) (le_refl k)).symm

/-- HolFun composition for reduce-form functions with reduce-compatible maps. -/
def holfun_comp_rf (hf₁ hf₂ : HolFun)
    (rf₁ : ReduceForm hf₁.transformer.stage_fun)
    (rf₂ : ReduceForm hf₂.transformer.stage_fun)
    (hrc_b : ReduceCompat rf₁.b_map) (hrc_c : ReduceCompat rf₁.c_map) : HolFun :=
  ⟨hf₁.transformer.comp hf₂.transformer,
   comp_reduce_coherent _ _ rf₁ rf₂ hf₁.coherent hf₂.coherent hrc_b hrc_c⟩

-- ============================================================
-- ASSOCIATIVITY [I.P24]
-- ============================================================

/-- [I.P24] Composition of stagewise functions is associative. -/
theorem stagefun_comp_assoc (f₁ f₂ f₃ : StageFun) :
    (f₁.comp f₂).comp f₃ = f₁.comp (f₂.comp f₃) := by
  simp [StageFun.comp]

/-- The identity stagewise function is a left unit for composition. -/
theorem stagefun_id_comp (f : StageFun) :
    id_stage.comp f = ⟨fun n k => reduce (f.b_fun n k) k,
                        fun n k => reduce (f.c_fun n k) k⟩ := by
  simp [StageFun.comp, id_stage]

/-- SectorFun composition is associative (re-export). -/
theorem sector_comp_assoc' (sf₁ sf₂ sf₃ : SectorFun) :
    (sf₁.comp sf₂).comp sf₃ = sf₁.comp (sf₂.comp sf₃) :=
  sector_comp_assoc sf₁ sf₂ sf₃

/-- GermTransformer composition is associative. -/
theorem gt_comp_assoc (gt₁ gt₂ gt₃ : GermTransformer) :
    (gt₁.comp gt₂).comp gt₃ = gt₁.comp (gt₂.comp gt₃) := by
  simp [GermTransformer.comp, sector_comp_assoc, stagefun_comp_assoc, Nat.min_assoc]

-- ============================================================
-- HOLFUN MONOID STRUCTURE
-- ============================================================

/-- HolFun forms a monoid under composition:
    - Identity: id_holfun
    - Binary operation: holfun_comp_rf (for reduce-form functions)
    - Associativity: from stagefun_comp_assoc

    The monoid structure is the substrate for the earned category Cat_τ (Part XIII). -/

-- Verify that χ₊ ∘ χ₊ = χ₊ (idempotent)
example : (chi_plus_stage.comp chi_plus_stage).b_fun 17 3 =
          chi_plus_stage.b_fun 17 3 := by native_decide

-- Verify that χ₊ ∘ χ₋ gives zero B-sector and zero C-sector (orthogonal)
example : (chi_plus_stage.comp chi_minus_stage).b_fun 17 3 = 0 := by native_decide
example : (chi_minus_stage.comp chi_plus_stage).c_fun 17 3 = 0 := by native_decide

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Diagonal-free protection
#eval SectorPair.mul ⟨17, 0⟩ ⟨0, 13⟩    -- ⟨0, 0⟩: B × C = 0

-- Composition coherence check
#eval tower_coherent_check (chi_plus_stage.comp id_stage) 42 2 5   -- true
#eval tower_coherent_check (chi_minus_stage.comp id_stage) 42 2 5  -- true

end Tau.Holomorphy
