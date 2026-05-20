import TauLib.BookI.Boundary.TorusDefectSystem

/-!
# TauLib.BookI.Boundary.RefinementGrowingTorus

**Refinement-growing torus instance — Wave 14 successor with
non-trivial geometric refinement.**

A second concrete instance of Wave 12's abstract `DefectInverseSystem`,
demonstrating the scaffold handles a more sophisticated geometric
shape than Wave 14's static 3-element model:

  - **Defect levels GROW with depth**: at depth `n`, the defect
    has `2(n+1) + 1` elements (one crossing anchor + `n+1` B-lobe
    entries + `n+1` C-lobe entries).
  - **Refinement projection** is **non-trivial**: indexes are
    reduced modulo `n+1`.
  - **σ-involution** swaps lobe entries (B↔C) with the same index,
    fixing the crossing anchor.

This is the **second litmus test**: confirms the abstract
`DefectInverseSystem` framework accepts a *type-growing* instance
where the carrier type at each depth changes (not just the
content).  Wave 14 shipped the simplest 3-element constant model;
Wave 19b shows the framework handles richer structural growth.

## Why this matters

Wave 14's `TorusDefect` was the absolute minimum non-trivial test:
3 elements, identity projection.  This Wave 19b instance adds:

1. **Type-level growth**: `defect_level n` has type
   `RefinedTorusDefect n` whose size is `2(n+1) + 1`.  At depth 0:
   3 elements (matches Wave 14).  At depth 1: 5 elements.  At
   depth 2: 7 elements.  Etc.

2. **Non-trivial projection**: the projection
   `defect_level (n+1) → defect_level n` reduces indices modulo
   `n+1` rather than acting as identity.

3. **σ-projection commutativity** is now a *real* theorem (not
   trivial): proves σ commutes with mod-reduction on the indices.

The scaffold's σ-invariance theorem still fires on the unique
σ-fixed thread (`constant crossing`); singleton uniqueness still
holds.  The framework accepts the richer geometry.

## Registry Cross-References

- [I.D125] Tau.Boundary.DefectInverseSystem (Wave 12)
- [I.D127] Tau.Boundary.TorusDefect (Wave 14)
- [I.T75]  Wave 14 sigma_fixed_thread_is_crossing
- [I.T76]  Wave 14 torusSingletonUniqueness
- [I.T-RefTorus-Type]      RefinedTorusDefect (this module)
- [I.T-RefTorus-System]    refinementGrowingTorusSystem
- [I.T-RefTorus-Singleton] refinement uniqueness theorem

## Public API

- `RefinedTorusDefect n` — inductive type with `crossing`,
  `bSide (k : Fin (n+1))`, `cSide (k : Fin (n+1))`.
- `RefinedTorusDefect.sigmaSwap` — B↔C swap, crossing fixed.
- `refinementGrowingTorusSystem : DefectInverseSystem`.
- `refinementCrossingThread` — the unique σ-fixed thread.
- `refinement_singleton_uniqueness` — every crossing-point thread
  is the constant-crossing thread.
- `RefinementIdentity.universal_fixed_unconditional` — Wave 13
  universal-fixed theorem applied to this instance.

## Scope

`\scopetau`, **unconditional at the litmus-test level**, second
data point that the framework accepts varied geometric instances.
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Polarity

-- ============================================================
-- PART 1: The refinement-growing defect type
-- ============================================================

/-- **Refinement-growing defect type** at depth `n`: an inductive
    type with `crossing` (the σ-fixed anchor), `bSide k`
    (B-lobe entry indexed `k : Fin (n+1)`), and `cSide k` (C-lobe
    entry).

    At depth `n`, the type has `2(n+1) + 1` total elements.  The
    cardinality grows linearly in depth, demonstrating the
    framework handles size-growing carrier types. -/
inductive RefinedTorusDefect (n : Nat) where
  | crossing : RefinedTorusDefect n
  | bSide : Fin (n + 1) → RefinedTorusDefect n
  | cSide : Fin (n + 1) → RefinedTorusDefect n
  deriving DecidableEq

-- ============================================================
-- PART 2: σ-involution (B↔C swap, crossing fixed)
-- ============================================================

/-- **σ-swap on RefinedTorusDefect**: swap lobe sides (preserving
    the index), fix crossing anchor. -/
def RefinedTorusDefect.sigmaSwap {n : Nat} :
    RefinedTorusDefect n → RefinedTorusDefect n
  | RefinedTorusDefect.crossing => RefinedTorusDefect.crossing
  | RefinedTorusDefect.bSide k => RefinedTorusDefect.cSide k
  | RefinedTorusDefect.cSide k => RefinedTorusDefect.bSide k

@[simp] theorem RefinedTorusDefect.sigmaSwap_crossing (n : Nat) :
    RefinedTorusDefect.sigmaSwap (RefinedTorusDefect.crossing : RefinedTorusDefect n)
      = RefinedTorusDefect.crossing := rfl

@[simp] theorem RefinedTorusDefect.sigmaSwap_bSide {n : Nat} (k : Fin (n + 1)) :
    RefinedTorusDefect.sigmaSwap (RefinedTorusDefect.bSide k) =
    RefinedTorusDefect.cSide k := rfl

@[simp] theorem RefinedTorusDefect.sigmaSwap_cSide {n : Nat} (k : Fin (n + 1)) :
    RefinedTorusDefect.sigmaSwap (RefinedTorusDefect.cSide k) =
    RefinedTorusDefect.bSide k := rfl

/-- σ is involutive on RefinedTorusDefect. -/
theorem RefinedTorusDefect.sigmaSwap_involutive {n : Nat}
    (x : RefinedTorusDefect n) :
    RefinedTorusDefect.sigmaSwap (RefinedTorusDefect.sigmaSwap x) = x := by
  cases x <;> rfl

/-- **σ-fixed iff crossing** (the singleton uniqueness key fact). -/
theorem RefinedTorusDefect.sigma_fixed_iff_crossing {n : Nat}
    (x : RefinedTorusDefect n) :
    RefinedTorusDefect.sigmaSwap x = x ↔
    x = RefinedTorusDefect.crossing := by
  constructor
  · intro h
    cases x with
    | crossing => rfl
    | bSide k =>
      -- σ(bSide k) = cSide k = bSide k → contradiction
      exact absurd h (by intro heq; cases heq)
    | cSide k =>
      exact absurd h (by intro heq; cases heq)
  · intro h
    subst h
    rfl

-- ============================================================
-- PART 3: Refinement projection (mod-reduction on indices)
-- ============================================================

/-- **Refinement projection** from depth `n+1` to depth `n`.

    On crossing: identity.
    On `bSide ⟨k, hk⟩` at depth `n+1` (so `hk : k < n + 2`): map to
    `bSide ⟨k % (n+1), _⟩` at depth `n`.
    Symmetric for cSide.

    The mod-reduction yields a structurally non-trivial projection
    while preserving the lobe label and σ-equivariance. -/
def RefinedTorusDefect.proj {n : Nat} :
    RefinedTorusDefect (n + 1) → RefinedTorusDefect n
  | RefinedTorusDefect.crossing => RefinedTorusDefect.crossing
  | RefinedTorusDefect.bSide ⟨k, _⟩ =>
    RefinedTorusDefect.bSide ⟨k % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩
  | RefinedTorusDefect.cSide ⟨k, _⟩ =>
    RefinedTorusDefect.cSide ⟨k % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩

/-- **σ commutes with projection** (the key structural property
    for inverse-system compatibility). -/
theorem RefinedTorusDefect.proj_commutes_sigma {n : Nat}
    (x : RefinedTorusDefect (n + 1)) :
    RefinedTorusDefect.proj (RefinedTorusDefect.sigmaSwap x) =
    RefinedTorusDefect.sigmaSwap (RefinedTorusDefect.proj x) := by
  cases x with
  | crossing => rfl
  | bSide k => rfl
  | cSide k => rfl

-- ============================================================
-- PART 4: DefectInverseSystem instance
-- ============================================================

/-- **The refinement-growing torus DefectInverseSystem**.

    Defect levels grow with depth (size = 2(n+1) + 1).  Projections
    reduce indices mod `n+1`.  σ swaps lobe sides, fixes crossing.
    All compatibility, involutivity, and commutation conditions hold
    by direct case analysis. -/
def refinementGrowingTorusSystem : DefectInverseSystem where
  defect_level := RefinedTorusDefect
  proj := fun _ => RefinedTorusDefect.proj
  sigma_level := fun _ => RefinedTorusDefect.sigmaSwap
  sigma_involutive := fun _ => RefinedTorusDefect.sigmaSwap_involutive
  sigma_commutes_proj := fun _ x => by
    show RefinedTorusDefect.proj (RefinedTorusDefect.sigmaSwap x) = _
    rw [RefinedTorusDefect.proj_commutes_sigma]

-- ============================================================
-- PART 5: The unique σ-fixed thread (constant crossing)
-- ============================================================

/-- **The crossing-anchored thread** in the refinement-growing
    torus system: constantly `crossing` at every depth. -/
def refinementCrossingThread :
    DefectInverseSystem.SigmaFixedThread refinementGrowingTorusSystem where
  point := fun _ => RefinedTorusDefect.crossing
  compat := fun _ => rfl
  sigma_fixed := fun _ => rfl

-- ============================================================
-- PART 6: Singleton uniqueness — every σ-fixed thread = crossing
-- ============================================================

/-- **σ-fixed thread is pointwise crossing** (analogue of Wave 14
    `sigma_fixed_thread_pointwise_crossing`).

    Because σ-fixedness on `RefinedTorusDefect n` forces every point
    to be `crossing` (by `sigma_fixed_iff_crossing`), every σ-fixed
    thread is constantly `crossing`. -/
theorem refinement_sigma_fixed_thread_pointwise_crossing
    (t : DefectInverseSystem.SigmaFixedThread refinementGrowingTorusSystem)
    (n : Nat) :
    t.point n = RefinedTorusDefect.crossing := by
  have h_sigma := t.sigma_fixed n
  show t.point n = _
  exact (RefinedTorusDefect.sigma_fixed_iff_crossing (t.point n)).mp h_sigma

/-- **Every σ-fixed thread is the crossing thread**. -/
theorem refinement_sigma_fixed_thread_is_crossing
    (t : DefectInverseSystem.SigmaFixedThread refinementGrowingTorusSystem) :
    t = refinementCrossingThread := by
  apply DefectInverseSystem.SigmaFixedThread.ext
  intro n
  rw [refinement_sigma_fixed_thread_pointwise_crossing t n]
  rfl

-- ============================================================
-- PART 7: Crossing-point predicates with concrete anchor / mwd
-- ============================================================

/-- **Anchor predicate** on the refinement-growing torus: a point
    is "anchored" iff it is the `crossing` constructor. -/
def refinementAnchor : ∀ n, refinementGrowingTorusSystem.defect_level n → Prop :=
  fun _ x => x = RefinedTorusDefect.crossing

/-- **Trivial mwd function**. -/
def refinementMwd :
    DefectInverseSystem.SigmaFixedThread refinementGrowingTorusSystem → Nat :=
  fun _ => 0

/-- **Singleton uniqueness on the refinement-growing torus**
    (Wave 13 hypothesis discharged unconditionally — second
    instance after Wave 14's `torusSingletonUniqueness`). -/
theorem refinement_singleton_uniqueness
    (t₁ t₂ : DefectInverseSystem.SigmaFixedThread refinementGrowingTorusSystem)
    (_h₁ : DefectInverseSystem.IsCrossingPoint refinementAnchor refinementMwd t₁)
    (_h₂ : DefectInverseSystem.IsCrossingPoint refinementAnchor refinementMwd t₂) :
    t₁ = t₂ := by
  rw [refinement_sigma_fixed_thread_is_crossing t₁,
      refinement_sigma_fixed_thread_is_crossing t₂]

/-- The crossing thread satisfies `IsCrossingPoint`. -/
theorem refinementCrossingThread_is_crossingPoint :
    DefectInverseSystem.IsCrossingPoint refinementAnchor refinementMwd
      refinementCrossingThread := by
  refine ⟨?_, ?_⟩
  · -- IsNonPolar
    exact ⟨0, fun _ _ => rfl⟩
  · -- IsOmegaApproaching
    exact ⟨0, Nat.le_refl 0⟩

-- ============================================================
-- PART 8: Identity HolEnd applied unconditionally (Wave 13 → uncond.)
-- ============================================================

/-- **Identity HolEnd morphism** on the refinement-growing torus. -/
def RefinementIdentity : HolEndMorphism refinementGrowingTorusSystem where
  act := fun t => t
  preserves_sigma_fixed := fun _ h => h

/-- **Identity full HolEnd morphism** with NP/OA preservation. -/
def RefinementIdentityFull :
    HolEndMorphismFull refinementGrowingTorusSystem
      refinementAnchor refinementMwd where
  toHolEndMorphism := RefinementIdentity
  preserves_NP := fun _ h => by
    show DefectInverseSystem.IsNonPolar refinementAnchor _; exact h
  preserves_OA := fun _ h => by
    show DefectInverseSystem.IsOmegaApproaching refinementMwd _; exact h

/-- **Wave 13 universal_fixed_theorem applied unconditionally**
    on the refinement-growing torus.  Second instance demonstrating
    the Wave 13 → Wave 14 → Wave 19b pattern: each new concrete
    instance discharges the singleton hypothesis from its own
    structural facts. -/
theorem RefinementIdentity.universal_fixed_unconditional
    (g : DefectInverseSystem.SigmaFixedThread refinementGrowingTorusSystem)
    (h_g : DefectInverseSystem.IsCrossingPoint refinementAnchor refinementMwd g) :
    RefinementIdentityFull.toHolEndMorphism.actSigmaFixed g = g :=
  RefinementIdentityFull.universal_fixed_theorem g h_g
    refinement_singleton_uniqueness

/-- **Specialisation to the crossing thread** — identity fixes
    the crossing thread unconditionally, no hypotheses. -/
theorem RefinementIdentity.fixes_crossing_thread :
    RefinementIdentityFull.toHolEndMorphism.actSigmaFixed
      refinementCrossingThread =
    refinementCrossingThread :=
  RefinementIdentity.universal_fixed_unconditional
    refinementCrossingThread refinementCrossingThread_is_crossingPoint

-- ============================================================
-- PART 9: §4.4 Theorem 4.7 unpolarisation — refinement witness
-- ============================================================

/-- **Refinement projection is surjective** — every depth-`n`
    element has a depth-`(n+1)` preimage under the mod-reduction
    projection.

    Proof: a depth-`n` element `bSide ⟨k, h_k⟩` with `k < n + 1`
    has preimage `bSide ⟨k, h_k'⟩` at depth `n + 1` (where
    `h_k' : k < n + 2` weakens `h_k`).  Then
    `k % (n + 1) = k` (since `k < n + 1`), so the projection
    is the original element.  Symmetric for cSide; crossing
    maps to crossing. -/
theorem RefinedTorusDefect.proj_surjective {n : Nat}
    (y : RefinedTorusDefect n) :
    ∃ x : RefinedTorusDefect (n + 1), RefinedTorusDefect.proj x = y := by
  cases y with
  | crossing => exact ⟨RefinedTorusDefect.crossing, rfl⟩
  | bSide k =>
    refine ⟨RefinedTorusDefect.bSide ⟨k.1, Nat.lt_succ_of_lt k.2⟩, ?_⟩
    show RefinedTorusDefect.bSide _ = RefinedTorusDefect.bSide _
    congr 1
    apply Fin.ext
    show k.1 % (n + 1) = k.1
    exact Nat.mod_eq_of_lt k.2
  | cSide k =>
    refine ⟨RefinedTorusDefect.cSide ⟨k.1, Nat.lt_succ_of_lt k.2⟩, ?_⟩
    show RefinedTorusDefect.cSide _ = RefinedTorusDefect.cSide _
    congr 1
    apply Fin.ext
    show k.1 % (n + 1) = k.1
    exact Nat.mod_eq_of_lt k.2

/-- **`refinementGrowingTorusSystem`'s projection is surjective**. -/
theorem refinementGrowingTorusSystem_projSurjective :
    refinementGrowingTorusSystem.ProjSurjective :=
  fun _ => RefinedTorusDefect.proj_surjective

/-- **`refinementGrowingTorusSystem` is unpolarised**: at every
    depth `n`, the `bSide ⟨0, _⟩` element is not σ-fixed (its
    σ-image is `cSide ⟨0, _⟩`).

    Concretely discharges `DefectInverseSystem.IsUnpolarised` on
    the refinement-growing instance with non-trivial geometric
    growth.  Paper §4.4 Theorem 4.7 backing: even with growing
    defect-level cardinality and non-trivial mod-reduction
    projection, the non-polarisation witness is preserved. -/
theorem refinementGrowingTorusSystem_isUnpolarised :
    refinementGrowingTorusSystem.IsUnpolarised := by
  intro n
  refine ⟨RefinedTorusDefect.bSide ⟨0, Nat.succ_pos n⟩, ?_⟩
  -- σ-image of `bSide ⟨0, _⟩` is `cSide ⟨0, _⟩`, distinct
  -- constructor from `bSide`.
  intro h
  have h' : RefinedTorusDefect.sigmaSwap
              (RefinedTorusDefect.bSide ⟨0, Nat.succ_pos n⟩) =
            RefinedTorusDefect.bSide ⟨0, Nat.succ_pos n⟩ := h
  rw [RefinedTorusDefect.sigmaSwap_bSide] at h'
  cases h'

/-- **The constant-`bSide ⟨0, _⟩` unpolarised thread**: a coherent
    thread in the refinement-growing torus with non-σ-fixed
    `bSide ⟨0, _⟩` at every depth.

    Refinement compatibility: at depth `n + 1`, the index `0`
    reduces to `0 % (n + 1) = 0` at depth `n`, so the projection
    is `bSide ⟨0, _⟩` at depth `n` — same element, same lobe.
    Coherent. -/
def refinementBSideConstantThread :
    DefectInverseSystem.UnpolarisedThread refinementGrowingTorusSystem where
  point := fun n => RefinedTorusDefect.bSide ⟨0, Nat.succ_pos n⟩
  compat := fun n => by
    -- `proj (bSide ⟨0, _⟩)` reduces to `bSide ⟨0 % (n+1), _⟩`
    -- = `bSide ⟨0, _⟩` since `0 % k = 0`.
    show RefinedTorusDefect.bSide _ = RefinedTorusDefect.bSide _
    congr 1
  not_sigma_fixed := fun n h => by
    have h' : RefinedTorusDefect.sigmaSwap
                (RefinedTorusDefect.bSide ⟨0, Nat.succ_pos n⟩) =
              RefinedTorusDefect.bSide ⟨0, Nat.succ_pos n⟩ := h
    rw [RefinedTorusDefect.sigmaSwap_bSide] at h'
    cases h'

/-- **Theorem 4.7 applied to `refinementGrowingTorusSystem`**:
    both halves of `unpolarisation_theorem` hold unconditionally
    on this geometric-growth instance.

    Concretely:
    1. `IsUnpolarised`: `bSide ⟨0, _⟩` witnesses non-σ-fixedness
       at every depth.
    2. The `refinementBSideConstantThread` is a coherent
       inverse-limit configuration with non-σ-fixed content at
       every depth, surviving the mod-reduction projection.

    Second concrete instance discharging Theorem 4.7 abstractly
    (after `TorusDefectSystem.theorem_4_7_unconditional`),
    confirming the scaffold handles geometric growth. -/
theorem refinementGrowingTorusSystem_theorem_4_7_unconditional :
    refinementGrowingTorusSystem.IsUnpolarised ∧
    (∀ n, refinementGrowingTorusSystem.sigma_level n
            (refinementBSideConstantThread.point n) ≠
          refinementBSideConstantThread.point n) :=
  DefectInverseSystem.unpolarisation_theorem
    refinementGrowingTorusSystem refinementBSideConstantThread

end Tau.Boundary
