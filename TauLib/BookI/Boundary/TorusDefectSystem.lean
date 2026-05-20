import TauLib.BookI.Boundary.UniversalFixedScalar

/-!
# TauLib.BookI.Boundary.TorusDefectSystem

**Concrete torus instantiation of `DefectInverseSystem` — the
structural litmus test for the H3 scaffold.**

A minimal non-trivial concrete instance of Wave 12's abstract
`DefectInverseSystem` framework, realising paper §4's
"defect = torus minus realised relation" structure at its
simplest non-trivial form:

  - **Torus defect type**: `Option (Fin 2)` — two lobe sides plus a
    distinguished **crossing anchor** `none`.
  - **σ-involution**: swap the two lobe sides, fix the crossing.
  - **Realisation**: the crossing anchor is the unique σ-fixed
    element; lobe sides pair-swap under σ.

This minimal model captures the paper's **key topological feature**
(the σ-fixed defect element is exactly the crossing anchor) without
the full geometric content (refinement growth, cylinder threads,
lobe-lattice).  It is the simplest concrete instance on which the
entire Wave 12/13 abstract scaffold applies, and on which the
**singleton uniqueness** hypothesis from Wave 13's
`universal_fixed_theorem` is **provable unconditionally**.

## Why this is the litmus test

Wave 12's `DefectInverseSystem` and Wave 13's
`universal_fixed_theorem` were both stated in **abstract** form,
parameterised over the geometric content.  The natural question:
does the scaffold actually accept a concrete instance, and do its
conditional theorems become unconditional on that instance?

This module answers **yes**:

1. `TorusDefectSystem` instantiates `DefectInverseSystem`.
2. `torusSingletonUniqueness` **proves** singleton uniqueness on
   this instance (discharging Wave 13's hypothesis).
3. `TorusIdentity.universal_fixed_unconditional` applies Wave 13's
   `universal_fixed_theorem` with the discharged hypothesis, yielding
   an **unconditional** fixed-point theorem on the concrete instance.

The scaffold works.  Future waves with richer geometric instances
(refinement-growing torus, concrete lobe-lattice) will follow the
same pattern.

## Registry Cross-References

- [I.D125] Tau.Boundary.DefectInverseSystem (Wave 12)
- [I.D126] Tau.Boundary.HolEndMorphism (Wave 13)
- [I.T72]  fixed_point_inheritance (Wave 13)
- [I.T73]  universal_fixed_theorem (Wave 13 conditional)
- [I.T-H3-TorusInstance] TorusDefectSystem (this module)
- [I.T-H3-TorusUniqueness] torusSingletonUniqueness (litmus test)
- [I.T-H3-TorusUniversal] universal_fixed_unconditional

## Mathematical Content

**Paper §4 concrete minimal rendering**:

  - Torus `T = {B-side, C-side, crossing}` = `Option (Fin 2)`
  - Realised relation: `R = {B-side paired with C-side}` — implicit,
    because we represent the defect `Δ = T \ R` directly as the
    `Option (Fin 2)` carrier
  - σ: swap B ↔ C, fix crossing — paper's `σ_n` on the torus
  - Projection: identity (static instance) — simplest compatible
    inverse-system shape

**σ-fixed points of TorusDefect**: the crossing `none` is the
**unique** σ-fixed element.  Proof: direct 3-case analysis on
`Option (Fin 2)`.

**σ-fixed threads**: by pointwise σ-fixedness and uniqueness of the
σ-fixed defect element, every σ-fixed thread is the constant-`none`
thread.  This gives **unconditional** singleton uniqueness on this
instance.

**Paper Thm 5.7 at the concrete level**: since the identity
endomorphism is a HolEnd morphism and the crossing thread is the
unique crossing-point, the identity fixes the crossing thread —
which is both definitionally true and a **specific instance of the
Wave 13 universal_fixed_theorem applied with discharged hypothesis**.

## Public API

- `TorusDefect` — the concrete defect type `Option (Fin 2)`.
- `TorusDefect.sigmaSwap` — σ-involution: swap lobe sides, fix
  crossing.
- `TorusDefectSystem` — the concrete `DefectInverseSystem` instance.
- `TorusDefectSystem.crossingThread` — the σ-fixed constant-`none`
  thread.
- `TorusDefect.sigma_fixed_iff_none` — key characterisation of
  σ-fixed defect elements.
- `torusSigmaFixedThread_is_crossing` — every σ-fixed thread in
  `TorusDefectSystem` is `crossingThread`.
- `torusSingletonUniqueness` — two crossing-point threads are
  equal (the Wave 13 hypothesis, **proved** unconditionally here).
- `TorusIdentity` / `TorusIdentityFull` — identity HolEnd
  endomorphism (Wave 13 instance with discharged hypotheses).
- `TorusIdentity.universal_fixed_unconditional` — Wave 13 Thm 5.7
  applied to the concrete instance, fully unconditional.
- `TorusIdentity.universal_fixed_scalar_unconditional` — scalar
  form, fully unconditional.

## Scope

`\scopetau`, **unconditional at the litmus-test level**.  Richer
geometric instances with refinement-growing torus are deferred
to future waves; this module verifies the framework accepts a
concrete instance and that its conditional theorems become
unconditional once the discharged-hypothesis pattern is in place.
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation Tau.Polarity

-- ============================================================
-- PART 1: The concrete TorusDefect type
-- ============================================================

/-- **Concrete defect type** at each depth: three constructors
    encoding the two lobe sides plus the crossing anchor.

    - `bSide` = B-lobe side (paper's off-diagonal `b ∈ B_n`)
    - `cSide` = C-lobe side (paper's off-diagonal `c ∈ C_n`)
    - `crossing` = the crossing anchor (paper's `×`-labelled class)

    This is the **minimal non-trivial** off-diagonal defect carrier.
    The singleton `crossing` is σ-fixed; `bSide` and `cSide` swap
    under σ.

    A custom inductive type (rather than `Option (Fin 2)`) avoids
    `Fin`-destructuring pitfalls in subsequent proofs — a
    calibration lesson from the "three-iteration tactics-dance"
    playbook. -/
inductive TorusDefect where
  | bSide   : TorusDefect
  | cSide   : TorusDefect
  | crossing : TorusDefect
  deriving DecidableEq, Repr

/-- **σ-involution on TorusDefect**: swap lobe sides, fix crossing.

    Realises paper §4's `σ_n : T_n → T_n` as the
    B↔C lobe exchange with the crossing as the unique fixed
    element. -/
def TorusDefect.sigmaSwap : TorusDefect → TorusDefect
  | bSide => cSide
  | cSide => bSide
  | crossing => crossing

@[simp] theorem TorusDefect.sigmaSwap_bSide :
    TorusDefect.sigmaSwap TorusDefect.bSide = TorusDefect.cSide := rfl

@[simp] theorem TorusDefect.sigmaSwap_cSide :
    TorusDefect.sigmaSwap TorusDefect.cSide = TorusDefect.bSide := rfl

@[simp] theorem TorusDefect.sigmaSwap_crossing :
    TorusDefect.sigmaSwap TorusDefect.crossing = TorusDefect.crossing := rfl

/-- **σ is involutive on TorusDefect**: `σ² = id`. -/
theorem TorusDefect.sigmaSwap_involutive (x : TorusDefect) :
    TorusDefect.sigmaSwap (TorusDefect.sigmaSwap x) = x := by
  cases x <;> rfl

/-- **Characterisation of σ-fixed TorusDefect elements**: `x` is
    σ-fixed **iff** `x = crossing`.

    This is the structural content that the crossing anchor is the
    unique σ-fixed defect element — paper's §5.1 "unique σ-fixed
    boundary locus" realised on this minimal concrete instance. -/
theorem TorusDefect.sigma_fixed_iff_crossing (x : TorusDefect) :
    TorusDefect.sigmaSwap x = x ↔ x = TorusDefect.crossing := by
  cases x <;> simp [TorusDefect.sigmaSwap]

-- ============================================================
-- PART 2: TorusDefectSystem instance
-- ============================================================

/-- **Concrete `DefectInverseSystem`** built from `TorusDefect`.

    - `defect_level n = TorusDefect` at every depth (static instance)
    - `proj = id` (simplest compatible projection)
    - `sigma_level = TorusDefect.sigmaSwap` at every depth
    - `sigma_involutive` and `sigma_commutes_proj` both hold trivially. -/
def TorusDefectSystem : DefectInverseSystem where
  defect_level := fun _ => TorusDefect
  proj := fun _ x => x
  sigma_level := fun _ => TorusDefect.sigmaSwap
  sigma_involutive := fun _ => TorusDefect.sigmaSwap_involutive
  sigma_commutes_proj := fun _ _ => rfl

-- ============================================================
-- PART 3: The crossing-anchored σ-fixed thread
-- ============================================================

/-- **The crossing-anchored thread**: constant `crossing` at every depth.

    This is the Lean realisation of paper's `G_×[ω]` — the unique
    σ-fixed non-polar ω-germ — on this concrete instance. -/
def TorusDefectSystem.crossingThread :
    DefectInverseSystem.SigmaFixedThread TorusDefectSystem where
  point := fun _ => TorusDefect.crossing
  compat := fun _ => rfl
  sigma_fixed := fun _ => rfl

-- ============================================================
-- PART 4: The litmus test — singleton uniqueness (unconditional)
-- ============================================================

/-- **Every σ-fixed thread on `TorusDefectSystem` is the crossing
    thread (pointwise).**

    Because σ-fixedness on `TorusDefect` forces `point n = crossing`
    at every depth (by `sigma_fixed_iff_crossing`), every σ-fixed
    thread's `point` function is constantly `crossing`. -/
theorem TorusDefectSystem.sigma_fixed_thread_pointwise_crossing
    (t : DefectInverseSystem.SigmaFixedThread TorusDefectSystem) (n : Nat) :
    t.point n = TorusDefect.crossing := by
  have h_sigma := t.sigma_fixed n
  have h_iff := TorusDefect.sigma_fixed_iff_crossing (t.point n)
  exact h_iff.mp h_sigma

/-- **Structural extensionality for `SigmaFixedThread`**: two
    σ-fixed threads with pointwise-equal `point` functions are
    equal.

    Proof: destructure both threads, use `funext` on the `point`
    field, and appeal to proof irrelevance of the Prop-valued
    fields. -/
theorem DefectInverseSystem.SigmaFixedThread.ext
    {D : DefectInverseSystem}
    (t₁ t₂ : DefectInverseSystem.SigmaFixedThread D)
    (h : ∀ n, t₁.point n = t₂.point n) : t₁ = t₂ := by
  obtain ⟨⟨p₁, c₁⟩, sf₁⟩ := t₁
  obtain ⟨⟨p₂, c₂⟩, sf₂⟩ := t₂
  have hp : p₁ = p₂ := funext h
  subst hp
  rfl

/-- **Uniqueness of the σ-fixed thread on `TorusDefectSystem`**:
    every σ-fixed thread is the crossing thread.

    Combines `sigma_fixed_thread_pointwise_crossing` (every σ-fixed
    thread is pointwise `crossing`) with `SigmaFixedThread.ext`
    (pointwise equality ⇒ equality). -/
theorem TorusDefectSystem.sigma_fixed_thread_is_crossing
    (t : DefectInverseSystem.SigmaFixedThread TorusDefectSystem) :
    t = TorusDefectSystem.crossingThread := by
  apply DefectInverseSystem.SigmaFixedThread.ext
  intro n
  rw [TorusDefectSystem.sigma_fixed_thread_pointwise_crossing t n]
  rfl

-- ============================================================
-- PART 5: IsCrossingPoint parameters and singleton_uniqueness
-- ============================================================

/-- **Anchor predicate** on `TorusDefectSystem`: a point is
    "anchored" iff it is the `crossing` constructor. -/
def torusAnchor : ∀ n, TorusDefectSystem.defect_level n → Prop :=
  fun _ x => x = TorusDefect.crossing

/-- **Trivial mwd function**: every thread has maturity depth 0.
    On `TorusDefectSystem` this is appropriate because the unique
    σ-fixed thread is already crossing-anchored at depth 0 (indeed
    at every depth). -/
def torusMwd :
    DefectInverseSystem.SigmaFixedThread TorusDefectSystem → Nat :=
  fun _ => 0

/-- **Singleton uniqueness, the Wave 13 hypothesis discharged
    unconditionally.**

    On `TorusDefectSystem`, any two crossing-point threads are
    equal — because σ-fixedness alone (without the crossing-point
    condition) already forces equality with `crossingThread`. -/
theorem torusSingletonUniqueness
    (t₁ t₂ : DefectInverseSystem.SigmaFixedThread TorusDefectSystem)
    (_h₁ : DefectInverseSystem.IsCrossingPoint torusAnchor torusMwd t₁)
    (_h₂ : DefectInverseSystem.IsCrossingPoint torusAnchor torusMwd t₂) :
    t₁ = t₂ := by
  rw [TorusDefectSystem.sigma_fixed_thread_is_crossing t₁,
      TorusDefectSystem.sigma_fixed_thread_is_crossing t₂]

/-- **The crossing thread is a crossing-point** (IsCrossingPoint
    predicate holds for it):
    - IsNonPolar: the constant-`none` thread is at the anchor from
      depth 0.
    - IsOmegaApproaching: mwd is 0 which is ≤ any bound.  -/
theorem TorusDefectSystem.crossingThread_is_crossingPoint :
    DefectInverseSystem.IsCrossingPoint torusAnchor torusMwd
      TorusDefectSystem.crossingThread := by
  refine ⟨?_, ?_⟩
  · -- IsNonPolar: ∃ maturity_depth, ∀ n ≥ maturity_depth, anchor n (point n)
    exact ⟨0, fun _ _ => rfl⟩
  · -- IsOmegaApproaching: ∃ bound, mwd t ≤ bound
    exact ⟨0, Nat.le_refl 0⟩

-- ============================================================
-- PART 6: HolEndMorphism on the concrete instance
-- ============================================================

/-- **Identity HolEnd morphism** on `TorusDefectSystem`.  The
    simplest endomorphism: acts as the identity on threads. -/
def TorusIdentity : HolEndMorphism TorusDefectSystem where
  act := fun t => t
  preserves_sigma_fixed := fun _ h => h

/-- **Identity full HolEnd morphism** with NP / OA preservation.
    The identity trivially preserves both halves. -/
def TorusIdentityFull :
    HolEndMorphismFull TorusDefectSystem torusAnchor torusMwd where
  toHolEndMorphism := TorusIdentity
  preserves_NP := fun _ h => by
    -- Identity acts as identity on SigmaFixedThread, so NP is preserved
    show DefectInverseSystem.IsNonPolar torusAnchor _
    exact h
  preserves_OA := fun _ h => by
    show DefectInverseSystem.IsOmegaApproaching torusMwd _
    exact h

-- ============================================================
-- PART 7: Unconditional application of universal_fixed_theorem
-- ============================================================

/-- **Wave 13 universal_fixed_theorem applied unconditionally** on
    `TorusDefectSystem`.

    The conditional Wave 13 theorem required the
    `singleton_uniqueness` hypothesis; on this concrete instance we
    discharged that hypothesis via `torusSingletonUniqueness`
    (which exploits the concrete fact that `TorusDefect`'s σ-fixed
    points are exactly `{none}`).

    Plugging in, the Wave 13 theorem becomes an **unconditional
    structural result** on this instance: the identity HolEnd
    morphism fixes the (unique) crossing-point thread. -/
theorem TorusIdentity.universal_fixed_unconditional
    (g : DefectInverseSystem.SigmaFixedThread TorusDefectSystem)
    (h_g : DefectInverseSystem.IsCrossingPoint torusAnchor torusMwd g) :
    TorusIdentityFull.toHolEndMorphism.actSigmaFixed g = g :=
  TorusIdentityFull.universal_fixed_theorem g h_g torusSingletonUniqueness

/-- **Wave 13 universal_fixed_scalar applied unconditionally** on
    `TorusDefectSystem`.  The scalar-readout form of the
    universal-fixed theorem, with singleton_uniqueness discharged. -/
theorem TorusIdentity.universal_fixed_scalar_unconditional
    (g : DefectInverseSystem.SigmaFixedThread TorusDefectSystem)
    (h_g : DefectInverseSystem.IsCrossingPoint torusAnchor torusMwd g)
    (readout_level : ∀ n, TorusDefectSystem.defect_level n → TauRat) :
    TorusDefectSystem.threadReadoutTauReal readout_level
      (TorusIdentityFull.toHolEndMorphism.actSigmaFixed g).toThread =
    TorusDefectSystem.threadReadoutTauReal readout_level g.toThread :=
  TorusIdentityFull.universal_fixed_scalar g h_g torusSingletonUniqueness
    readout_level

/-- **Specialisation to the concrete crossing thread**: the identity
    fixes the crossing thread unconditionally and **computationally**
    (no hypotheses at all).

    This is the sharpest form of the litmus test: the entire Wave 12
    + Wave 13 structural scaffold applied to a specific concrete
    thread with no external dependencies. -/
theorem TorusIdentity.fixes_crossing_thread :
    TorusIdentityFull.toHolEndMorphism.actSigmaFixed
      TorusDefectSystem.crossingThread =
    TorusDefectSystem.crossingThread :=
  TorusIdentity.universal_fixed_unconditional
    TorusDefectSystem.crossingThread
    TorusDefectSystem.crossingThread_is_crossingPoint

-- ============================================================
-- PART 8: §4.4 Theorem 4.7 unpolarisation — concrete witness
-- ============================================================

/-- **`TorusDefectSystem` is unpolarised**: at every depth, the
    `bSide` element is not σ-fixed (its σ-image is `cSide`).

    This concretely discharges the abstract
    `DefectInverseSystem.IsUnpolarised` predicate on this
    instance, no hypotheses needed.

    Paper §4.4 Theorem 4.7 backing: the "(b, c) with both
    channels non-trivial" content is rendered by exhibiting
    `bSide` (a B-only element with no σ-symmetric partner) at
    every depth — equivalently, the non-σ-fixed witness that
    defines `IsUnpolarised`. -/
theorem TorusDefectSystem.isUnpolarised :
    TorusDefectSystem.IsUnpolarised :=
  fun _ => ⟨TorusDefect.bSide, by simp [TorusDefectSystem]⟩

/-- **`TorusDefectSystem`'s projection is surjective** — paper's
    "projections are surjective" hypothesis discharged.

    Because `proj = id` on this instance, surjectivity is
    immediate. -/
theorem TorusDefectSystem.projSurjective :
    TorusDefectSystem.ProjSurjective :=
  fun _ y => ⟨y, rfl⟩

/-- **The constant-`bSide` unpolarised thread**: a concrete thread
    in `TorusDefectSystem` whose every depth carries the
    non-σ-fixed `bSide` element.

    This is the paper §4.4 inverse-limit witness on this
    concrete instance: a coherent thread in the defect inverse
    system that *fails* σ-symmetry at every depth.

    Compare with `crossingThread` (the σ-fixed witness): both
    are coherent threads in `TorusDefectSystem`, but
    `bSideConstantThread` witnesses unpolarisation while
    `crossingThread` witnesses σ-fixedness. -/
def TorusDefectSystem.bSideConstantThread :
    DefectInverseSystem.UnpolarisedThread TorusDefectSystem where
  point := fun _ => TorusDefect.bSide
  compat := fun _ => rfl
  not_sigma_fixed := fun _ => by simp [TorusDefectSystem]

/-- **Theorem 4.7 applied to `TorusDefectSystem`**: both halves
    of `unpolarisation_theorem` hold unconditionally on this
    concrete instance.

    Concretely:
    1. `IsUnpolarised`: `TorusDefect.bSide` witnesses non-σ-fixedness
       at every depth.
    2. The `bSideConstantThread` is a coherent inverse-limit
       configuration with non-σ-fixed content at every depth.

    This is the litmus test that the abstract Theorem 4.7
    scaffold applies on a concrete instance, fully discharged. -/
theorem TorusDefectSystem.theorem_4_7_unconditional :
    TorusDefectSystem.IsUnpolarised ∧
    (∀ n, TorusDefectSystem.sigma_level n
            (TorusDefectSystem.bSideConstantThread.point n) ≠
          TorusDefectSystem.bSideConstantThread.point n) :=
  DefectInverseSystem.unpolarisation_theorem
    TorusDefectSystem TorusDefectSystem.bSideConstantThread

end Tau.Boundary
