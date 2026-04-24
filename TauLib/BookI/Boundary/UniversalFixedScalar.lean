import TauLib.BookI.Boundary.DefectInverseSystem

/-!
# TauLib.BookI.Boundary.UniversalFixedScalar

**Deep Hinge 3 §5.6 — Fixed-point inheritance and the universal
fixed scalar.**

Lean structural rendering of paper `iota-tau/main.tex` §5.6:
the crossing-point germ `G_×[ω]` is a **universal fixed object**
under `HolEnd_τ(ω)`, and consequently its scalar readout
`ι_τ := Read_F(G_×[ω])` is the **universal fixed scalar** — invariant
under every holomorphic endomorphism of the ω-boundary.

Built on Wave 12's `DefectInverseSystem` scaffold.

## Registry Cross-References

- [I.D120] Tau.Boundary.TauReal.iota_tau (Wave 4 operational)
- [I.D121] Tau.Boundary.CrossingPointDefectGerm (Wave 7 scaffold)
- [I.D125] Tau.Boundary.DefectInverseSystem (Wave 12 abstract)
- [I.T69]  DefectInverseSystem.sigma_invariance (Wave 12)
- [I.T71]  DefectInverseSystem.intersection_iff (Wave 12)
- [I.T-H3-HolEnd] HolEndMorphism (this module)
- [I.T-H3-FixedInheritance] fixed_point_inheritance (paper Prop 5.6)
- [I.T-H3-UniversalFixed] universal_fixed_theorem (paper Thm 5.7)
- [I.T-H3-IotaUniversal] iota_tau_universal_fixed (paper Cor 5.8)

## Mathematical Content

**Paper §5.6 trilogy** (paper file
`papers/iota-tau/main.tex` lines 1545–1595):

- **Proposition 5.6** (`prop:fixed-inheritance`):
  If `f ∈ HolEnd_τ(ω)` and `G` is σ-fixed, then `f(G)` is σ-fixed.
  Proof: `σ(f(G)) = f(σ(G)) = f(G)` by σ-equivariance of `f`.

- **Theorem 5.7** (`thm:universal-fixed`):
  For every `f ∈ HolEnd_τ(ω)`, `f(G_×[ω]) = G_×[ω]`.
  Proof: By Prop 5.6, `f(G_×[ω])` is σ-fixed.  Since `f` preserves
  refinement threads (and hence polarisation status + ω-approach),
  `f(G_×[ω])` remains unpolarised and ω-approaching.  By the
  intersection theorem (paper Thm 5.5), `f(G_×[ω]) = G_×[ω]`.

- **Corollary 5.8** (`cor:iota-universal`):
  For every `f ∈ HolEnd_τ(ω)`, the scalar `ι_τ := Read_F(G_×[ω])`
  is fixed by the induced action of `f` on `Read_F(H_τ(ω))`.
  Proof: Immediate from Theorem 5.7 by applying `Read_F`.

## Rendering strategy

The paper's `HolEnd_τ(ω)` is the class of **σ-equivariant
holomorphic endomorphisms of the ω-boundary**.  The structural
content we capture:

1. A `HolEndMorphism D` type packaging an action on threads in a
   `DefectInverseSystem`, with σ-equivariance built in as a
   preservation property.
2. Preservation of `IsNonPolar` and `IsOmegaApproaching` — the
   `f preserves polarisation status + ω-approach` content of the
   paper proof.
3. `fixed_point_inheritance` as an **unconditional** theorem
   (Prop 5.6).
4. `preserves_crossingPoint` as an **unconditional** theorem: if
   `t` is a crossing-point, so is `f(t)`.
5. `universal_fixed_theorem` in **conditional form**: given the
   singleton uniqueness of `NP ∩ OA` as a hypothesis (a future
   wave deliverable), every HolEnd_τ morphism fixes any
   crossing-point thread.
6. `universal_fixed_scalar` as the scalar-readout form
   (Corollary 5.8), again conditional on singleton uniqueness.

**Scope**: \scopetau, modulo Hinge 7 NF confluence + the
singleton uniqueness of `NP ∩ OA` (paper Thm 5.5, rendered
structurally in Wave 12 as `intersection_iff` but not as a
singleton claim).  The fixed-point inheritance and preservation
theorems are **unconditional**; the universal-fixed theorem is
conditional on the singleton hypothesis, which future waves with
geometric lobe-lattice + meta-witness-depth instances will
provide.

## Public API

- `HolEndMorphism D` — σ-equivariant endomorphism on `D`-threads.
- `HolEndMorphism.actSigmaFixed` — lifting to `SigmaFixedThread`.
- `fixed_point_inheritance` — paper Prop 5.6, unconditional.
- `preserves_crossingPoint` — unconditional preservation.
- `universal_fixed_theorem` — paper Thm 5.7, conditional on
  NP ∩ OA singleton uniqueness.
- `universal_fixed_scalar` — paper Cor 5.8, scalar form.
- `iota_tau_universal_fixed` — concrete instantiation at the
  `TauReal`-readout level (connects to Wave 7's
  `CrossingPointDefectGerm` and Wave 4's operational `iota_tau`).
- `TrivialHolEndMorphism` — identity endomorphism on
  `TrivialDefectSystem`, sanity check that the scaffold compiles
  end-to-end.
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation Tau.Polarity

-- ============================================================
-- PART 1: HolEndMorphism — σ-equivariant thread endomorphism
-- ============================================================

/-- **A HolEnd_τ morphism on a `DefectInverseSystem`**
    (paper's `HolEnd_τ(ω)` class restricted to the defect tower).

    Packages:
    - `act : D.Thread → D.Thread`: the action on threads.
    - `preserves_sigma_fixed`: σ-equivariance at the thread level —
      σ-fixed threads map to σ-fixed threads (paper Prop 5.6's
      content, built in as a structural field).
    - `preserves_NP` and `preserves_OA`: preservation of the
      paper §5 non-polarity and ω-approach halves.

    σ-equivariance via `σ(f(G)) = f(σ(G))` would require the
    underlying σ-action on arbitrary threads; the preservation
    form `f(σ-fixed) = σ-fixed` is equivalent and cleaner. -/
structure HolEndMorphism (D : DefectInverseSystem) where
  /-- Action on arbitrary threads. -/
  act : D.Thread → D.Thread
  /-- **σ-equivariance** (paper Prop 5.6): σ-fixed threads map
      to σ-fixed threads. -/
  preserves_sigma_fixed : ∀ (t : D.Thread),
    (∀ n, D.sigma_level n (t.point n) = t.point n) →
    (∀ n, D.sigma_level n ((act t).point n) = (act t).point n)

/-- **Lift `HolEndMorphism.act` to `SigmaFixedThread`** using the
    `preserves_sigma_fixed` field.  This is the form consumed by
    the universal-fixed theorem. -/
def HolEndMorphism.actSigmaFixed
    {D : DefectInverseSystem} (f : HolEndMorphism D)
    (t : D.SigmaFixedThread) : D.SigmaFixedThread where
  point := (f.act t.toThread).point
  compat := (f.act t.toThread).compat
  sigma_fixed := f.preserves_sigma_fixed t.toThread t.sigma_fixed

-- ============================================================
-- PART 2: Paper Prop 5.6 — Fixed-point inheritance (unconditional)
-- ============================================================

/-- **Fixed-point inheritance under σ-equivariance**
    (paper Proposition 5.6, `prop:fixed-inheritance`): if `f` is a
    HolEnd_τ morphism and `t` is a σ-fixed thread, then `f.act t`
    is σ-fixed.

    Proof: direct from `HolEndMorphism.preserves_sigma_fixed`
    applied to `t.sigma_fixed`.  Structurally, the codomain of
    `actSigmaFixed` is `SigmaFixedThread`, so σ-fixedness is
    built in.

    This is the σ-equivariance content of paper's one-line proof:
    `σ(f(G)) = f(σ(G)) = f(G)`. -/
theorem HolEndMorphism.fixed_point_inheritance
    {D : DefectInverseSystem} (f : HolEndMorphism D)
    (t : D.SigmaFixedThread) :
    ∀ n, D.sigma_level n ((f.actSigmaFixed t).point n) =
         (f.actSigmaFixed t).point n :=
  (f.actSigmaFixed t).sigma_fixed

/-- **Thread-compatibility of the σ-fixed image** — a companion to
    `fixed_point_inheritance`: the σ-commutes-with-projection
    property lifts through `f.actSigmaFixed`.  This is the "passage
    to the inverse limit preserves σ-invariance" content at the
    abstract scaffold level. -/
theorem HolEndMorphism.actSigmaFixed_commutes_proj
    {D : DefectInverseSystem} (f : HolEndMorphism D)
    (t : D.SigmaFixedThread) (n : Nat) :
    D.proj n (D.sigma_level (n + 1) ((f.actSigmaFixed t).point (n + 1)))
      = D.sigma_level n ((f.actSigmaFixed t).point n) :=
  D.sigma_thread_compatible (f.actSigmaFixed t).toThread n

-- ============================================================
-- PART 3: Preservation of IsNonPolar and IsOmegaApproaching
-- ============================================================

/-- **HolEnd_τ morphism equipped with NP / OA preservation data**.
    Extending `HolEndMorphism` with the paper's "preserves
    polarisation status" and "preserves ω-approach" content
    (paper Thm 5.7 proof lines 1567–1572). -/
structure HolEndMorphismFull (D : DefectInverseSystem)
    (anchor : ∀ n, D.defect_level n → Prop)
    (mwd : D.SigmaFixedThread → Nat) extends HolEndMorphism D where
  /-- Preserves the non-polarity half (paper §5.2). -/
  preserves_NP : ∀ (t : D.SigmaFixedThread),
    DefectInverseSystem.IsNonPolar anchor t →
    DefectInverseSystem.IsNonPolar anchor (toHolEndMorphism.actSigmaFixed t)
  /-- Preserves the ω-approach half (paper §5.3). -/
  preserves_OA : ∀ (t : D.SigmaFixedThread),
    DefectInverseSystem.IsOmegaApproaching mwd t →
    DefectInverseSystem.IsOmegaApproaching mwd
      (toHolEndMorphism.actSigmaFixed t)

/-- **Preservation of the crossing-point property** — combines
    `preserves_NP` and `preserves_OA` via `IsCrossingPoint`'s
    conjunctive definition. -/
theorem HolEndMorphismFull.preserves_crossingPoint
    {D : DefectInverseSystem}
    {anchor : ∀ n, D.defect_level n → Prop}
    {mwd : D.SigmaFixedThread → Nat}
    (f : HolEndMorphismFull D anchor mwd)
    (t : D.SigmaFixedThread)
    (h : DefectInverseSystem.IsCrossingPoint anchor mwd t) :
    DefectInverseSystem.IsCrossingPoint anchor mwd
      (f.toHolEndMorphism.actSigmaFixed t) :=
  ⟨f.preserves_NP t h.1, f.preserves_OA t h.2⟩

-- ============================================================
-- PART 4: Paper Thm 5.7 — Universality (conditional form)
-- ============================================================

/-- **Universal fixed theorem** (paper Theorem 5.7,
    `thm:universal-fixed`) in conditional form.

    Given the **singleton uniqueness** of `NP ∩ OA` as a hypothesis
    (a future wave deliverable from the geometric lobe-lattice +
    meta-witness-depth infrastructure), every `HolEnd_τ`-morphism
    fixes any crossing-point germ.

    Paper proof: by `preserves_crossingPoint`, `f.act t` is a
    crossing-point if `t` is.  By singleton uniqueness,
    `f.act t = t`.

    Consumers supplying the singleton hypothesis make this
    unconditional. -/
theorem HolEndMorphismFull.universal_fixed_theorem
    {D : DefectInverseSystem}
    {anchor : ∀ n, D.defect_level n → Prop}
    {mwd : D.SigmaFixedThread → Nat}
    (f : HolEndMorphismFull D anchor mwd)
    (g : D.SigmaFixedThread)
    (h_g : DefectInverseSystem.IsCrossingPoint anchor mwd g)
    (singleton_uniqueness :
      ∀ t₁ t₂ : D.SigmaFixedThread,
        DefectInverseSystem.IsCrossingPoint anchor mwd t₁ →
        DefectInverseSystem.IsCrossingPoint anchor mwd t₂ →
        t₁ = t₂) :
    f.toHolEndMorphism.actSigmaFixed g = g := by
  have h_fg : DefectInverseSystem.IsCrossingPoint anchor mwd
                (f.toHolEndMorphism.actSigmaFixed g) :=
    f.preserves_crossingPoint g h_g
  exact singleton_uniqueness _ _ h_fg h_g

-- ============================================================
-- PART 5: Paper Cor 5.8 — Universal fixed scalar
-- ============================================================

/-- **Universal fixed scalar** (paper Corollary 5.8,
    `cor:iota-universal`) at the abstract readout level.

    Given the universal-fixed property at the thread level, the
    scalar readout is fixed by the induced action of `f` on
    `Read_F`.  Paper proof: immediate from Theorem 5.7 by
    applying `Read_F`. -/
theorem HolEndMorphismFull.universal_fixed_scalar
    {D : DefectInverseSystem}
    {anchor : ∀ n, D.defect_level n → Prop}
    {mwd : D.SigmaFixedThread → Nat}
    (f : HolEndMorphismFull D anchor mwd)
    (g : D.SigmaFixedThread)
    (h_g : DefectInverseSystem.IsCrossingPoint anchor mwd g)
    (singleton_uniqueness :
      ∀ t₁ t₂ : D.SigmaFixedThread,
        DefectInverseSystem.IsCrossingPoint anchor mwd t₁ →
        DefectInverseSystem.IsCrossingPoint anchor mwd t₂ →
        t₁ = t₂)
    (readout_level : ∀ n, D.defect_level n → TauRat) :
    D.threadReadoutTauReal readout_level
      (f.toHolEndMorphism.actSigmaFixed g).toThread =
    D.threadReadoutTauReal readout_level g.toThread := by
  rw [f.universal_fixed_theorem g h_g singleton_uniqueness]

/-- **Abstract universal fixed scalar (statement-level form)** —
    records the paper's Corollary 5.8 claim as a structural
    identity *without* requiring the scalar readout to be supplied
    at the point of statement.  This is the "ι_τ is universally
    fixed" claim at the most general abstract level. -/
theorem HolEndMorphismFull.threadReadout_universal_fixed
    {D : DefectInverseSystem}
    {anchor : ∀ n, D.defect_level n → Prop}
    {mwd : D.SigmaFixedThread → Nat}
    (f : HolEndMorphismFull D anchor mwd)
    (g : D.SigmaFixedThread)
    (h_g : DefectInverseSystem.IsCrossingPoint anchor mwd g)
    (singleton_uniqueness :
      ∀ t₁ t₂ : D.SigmaFixedThread,
        DefectInverseSystem.IsCrossingPoint anchor mwd t₁ →
        DefectInverseSystem.IsCrossingPoint anchor mwd t₂ →
        t₁ = t₂)
    (readout_level : ∀ n, D.defect_level n → TauRat) (n : Nat) :
    D.threadReadout readout_level
      (f.toHolEndMorphism.actSigmaFixed g).toThread n =
    D.threadReadout readout_level g.toThread n := by
  rw [f.universal_fixed_theorem g h_g singleton_uniqueness]

-- ============================================================
-- PART 6: Concrete ι_τ-level connection
-- ============================================================

/-- **Master constant `ι_τ` as universal fixed scalar**
    (paper Definition `def:iota-tau` + Corollary 5.8).

    The paper defines `ι_τ := Read_F(G_×[ω]) = Read_F(Δ_ω)` as the
    canonical scalar readout of the crossing-point defect germ,
    and Corollary 5.8 asserts it is universally fixed.

    At the TauLib level: we already have Wave 7's
    `CrossingPointDefectGerm` with its scalar readout via
    `toTauReal`, and Wave 4's operational `TauReal.iota_tau`.
    The universal-fixed-scalar theorem at the concrete level is:
    for any HolEnd_τ morphism `f` lifting to a `CrossingPointDefectGerm`
    action, `f.readout ≡ TauReal.iota_tau` at Cauchy equivalence.

    Rendered here as a **structural observation** tying the
    abstract `universal_fixed_scalar` back to the operational
    `iota_tau` — the concrete instantiation is deferred to a
    future wave that supplies the geometric `DefectInverseSystem`
    instance with the `anchor` / `mwd` machinery satisfying
    singleton uniqueness. -/
theorem iota_tau_universal_fixed_structural
    {D : DefectInverseSystem}
    {anchor : ∀ n, D.defect_level n → Prop}
    {mwd : D.SigmaFixedThread → Nat}
    (f : HolEndMorphismFull D anchor mwd)
    (g : D.SigmaFixedThread)
    (h_g : DefectInverseSystem.IsCrossingPoint anchor mwd g)
    (singleton_uniqueness :
      ∀ t₁ t₂ : D.SigmaFixedThread,
        DefectInverseSystem.IsCrossingPoint anchor mwd t₁ →
        DefectInverseSystem.IsCrossingPoint anchor mwd t₂ →
        t₁ = t₂)
    (readout_level : ∀ n, D.defect_level n → TauRat)
    (iota_approx_eq :
      ∀ n, D.threadReadout readout_level g.toThread n =
           TauReal.iota_tau.approx n) :
    ∀ n, D.threadReadout readout_level
           (f.toHolEndMorphism.actSigmaFixed g).toThread n =
         TauReal.iota_tau.approx n := by
  intro n
  rw [f.threadReadout_universal_fixed g h_g singleton_uniqueness readout_level n]
  exact iota_approx_eq n

-- ============================================================
-- PART 7: Trivial instance sanity check
-- ============================================================

/-- **Trivial HolEnd_τ morphism** on `TrivialDefectSystem`: the
    identity action.  Sanity check that the scaffold compiles
    end-to-end. -/
def TrivialHolEndMorphism : HolEndMorphism TrivialDefectSystem where
  act t := t
  preserves_sigma_fixed := fun _ h_sigma => h_sigma

/-- Fixed-point inheritance fires on the trivial instance. -/
theorem trivial_fixed_point_inheritance (n : Nat) :
    TrivialDefectSystem.sigma_level n
      ((TrivialHolEndMorphism.actSigmaFixed
         TrivialDefectSystem.trivialThread).point n)
      = (TrivialHolEndMorphism.actSigmaFixed
           TrivialDefectSystem.trivialThread).point n :=
  TrivialHolEndMorphism.fixed_point_inheritance
    TrivialDefectSystem.trivialThread n

/-- **The trivial HolEndMorphism is the identity on its
    SigmaFixedThread**: a sanity check on `actSigmaFixed`'s
    definition. -/
theorem trivial_actSigmaFixed_identity (n : Nat) :
    (TrivialHolEndMorphism.actSigmaFixed
       TrivialDefectSystem.trivialThread).point n
      = TrivialDefectSystem.trivialThread.point n :=
  rfl

end Tau.Boundary
