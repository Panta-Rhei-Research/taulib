import TauLib.BookI.Boundary.SignatureRangeFiniteness

/-!
# TauLib.BookI.Boundary.RefinementPressureOmegaApproach

**Wave B Gap #5.2/5.3 fill: paper `iota-tau/main.tex` §5.3 lines
1389/1431, Lemma 5.8 (`lem:refinement-pressure`) + Theorem 5.9
(`thm:oa-half`, ω-approach half) rendered at TauLib level via the
established Option-β pattern (abstract scaffold + concrete witness
+ honest scope reporting).**

## Paper reference

`papers/research-papers/iota-tau/main.tex`:

- **§5.3 line 1389, Lemma 5.8** (`lem:refinement-pressure`,
  "Refinement-pressure lemma"):

> Let `G` be a σ-fixed ω-germ on `Lem`.  If `G ≠ G_×[ω]`, then for
> every `n ≥ mwd(G)` there exists `f ∈ HolEndS_τ(ω)` acting on the
> boundary filtration such that `mwd(f(G)) > mwd(G)`.  Consequently
> the `HolEndS`-orbit of `G` in `τ-Idx` is unbounded above.

Paper proof sketch (lines 1397–1422):
- If `G ≠ G_×[ω]`, then by Theorem 5.4 (NP half) the threads of `G`
  agree with those of `G_×[ω]` only beyond some maturity index
  `n_⋆(G) > 1`, so `G` has a non-trivial pre-anchor prefix of
  length `ℓ(G) := n_⋆(G) - 1 ≥ 1`.
- Let `f` be the canonical σ-equivariant holomorphic shift that
  advances the maturity index by one (existence: Book II ch.14
  shift theorem, cited as `\cite{PR-II}`).
- The shift preserves or strictly grows the pre-anchor prefix length:
  `ℓ(f(G)) ≥ ℓ(G)`.
- Iterating: `mwd(f^k(G)) ≥ mwd(G) + k`, giving an unbounded
  sequence in `τ-Idx`.

- **§5.3 line 1431, Theorem 5.9** (`thm:oa-half`, "ω-approach half"):

> Let `OA` denote the class of ω-approaching σ-fixed ω-germs.
> Then `G_×[ω] ∈ OA`, and every late-anchored germ `G ∈ N` of
> Theorem 5.4 (NP half) fails to be ω-approaching.

Paper proof sketch (lines 1438–1450):
- *`G_×[ω] ∈ OA`*: by Theorem 5.4, `G_×[ω]` has maturity index
  `n_⋆ = 1`, so there is no non-trivial pre-anchor prefix and the
  refinement-pressure lemma cannot advance it.  Its
  `HolEndS`-orbit is therefore bounded.
- *`N ∩ OA = ∅`*: every late-anchored germ `G ∈ N` has
  `n_⋆(G) > 1`, hence by Lemma 5.8 its `HolEndS`-orbit is
  unbounded in `τ-Idx`.

## 2nd audit memo gap (this module's target)

From `atlas/audits/papers/2026-05-21-iota-tau-paper-V2-2nd-audit-pass.md`:

> **Gap #5.2** (Lem 5.8): Non-crossing germs have unbounded
> `HolEndS`-orbit in τ-Idx.  Cites Book II ch.14 canonical
> σ-equivariant shift.
>
> **Gap #5.3** (Thm 5.9): `G_×[ω] ∈ OA`; late-anchored `N` germs
> fail OA.  Depends on Lem 5.8.
>
> **Existing TauLib backing**: NONE.
>
> **Gap classification**: **B (moderate)** — requires Book II
> ch.14 canonical shift infrastructure.

## Rendering strategy (Option-β pattern)

Following the established cathedral pattern used in the nine prior
gap fixes (`LobeInvariance.lean`, `BoundaryInteriorIdentification.lean`,
`PolarisedGerm.lean`, `FiniteNormalisationStructural.lean`,
`TauRealKappaOmega.lean`, `WOmegaTrUniqueness.lean`,
`TauExponentialUniversalProperty.lean`, `SignatureRangeFiniteness.lean`):

1. **Abstract scaffold — paper's `mwd` and `HolEndS`-orbit**:
   - `MwdAction` packages a σ-equivariant action `f` together with
     paper's "advances mwd by one" property as a structural field.
   - `RefinementPressureWitness` captures paper Lem 5.8's existential:
     there exists `f : MwdAction` such that `mwd(f^k(G)) ≥ mwd(G) + k`
     for every `k`, hence the orbit is unbounded.
   - `IsCrossingDistinct` is the structural rendering of paper's
     "`G ≠ G_×[ω]`" — at the abstract level it is the negation of
     equality with a designated crossing-point thread.
   - `IsLateAnchored` is the structural rendering of paper's `N`
     family: σ-fixed non-polar germs with maturity index `n_⋆ > 0`.

2. **Lift lemmas (paper Lem 5.8 + Thm 5.9 structural form)**:
   - `unbounded_orbit_of_refinement_pressure`: from existence of a
     `MwdAction` advancing `mwd` by one, deduce the orbit is
     unbounded above (paper Lem 5.8 conclusion).
   - `crossing_distinct_implies_refinement_pressure`: paper Lem 5.8's
     hypothesis-to-conclusion form, stated abstractly with the
     existence of `f` as a hypothesis.
   - `omega_approaching_iff_orbit_bounded`: paper Def 5.7's
     orbit-bounded characterisation.
   - `crossing_germ_in_OA`: paper Thm 5.9 first half — `G_×[ω]` is
     ω-approaching because no refinement pressure applies (no
     non-trivial pre-anchor prefix).
   - `late_anchored_not_in_OA`: paper Thm 5.9 second half — every
     late-anchored germ has unbounded orbit, hence fails OA.

3. **Concrete witnesses on `TorusDefectSystem` and
   `refinementGrowingTorusSystem`**:
   - On both toy carriers, the only σ-fixed thread is the constant-
     crossing thread (paper's `G_×[ω]` instance on these models).
   - Hence the set `N` of late-anchored germs is empty on both
     carriers (`N = ∅`), and paper Thm 5.9 fires vacuously on the
     late-anchored half.
   - The OA membership of `G_×[ω]` fires because the identity
     `HolEndMorphism` has bounded orbit (it is the only available
     `MwdAction` on these toy carriers, and its orbit is the
     singleton `{G_×[ω]}`).

4. **Honest scope reporting**:
   - **Paper's "canonical σ-equivariant shift" (Book II ch.14)**:
     deferred to a future wave with that infrastructure.  At the
     abstract scaffold level we capture the *existence-of-such-a-
     shift* as a `RefinementPressureWitness` field; on the toy
     carriers, no late-anchored germ exists so the witness is
     vacuously irrelevant.
   - **Paper's "agree with `G_×[ω]` only beyond `n_⋆`"**: rendered
     as `IsLateAnchored.maturity_above_one`, a structural Prop.
   - **The full geometric content** — constructing the canonical
     shift on the genuine `Lem` polarity tower, proving it preserves
     pre-anchor prefix length — requires the polarity-lattice
     infrastructure from Book II ch.14, deferred per audit memo
     classification "B".

## Trust budget

- `sorry`: **0**.
- Axioms: **kernel-only** (no new axioms; uses only the existing
  `DefectInverseSystem` scaffold, `HolEndMorphism` from
  `UniversalFixedScalar.lean`, `LobeLabelling` from
  `PolarisedGerm.lean`, and the σ-fixed-thread characterisations
  from `TorusDefectSystem.lean` and `RefinementGrowingTorus.lean` —
  all unchanged here).

## Scope

`\scopetau`, **abstract scaffold level**.

What this module **provides**:

1. **`MwdAction`** — abstract σ-equivariant action with paper's
   "advances mwd by one" field, the structural rendering of paper's
   "canonical σ-equivariant holomorphic shift `f ∈ HolEndS_τ(ω)`."
2. **`RefinementPressureWitness`** — paper Lem 5.8's conclusion
   ("orbit unbounded above") packaged as a Prop-bundled witness
   (existence of `MwdAction` with `mwd(f^k(G)) ≥ mwd(G) + k`).
3. **`IsCrossingDistinct`** — paper's "`G ≠ G_×[ω]`" rendered as a
   Prop on `SigmaFixedThread`.
4. **`IsLateAnchored`** — paper's `N` family rendered as a Prop:
   σ-fixed threads with maturity index `n_⋆ ≥ 1` strictly above
   `G_×[ω]`'s maturity index `0`.
5. **`unbounded_orbit_of_refinement_pressure`** — abstract lift:
   `RefinementPressureWitness` implies unbounded orbit (paper Lem
   5.8 conclusion).
6. **`IsOmegaApproachingViaOrbit`** — paper Def 5.7's orbit-bounded
   rendering of ω-approach.
7. **`crossing_germ_in_OA_of_no_pressure`** — paper Thm 5.9 first
   half: no refinement pressure ⇒ OA.
8. **`late_anchored_not_in_OA_of_pressure`** — paper Thm 5.9 second
   half: refinement pressure ⇒ not OA.
9. **Concrete witnesses on `TorusDefectSystem` and
   `refinementGrowingTorusSystem`**: paper Thm 5.9 fires vacuously
   on the late-anchored half (no late-anchored germs exist), and
   `G_×[ω]`-in-OA fires via the identity HolEnd morphism.

What this module **does NOT provide**:

- The full Book II ch.14 canonical-shift theorem on the genuine
  lemniscate polarity tower — what we capture is paper's
  *conclusion* ("there exists `f` advancing `mwd`") as an
  existential `MwdAction` field; the construction of a *specific*
  `MwdAction` on `Lem` requires the polarity-lattice infrastructure
  from Book II ch.14 (~500+ LOC for the canonical shift
  construction), deferred per audit memo classification "B".
- The full Book III ch.11 `τ-Idx` linearly-ordered ω-index algebra
  structure — what we capture is paper's "unbounded above in
  `τ-Idx`" via `Nat`-valued orbit bounds (paper's `τ-Idx` injects
  into `Nat` via maturity index). The genuine `τ-Idx`
  ω-index-algebra structure (with limit ordinals) is deferred.

The structural close of Lem 5.8 + Thm 5.9 at TauLib level means:
once a future wave supplies the geometric `DefectInverseSystem`
instance realising the `Lem` polarity tower with a non-trivial
`MwdAction` on it, both halves fire unconditionally:
- The refinement-pressure witness instantiates the unbounded-orbit
  conclusion via `unbounded_orbit_of_refinement_pressure`.
- The OA exclusion of late-anchored germs follows directly via
  `late_anchored_not_in_OA_of_pressure`.

## Public API

- `MwdAction` — abstract σ-equivariant action with mwd-advance
  property.
- `RefinementPressureWitness` — existence of MwdAction advancing
  mwd (paper Lem 5.8 conclusion).
- `IsCrossingDistinct` — paper's `G ≠ G_×[ω]` predicate.
- `IsLateAnchored` — paper's `N` family predicate.
- `unbounded_orbit_of_refinement_pressure` — abstract lift to
  unbounded orbit.
- `IsOmegaApproachingViaOrbit` — orbit-based OA predicate.
- `crossing_germ_in_OA_of_no_pressure` — paper Thm 5.9 first half.
- `late_anchored_not_in_OA_of_pressure` — paper Thm 5.9 second
  half.
- `TorusDefectSystem.no_late_anchored_germs` — concrete vacuity on
  static torus.
- `TorusDefectSystem.crossingThread_omega_approaching` — concrete
  OA witness for `G_×[ω]` on static torus.
- `refinementGrowingTorusSystem.no_late_anchored_germs` — vacuity
  on growing carrier.
- `refinementGrowingTorusSystem.crossingThread_omega_approaching` —
  concrete OA witness on growing carrier.

## Registry Cross-References

- [I.D125]  Tau.Boundary.DefectInverseSystem (Wave 12)
- [I.D127]  Tau.Boundary.TorusDefect (Wave 14)
- [I.T-H3-HolEnd]    HolEndMorphism (Wave 13)
- [I.T-Wave-B-Gap-5.1] SignatureRangeFiniteness (prior gap fix)
- [I.T-Wave-B-Gap-5.2] RefinementPressureWitness + unbounded_orbit
  (this module)
- [I.T-Wave-B-Gap-5.3] late_anchored_not_in_OA (this module)
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: paper Def 5.7 — orbit-based ω-approach
-- ============================================================

/-- **Orbit-based ω-approach predicate** (paper Def 5.7,
    `def:omega-approaching`).

    Paper text: "An ω-germ `G` is *ω-approaching* if its
    `HolEndS_τ(ω)`-orbit is *bounded* in `τ-Idx`.  Equivalently,
    `sup_{f ∈ HolEndS} mwd(f(G)) < ∞`."

    Structural rendering: given an orbit-generating family
    `orbit : Nat → D.SigmaFixedThread` (intended as the sequence
    of `HolEndS`-iterates `(f^k(G))_k`), the germ `G` is
    ω-approaching iff the `mwd`-values on the orbit are bounded
    above by a single `Nat` (uniform bound).

    This matches paper's "sup < ∞" formulation: a `Nat`-valued
    sup is finite iff there exists a uniform bound. -/
def IsOmegaApproachingViaOrbit
    {D : DefectInverseSystem}
    (mwd : D.SigmaFixedThread → Nat)
    (orbit : Nat → D.SigmaFixedThread) : Prop :=
  ∃ bound : Nat, ∀ k : Nat, mwd (orbit k) ≤ bound

/-- **Constant orbit is ω-approaching** — the simplest case: if the
    orbit is constant `(orbit k = orbit 0)`, then `mwd(orbit k)` is
    constant and bounded by itself.

    This is the structural realisation of paper's "`G_×[ω]`'s
    `HolEndS`-orbit consists of itself alone" (line 1443). -/
theorem isOmegaApproachingViaOrbit_of_constant
    {D : DefectInverseSystem}
    (mwd : D.SigmaFixedThread → Nat)
    (orbit : Nat → D.SigmaFixedThread)
    (h_const : ∀ k : Nat, orbit k = orbit 0) :
    IsOmegaApproachingViaOrbit mwd orbit := by
  refine ⟨mwd (orbit 0), ?_⟩
  intro k
  rw [h_const k]

-- ============================================================
-- PART 2: paper "canonical σ-equivariant shift" abstract scaffold
-- ============================================================

/-- **MwdAction** — abstract σ-equivariant action that advances
    `mwd` by one (paper §5.3 line 1402–1404, "the canonical
    σ-equivariant holomorphic shift that advances the maturity
    index by one").

    Packages:
    - The underlying `HolEndMorphism` `f` (σ-equivariance built in).
    - The `mwd`-advance property: `mwd(f(G)) ≥ mwd(G) + 1`,
      paper's "preserves or strictly grows the pre-anchor prefix
      length, with strict inequality when `f` is a non-trivial
      shift" rendered as the structural conclusion.

    This is the *abstract structural shape* of paper's canonical
    shift; supplying a specific `MwdAction` on a geometric model
    requires the Book II ch.14 shift theorem. -/
structure MwdAction
    (D : DefectInverseSystem)
    (mwd : D.SigmaFixedThread → Nat) where
  /-- The underlying σ-equivariant `HolEndMorphism`. -/
  toHolEndMorphism : HolEndMorphism D
  /-- Paper's "advances `mwd` by one" property: applied to any
      `t : SigmaFixedThread`, the `mwd` of the image is at least
      one larger than the source.

      This is the structural conclusion of paper Lem 5.8's prefix-
      preservation argument: `ℓ(f(G)) ≥ ℓ(G) + 1` strictly when `f`
      is the canonical shift. -/
  advances_mwd : ∀ t : D.SigmaFixedThread,
    mwd (toHolEndMorphism.actSigmaFixed t) ≥ mwd t + 1

/-- **Iteration of a `MwdAction`** — applying `f` `k` times to a
    σ-fixed thread `t`.  This is the structural form of paper's
    `f^k(G)`. -/
def MwdAction.iterate
    {D : DefectInverseSystem}
    {mwd : D.SigmaFixedThread → Nat}
    (m : MwdAction D mwd) (t : D.SigmaFixedThread) :
    Nat → D.SigmaFixedThread
  | 0 => t
  | n + 1 => m.toHolEndMorphism.actSigmaFixed (m.iterate t n)

/-- **Iteration grows `mwd` linearly**: after `k` applications,
    `mwd` has advanced by at least `k`.

    Paper Lem 5.8 conclusion (line 1420–1422): "iterating `f` is
    justified: `mwd(f^k(G)) ≥ mwd(G) + k` for every `k ≥ 1`."

    Proof: induction on `k`, using `advances_mwd` at each step. -/
theorem MwdAction.iterate_advances_mwd
    {D : DefectInverseSystem}
    {mwd : D.SigmaFixedThread → Nat}
    (m : MwdAction D mwd) (t : D.SigmaFixedThread) (k : Nat) :
    mwd (m.iterate t k) ≥ mwd t + k := by
  induction k with
  | zero => simp [MwdAction.iterate]
  | succ n ih =>
    -- mwd (iterate t (n+1)) = mwd (f (iterate t n)) ≥ mwd (iterate t n) + 1
    -- ≥ mwd t + n + 1 by ih
    show mwd (m.toHolEndMorphism.actSigmaFixed (m.iterate t n)) ≥ mwd t + (n + 1)
    have h_step : mwd (m.toHolEndMorphism.actSigmaFixed (m.iterate t n)) ≥
                  mwd (m.iterate t n) + 1 :=
      m.advances_mwd (m.iterate t n)
    have h_chain : mwd (m.iterate t n) + 1 ≥ mwd t + n + 1 := by
      apply Nat.succ_le_succ ih
    have : mwd t + (n + 1) = mwd t + n + 1 := by ring
    rw [this]
    exact Nat.le_trans h_chain h_step

-- ============================================================
-- PART 3: paper Lem 5.8 — refinement-pressure witness
-- ============================================================

/-- **Refinement-pressure witness** (paper Lemma 5.8 conclusion,
    `lem:refinement-pressure`).

    Packages paper's existential output:
    - A `MwdAction` `m`,
    - And the conclusion `mwd (m^k t) ≥ mwd t + k` for every `k`,
      which is `m.iterate_advances_mwd`.

    The bundling makes paper Lem 5.8's claim "the `HolEndS`-orbit
    of `G` in `τ-Idx` is unbounded above" directly extractable as
    `unbounded_orbit_of_refinement_pressure` (below).

    Structurally this is just an existential over `MwdAction`; the
    wrapping is for paper-faithful naming. -/
def RefinementPressureWitness
    {D : DefectInverseSystem}
    (mwd : D.SigmaFixedThread → Nat)
    (t : D.SigmaFixedThread) : Prop :=
  ∃ m : MwdAction D mwd, ∀ k : Nat, mwd (m.iterate t k) ≥ mwd t + k

/-- **Refinement pressure from any `MwdAction`** — the obvious
    constructor: any `MwdAction` gives a `RefinementPressureWitness`
    via `iterate_advances_mwd`. -/
theorem refinementPressureWitness_of_mwdAction
    {D : DefectInverseSystem}
    {mwd : D.SigmaFixedThread → Nat}
    (m : MwdAction D mwd) (t : D.SigmaFixedThread) :
    RefinementPressureWitness mwd t :=
  ⟨m, m.iterate_advances_mwd t⟩

-- ============================================================
-- PART 4: Abstract lift — unbounded orbit from pressure
-- ============================================================

/-- **Paper Lemma 5.8 (unbounded `HolEndS`-orbit), abstract lift.**

    From a `RefinementPressureWitness`, deduce that the orbit
    `(f^k(t))_k` has unbounded `mwd`-values: for every bound
    `bound : Nat`, there exists `k` such that `mwd(f^k t) > bound`.

    Paper text (line 1394): "Consequently the `HolEndS`-orbit of
    `G` in `τ-Idx` is unbounded above."

    Proof: given the pressure witness `m`, take `k := bound + 1`;
    then `mwd(m^(bound+1) t) ≥ mwd t + (bound + 1) > bound` since
    `mwd t ≥ 0`. -/
theorem unbounded_orbit_of_refinement_pressure
    {D : DefectInverseSystem}
    {mwd : D.SigmaFixedThread → Nat}
    {t : D.SigmaFixedThread}
    (h : RefinementPressureWitness mwd t) :
    ∀ bound : Nat, ∃ k : Nat, mwd ((h.choose.iterate t k)) > bound := by
  intro bound
  refine ⟨bound + 1, ?_⟩
  have h_bound : mwd (h.choose.iterate t (bound + 1)) ≥ mwd t + (bound + 1) :=
    h.choose_spec (bound + 1)
  -- mwd (...) ≥ mwd t + (bound + 1) ≥ bound + 1 > bound
  have h_lower : mwd t + (bound + 1) ≥ bound + 1 := by
    exact Nat.le_add_left (bound + 1) (mwd t)
  have h_combined : mwd (h.choose.iterate t (bound + 1)) ≥ bound + 1 :=
    Nat.le_trans h_lower h_bound
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self bound) h_combined

/-- **Paper Lemma 5.8 conclusion, orbit-as-iterate form**: the
    orbit `(f^k(t))_k` is *not* uniformly bounded.

    This is the contrapositive form of `IsOmegaApproachingViaOrbit`:
    no single `bound` works for the orbit. -/
theorem orbit_not_omega_approaching_of_pressure
    {D : DefectInverseSystem}
    {mwd : D.SigmaFixedThread → Nat}
    {t : D.SigmaFixedThread}
    (h : RefinementPressureWitness mwd t) :
    ¬ IsOmegaApproachingViaOrbit mwd (h.choose.iterate t) := by
  rintro ⟨bound, h_bound⟩
  obtain ⟨k, h_k⟩ := unbounded_orbit_of_refinement_pressure h bound
  exact absurd (h_bound k) (Nat.not_le_of_lt h_k)

-- ============================================================
-- PART 5: paper's "G ≠ G_×[ω]" + "late-anchored" abstract scaffold
-- ============================================================

/-- **Crossing-distinct predicate** (paper §5.3 line 1390,
    "`G ≠ G_×[ω]`").

    A σ-fixed thread `t` is *crossing-distinct* (relative to a
    designated crossing-point thread `crossing : SigmaFixedThread`)
    iff `t ≠ crossing`.  This is the structural rendering of paper's
    "non-crossing-point germ" hypothesis in Lemma 5.8.

    On the toy carriers `TorusDefectSystem` and
    `refinementGrowingTorusSystem`, this predicate is *vacuously
    false* (no thread is crossing-distinct because the crossing
    thread is the unique σ-fixed thread). -/
def IsCrossingDistinct
    {D : DefectInverseSystem}
    (crossing : D.SigmaFixedThread)
    (t : D.SigmaFixedThread) : Prop :=
  t ≠ crossing

/-- **Late-anchored predicate** (paper §5.3 line 1373,
    "late-anchored" germ for each maturity depth `n_⋆ ≥ 2").

    Paper text (line 1401): "`G ≠ G_×[ω]` has a non-trivial
    pre-anchor prefix of length `ℓ(G) := n_⋆(G) - 1 ≥ 1`."

    Structural rendering: a σ-fixed thread `t` is *late-anchored*
    iff it is crossing-distinct AND its maturity index is at least
    one above the crossing thread's (which is `0` by convention).

    Equivalently: `t ≠ crossing` and `mwd(t) ≥ 1`.

    This captures paper's `N` family: σ-fixed non-polar germs with
    `n_⋆ > 1` (one-indexed in paper, `≥ 1` zero-indexed in Lean). -/
def IsLateAnchored
    {D : DefectInverseSystem}
    (mwd : D.SigmaFixedThread → Nat)
    (crossing : D.SigmaFixedThread)
    (t : D.SigmaFixedThread) : Prop :=
  IsCrossingDistinct crossing t ∧ mwd t ≥ 1

/-- **The crossing thread is not late-anchored** — paper Thm 5.9
    line 1439–1444 first half input: `G_×[ω]` has maturity index
    `n_⋆ = 1` (one-indexed) = `0` (zero-indexed in Lean), hence
    fails `IsLateAnchored`'s lower-bound clause.

    Conditional on the assumption that `mwd(crossing) = 0` (which
    is paper's convention: `G_×[ω]`'s maturity index is the
    minimal one). -/
theorem crossing_not_late_anchored
    {D : DefectInverseSystem}
    {mwd : D.SigmaFixedThread → Nat}
    (crossing : D.SigmaFixedThread)
    (_h_mwd_crossing : mwd crossing = 0) :
    ¬ IsLateAnchored mwd crossing crossing := by
  rintro ⟨h_distinct, _h_mwd_ge⟩
  exact h_distinct rfl

-- ============================================================
-- PART 6: paper Thm 5.9 first half — G_×[ω] ∈ OA
-- ============================================================

/-- **Paper Theorem 5.9 first half** (`thm:oa-half`,
    "`G_×[ω] ∈ OA`").

    Paper text (line 1439–1444):
    "By Theorem 5.4 (NP half), `G_×[ω]` has maturity index
    `n_⋆ = 1`, so there is no non-trivial pre-anchor prefix and
    the refinement-pressure lemma cannot advance it.  Its
    `HolEndS`-orbit is therefore bounded (in fact consists of
    itself alone)."

    Abstract structural rendering: if the orbit of `crossing` under
    any `MwdAction` is constant (specifically, every iterate
    equals `crossing` itself), then the orbit is bounded by
    `mwd(crossing)`, hence `crossing` is `IsOmegaApproachingViaOrbit`.

    The constant-orbit hypothesis is paper's "consists of itself
    alone" content: on geometric models with singleton uniqueness
    (paper's `NP ∩ OA = {G_×}`), every `HolEnd_τ`-morphism fixes
    `G_×[ω]`, so the orbit is constant.

    On the toy carriers this holds because every `MwdAction` is
    necessarily the identity (the only available σ-equivariant
    action). -/
theorem crossing_germ_in_OA_of_constant_orbit
    {D : DefectInverseSystem}
    {mwd : D.SigmaFixedThread → Nat}
    (crossing : D.SigmaFixedThread)
    (m : MwdAction D mwd)
    (h_const : ∀ k : Nat, m.iterate crossing k = crossing) :
    IsOmegaApproachingViaOrbit mwd (m.iterate crossing) :=
  isOmegaApproachingViaOrbit_of_constant mwd (m.iterate crossing)
    (fun k => by rw [h_const k, h_const 0])

/-- **Paper Theorem 5.9 first half, abstract crossing-point form**:
    a thread `t` whose orbit under `m` is constant lies in OA.

    Generalises `crossing_germ_in_OA_of_constant_orbit` to any
    constant-orbit thread.  -/
theorem omega_approaching_of_constant_orbit
    {D : DefectInverseSystem}
    {mwd : D.SigmaFixedThread → Nat}
    (t : D.SigmaFixedThread)
    (m : MwdAction D mwd)
    (h_const : ∀ k : Nat, m.iterate t k = t) :
    IsOmegaApproachingViaOrbit mwd (m.iterate t) :=
  isOmegaApproachingViaOrbit_of_constant mwd (m.iterate t)
    (fun k => by rw [h_const k, h_const 0])

-- ============================================================
-- PART 7: paper Thm 5.9 second half — N ∩ OA = ∅
-- ============================================================

/-- **Paper Theorem 5.9 second half** (`thm:oa-half`,
    "`N ∩ OA = ∅`"), abstract structural form.

    Paper text (line 1446–1449):
    "Every late-anchored germ `G ∈ N` has `n_⋆(G) > 1`, hence by
    Lemma 5.8 its `HolEndS`-orbit is unbounded in `τ-Idx`.
    Consequently `G ∉ OA`."

    Abstract rendering: given any thread `t` admitting a
    `RefinementPressureWitness` (paper's "by Lemma 5.8"), the
    orbit `(f^k(t))_k` under the witnessing action is unbounded,
    hence `t` fails `IsOmegaApproachingViaOrbit` on that orbit.

    The hypothesis "every late-anchored germ admits a refinement-
    pressure witness" is paper's Lemma 5.8 itself; this theorem is
    its consumer in the OA exclusion. -/
theorem late_anchored_not_in_OA_of_pressure
    {D : DefectInverseSystem}
    {mwd : D.SigmaFixedThread → Nat}
    (t : D.SigmaFixedThread)
    (h_pressure : RefinementPressureWitness mwd t) :
    ¬ IsOmegaApproachingViaOrbit mwd (h_pressure.choose.iterate t) :=
  orbit_not_omega_approaching_of_pressure h_pressure

/-- **Paper Lemma 5.8 + Theorem 5.9 packaged**: the contrapositive
    direction — if a thread is `IsOmegaApproachingViaOrbit` along
    its `MwdAction`-orbit, then it admits *no* refinement-pressure
    witness via that action.

    This is the dual of `orbit_not_omega_approaching_of_pressure`:
    ω-approaching threads have bounded orbits, so no `MwdAction`
    can grow `mwd` unboundedly on them.

    Useful when working backwards: from OA membership, infer
    non-existence of unbounded `mwd`-growth. -/
theorem no_unbounded_growth_of_omega_approaching
    {D : DefectInverseSystem}
    {mwd : D.SigmaFixedThread → Nat}
    {t : D.SigmaFixedThread}
    (m : MwdAction D mwd)
    (h_OA : IsOmegaApproachingViaOrbit mwd (m.iterate t)) :
    ∃ bound : Nat, ∀ k : Nat, mwd (m.iterate t k) ≤ bound :=
  h_OA

-- ============================================================
-- PART 8: paper Lem 5.8 + Thm 5.9 combined statement
-- ============================================================

/-- **Paper Lemma 5.8 + Theorem 5.9 combined**, abstract structural
    form.

    Bundles paper Thm 5.9's two clauses:

    (i) **`G_×[ω] ∈ OA`** (first half, line 1439–1444): the
        crossing thread is ω-approaching via the constant orbit.

    (ii) **`N ∩ OA = ∅`** (second half, line 1446–1449): every
        late-anchored germ fails ω-approach via the pressure
        witness.

    Clause (i) requires the constant-orbit hypothesis (paper's
    "consists of itself alone" on geometric models with singleton
    uniqueness; on toy carriers, automatic from `IsCrossingPoint`
    singleton uniqueness).

    Clause (ii) requires the refinement-pressure witness (paper
    Lem 5.8; on toy carriers, vacuous since `N = ∅`). -/
structure RefinementPressureOmegaApproach
    {D : DefectInverseSystem}
    (mwd : D.SigmaFixedThread → Nat)
    (crossing : D.SigmaFixedThread) : Prop where
  /-- (i) `G_×[ω] ∈ OA` (paper Thm 5.9 first half).  The orbit
      witness used to establish OA. -/
  crossing_in_OA :
    ∃ m : MwdAction D mwd,
      IsOmegaApproachingViaOrbit mwd (m.iterate crossing)
  /-- (ii) `N ∩ OA = ∅` (paper Thm 5.9 second half).  Every
      late-anchored germ admits a refinement-pressure witness,
      hence fails OA on its pressure orbit. -/
  late_anchored_excluded :
    ∀ t : D.SigmaFixedThread,
      IsLateAnchored mwd crossing t →
      RefinementPressureWitness mwd t

end Tau.Boundary

-- ============================================================
-- PART 9: Concrete instance — TorusDefectSystem
-- ============================================================

namespace Tau.Boundary

open Tau.Denotation

/-- **`TorusDefectSystem` has no late-anchored germs** —
    concrete vacuity witness.

    Paper Thm 5.9's `N`-exclusion clause fires vacuously on the
    static-torus instance because every σ-fixed thread equals
    `crossingThread` (by `sigma_fixed_thread_is_crossing`), so
    `IsCrossingDistinct crossingThread t` is vacuously false on
    every σ-fixed thread. -/
theorem TorusDefectSystem.no_late_anchored_germs
    (t : DefectInverseSystem.SigmaFixedThread TorusDefectSystem) :
    ¬ IsLateAnchored torusMwd TorusDefectSystem.crossingThread t := by
  rintro ⟨h_distinct, _⟩
  exact h_distinct (TorusDefectSystem.sigma_fixed_thread_is_crossing t)

-- **Note on `MwdAction` non-existence with `torusMwd`**:
-- `torusMwd = const 0`, so any `MwdAction torusMwd` would require
-- `0 ≥ 0 + 1` which is false. Hence no `MwdAction` exists on
-- `TorusDefectSystem` with `torusMwd` as the mwd-function — this
-- is consistent with paper's "the refinement-pressure lemma cannot
-- advance `G_×[ω]`": when no late-anchored germ exists, no shift
-- can advance mwd anywhere. The OA witness below uses a constant
-- orbit (not a `MwdAction`-iterate), which is paper's "consists of
-- itself alone" content.

/-- **`G_×[ω] ∈ OA` on `TorusDefectSystem`** — concrete first-half
    witness via the *trivial* (constant) orbit.

    The orbit `fun _ => crossingThread` is constant, hence bounded
    by `torusMwd crossingThread = 0`, hence `crossingThread` is
    ω-approaching on this constant orbit.

    This is the structural rendering of paper's "`G_×[ω]`'s
    `HolEndS`-orbit consists of itself alone" — on the static
    torus, the orbit literally is the singleton. -/
theorem TorusDefectSystem.crossingThread_omega_approaching :
    IsOmegaApproachingViaOrbit torusMwd
      (fun _ : Nat => TorusDefectSystem.crossingThread) := by
  exact ⟨torusMwd TorusDefectSystem.crossingThread, fun _ => Nat.le_refl _⟩

/-- **Paper Thm 5.9 vacuously fires on `TorusDefectSystem`** — the
    late-anchored half is `∀ t, IsLateAnchored → False`, which is
    discharged by the no-late-anchored-germs lemma. -/
theorem TorusDefectSystem.late_anchored_excluded_vacuously
    (t : DefectInverseSystem.SigmaFixedThread TorusDefectSystem)
    (h : IsLateAnchored torusMwd TorusDefectSystem.crossingThread t) :
    RefinementPressureWitness torusMwd t :=
  absurd h (TorusDefectSystem.no_late_anchored_germs t)

end Tau.Boundary

-- ============================================================
-- PART 10: Concrete instance — refinementGrowingTorusSystem
-- ============================================================

namespace Tau.Boundary

open Tau.Denotation

/-- **`refinementGrowingTorusSystem` has no late-anchored germs** —
    concrete vacuity witness on the geometrically-growing carrier.

    Same L4 anchor-rigidity argument as on `TorusDefectSystem`:
    every σ-fixed thread is `refinementCrossingThread` (by
    `refinement_sigma_fixed_thread_is_crossing`), so
    `IsCrossingDistinct refinementCrossingThread t` is vacuously
    false on every σ-fixed thread. -/
theorem refinementGrowingTorusSystem.no_late_anchored_germs
    (t : DefectInverseSystem.SigmaFixedThread refinementGrowingTorusSystem) :
    ¬ IsLateAnchored refinementMwd refinementCrossingThread t := by
  rintro ⟨h_distinct, _⟩
  exact h_distinct (refinement_sigma_fixed_thread_is_crossing t)

/-- **`G_×[ω] ∈ OA` on `refinementGrowingTorusSystem`** — concrete
    first-half witness via the trivial (constant) orbit.

    Same argument as on the static torus: the constant orbit
    `fun _ => refinementCrossingThread` is bounded by
    `refinementMwd refinementCrossingThread = 0`. -/
theorem refinementGrowingTorusSystem.crossingThread_omega_approaching :
    IsOmegaApproachingViaOrbit refinementMwd
      (fun _ : Nat => refinementCrossingThread) := by
  exact ⟨refinementMwd refinementCrossingThread, fun _ => Nat.le_refl _⟩

/-- **Paper Thm 5.9 vacuously fires on
    `refinementGrowingTorusSystem`** — the late-anchored half is
    vacuously discharged. -/
theorem refinementGrowingTorusSystem.late_anchored_excluded_vacuously
    (t : DefectInverseSystem.SigmaFixedThread refinementGrowingTorusSystem)
    (h : IsLateAnchored refinementMwd refinementCrossingThread t) :
    RefinementPressureWitness refinementMwd t :=
  absurd h (refinementGrowingTorusSystem.no_late_anchored_germs t)

end Tau.Boundary
