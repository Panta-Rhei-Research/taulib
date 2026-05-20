import TauLib.BookI.Polarity.InverseLimit
import TauLib.BookI.Boundary.IotaTauStructural

/-!
# TauLib.BookI.Boundary.DefectInverseSystem

**Deep Hinge 3 Steps 1–6 — The crossing-point defect ω-germ as an
abstract inverse-system scaffold.**

Lean structural rendering of paper `iota-tau/main.tex` §4
("The Crossing-Point Defect ω-Germ", five-step construction program)
and §5 ("Crossing-Point Uniqueness and Universal Fixed Scalar",
NP / OA halves + intersection).

## Registry Cross-References

- [I.D25]  OmegaTail (depth-truncated)
- [I.D27]  SplitComplex
- [I.D120] Tau.Boundary.TauReal.iota_tau (Wave 4 operational)
- [I.D121] Tau.Boundary.CrossingPointDefectGerm (Wave 7 scaffold)
- [I.D122] Tau.Polarity.OmegaInverseLimit (Wave 8 infrastructure)
- [I.T-H3-DefectSystem] DefectInverseSystem (this module)
- [I.T-H3-SigmaInvariance] σ-invariance theorem (paper Thm 4.2)
- [I.T-H3-Uniqueness] NP ∩ OA = {G_×} (paper Thm 5.5)

## Mathematical Content

**Paper §4 five-step program** (paper `sec:five-step`):

  - **Step 1**: Finite torus `T_n = B_n × C_n` at each depth
    (`Definitions channel-quotients + torus-realised`).
  - **Step 2**: Circle-thread map `Φ_n : C^n → T_n`, realised
    relation `R_n := Im(Φ_n)`.
  - **Step 3**: Coupling defect `Δ_n := T_n \ R_n` (the obstructions
    to `Φ_n`-surjectivity).
  - **Step 4**: Refinement compatibility `Δ_{n+1} → Δ_n` makes
    `{Δ_n}` an inverse system (Lemma `lem:defect-compatible`).
  - **Step 5**: σ-invariance of the tower
    (paper Theorem `thm:defect-sigma-inv`).

The inverse limit `Δ_ω = lim_n Δ_n` is the crossing-point defect
ω-germ (paper Definition `def:crossing-germ`).

**Paper §5 uniqueness halves**:

  - **NP half** (`thm:np-half`): σ-fixed non-polar germs form a
    countable family `{G_×} ∪ N`, where `N` consists of germs
    whose threads visit the crossing anchor at depths `n ≥ n_⋆`
    for some maturity index.
  - **OA half** (`thm:oa-half`): ω-approaching germs (bounded
    mwd-orbit) exclude `N`; only `G_×` lies in both classes.
  - **Intersection** (`thm:intersection`): `NP ∩ OA = {G_×}` —
    the crossing-point uniqueness theorem.

## Scope and rendering strategy

The paper's §4–§5 are heavy on geometric content (torus, cylinder
threads, refinement projections, lobe labels) that is **not
directly reachable** in TauLib's tactics-only Mathlib budget
without substantial combinatorial infrastructure that itself spans
multiple waves.

**We render the *abstract inverse-system shape* of the construction,
not its geometric content.**  The key deliverables at the
structural level:

1. An **abstract `DefectInverseSystem` structure** packaging Steps 1–4:
   depth-indexed families `defect_level : Nat → Type` with
   refinement projections, σ-involutions at every level, and
   compatibility conditions.
2. A **`SigmaFixedThread`** type capturing the inverse-limit
   threading by σ-fixed compatible classes.
3. **The σ-invariance theorem** (Step 5) at the abstract level:
   σ-equivariance of projections + σ-involutivity → σ-fixed
   threads have σ-fixed inverse-limit image.
4. **Predicate scaffolding for §5 NP / OA halves** and the
   intersection claim `NP ∩ OA = {G_×}`, as structural Prop-level
   predicates over `SigmaFixedThread`.
5. **A concrete toy instance** on a trivial 2-element lattice,
   verifying the scaffold compiles and the σ-invariance lemma
   applies.
6. **Connection hook** from the abstract scaffold to Wave 7's
   `CrossingPointDefectGerm` (a `CrossingPointDefectGerm` supplies
   the scalar-readout data; the abstract `DefectInverseSystem`
   supplies the structural underneath).

The **specific geometric content** — constructing T_n, B_n, C_n,
R_n from the τ-circle presentation, and proving the surjectivity
failure of a specific Φ_n — is deferred to a future wave with
combinatorial torus infrastructure.  What we **do** capture
abstractly is the **inverse-system shape of unpolarisation**
(paper Thm `defect-unpolarised`): see PART 8 below.

**Scope**: \scopetau, modulo Hinge 7 NF confluence (for the full
primorial-convergence claim of paper `thm:primorial-convergence`,
which requires the Book II ch.~30 BndLift infrastructure).  The
abstract scaffold established here is **unconditional**.

## Public API

- `DefectInverseSystem` — abstract inverse-system structure
  (Steps 1–4).
- `SigmaFixedThread D` — σ-fixed compatible thread in `D`.
- `DefectInverseSystem.sigmaInvariance` — Step 5 σ-invariance
  theorem at the abstract level.
- `IsNonPolar t` / `IsOmegaApproaching t` — paper §5 NP / OA
  predicates on threads.
- `IsCrossingPoint t` — predicate combining both halves, paper's
  `G_×` characterisation.
- `intersection_uniqueness` — paper Thm 5.5 `NP ∩ OA = {G_×}`
  intersection claim, stated at the structural-predicate level.
- `TrivialDefectSystem` — toy 2-element example verifying the
  scaffold builds and σ-invariance applies.
- `defectGerm_to_crossingPoint` — bridge from the abstract
  scaffold back to Wave 7's `CrossingPointDefectGerm` readout.
- **PART 8**: `IsUnpolarised`, `ProjSurjective`,
  `unpolarisation_pulled_back`, `UnpolarisedThread` —
  paper §4.4 Theorem 4.7 unpolarisation, rendered as an
  abstract structural theorem (existence of non-σ-fixed defect
  elements at every depth, preservation under projection).
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation Tau.Polarity

-- ============================================================
-- PART 1: Abstract DefectInverseSystem (Steps 1–4 of paper §4)
-- ============================================================

/-- **An abstract defect inverse system** (paper §4.1 five-step
    program, Steps 1–4 packaged structurally).

    Captures:
    - Step 1/3: a depth-indexed family of "defect levels"
      (the complement `Δ_n = T_n \ R_n` at every depth).
    - Step 4: refinement-compatibility projections
      `Δ_{n+1} → Δ_n`.
    - Step 5 data (σ-involution): σ acts on every level,
      involutively, and commutes with projections.

    The *geometric* content (what torus, what realised relation,
    what lobe labels) is abstracted away; what remains is the
    inverse-system shape that Wave 8's `OmegaInverseLimit`
    infrastructure consumes.  Consumers plug in specific
    instances (e.g. the τ-circle presentation's refinement
    tower) to recover the full paper §4 construction. -/
structure DefectInverseSystem where
  /-- The defect object at each depth `n ≥ 1`.
      Encodes Step 3's `Δ_n = T_n \ R_n`. -/
  defect_level : Nat → Type
  /-- The refinement projection `Δ_{n+1} → Δ_n` of Step 4.
      Witnesses paper's `lem:defect-compatible`. -/
  proj : ∀ n, defect_level (n + 1) → defect_level n
  /-- The polarity involution σ restricted to depth `n`.
      Step 5 data. -/
  sigma_level : ∀ n, defect_level n → defect_level n
  /-- σ is involutive at every depth: `σ² = id`. -/
  sigma_involutive : ∀ n (x : defect_level n),
    sigma_level n (sigma_level n x) = x
  /-- σ commutes with refinement projection: the key
      compatibility that lifts σ-invariance to the inverse limit. -/
  sigma_commutes_proj : ∀ n (x : defect_level (n + 1)),
    proj n (sigma_level (n + 1) x) = sigma_level n (proj n x)

-- ============================================================
-- PART 2: Threads in the inverse system
-- ============================================================

/-- **A compatible thread** in a `DefectInverseSystem` — a family
    of points, one per depth, with projections respected.

    This is the "points of the inverse limit" concept: an element
    of `lim_n Δ_n` is *by definition* a compatible thread.  The
    rendering in Lean 4 via a `structure` with a `compat` field is
    the constructive form. -/
structure DefectInverseSystem.Thread (D : DefectInverseSystem) where
  /-- The point at each depth `n`. -/
  point : ∀ n, D.defect_level n
  /-- Refinement compatibility: `proj_n(point_{n+1}) = point_n`. -/
  compat : ∀ n, D.proj n (point (n + 1)) = point n

/-- **A σ-fixed compatible thread** — the structural realisation
    of a "σ-invariant point of the inverse limit," which paper §4.2
    calls out as the content of Theorem `defect-sigma-inv`. -/
structure DefectInverseSystem.SigmaFixedThread (D : DefectInverseSystem)
    extends DefectInverseSystem.Thread D where
  /-- The σ-fixedness condition at every depth. -/
  sigma_fixed : ∀ n, D.sigma_level n (point n) = point n

-- ============================================================
-- PART 3: Step 5 σ-invariance theorem (abstract form)
-- ============================================================

/-- **σ-invariance of the defect germ at the abstract level**
    (paper Thm 4.2 / `thm:defect-sigma-inv`).

    Given a thread with σ-fixed points at every depth, the entire
    thread is preserved by σ — a structural manifestation of the
    paper's "passage to the inverse limit preserves σ-invariance"
    claim.  Concretely: applying σ levelwise to a σ-fixed thread
    yields the same thread, which is the inverse-limit-level
    σ-fixedness. -/
theorem DefectInverseSystem.sigma_invariance
    (D : DefectInverseSystem) (t : D.SigmaFixedThread) :
    ∀ n, D.sigma_level n (t.point n) = t.point n :=
  t.sigma_fixed

/-- **σ-commutes-with-projection preserves thread compatibility**
    (structural form of paper §4.2's closing line: "passage to
    the inverse limit preserves this invariance since projections
    commute with σ"). -/
theorem DefectInverseSystem.sigma_thread_compatible
    (D : DefectInverseSystem) (t : D.Thread) (n : Nat) :
    D.proj n (D.sigma_level (n + 1) (t.point (n + 1)))
      = D.sigma_level n (t.point n) := by
  rw [D.sigma_commutes_proj]
  rw [t.compat]

-- ============================================================
-- PART 4: NP / OA predicates (paper §5 halves)
-- ============================================================

/-- **Non-polarity predicate** (paper §5.2 NP half setup).

    At the structural level we package NP as *paper-faithful but
    minimal*: a thread is non-polar if at every depth `n ≥ 1` it
    admits a maturity-index structure (the paper's `n_⋆(G)`).  For
    the abstract scaffold we simply require the existence of a
    natural number `maturity_depth` beyond which the thread is
    "crossing-anchored" — represented as a Prop-level witness
    `is_crossing_anchored_beyond : ∀ n ≥ maturity_depth, ...`.

    The concrete `..."crossing anchor" ...` is geometric content;
    we abstract over it via an external predicate `anchor` the
    user supplies. -/
def DefectInverseSystem.IsNonPolar
    {D : DefectInverseSystem}
    (anchor : ∀ n, D.defect_level n → Prop)
    (t : D.SigmaFixedThread) : Prop :=
  ∃ maturity_depth : Nat,
    ∀ n : Nat, maturity_depth ≤ n → anchor n (t.point n)

/-- **ω-approaching predicate** (paper §5.3 OA half setup).

    A thread is ω-approaching if its meta-witness-depth orbit
    under the abstract `HolEnd_τ` action is bounded.  At the
    structural level we abstract `HolEnd_τ` as a user-supplied
    action-like function and package boundedness as the
    existence of a uniform bound. -/
def DefectInverseSystem.IsOmegaApproaching
    {D : DefectInverseSystem}
    (mwd : D.SigmaFixedThread → Nat)
    (t : D.SigmaFixedThread) : Prop :=
  ∃ bound : Nat, mwd t ≤ bound

/-- **Crossing-point characterisation** (paper Thm 5.5
    intersection).  A thread is a "crossing-point germ" if it
    lies in both NP and OA. -/
def DefectInverseSystem.IsCrossingPoint
    {D : DefectInverseSystem}
    (anchor : ∀ n, D.defect_level n → Prop)
    (mwd : D.SigmaFixedThread → Nat)
    (t : D.SigmaFixedThread) : Prop :=
  DefectInverseSystem.IsNonPolar anchor t ∧
  DefectInverseSystem.IsOmegaApproaching mwd t

/-- **Paper §5.5 intersection theorem at the structural level**:
    `NP ∩ OA` is characterised by the `IsCrossingPoint` predicate.

    The paper's Theorem 5.5 `thm:intersection` asserts this is a
    singleton `{G_×}`.  At the abstract structural level we render
    the *characterisation* (iff form); the singleton claim
    requires the specific NP/OA instances derived from the paper's
    geometric lobe-lattice + meta-witness-depth machinery, which
    is deferred to future waves with that infrastructure.

    Future waves can supply concrete `anchor` and `mwd` such that
    NP ∩ OA is provably a singleton. -/
theorem DefectInverseSystem.intersection_iff
    {D : DefectInverseSystem}
    (anchor : ∀ n, D.defect_level n → Prop)
    (mwd : D.SigmaFixedThread → Nat)
    (t : D.SigmaFixedThread) :
    DefectInverseSystem.IsCrossingPoint anchor mwd t ↔
    (DefectInverseSystem.IsNonPolar anchor t ∧
     DefectInverseSystem.IsOmegaApproaching mwd t) :=
  Iff.rfl

-- ============================================================
-- PART 5: Concrete toy instance (sanity check)
-- ============================================================

/-- **Trivial 1-element defect system**: `Δ_n = Unit` at every depth,
    with trivial projection and σ-involution.  A sanity check that
    the scaffold compiles and that the σ-invariance theorem fires.

    All compatibility, involutivity, and commutation conditions
    are trivially satisfied because the target type is `Unit`. -/
def TrivialDefectSystem : DefectInverseSystem where
  defect_level := fun _ => Unit
  proj := fun _ _ => ()
  sigma_level := fun _ _ => ()
  sigma_involutive := fun _ _ => rfl
  sigma_commutes_proj := fun _ _ => rfl

/-- The unique thread in the trivial system. -/
def TrivialDefectSystem.trivialThread :
    DefectInverseSystem.SigmaFixedThread TrivialDefectSystem where
  point := fun _ => ()
  compat := fun _ => rfl
  sigma_fixed := fun _ => rfl

/-- **σ-invariance theorem fires on the trivial instance**: a sanity
    check that the abstract scaffold compiles all the way through. -/
theorem trivial_sigma_invariance (n : Nat) :
    TrivialDefectSystem.sigma_level n
      (TrivialDefectSystem.trivialThread.point n)
      = TrivialDefectSystem.trivialThread.point n :=
  DefectInverseSystem.sigma_invariance TrivialDefectSystem
    TrivialDefectSystem.trivialThread n

-- ============================================================
-- PART 6: Bridge to Wave 7 CrossingPointDefectGerm
-- ============================================================

/-- **Scalar readout functor on threads** — the abstract form of
    paper's `ReadF : defect-germ → Scalar`.

    Given a thread `t` and a levelwise readout function
    `readout_level : ∀ n, D.defect_level n → TauRat`, the thread's
    scalar readout is the sequence of per-level readouts.  For
    Cauchy-convergent systems this sequence gives a `TauReal`
    approximation. -/
def DefectInverseSystem.threadReadout
    (D : DefectInverseSystem)
    (readout_level : ∀ n, D.defect_level n → TauRat)
    (t : D.Thread) : Nat → TauRat :=
  fun n => readout_level n (t.point n)

/-- **Bridge**: every thread readout yields a `TauReal` (wrapping
    the `Nat → TauRat` approximation sequence).  This is the
    structural form of the paper's "scalar readout functor
    `Read_F`." -/
def DefectInverseSystem.threadReadoutTauReal
    (D : DefectInverseSystem)
    (readout_level : ∀ n, D.defect_level n → TauRat)
    (t : D.Thread) : TauReal :=
  ⟨D.threadReadout readout_level t⟩

/-- **Bridge to Wave 7's `CrossingPointDefectGerm`**: a σ-fixed
    thread in a `DefectInverseSystem`, paired with a levelwise
    readout, gives a `CrossingPointDefectGerm` — the Wave 7 type
    capturing the operational scalar-readout side.

    This closes the structural loop: the abstract defect system
    of this module supplies the inverse-system side; Wave 7's
    `CrossingPointDefectGerm` supplies the scalar-readout side;
    the bridge here connects them. -/
def DefectInverseSystem.toCrossingPointDefectGerm
    (D : DefectInverseSystem)
    (readout_level : ∀ n, D.defect_level n → TauRat)
    (t : D.Thread) : CrossingPointDefectGerm where
  approx := D.threadReadout readout_level t
  is_defect_germ := trivial

-- ============================================================
-- PART 7: Connection to Wave 8 OmegaInverseLimit
-- ============================================================

/-- **Structural connection to Wave 8's `OmegaInverseLimit`**:
    given an `OmegaInverseLimit`, we can build a `DefectInverseSystem`
    whose defect levels are unit (vacuous content) but whose
    threading is controlled by the coherent family in the
    inverse-limit element.

    This demonstrates that Wave 8's `OmegaInverseLimit` is
    *structurally comparable* to the `DefectInverseSystem` at the
    inverse-system level, even though their carrier types differ
    (residues mod primorials vs. generic defect levels).  The
    connection is the "inverse-limit coherent family" shape. -/
def OmegaInverseLimit.toDefectThread
    (_omega : OmegaInverseLimit) :
    DefectInverseSystem.Thread TrivialDefectSystem where
  point := fun _ => ()
  compat := fun _ => rfl

-- The `omega` parameter carries residue data which is discarded at
-- the trivial-defect-system level; a non-trivial defect system
-- using `OmegaInverseLimit` residues as its carrier type would
-- preserve that data.  This is recorded as a structural
-- compatibility observation rather than a non-trivial theorem.

-- ============================================================
-- PART 8: §4.4 Theorem 4.7 — Unpolarisation (paper Thm 4.7)
-- ============================================================

/-- **The unpolarisation predicate** (paper §4.4 Theorem 4.7,
    `thm:defect-unpolarised`).

    Paper's claim: `Δ_ω` is genuinely unpolarised — at every
    finite depth `n ≥ 2`, `Δ_n` contains pairs `(b, c)` with
    `b, c` simultaneously non-trivial on both channels.

    **Abstract rendering**: at every depth `n`, the defect level
    contains at least one element that is *not* σ-fixed.  This
    captures the paper's content abstractly: σ swaps the two
    channels (B ↔ C), so a non-σ-fixed element is one with
    *asymmetric* content between the two channels, i.e. an
    obstruction to polarised (single-channel-only) structure.

    **Why this is faithful**: the paper's "(b, c) with both
    channels non-trivial" requires *cross-lobe support*; on a
    σ-acting carrier, cross-lobe content means non-symmetric
    content under the B↔C exchange, which is exactly
    non-σ-fixedness.  Conversely, σ-fixed elements have
    *symmetric* content and so are "polarisation-trivial"
    (they don't witness cross-channel structure).

    **Why we drop the `n ≥ 2` qualifier**: the paper's
    qualifier comes from the τ-circle presentation needing
    non-trivial refinement on both channels, which holds
    `n ≥ 2` by construction.  At the abstract scaffold level
    we work over any depth; on concrete instances (e.g.,
    `TorusDefectSystem`, `RefinementGrowingTorus`) the
    non-polar witnesses exist at every depth uniformly. -/
def DefectInverseSystem.IsUnpolarised (D : DefectInverseSystem) : Prop :=
  ∀ n : Nat, ∃ x : D.defect_level n, D.sigma_level n x ≠ x

/-- **Projection surjectivity** — the paper's "passage to the
    inverse limit preserves this since projections are
    surjective" content, packaged as a structural Prop.

    The paper's Theorem 4.7 proof closes with: "Passage to the
    inverse limit preserves this since projections are
    surjective."  In the abstract scaffold, "passage to the
    inverse limit" is the thread construction; "projections
    are surjective" is this predicate. -/
def DefectInverseSystem.ProjSurjective (D : DefectInverseSystem) : Prop :=
  ∀ n, Function.Surjective (D.proj n)

/-- **Unpolarisation pulls back through projection** — the
    structural content of paper §4.4's "Passage to the inverse
    limit preserves this since projections are surjective."

    Given a non-σ-fixed element `x_n` at depth `n` and surjective
    projection, there exists a preimage `x_succ` at depth `n+1`
    that is *also* non-σ-fixed.

    **Proof structure**: take any preimage of `x_n` under
    surjective projection.  If it were σ-fixed at depth `n+1`,
    then applying `D.proj` and `D.sigma_commutes_proj` would
    yield σ-fixedness of `x_n`, contradiction. -/
theorem DefectInverseSystem.unpolarisation_pulled_back
    (D : DefectInverseSystem) (h_surj : D.ProjSurjective)
    (n : Nat) (x_n : D.defect_level n) (h_x : D.sigma_level n x_n ≠ x_n) :
    ∃ x_succ : D.defect_level (n + 1),
      D.proj n x_succ = x_n ∧ D.sigma_level (n + 1) x_succ ≠ x_succ := by
  obtain ⟨x_succ, h_proj⟩ := h_surj n x_n
  refine ⟨x_succ, h_proj, ?_⟩
  intro h_fixed
  apply h_x
  calc D.sigma_level n x_n
      = D.sigma_level n (D.proj n x_succ) := by rw [h_proj]
    _ = D.proj n (D.sigma_level (n + 1) x_succ) :=
        (D.sigma_commutes_proj n x_succ).symm
    _ = D.proj n x_succ := by rw [h_fixed]
    _ = x_n := h_proj

/-- **Unpolarisation at finite stage**: this is just unfolding
    `IsUnpolarised`, named for clarity to match paper §4.4. -/
theorem DefectInverseSystem.unpolarisation_finite_stage
    {D : DefectInverseSystem} (hD : D.IsUnpolarised) (n : Nat) :
    ∃ x : D.defect_level n, D.sigma_level n x ≠ x :=
  hD n

/-- **An unpolarised thread**: a `Thread` in the inverse system
    whose every depth has a non-σ-fixed point.

    This is the **inverse-limit-level** rendering of paper §4.4:
    a "configuration" (= compatible thread) in `Δ_ω` that
    genuinely fails σ-symmetry at every depth.  Existence of
    such a thread is the inverse-limit form of unpolarisation. -/
structure DefectInverseSystem.UnpolarisedThread (D : DefectInverseSystem)
    extends DefectInverseSystem.Thread D where
  /-- The non-σ-fixedness condition at every depth — paper §4.4
      "non-trivial on both channels" rendered as a per-depth
      non-σ-fixed condition. -/
  not_sigma_fixed : ∀ n, D.sigma_level n (point n) ≠ point n

/-- **An unpolarised thread is the inverse-limit witness for
    Theorem 4.7**: its existence shows the inverse limit
    contains genuinely unpolarised configurations. -/
theorem DefectInverseSystem.unpolarised_thread_witnesses_IsUnpolarised
    {D : DefectInverseSystem} (t : D.UnpolarisedThread) :
    D.IsUnpolarised :=
  fun n => ⟨t.point n, t.not_sigma_fixed n⟩

/-- **Theorem 4.7 (paper `thm:defect-unpolarised`) — abstract
    inverse-limit form.**

    Existence of an unpolarised thread implies `IsUnpolarised`
    at every finite depth (which is the paper's claim "Δ_n
    contains pairs (b,c) non-trivial on both channels at every
    depth"), and the thread itself is the inverse-limit
    `Δ_ω` configuration witnessing the unpolarised structure.

    **What this theorem provides**:
    1. The abstract structural rendering of paper's Theorem 4.7.
    2. A clean separation between the finite-stage statement
       (`IsUnpolarised`, requires only per-depth witnesses)
       and the inverse-limit witness (`UnpolarisedThread`,
       requires coherent thread structure).
    3. The bridge lemma `unpolarisation_pulled_back` showing
       how finite-stage non-polarisation lifts through projection
       — the paper's "projections are surjective" content.

    **What it does NOT provide**:
    - The *specific geometric* witness from the τ-circle
      presentation; that requires combinatorial torus
      infrastructure deferred to future waves.

    For concrete instances (`TorusDefectSystem`,
    `RefinementGrowingTorus`), unpolarised thread witnesses
    are constructed directly without choice — see the
    respective instance files. -/
theorem DefectInverseSystem.unpolarisation_theorem
    (D : DefectInverseSystem) (t : D.UnpolarisedThread) :
    D.IsUnpolarised ∧
    (∀ n, D.sigma_level n (t.point n) ≠ t.point n) :=
  ⟨D.unpolarised_thread_witnesses_IsUnpolarised t, t.not_sigma_fixed⟩

end Tau.Boundary
