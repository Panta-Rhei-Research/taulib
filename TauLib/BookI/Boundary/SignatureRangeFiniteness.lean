import TauLib.BookI.Boundary.PolarisedGerm

/-!
# TauLib.BookI.Boundary.SignatureRangeFiniteness

**Wave B Gap #5.1 fill: paper `iota-tau/main.tex` §5.2 line 1348,
Corollary 5.6 (`cor:signature-range`, finite signature range)
rendered at TauLib level via the established Option-D pattern
(abstract scaffold + concrete witness + honest scope reporting).**

## Paper reference

`papers/research-papers/iota-tau/main.tex`:

- **§5.2 line 1348, Corollary 5.6** (`cor:signature-range`,
  "Finite signature range"):

> The set of σ-signatures
> `{ (ℓ(x_n))_n : (x_n)_n ∈ lim_n Λ[n], (x_n)_n is Swap-fixed }`
> is finite at each depth, and stabilises beyond some finite
> *maturity index* `n_⋆`.

Paper proof sketch (lines 1356–1363):

- **Finite-at-each-depth**: each `Λ[n]` is finite (Book I ch.44
  finite-lattice theorem), so the `Swap_n`-fixed subset is finite,
  and its image under the lobe-labelling `ℓ : Λ[n] → {B, C, ×}` is
  trivially finite (the codomain itself is finite, with three
  elements).
- **Stabilisation**: applies Book III ch.12 normal-form (NF)
  stability theorem to the polarity tower: the σ-NF of a
  `Swap`-fixed thread stabilises at the level where its deepest
  lobe-swap ceases to contribute, which occurs at a finite index
  by finiteness of the signature set.

## 2nd audit memo gap (this module's target)

From `atlas/audits/papers/2026-05-21-iota-tau-paper-V2-2nd-audit-pass.md`:

> **Gap #5.1** (CARRIED FROM 1ST AUDIT — UNCHANGED):
> Corollary 5.6 (signature range finiteness).
> - **Paper location**: §5.2 line 1348, `cor:signature-range`.
> - **Statement**: Σ-signature range is finite at each depth,
>   stabilises at maturity index `n_⋆`.
> - **Existing TauLib backing**: NONE. Cites Book I ch.44
>   finite-lattice + Book III ch.12 NF-stability — neither in TauLib.
> - **Gap classification**: **B (moderate)** — requires Book I ch.44
>   polarity-lattice infrastructure.

## Rendering strategy (Option-D pattern)

Following the established cathedral pattern used in the eight
prior gap fixes (`LobeInvariance.lean`,
`BoundaryInteriorIdentification.lean`, `PolarisedGerm.lean`,
`FiniteNormalisationStructural.lean`, `TauRealKappaOmega.lean`,
`WOmegaTrUniqueness.lean`, `TauExponentialUniversalProperty.lean`):

1. **Abstract scaffold** — paper's "signature at depth `n`" is
   rendered as the `LobeLabel` value of the thread's point at
   depth `n` (under a depth-indexed labelling `L`). The
   "signature range at depth `n`" is then the set of label values
   actually attained by σ-fixed threads at that depth — and since
   `LobeLabel` itself is a finite 3-element inductive, the range
   is automatically a subset of `{B, C, Cross}`, hence finite.

2. **Finite enumeration witness** — the `signatureRangeAtDepth`
   list enumerates `LobeLabel`'s three values explicitly, and
   `signature_range_subset_full_list` proves every value attained
   by a σ-fixed thread at depth `n` lies in this finite list.

3. **Stabilisation predicate** — `SignatureStabilises` captures
   paper's "stabilises beyond maturity index `n_⋆`" as: there
   exists `n_⋆` such that for every `n ≥ n_⋆`, every σ-fixed
   thread's label at depth `n` equals its label at depth `n_⋆`.

4. **Concrete witnesses** — on the static `TorusDefectSystem`,
   the σ-fixed-thread characterisation `crossingThread` forces the
   label to be `Cross` at every depth (paper's L4 anchor rigidity
   instance), so stabilisation holds at `n_⋆ = 0`. On
   `refinementGrowingTorusSystem`, the same anchor-rigidity
   argument fires (every σ-fixed thread is the constant-`crossing`
   thread), again giving stabilisation at `n_⋆ = 0`.

5. **Scope honesty** — paper's "finite-at-each-depth" half is
   structural (true for any finite-label-codomain σ-fixed thread
   space, regardless of the underlying lattice's cardinality at
   depth `n`); paper's NF-stability half is captured at the
   strict-stabilisation level on the toy carriers, where σ-fixed
   threads are constant. The full Book III ch.12 NF-stability
   theorem on the genuine lemniscate polarity tower is deferred
   to a later wave with that infrastructure.

## Trust budget

- `sorry`: **0**.
- Axioms: **kernel-only** (no new axioms; uses only the existing
  `LobeLabel`, `LobeLabelling`, `IsBPolarised`/`IsCPolarised`
  predicates from `PolarisedGerm.lean`, the `DefectInverseSystem`
  scaffold from `DefectInverseSystem.lean`, and the σ-fixed-thread
  characterisations from `TorusDefectSystem.lean` /
  `RefinementGrowingTorus.lean` — all unchanged here).

## Scope

`\scopetau`, **abstract scaffold level**.

What this module **provides**:

1. **`signatureRangeAtDepth`** — the `List LobeLabel` enumerating
   paper's three possible label values `{B, C, Cross}`.
2. **`signature_range_finite_at_each_depth`** — paper Cor 5.6
   first half: at every depth, the σ-fixed thread's signature
   value is one of three possibilities, hence the range is
   finite (bounded by three).
3. **`SignatureStabilises`** — paper Cor 5.6 second half rendered
   as a Prop: there exists a maturity index `n_⋆` past which the
   σ-fixed thread's signature stabilises.
4. **`signatureStabilises_of_anchor_constant`** — abstract lift:
   if every σ-fixed thread is the constant-anchor thread (the
   strict-uniqueness conclusion of paper's L4 anchor rigidity),
   then the signature stabilises at `n_⋆ = 0`.
5. **Concrete witnesses** on `TorusDefectSystem` and
   `refinementGrowingTorusSystem`: paper Cor 5.6 fires
   unconditionally on both toy carriers via the L4 anchor-rigidity
   instance (every σ-fixed thread is the constant-crossing
   thread).

What this module **does NOT provide**:

- The full Book I ch.44 finite-lattice theorem on the genuine
  lemniscate polarity tower `Λ[n]` — what we capture is the
  signature-codomain finiteness (the `LobeLabel` three-element
  type is finite by construction), not the lattice-domain
  finiteness. The latter requires the polarity-lattice
  infrastructure from Book I ch.44 (~600+ LOC for the geometric
  realisation), deferred per audit memo classification "B".
- The full Book III ch.12 NF-stability theorem on the genuine
  lemniscate polarity tower — what we capture is the
  strict-stabilisation form on toy carriers (where σ-fixed
  threads are constant). The geometric NF-stability content is
  paper's "deepest lobe-swap ceases to contribute" line, requiring
  the lobe-lattice geometric realisation from Book I ch.44 plus
  Book III ch.12, deferred per audit memo classification "B".

The structural close of Cor 5.6 at TauLib level means: once a
future wave supplies the geometric `DefectInverseSystem` instance
realising the τ-circle polarity tower with σ acting non-trivially
on the genuine `Λ[n]`, the finite-signature-range claim fires
unconditionally via `signature_range_finite_at_each_depth`, and
the stabilisation claim fires once Book III ch.12 NF-stability is
proved on that instance.

## Public API

- `signatureRangeAtDepth` — paper's "signature range" rendered as
  the 3-element `List LobeLabel`.
- `signature_range_complete` — every `LobeLabel` value is in the
  list (sanity).
- `signature_range_finite_at_each_depth` — paper Cor 5.6 first
  half: for any σ-fixed thread, the label at depth `n` is in
  `signatureRangeAtDepth`.
- `SignatureStabilises` — paper Cor 5.6 second half (predicate).
- `signatureStabilises_of_constant_signature` — abstract lift to
  the strict-constant-signature setting (L4 anchor rigidity
  consequence).
- `signatureStabilises_of_anchor_constant` — abstract lift
  reformulated for the L4 strict-uniqueness output.
- `TorusDefectSystem.signature_range_finite_at_each_depth` —
  concrete witness on static torus.
- `TorusDefectSystem.signature_stabilises` — concrete
  stabilisation witness on static torus.
- `refinementGrowingTorusSystem.signature_range_finite_at_each_depth` —
  concrete witness on the growing carrier.
- `refinementGrowingTorusSystem.signature_stabilises` — concrete
  stabilisation witness on the growing carrier.

## Registry Cross-References

- [I.D125] Tau.Boundary.DefectInverseSystem (Wave 12)
- [I.T-LobeL4] LobeInvariance.LobeL4_uniqueness (Gap #1 fix)
- [I.T-PolUniv] PolarisedGerm.PolarisedUniversalProperty (Gap #3)
- [I.T-Wave-B-Gap-5.1] signature_range_finite_at_each_depth +
  signatureStabilises (this module)
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: paper Cor 5.6 — finite-at-each-depth, signature range
-- ============================================================

/-- **The signature range at any depth** (paper §5.2 line 1349 —
    finite signature range, codomain enumeration).

    Paper text: the set of σ-signatures
    `{ (ℓ(x_n))_n : (x_n)_n ∈ lim_n Λ[n], (x_n)_n is Swap-fixed }`.

    At any fixed depth `n`, the signature value `ℓ(x_n)` lies in
    `{B, C, ×}` (the codomain of the lobe-labelling). We render
    "the signature range at depth `n`" by enumerating these three
    possibilities explicitly — independent of the underlying
    polarity lattice `Λ[n]`, which is paper-only infrastructure.

    This is paper Cor 5.6's first half at the codomain level:
    finiteness is automatic from `LobeLabel`'s three-constructor
    inductive definition, irrespective of `Λ[n]`'s cardinality. -/
def signatureRangeAtDepth : List LobeLabel :=
  [LobeLabel.B, LobeLabel.C, LobeLabel.Cross]

/-- **The signature range list has length three** — direct from
    the definition. -/
@[simp] theorem signatureRangeAtDepth_length :
    signatureRangeAtDepth.length = 3 := rfl

/-- **Every `LobeLabel` appears in `signatureRangeAtDepth`** —
    sanity that the enumeration is exhaustive. -/
theorem signature_range_complete (l : LobeLabel) :
    l ∈ signatureRangeAtDepth := by
  cases l
  · exact List.mem_cons_self ..
  · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))

/-- **Paper Cor 5.6 first half (finite-at-each-depth, structural
    form)**: for any defect inverse system `D`, any depth-indexed
    lobe-labelling `L`, any thread `t : D.Thread`, and any depth
    `n`, the label of `t` at depth `n` lies in the finite list
    `signatureRangeAtDepth`.

    Paper text (lines 1356–1358): "each `Λ[n]` is finite (Book I
    ch.44 finite-lattice theorem), so the `Swap_n`-fixed subset
    is finite."

    Our structural rendering: the finiteness is automatic because
    the codomain of the labelling is the 3-element `LobeLabel`
    inductive type. We do NOT need finiteness of `Λ[n]` itself
    (paper's domain-side claim) — the σ-signature is a function
    landing in `LobeLabel`, so its image is bounded by the
    3-element codomain.

    This is the structural strengthening: paper's argument routes
    through domain-finiteness (`Λ[n]` finite by Book I ch.44), but
    the conclusion (signature-range finite) follows just from
    codomain-finiteness, which is automatic at TauLib level. -/
theorem signature_range_finite_at_each_depth
    {D : DefectInverseSystem}
    (L : ∀ n, D.LobeLabelling n) (t : D.Thread) (n : Nat) :
    (L n).label (t.point n) ∈ signatureRangeAtDepth :=
  signature_range_complete _

/-- **Paper Cor 5.6 first half, σ-fixed-thread form**: the
    signature at depth `n` of any σ-fixed thread lies in the
    finite range list.

    Paper's "σ-fixed signatures" subset is a special case of the
    general signature-range claim: the same codomain-finiteness
    argument applies. This is the form paper Cor 5.6 stresses
    (σ-fixed threads as the index set). -/
theorem signature_range_finite_at_each_depth_sigma_fixed
    {D : DefectInverseSystem}
    (L : ∀ n, D.LobeLabelling n) (t : D.SigmaFixedThread) (n : Nat) :
    (L n).label (t.point n) ∈ signatureRangeAtDepth :=
  signature_range_complete _

-- ============================================================
-- PART 2: paper Cor 5.6 — signature stabilisation predicate
-- ============================================================

/-- **Signature stabilisation predicate** (paper Cor 5.6 second
    half, `cor:signature-range`).

    Paper text (line 1352–1353): "stabilises beyond some finite
    *maturity index* `n_⋆`."

    Structural rendering: a thread's signature *stabilises* iff
    there exists a depth `n_⋆` past which the label at every
    depth `n ≥ n_⋆` agrees with the label at `n_⋆`.

    This matches paper's "the σ-NF of a `Swap`-fixed thread
    stabilises at the level where its deepest lobe-swap ceases to
    contribute" (line 1361–1363): beyond `n_⋆`, the signature is
    a constant sequence. -/
def SignatureStabilises
    {D : DefectInverseSystem}
    (L : ∀ n, D.LobeLabelling n) (t : D.Thread) : Prop :=
  ∃ n_star : Nat,
    ∀ n : Nat, n_star ≤ n →
      (L n).label (t.point n) = (L n_star).label (t.point n_star)

/-- **Signature stabilisation for σ-fixed threads** — the
    paper-faithful instantiation. Same definition as
    `SignatureStabilises` but on `SigmaFixedThread`, matching paper
    Cor 5.6's "for `Swap`-fixed threads" quantifier. -/
def SignatureStabilisesSigmaFixed
    {D : DefectInverseSystem}
    (L : ∀ n, D.LobeLabelling n) (t : D.SigmaFixedThread) : Prop :=
  SignatureStabilises L t.toThread

/-- **Reflexivity of `SignatureStabilises`** — every thread
    trivially stabilises at `n_star := 0` if and only if its
    signature is constant from depth `0` onward. This is the
    paper-strict case `n_⋆ = 1` (paper uses 1-indexed depths;
    Lean uses 0-indexed).

    More general: any thread whose signature is eventually
    constant stabilises in our sense. -/
theorem signatureStabilises_of_eventually_constant
    {D : DefectInverseSystem}
    (L : ∀ n, D.LobeLabelling n) (t : D.Thread)
    (n_star : Nat)
    (h_const : ∀ n : Nat, n_star ≤ n →
      (L n).label (t.point n) = (L n_star).label (t.point n_star)) :
    SignatureStabilises L t :=
  ⟨n_star, h_const⟩

-- ============================================================
-- PART 3: Abstract lift — anchor-constant ⇒ stabilises
-- ============================================================

/-- **Anchor-constant signature lift to stabilisation**: if the
    thread's signature is identically `Cross` at every depth, then
    the signature stabilises (trivially, at `n_star = 0`).

    Paper's L4 anchor rigidity (`AnchorRigidity.uniqueness`) gives
    that every σ-fixed thread is constant-anchored on any carrier
    with a rigid anchor, forcing its signature to be `Cross` at
    every depth. This abstract lemma packages the lift from
    "always Cross" to `SignatureStabilises`. -/
theorem signatureStabilises_of_constant_cross
    {D : DefectInverseSystem}
    (L : ∀ n, D.LobeLabelling n) (t : D.Thread)
    (h_cross : ∀ n : Nat, (L n).label (t.point n) = LobeLabel.Cross) :
    SignatureStabilises L t := by
  refine ⟨0, ?_⟩
  intro n _
  rw [h_cross n, h_cross 0]

/-- **Anchor-constant signature lift (general form)**: if the
    thread's signature is identically `l` at every depth (for any
    fixed `l : LobeLabel`), then the signature stabilises at
    `n_star = 0`.

    Generalises `signatureStabilises_of_constant_cross` to
    arbitrary constant labels. -/
theorem signatureStabilises_of_constant_label
    {D : DefectInverseSystem}
    (L : ∀ n, D.LobeLabelling n) (t : D.Thread)
    (l : LobeLabel)
    (h_const : ∀ n : Nat, (L n).label (t.point n) = l) :
    SignatureStabilises L t := by
  refine ⟨0, ?_⟩
  intro n _
  rw [h_const n, h_const 0]

/-- **Anchor-constant thread lift**: if the thread's points are
    identically the anchor at every depth (i.e., `t.point n =
    (L n).anchor` for all `n`), then the signature stabilises.

    This is the form most directly applicable to the L4 strict-
    uniqueness output: paper's "every σ-fixed thread is constant-
    anchored" + anchor's `Cross` label ⇒ signature is constant-
    `Cross` ⇒ stabilises at depth `0`. -/
theorem signatureStabilises_of_anchor_constant
    {D : DefectInverseSystem}
    (L : ∀ n, D.LobeLabelling n) (t : D.Thread)
    (h_anchor : ∀ n : Nat, t.point n = (L n).anchor) :
    SignatureStabilises L t := by
  apply signatureStabilises_of_constant_cross
  intro n
  rw [h_anchor n, (L n).anchor_label]

-- ============================================================
-- PART 4: paper Cor 5.6 — combined statement
-- ============================================================

/-- **Paper Corollary 5.6 (signature range finiteness),
    abstract structural form.**

    Bundles paper Cor 5.6's two clauses:

    (i) **Finite at each depth**: the σ-signature at depth `n` of
        any σ-fixed thread lies in the 3-element finite range
        `signatureRangeAtDepth`.

    (ii) **Stabilisation at maturity index**: there exists `n_⋆`
        past which the σ-signature is constant.

    Clause (i) is unconditional at the TauLib level (codomain-
    finiteness of the labelling). Clause (ii) requires a
    stabilisation witness, supplied either by the abstract
    L4-anchor-constant lift or by concrete instance arguments.

    This packages paper Cor 5.6 as a Prop-structure suitable for
    consumers of the finite-signature-range fact. -/
structure SignatureRangeFiniteness
    {D : DefectInverseSystem}
    (L : ∀ n, D.LobeLabelling n) (t : D.Thread) : Prop where
  /-- (i) Finiteness at each depth (paper Cor 5.6 first half). -/
  finite_at_depth : ∀ n : Nat,
    (L n).label (t.point n) ∈ signatureRangeAtDepth
  /-- (ii) Stabilisation at maturity index (paper Cor 5.6 second
      half). -/
  stabilises : SignatureStabilises L t

/-- **Constructor: any thread whose signature is constant-`Cross`
    satisfies `SignatureRangeFiniteness`.**

    This packages the L4-anchor-rigidity lift through both clauses
    in one go. -/
theorem signatureRangeFiniteness_of_constant_cross
    {D : DefectInverseSystem}
    (L : ∀ n, D.LobeLabelling n) (t : D.Thread)
    (h_cross : ∀ n : Nat, (L n).label (t.point n) = LobeLabel.Cross) :
    SignatureRangeFiniteness L t where
  finite_at_depth _ := signature_range_complete _
  stabilises := signatureStabilises_of_constant_cross L t h_cross

/-- **Constructor: any thread whose points are identically the
    anchor satisfies `SignatureRangeFiniteness`.**

    The directly L4-applicable form: paper's anchor-rigid carriers
    have every σ-fixed thread satisfying `t.point n = (L n).anchor`,
    which discharges both clauses through this constructor. -/
theorem signatureRangeFiniteness_of_anchor_constant
    {D : DefectInverseSystem}
    (L : ∀ n, D.LobeLabelling n) (t : D.Thread)
    (h_anchor : ∀ n : Nat, t.point n = (L n).anchor) :
    SignatureRangeFiniteness L t where
  finite_at_depth _ := signature_range_complete _
  stabilises := signatureStabilises_of_anchor_constant L t h_anchor

end Tau.Boundary

-- ============================================================
-- PART 5: Concrete instance — TorusDefectSystem
-- ============================================================

namespace Tau.Boundary

open Tau.Denotation

/-- **Helper: σ-fixed-thread points on `TorusDefectSystem` are
    constantly `crossing`** — follows from `TorusDefect`'s
    σ-fixed-iff-crossing characterisation.

    Paper's L4 anchor rigidity instance: `TorusDefect.crossing` is
    the unique σ-fixed defect element, so every σ-fixed thread's
    point at every depth equals `crossing` (which is the anchor of
    `TorusDefectSystem.lobeLabelling`). -/
theorem TorusDefectSystem.sigma_fixed_thread_points_crossing
    (t : TorusDefectSystem.SigmaFixedThread) (n : Nat) :
    t.point n = TorusDefect.crossing := by
  -- From `sigma_fixed`, the point is σ-fixed at every depth.
  have h_fix : TorusDefect.sigmaSwap (t.point n) = t.point n := t.sigma_fixed n
  exact (TorusDefect.sigma_fixed_iff_crossing (t.point n)).mp h_fix

/-- **Paper Cor 5.6 (signature range finiteness) on
    `TorusDefectSystem`** — finite-at-each-depth half.

    Concrete witness: for any thread `t : TorusDefectSystem.Thread`
    and any depth `n`, the label `(L n).label (t.point n)` lies in
    the 3-element finite range `signatureRangeAtDepth`. This is
    automatic from the codomain-finiteness of
    `TorusDefectSystem.lobeLabelling`. -/
theorem TorusDefectSystem.signature_range_finite_at_each_depth
    (t : DefectInverseSystem.Thread TorusDefectSystem) (n : Nat) :
    (TorusDefectSystem.lobeLabelling n).label (t.point n) ∈
      signatureRangeAtDepth :=
  Tau.Boundary.signature_range_finite_at_each_depth
    TorusDefectSystem.lobeLabelling t n

/-- **Paper Cor 5.6 stabilisation half on `TorusDefectSystem`** —
    on σ-fixed threads.

    Since σ-fixed threads on `TorusDefectSystem` are constant-
    `crossing` (paper's L4 anchor rigidity instance), their
    signatures are constant-`Cross` from depth `0` onward, hence
    stabilise at `n_⋆ = 0`. -/
theorem TorusDefectSystem.signature_stabilises
    (t : TorusDefectSystem.SigmaFixedThread) :
    SignatureStabilises TorusDefectSystem.lobeLabelling t.toThread := by
  apply signatureStabilises_of_constant_cross
  intro n
  -- `t.point n = crossing` from σ-fixed characterisation;
  -- `lobeLabel crossing = .Cross` by definition.
  show TorusDefect.lobeLabel (t.point n) = LobeLabel.Cross
  rw [TorusDefectSystem.sigma_fixed_thread_points_crossing t n]
  rfl

/-- **Paper Cor 5.6 combined on `TorusDefectSystem`** —
    `SignatureRangeFiniteness` witness for any σ-fixed thread.

    Concrete demonstration that paper Cor 5.6 fires unconditionally
    on the static-torus instance: both clauses (finite-at-depth and
    stabilisation) hold via the L4 anchor-rigidity argument
    (σ-fixed threads are constant-`crossing`). -/
theorem TorusDefectSystem.signature_range_finiteness
    (t : TorusDefectSystem.SigmaFixedThread) :
    SignatureRangeFiniteness TorusDefectSystem.lobeLabelling
      t.toThread :=
  signatureRangeFiniteness_of_constant_cross
    TorusDefectSystem.lobeLabelling t.toThread
    (fun n => by
      show TorusDefect.lobeLabel (t.point n) = LobeLabel.Cross
      rw [TorusDefectSystem.sigma_fixed_thread_points_crossing t n]
      rfl)

end Tau.Boundary

-- ============================================================
-- PART 6: Concrete instance — refinementGrowingTorusSystem
-- ============================================================

namespace Tau.Boundary

open Tau.Denotation

/-- **Helper: σ-fixed-thread points on
    `refinementGrowingTorusSystem` are constantly `crossing`** —
    follows from `RefinedTorusDefect`'s σ-fixed-iff-crossing
    characterisation.

    Paper's L4 anchor rigidity instance on the growing carrier:
    `RefinedTorusDefect.crossing` is the unique σ-fixed defect
    element at every depth, so every σ-fixed thread's point at
    every depth equals `crossing` (= the anchor of
    `refinementGrowingTorusSystem.lobeLabelling`). -/
theorem refinementGrowingTorusSystem.sigma_fixed_thread_points_crossing
    (t : refinementGrowingTorusSystem.SigmaFixedThread) (n : Nat) :
    t.point n = RefinedTorusDefect.crossing := by
  have h_fix : RefinedTorusDefect.sigmaSwap (t.point n) = t.point n :=
    t.sigma_fixed n
  exact (RefinedTorusDefect.sigma_fixed_iff_crossing (t.point n)).mp h_fix

/-- **Paper Cor 5.6 (signature range finiteness) on
    `refinementGrowingTorusSystem`** — finite-at-each-depth half.

    Concrete witness: for any thread on the geometrically-growing
    carrier and any depth `n`, the label lies in the 3-element
    finite range `signatureRangeAtDepth`. This is automatic from
    the codomain-finiteness of
    `refinementGrowingTorusSystem.lobeLabelling`, independent of
    the (geometrically growing) cardinality of
    `RefinedTorusDefect n`. -/
theorem refinementGrowingTorusSystem.signature_range_finite_at_each_depth
    (t : DefectInverseSystem.Thread refinementGrowingTorusSystem) (n : Nat) :
    (refinementGrowingTorusSystem.lobeLabelling n).label (t.point n) ∈
      signatureRangeAtDepth :=
  Tau.Boundary.signature_range_finite_at_each_depth
    refinementGrowingTorusSystem.lobeLabelling t n

/-- **Paper Cor 5.6 stabilisation half on
    `refinementGrowingTorusSystem`** — on σ-fixed threads.

    Same L4 anchor-rigidity argument as on `TorusDefectSystem`:
    σ-fixed threads are constant-`crossing`, signatures are
    constant-`Cross`, stabilisation at `n_⋆ = 0`. -/
theorem refinementGrowingTorusSystem.signature_stabilises
    (t : refinementGrowingTorusSystem.SigmaFixedThread) :
    SignatureStabilises refinementGrowingTorusSystem.lobeLabelling
      t.toThread := by
  apply signatureStabilises_of_constant_cross
  intro n
  show RefinedTorusDefect.lobeLabel (t.point n) = LobeLabel.Cross
  rw [refinementGrowingTorusSystem.sigma_fixed_thread_points_crossing t n]
  rfl

/-- **Paper Cor 5.6 combined on `refinementGrowingTorusSystem`** —
    `SignatureRangeFiniteness` witness for any σ-fixed thread.

    Concrete demonstration that paper Cor 5.6 fires unconditionally
    on the geometrically-growing carrier: both clauses fire via
    the L4 anchor-rigidity argument (σ-fixed threads are constant-
    `crossing`), exhibiting the abstract scaffold's bite on a
    non-trivial carrier where each `RefinedTorusDefect n` is itself
    of growing cardinality `2n + 3`. -/
theorem refinementGrowingTorusSystem.signature_range_finiteness
    (t : refinementGrowingTorusSystem.SigmaFixedThread) :
    SignatureRangeFiniteness refinementGrowingTorusSystem.lobeLabelling
      t.toThread :=
  signatureRangeFiniteness_of_constant_cross
    refinementGrowingTorusSystem.lobeLabelling t.toThread
    (fun n => by
      show RefinedTorusDefect.lobeLabel (t.point n) = LobeLabel.Cross
      rw [refinementGrowingTorusSystem.sigma_fixed_thread_points_crossing t n]
      rfl)

end Tau.Boundary
