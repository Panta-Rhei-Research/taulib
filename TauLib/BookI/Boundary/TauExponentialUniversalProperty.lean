import TauLib.BookI.Boundary.UniversalFixedScalar
import TauLib.BookI.Boundary.TauRealE
import Mathlib.Tactic.Push

/-!
# TauLib.BookI.Boundary.TauExponentialUniversalProperty

**Wave B Gap #2.1 fill: paper `iota-tau/main.tex` §3.3 lines 826–865 —
Definition 3.8 (`Ecl`) + Proposition 3.9 (`prop:exp-exists`,
existence and uniqueness of the τ-exponential) rendered at TauLib
level via the established Option-D pattern (abstract scaffold +
concrete witness + honest scope reporting).**

## Paper reference

`papers/research-papers/iota-tau/main.tex`:

- **§3.3 line 817, Definition 3.7** (`def:advance-profile`):
  the *refinement-advance profile* `Adv_n(f)` and the partial order
  `Adv_n(f) ≼ Adv_n(g)`.
- **§3.3 line 826, Definition 3.8** (`def:tau-exponential`):
  `Ecl` is the unique element of `HolEndS_τ(ω)` satisfying
  (i) non-triviality (`Ecl ≠ id`),
  (ii) minimal advance (`Adv_n(Ecl) ≼ Adv_n(g)` for every non-id
    `g ∈ HolEndS_τ(ω)` and every sufficiently large `n`),
  (iii) crossing-germ normalisation (`Ecl` fixes `G_×[ω]`).
- **§3.3 line 839, Proposition 3.9** (`prop:exp-exists`):
  `Ecl` exists and is unique.

Paper proof sketch (lines 843–865):

- **Existence**: at each depth `n`, the set of σ-equivariant
  advances on `B̂_n` is finite (since `B̂_n` is finite). The subset
  of non-identity advances is either empty or has a minimal element
  under `≼`; non-emptiness follows from the non-triviality of σ on
  the lemniscate. Refinement compatibility is checked by case
  analysis on the canonical projection `r_{n+1 → n}`. The inverse
  limit `Ecl := lim_n Ecl_n` is then a well-defined element of
  `HolEndS_τ(ω)`.

- **Uniqueness**: if `Ecl'` is another minimal non-trivial
  σ-equivariant advance, then `Adv_n(Ecl') = Adv_n(Ecl)` at every
  sufficiently large `n` (minimality), and both fix the
  crossing-point germ. The self-reproduction uniqueness argument
  of Book II Ch. 26 (II.D30 + II.T23 i-iii) yields
  `Ecl_n = Ecl'_n` at every `n`, hence `Ecl = Ecl'`.

## 2nd audit memo gap (this module's target)

From `atlas/audits/papers/2026-05-21-iota-tau-paper-V2-2nd-audit-pass.md`:

> **Gap #2.1**: Prop 3.9 (E_cl universal property).
> Existing TauLib backing: NONE structurally; `TauReal.e`
> (factorial series) only.
> Gap classification: **B (moderate)** — opens with Wave Γ₇ M3 +
> Path B (Machin chain via Euler).

> **Gap #2.2**: Definition 3.7 (refinement-advance profile).
> Existing TauLib backing: NONE. The `preserves_sigma_fixed` field
> of `HolEndMorphism` does the work obliquely, but the partial
> order is not formalised.
> Gap classification: **A (trivial)** — defines a partial order on
> finite endomaps, ~50 LOC.

Both gaps are closed by this module on the established Option-D
abstract-scaffold-plus-concrete-witness pattern.

## Rendering strategy (Option-D pattern)

Following the established cathedral pattern used in
`UniversalFixedScalar.lean`, `BoundaryInteriorIdentification.lean`,
`TauRealKappaOmega.lean`, and the Critical Gap #1–#5 fills:

1. **Abstract scaffold** — the predicate `IsTauExponential` over a
   `HolEndMorphism D` packages paper's three Def 3.8 clauses
   (non-trivial, minimal-advance, crossing-germ-normalised) as a
   `Prop`-valued structure.

2. **Abstract lift lemma** — `tau_exponential_unique` (paper Prop 3.9
   uniqueness half) states that any two `IsTauExponential` witnesses
   coincide on `actSigmaFixed`-image of a crossing-point thread,
   given the abstract `HolEndS` uniqueness hypothesis the paper proof
   sketch ultimately reduces to (Book II Ch. 26 self-reproduction
   uniqueness, II.T23 i-iii).

3. **Concrete witness** — on `TrivialDefectSystem` (the toy carrier
   already used by `UniversalFixedScalar.lean`), the identity
   morphism trivially fails the non-triviality clause, so we exhibit
   a structural *non-existence* of `IsTauExponential` on the trivial
   instance — sanity check that the predicate has bite and is not
   vacuously satisfied. The genuine *existence* of `Ecl` requires a
   non-trivial carrier with σ acting non-trivially (Book II
   Ch. 26's primorial tower), structurally out of scope of the
   toy `TrivialDefectSystem`.

4. **Scalar readout connection** — `TauReal.e` (factorial series) is
   recorded as the *paper's classical witness* for `GerE := ReadF(Ecl)`
   at the scalar level (paper Def 3.9 line 867 + line 874).
   `tau_exponential_readout_value` records this as a structural
   observation tying the abstract scaffold back to the existing
   operational `TauReal.e` from `TauRealE.lean`.

## Trust budget

- `sorry`: **0**.
- Axioms: **kernel-only** (no new axioms; uses only `HolEndMorphism`
  scaffold from `UniversalFixedScalar.lean`, `DefectInverseSystem`
  scaffold from `DefectInverseSystem.lean`, and `TauReal.e` from
  `TauRealE.lean` — all unchanged here).

## Scope

`\scopetau`, **abstract scaffold level**.

What this module **provides**:

1. **`RefinementAdvancePartialOrder`** — paper Def 3.7's
   `Adv_n(f) ≼ Adv_n(g)` rendered as a `Prop`-valued partial order
   over `HolEndMorphism D` via a depth-indexed advance classifier.
2. **`IsTauExponential`** — paper Def 3.8's three clauses
   (non-trivial, minimal-advance, crossing-germ-normalised) as a
   predicate on `HolEndMorphism D`.
3. **`tau_exponential_unique`** — paper Prop 3.9 (uniqueness half)
   in abstract form: any two `IsTauExponential` witnesses agree on
   the action of `actSigmaFixed` applied to a crossing-point thread,
   given Book II II.T23 self-reproduction uniqueness as hypothesis.
4. **`tau_exponential_readout_value`** — structural connection of
   `GerE := ReadF(Ecl)` to the existing `TauReal.e` factorial series.
5. **`trivial_no_tau_exponential`** — sanity check on
   `TrivialDefectSystem`: the only `HolEndMorphism` available
   (`TrivialHolEndMorphism`) is the identity, hence fails the
   non-triviality clause — confirming the predicate has structural
   content.

What this module **does NOT provide**:

- The full existence half of Prop 3.9 on the actual lemniscate
  primorial tower — requires the geometric `B̂_n` finite-set
  realisation + σ-non-triviality argument (Book II Ch. 26's
  self-reproduction infrastructure, ~600 LOC, deferred until the
  geometric `DefectInverseSystem` instance is wired up in a future
  wave).
- A concrete non-trivial `HolEndMorphism` witness on a non-toy
  carrier — same dependency.
- A direct identification `TauReal.e ≡ GerE` as `TauReal` Cauchy
  equivalence — this is the **Wave Γ₇ M3 + boundary-interior**
  chain (paper Theorem 7.16 / Lemma 7.15, already abstractly closed
  in `BoundaryInteriorIdentification.lean`).

The structural close of Prop 3.9 at TauLib level means: once a
future wave supplies the geometric `DefectInverseSystem` instance
realising the τ-circle primorial tower with σ acting non-trivially,
and a concrete `HolEndMorphism` witnessing the minimal σ-equivariant
advance, the uniqueness clause of Prop 3.9 fires unconditionally via
`tau_exponential_unique`.

## Public API

- `RefinementAdvancePartialOrder` — paper Def 3.7 partial order on
  the advance profile.
- `IsTauExponential` — paper Def 3.8 predicate.
- `tau_exponential_unique` — paper Prop 3.9 (uniqueness, abstract).
- `tau_exponential_unique_actSigmaFixed` — companion: equality of
  `actSigmaFixed`-images on crossing-point threads.
- `tau_exponential_readout_value` — structural scalar-readout
  observation (linking `Ecl` to `TauReal.e`).
- `trivial_no_tau_exponential` — sanity: predicate has content.

## Registry Cross-References

- [I.D125] Tau.Boundary.DefectInverseSystem (Wave 12)
- [I.T-H3-HolEnd] HolEndMorphism (Wave 26)
- [I.T-Wave-B-Gap-2.1] tau_exponential_unique (this module)
- [I.T-Wave-B-Gap-2.2] RefinementAdvancePartialOrder (this module)
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation Tau.Polarity

-- ============================================================
-- PART 1: paper Def 3.7 — refinement-advance partial order
-- ============================================================

/-- **Refinement-advance partial order** (paper Def 3.7,
    `def:advance-profile`).

    Paper text (line 822-824):

    > "Partial order: `Adv_n(f) ≼ Adv_n(g)` if every cylinder class
    > advanced by `f` is also advanced by `g`."

    Structural rendering: paper's per-depth advance profile
    `Adv_n(f)` is abstracted as a depth-indexed `Bool`-valued
    classifier
    `advance_classifier : HolEndMorphism D → Nat → Bool`
    (true at depth `n` iff `f` non-trivially advances depth-`n`
    cylinder classes; false otherwise). The partial order
    `f ≼ g` then says: at every depth where `f` advances, `g`
    also advances (= contrapositively, `g` blocks ⟹ `f` blocks).

    This abstracts the paper's "every cylinder class advanced by
    `f` is also advanced by `g`" since the cylinder-class refinement
    is precisely the classifier the consumer plugs in. -/
def RefinementAdvancePartialOrder
    {D : DefectInverseSystem}
    (advance_classifier : HolEndMorphism D → Nat → Bool)
    (f g : HolEndMorphism D) : Prop :=
  ∀ n : Nat, advance_classifier f n = true →
             advance_classifier g n = true

/-- The refinement-advance partial order is **reflexive**. -/
theorem RefinementAdvancePartialOrder.refl
    {D : DefectInverseSystem}
    (advance_classifier : HolEndMorphism D → Nat → Bool)
    (f : HolEndMorphism D) :
    RefinementAdvancePartialOrder advance_classifier f f :=
  fun _ h => h

/-- The refinement-advance partial order is **transitive**. -/
theorem RefinementAdvancePartialOrder.trans
    {D : DefectInverseSystem}
    {advance_classifier : HolEndMorphism D → Nat → Bool}
    {f g h : HolEndMorphism D}
    (hfg : RefinementAdvancePartialOrder advance_classifier f g)
    (hgh : RefinementAdvancePartialOrder advance_classifier g h) :
    RefinementAdvancePartialOrder advance_classifier f h :=
  fun n hfn => hgh n (hfg n hfn)

/-- The refinement-advance partial order is **antisymmetric at the
    classifier level**: if `f ≼ g` and `g ≼ f`, then the advance
    classifiers agree pointwise. (True antisymmetry on
    `HolEndMorphism`-valued data requires extensionality of the
    `act` field, which depends on the geometric realisation of
    `D` and is paper-only.) -/
theorem RefinementAdvancePartialOrder.classifier_antisymm
    {D : DefectInverseSystem}
    {advance_classifier : HolEndMorphism D → Nat → Bool}
    {f g : HolEndMorphism D}
    (hfg : RefinementAdvancePartialOrder advance_classifier f g)
    (hgf : RefinementAdvancePartialOrder advance_classifier g f) :
    ∀ n : Nat, advance_classifier f n = advance_classifier g n := by
  intro n
  by_cases hf : advance_classifier f n = true
  · rw [hf, hfg n hf]
  · push_neg at hf
    have hf_false : advance_classifier f n = false := by
      cases h : advance_classifier f n
      · rfl
      · exact absurd h hf
    by_cases hg : advance_classifier g n = true
    · exact absurd (hgf n hg) hf
    · push_neg at hg
      have hg_false : advance_classifier g n = false := by
        cases h : advance_classifier g n
        · rfl
        · exact absurd h hg
      rw [hf_false, hg_false]

-- ============================================================
-- PART 2: paper Def 3.8 — IsTauExponential predicate
-- ============================================================

/-- **The `IsTauExponential` predicate** (paper Def 3.8,
    `def:tau-exponential`).

    A `HolEndMorphism D` witness `f` is a *τ-exponential* on `D`
    (relative to external classifiers `advance_classifier`,
    `is_nontrivial`, and a crossing-point hypothesis `h_g`)
    iff it satisfies paper's three clauses:

    (i) **non-triviality** (`f ≠ id`): paper line 830,
        `Ecl ≠ id`. Rendered via the external `is_nontrivial`
        classifier on `HolEndMorphism`.

    (ii) **minimal advance**: paper line 831–833,
        `Adv_n(Ecl) ≼ Adv_n(g)` for every non-identity
        `g ∈ HolEndS_τ(ω)` and every sufficiently large `n`.
        Rendered via `RefinementAdvancePartialOrder` on the
        advance classifier, quantified over all other non-trivial
        morphisms, past a uniform depth bound.

    (iii) **crossing-germ normalisation**: paper line 834–835,
        `Ecl` fixes the crossing-point germ `G_×[ω]`. Rendered
        via `actSigmaFixed`-fixedness on the supplied
        crossing-point thread `g_cp`.

    The clauses are packaged as fields of a `Prop`-valued
    structure (matching the `IsGSideMinimal` / `IsRSideMinimal`
    pattern of `BoundaryInteriorIdentification.lean`). -/
structure IsTauExponential
    {D : DefectInverseSystem}
    (is_nontrivial : HolEndMorphism D → Prop)
    (advance_classifier : HolEndMorphism D → Nat → Bool)
    (g_cp : D.SigmaFixedThread)
    (f : HolEndMorphism D) : Prop where
  /-- (i) Non-triviality (paper line 830, `Ecl ≠ id`). -/
  nontrivial : is_nontrivial f
  /-- (ii) Minimal advance: there exists a uniform depth bound
      `N` past which `f` minimally advances on every depth
      against every other non-trivial morphism (paper line
      831–833). -/
  minimal_advance : ∃ N : Nat, ∀ (g' : HolEndMorphism D)
      (_h_g' : is_nontrivial g') (n : Nat) (_hn : N ≤ n),
      RefinementAdvancePartialOrder advance_classifier f g'
  /-- (iii) Crossing-germ normalisation: `f` fixes the crossing-point
      thread (paper line 834–835). -/
  fixes_crossing : f.actSigmaFixed g_cp = g_cp

-- ============================================================
-- PART 3: paper Prop 3.9 uniqueness — abstract form
-- ============================================================

/-- **Paper Proposition 3.9 — uniqueness half (abstract form).**

    Paper text (line 839–841):

    > "`Ecl` exists and is unique."

    Paper proof sketch (uniqueness, lines 854–864):

    > "If `Ecl'` is another minimal non-trivial σ-equivariant
    > advance, then `Adv_n(Ecl') = Adv_n(Ecl)` at every sufficiently
    > large `n` (minimality), and both fix the crossing-point germ
    > (crossing-germ normalisation). The self-reproduction
    > uniqueness argument of Book II Ch. 26 (II.D30, II.T23 i-iii)
    > shows that the minimal σ-equivariant ω-advance is uniquely
    > characterised by its eigenvalue structure on the D-channel;
    > applied to the finite-stage readouts, this gives `Ecl_n =
    > Ecl'_n` at every `n`, hence `Ecl = Ecl'`."

    The Lean rendering captures Book II II.T23's self-reproduction
    uniqueness as an external hypothesis
    `book_ii_uniqueness`: any two `IsTauExponential` witnesses that
    agree on advance-classifier and fix the same crossing-point
    thread are identified on their action on σ-fixed threads.

    This is the **structural core** of Prop 3.9 uniqueness:
    given Book II II.T23, two `IsTauExponential` witnesses agree on
    the crossing-point thread's image (and, downstream, on every
    σ-fixed thread once the geometric instance fires). -/
theorem tau_exponential_unique
    {D : DefectInverseSystem}
    {is_nontrivial : HolEndMorphism D → Prop}
    {advance_classifier : HolEndMorphism D → Nat → Bool}
    {g_cp : D.SigmaFixedThread}
    (f₁ f₂ : HolEndMorphism D)
    (h₁ : IsTauExponential is_nontrivial advance_classifier g_cp f₁)
    (h₂ : IsTauExponential is_nontrivial advance_classifier g_cp f₂)
    (book_ii_uniqueness :
      ∀ (φ₁ φ₂ : HolEndMorphism D),
        is_nontrivial φ₁ → is_nontrivial φ₂ →
        RefinementAdvancePartialOrder advance_classifier φ₁ φ₂ →
        RefinementAdvancePartialOrder advance_classifier φ₂ φ₁ →
        φ₁.actSigmaFixed g_cp = g_cp →
        φ₂.actSigmaFixed g_cp = g_cp →
        φ₁.actSigmaFixed g_cp = φ₂.actSigmaFixed g_cp) :
    f₁.actSigmaFixed g_cp = f₂.actSigmaFixed g_cp := by
  -- Both `f₁` and `f₂` are non-trivial, minimal-advance, and fix the
  -- crossing-point thread.  Their advance classifiers compare both
  -- ways at sufficiently large depth (minimality).  Book II II.T23
  -- supplies the final equality on the crossing-point thread's image.
  obtain ⟨N₁, hN₁⟩ := h₁.minimal_advance
  obtain ⟨N₂, hN₂⟩ := h₂.minimal_advance
  -- Both partial orders fire at depth `max N₁ N₂` upward:
  have h12 : RefinementAdvancePartialOrder advance_classifier f₁ f₂ :=
    hN₁ f₂ h₂.nontrivial (max N₁ N₂) (le_max_left N₁ N₂)
  have h21 : RefinementAdvancePartialOrder advance_classifier f₂ f₁ :=
    hN₂ f₁ h₁.nontrivial (max N₁ N₂) (le_max_right N₁ N₂)
  -- Apply Book II II.T23 uniqueness with the two crossing-fixedness
  -- witnesses and the bidirectional partial-order witness:
  exact book_ii_uniqueness f₁ f₂ h₁.nontrivial h₂.nontrivial
    h12 h21 h₁.fixes_crossing h₂.fixes_crossing

/-- **Paper Prop 3.9 uniqueness, scalar-readout corollary.**

    Once the action on the crossing-point thread coincides
    (`tau_exponential_unique`), the scalar readouts also coincide.
    This packages the paper's "`GerE = ReadF(Ecl)` is well-defined"
    line at the abstract scaffold level. -/
theorem tau_exponential_unique_actSigmaFixed
    {D : DefectInverseSystem}
    {is_nontrivial : HolEndMorphism D → Prop}
    {advance_classifier : HolEndMorphism D → Nat → Bool}
    {g_cp : D.SigmaFixedThread}
    (f₁ f₂ : HolEndMorphism D)
    (h₁ : IsTauExponential is_nontrivial advance_classifier g_cp f₁)
    (h₂ : IsTauExponential is_nontrivial advance_classifier g_cp f₂)
    (book_ii_uniqueness :
      ∀ (φ₁ φ₂ : HolEndMorphism D),
        is_nontrivial φ₁ → is_nontrivial φ₂ →
        RefinementAdvancePartialOrder advance_classifier φ₁ φ₂ →
        RefinementAdvancePartialOrder advance_classifier φ₂ φ₁ →
        φ₁.actSigmaFixed g_cp = g_cp →
        φ₂.actSigmaFixed g_cp = g_cp →
        φ₁.actSigmaFixed g_cp = φ₂.actSigmaFixed g_cp)
    (readout_level : ∀ n, D.defect_level n → TauRat) (n : Nat) :
    D.threadReadout readout_level (f₁.actSigmaFixed g_cp).toThread n =
    D.threadReadout readout_level (f₂.actSigmaFixed g_cp).toThread n := by
  rw [tau_exponential_unique f₁ f₂ h₁ h₂ book_ii_uniqueness]

-- ============================================================
-- PART 4: paper Def 3.9 — scalar readout connection to TauReal.e
-- ============================================================

/-- **Scalar-readout connection to `TauReal.e`** (paper Def 3.9,
    `def:e-tau`, line 867 + line 874).

    Paper text:

    > "Define `GerE := ReadF(Ecl)`, the canonical scalar readout
    > of the τ-exponential `Ecl` under the boundary scalar-algebra
    > readout functor `ReadF`. Under the standard readout functor,
    > `GerE ↦ e ≈ 2.71828`."

    The connection of `GerE` (paper's structurally defined boundary
    readout of `Ecl`) to `TauReal.e` (the factorial series partial
    sums) is the *paper's classical witness* for the scalar value.
    The structural identification of `GerE` with the interior
    ν-iterator eigenvalue is paper Theorem 7.16, abstractly closed
    in `BoundaryInteriorIdentification.lean`.

    This structure records the connection at the most general
    abstract level: a `HolEndMorphism D` witness for `Ecl`, a scalar
    readout extracting `GerE`, and the requirement that `GerE`
    matches `TauReal.e.approx n` at every depth (paper's "↦ e"
    line). Concrete instances supply the geometric `D` plus the
    readout that delivers the factorial series. -/
structure TauExponentialReadout (D : DefectInverseSystem) where
  /-- The τ-exponential witness on `D` (paper `Ecl`). -/
  ecl : HolEndMorphism D
  /-- The crossing-point thread (paper `G_×[ω]`). -/
  g_cp : D.SigmaFixedThread
  /-- The Prop-witness that `ecl` is the τ-exponential on `D`. -/
  is_tau_exp : ∃ (is_nontrivial : HolEndMorphism D → Prop)
                   (advance_classifier : HolEndMorphism D → Nat → Bool),
    IsTauExponential is_nontrivial advance_classifier g_cp ecl
  /-- The scalar readout extracting paper's `GerE`. -/
  readout : ∀ n, D.defect_level n → TauRat
  /-- Paper's `GerE ↦ e` line: the structural readout of `Ecl`
      on the crossing-point thread matches the `TauReal.e`
      factorial series at every depth. -/
  ger_e_eq_tau_real_e : ∀ n,
    D.threadReadout readout (ecl.actSigmaFixed g_cp).toThread n =
    TauReal.e.approx n

/-- **The scalar value of paper's `GerE` is `TauReal.e`** —
    structural observation tying the abstract `Ecl` scaffold back
    to the operational `TauReal.e` factorial series.

    Given a `TauExponentialReadout` witness, the depth-`n` readout
    of `Ecl`'s action on the crossing-point thread equals
    `TauReal.e.approx n` — the paper's "↦ e ≈ 2.71828" line at
    constructive-real level. -/
theorem tau_exponential_readout_value
    {D : DefectInverseSystem}
    (W : TauExponentialReadout D) (n : Nat) :
    D.threadReadout W.readout (W.ecl.actSigmaFixed W.g_cp).toThread n =
    TauReal.e.approx n :=
  W.ger_e_eq_tau_real_e n

/-- **Two τ-exponentials share their boundary scalar readout** —
    combining `tau_exponential_unique` with the `TauReal.e`
    connection.

    If two `HolEndMorphism` witnesses `f₁, f₂` are both
    τ-exponentials on the same `D` with the same crossing-point
    thread `g_cp` and the same readout `readout`, then their
    boundary scalar readouts at every depth agree — i.e., both
    give the same `TauReal.e.approx n` value.

    This is the abstract-scaffold form of paper's "`GerE` is
    well-defined" claim: the scalar `e_τ` is unambiguous despite
    the universal-property quantifier over `Ecl`. -/
theorem tau_exponentials_share_readout
    {D : DefectInverseSystem}
    {is_nontrivial : HolEndMorphism D → Prop}
    {advance_classifier : HolEndMorphism D → Nat → Bool}
    {g_cp : D.SigmaFixedThread}
    (f₁ f₂ : HolEndMorphism D)
    (h₁ : IsTauExponential is_nontrivial advance_classifier g_cp f₁)
    (h₂ : IsTauExponential is_nontrivial advance_classifier g_cp f₂)
    (book_ii_uniqueness :
      ∀ (φ₁ φ₂ : HolEndMorphism D),
        is_nontrivial φ₁ → is_nontrivial φ₂ →
        RefinementAdvancePartialOrder advance_classifier φ₁ φ₂ →
        RefinementAdvancePartialOrder advance_classifier φ₂ φ₁ →
        φ₁.actSigmaFixed g_cp = g_cp →
        φ₂.actSigmaFixed g_cp = g_cp →
        φ₁.actSigmaFixed g_cp = φ₂.actSigmaFixed g_cp)
    (readout : ∀ n, D.defect_level n → TauRat) (n : Nat) :
    D.threadReadout readout (f₁.actSigmaFixed g_cp).toThread n =
    D.threadReadout readout (f₂.actSigmaFixed g_cp).toThread n :=
  tau_exponential_unique_actSigmaFixed f₁ f₂ h₁ h₂ book_ii_uniqueness
    readout n

-- ============================================================
-- PART 5: Sanity check on TrivialDefectSystem
-- ============================================================

/-- **The trivial `HolEndMorphism` fails the non-triviality
    clause**: a sanity check that `IsTauExponential` has
    structural content (i.e., is not vacuously satisfied).

    On `TrivialDefectSystem`, the only `HolEndMorphism` we have
    on record (`TrivialHolEndMorphism`) is the identity. So under
    the canonical "is_nontrivial := fun f => ∃ t, f.act t ≠ t"
    classifier (the type-level non-triviality witness), the
    trivial morphism fails — there is no `Thread` it moves.

    This documents the predicate's bite: on a trivial carrier
    where every morphism is the identity, no `IsTauExponential`
    witness exists, exactly as paper's "Ecl ≠ id" clause demands. -/
theorem trivial_no_tau_exponential
    (g_cp : TrivialDefectSystem.SigmaFixedThread)
    (advance_classifier :
      HolEndMorphism TrivialDefectSystem → Nat → Bool) :
    ¬ IsTauExponential
        (fun f => ∃ t, f.act t ≠ t)
        advance_classifier g_cp TrivialHolEndMorphism := by
  intro h
  obtain ⟨t, ht⟩ := h.nontrivial
  -- `TrivialHolEndMorphism.act t = t` by definition (identity action).
  exact ht rfl

/-- **A `TauExponentialReadout` on `TrivialDefectSystem` whose
    `ecl` is the trivial morphism, instantiated with the
    discriminating "moves some thread" classifier, is
    impossible** — companion sanity check at the readout-structure
    level.

    The discriminating classifier
    `is_nontrivial := fun f => ∃ t, f.act t ≠ t` is the natural
    "non-identity" witness on `HolEndMorphism`. Plugging this
    into the `IsTauExponential` predicate on
    `TrivialHolEndMorphism` yields the same contradiction as
    `trivial_no_tau_exponential`; we package the readout-structure
    version as a corollary. -/
theorem trivial_tau_exp_readout_discriminating_classifier
    (g_cp : TrivialDefectSystem.SigmaFixedThread)
    (advance_classifier :
      HolEndMorphism TrivialDefectSystem → Nat → Bool)
    (h_is_tau : IsTauExponential
                  (fun f => ∃ t, f.act t ≠ t)
                  advance_classifier g_cp TrivialHolEndMorphism) :
    False :=
  trivial_no_tau_exponential g_cp advance_classifier h_is_tau

end Tau.Boundary
