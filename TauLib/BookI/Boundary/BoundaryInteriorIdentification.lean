import TauLib.BookI.Boundary.LobeInvariance
import TauLib.BookI.Boundary.UniversalFixedScalar

/-!
# TauLib.BookI.Boundary.BoundaryInteriorIdentification

**Critical-gap fill: paper `iota-tau/main.tex` §7.5 OQ5 closure
— Theorem 7.16 + Lemma 7.15, the boundary–interior identification
of `e_τ`, rendered as Lean theorems on an abstract scaffold.**

Paper §7.5 closes its fifth open question (OQ5) by showing
the boundary scalar readout `GerE = ReadF(E_cl)` of the
τ-exponential coincides *structurally* (not merely numerically)
with the radial D-channel ν-iterator eigenvalue `e_ν` of Book II
Chapter 26:

```
GerE = e_ν = lim_{k → ∞}(1 + 1/p_{k+1})^{p_{k+1}} = e ≈ 2.71828.
```

The argument is a **Yoneda-style uniqueness** argument
(paper Lemma 7.15 `lem:minimality-transport`) using:

1. **G-side universal property** (`E_cl` characterised by:
   non-trivial, bipolar-swap-fixed, refinement-compatible
   ω-germ transformer with |S_n| = 1 and unit-normalised
   amplitude — paper Step 1).
2. **R-side universal property** (ν-iterator's refinement
   tail characterised by: non-trivial, bipolar-swap-fixed,
   tower-coherent sequence with |S_n| = 1 and unit-normalised
   increment — paper Step 2).
3. **II.T27's bipolar-preserving bijection** preserves all
   identifying properties: tower coherence, |S_n|, bipolar
   decomposition, σ-equivariance (= bipolar swap, paper
   Remark `rem:sigma-bipolar-key`), and scalar values
   (paper Step 3 (i)-(v)).
4. **Yoneda conclusion**: `Π(E_cl)` satisfies the R-side
   universal property, hence equals the ν-iterator's
   refinement tail (paper Step 4).

Prior to this module, neither the proof architecture
(Proposition 7.13) nor the minimality-transport lemma
(Lemma 7.15) was formalised in TauLib.  The audit note at
`audits/papers/2026-05-20-iota-tau-paper-V2-TauLib-backing-audit.md`
flagged this as **Critical Gap #2** — the headline closure in
paper v2.7 that promotes the boundary–interior identification
from a conditional reduction to an unconditional theorem.

This module supplies the **abstract scaffold**: the five-feature
preservation predicate (`BipolarPreservingBijection`), the
universal-property predicates on both sides, and the
identification theorem (`boundary_interior_identification`)
showing that — given the bijection together with the universal
properties — the G-side and R-side minimal witnesses are
canonically paired.

Concrete instance witnesses on `TorusDefectSystem` and
`refinementGrowingTorusSystem` (PART 9 of each respective
file) discharge the abstract hypotheses on simple carriers,
demonstrating the framework fires.

## Registry Cross-References

- [I.D125]      Tau.Boundary.DefectInverseSystem (Wave 12)
- [I.T-BIP]     paper Definition "bipolar-preserving bijection"
- [I.T-OQ5-L]   paper Lemma 7.15 `lem:minimality-transport`
- [I.T-OQ5]    paper Theorem 7.16 `thm:oq5-unconditional`

## Mathematical content

### The five-feature preservation predicate

Paper §7.5 Step 3 enumerates the five structural features
II.T27's bipolar-preserving bijection preserves:

- (i)   **tower coherence**: thread structure (compat fields).
- (ii)  **finite spectral support |S_n|**: per-depth
        sparsity of the boundary-character data.
- (iii) **bipolar decomposition** `h = e_+ h_+ + e_- h_-`:
        σ-eigendecomposition on the spectral algebra.
- (iv)  **σ-equivariance**, since σ = bipolar swap (paper
        Remark `rem:sigma-bipolar-key`).
- (v)   **scalar values** across the (G)↔(R) chain
        (paper II.T40(e) calibration preservation).

We abstract these into the `BipolarPreservingBijection`
structure: a `G ≃ R` Equiv between G-side and R-side
"data types" (i.e. types parametrising the two-sided
abstract universal-property classifiers), bundled with five
preservation predicates.

### Universal-property predicates

The **G-side universal property** abstracts paper Step 1:

> "non-trivial, bipolar-swap-fixed, refinement-compatible
> ω-germ transformer with |S_n| = 1 at every finite stage n
> and unit-normalised amplitude in the single non-trivial
> channel."

We render this as a predicate `IsGSideMinimal` over an
arbitrary G-side carrier `G`, with five clauses (non-trivial,
σ-fixed, tower-coherent, |S_n| = 1, unit-normalised).

The **R-side universal property** abstracts paper Step 2:

> "non-trivial, bipolar-swap-fixed, tower-coherent sequence
> in `Ẑ` with |S_n| = 1 at every stage k and unit-normalised
> increment in the single non-trivial channel."

We render this analogously as `IsRSideMinimal` over an
arbitrary R-side carrier `R`.

### The identification theorem

Given:
- `Π : BipolarPreservingBijection G R` (II.T27 abstracted),
- `g : G` with `IsGSideMinimal g` (E_cl as G-side witness),
- a uniqueness clause on R-side minimal elements
  (the singleton-character of the universal property),

we show `Π.toEquiv g` is the unique R-side minimal element.

The proof is Yoneda-style: `Π` preserves every identifying
feature, so `Π.toEquiv g` inherits all the R-side minimality
clauses from `g`'s G-side minimality clauses.

### Theorem 7.16 (paper headline)

The paper-faithful headline form (`boundary_interior_identification`)
records:

> Given (a) E_cl is G-side minimal, (b) v is R-side minimal,
> (c) R-side uniqueness, (d) bipolar-preserving Π : G ↔ R:
>     Π(E_cl) = v.

The structural identity `Π(E_cl) = v` is paper's
`Π(E_cl) = ν-iterator's refinement tail` (Lemma 7.15).

Promoting to scalar level is the readout step: if both sides
carry compatible scalar readouts (paper Step 3a normalisation
compatibility, II.T40(e)), then `read_G(E_cl) = read_R(v)`,
which is paper's `GerE = e_ν` (Theorem 7.16).

## Public API

- `BipolarPreservingBijection` — structure abstracting II.T27's
  five-feature preserving bijection between G-side and R-side
  data types.
- `IsGSideMinimal`, `IsRSideMinimal` — universal-property
  predicates classifying minimal witnesses on each side.
- `BipolarPreservingBijection.preserves_minimality` —
  the Yoneda-style transport: `IsGSideMinimal g → IsRSideMinimal (Π g)`.
- `minimality_transport_lemma` — paper Lemma 7.15 in abstract
  form: under R-side uniqueness, `Π(E_cl) = v_min`.
- `boundary_interior_identification` — paper Theorem 7.16 in
  abstract form: the structural identification of the G-side
  minimal element with the R-side minimal element via Π.
- `boundary_interior_scalar_identification` — paper Theorem 7.16
  promoted to scalar-readout level: equal under any pair of
  scalar readouts that Π identifies.

## Scope

`\scopetau`, **unconditional at the abstract scaffold level**.
The five-feature preserving bijection (II.T27) is supplied as a
hypothesis; given it (and the universal-property witnesses), the
identification is a theorem.

Concrete instance witnesses on `TorusDefectSystem` and
`refinementGrowingTorusSystem` ship in the respective instance
files (PART 10 of each), demonstrating the framework fires on
toy carriers (identity bijection on a 3-element type).

**Dependency on II.T27 (full Book II)**:  The paper-level
content of II.T27 — that the *boundary lemniscate ↔ interior
ν-iterator* bijection actually is bipolar-preserving and
exists — depends on Book II Chapter 31's Mutual Determination
formalisation, which is not yet in TauLib (estimated ~600–1000
LOC of Book II infrastructure).  TauLib's `BookII.Hartogs.MutualDetermination`
provides the **computational** version (`mutual_determination_check`
verified by `native_decide` on `bound = 10, db = 4`), but the
type-level bijection on infinite carriers is paper-only.

**What this module DOES provide**:
1. An abstract scaffold rendering paper's Yoneda argument as
   Lean theorems.
2. The five-feature preservation predicate making the paper's
   "II.T27 preserves all identifying properties" line precise.
3. Concrete instance witnesses showing the framework fires.

**What this module does NOT provide**:
- The full type-level II.T27 bijection on the actual
  boundary lemniscate ↔ ν-iterator carriers (deferred until
  Book II Ch. 31 infrastructure comes online).
- A claim that `TauReal.e` (factorial series) and the
  ν-iterator (1 + 1/p)^p limit) agree as `TauReal`'s; the
  *structural* identification through Π is supplied here,
  the *numerical* identification is a separate readout step.

The abstract closure of OQ5 at TauLib level means: as soon as
a future wave supplies the concrete II.T27 bijection on the
actual lemniscate/ν-iterator carriers, paper Theorem 7.16
fires unconditionally via `boundary_interior_identification`.
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: The five-feature preserving bijection (II.T27)
-- ============================================================

/-- **Bipolar-preserving bijection between G-side and R-side
    data** (paper §7.5 Step 3, structural form of II.T27).

    Abstracts the (G)↔(R) chain of paper II.L02–II.L05
    composed with II.T40(e) calibration preservation.

    The structure bundles:
    - An `Equiv` (bijection of types) `G ≃ R`.
    - Five preservation predicates: tower coherence (i),
      finite spectral support (ii), bipolar decomposition (iii)
      = σ-equivariance (iv), and scalar value (v) preservation.

    The five preservation clauses are **predicates over external
    classifiers** supplied by the consumer:
    - `tower_coherent_G/R : G/R → Prop` (tower coherence)
    - `spec_support_G/R : G/R → Nat → Bool` (the |S_n|=1 check)
    - `sigma_fixed_G/R : G/R → Prop` (σ = bipolar swap fixedness)
    - `scalar_G/R : G/R → TauRat` (scalar readout)

    Each clause states that the bijection respects the
    corresponding classifier.

    **Paper §7.5 Step 3 lines 2552–2560** enumerate these five:

    > (i) tower coherence (Book II ch.31 lines 67–78),
    > (ii) finite spectral support |S_n| (line 556),
    > (iii) bipolar decomposition h = e_+ h_+ + e_- h_-,
    > (iv) hence σ-equivariance, since σ = bipolar swap,
    > (v) scalar values across the (G)↔(R) chain (II.T40(e)).

    We expose (iii) directly through σ-fixedness preservation
    (iv): paper Remark `rem:sigma-bipolar-key` collapses (iii)
    and (iv) into one structural identity. -/
structure BipolarPreservingBijection
    (G R : Type)
    (tower_coherent_G : G → Prop) (tower_coherent_R : R → Prop)
    (spec_support_G : G → Nat → Bool) (spec_support_R : R → Nat → Bool)
    (sigma_fixed_G : G → Prop) (sigma_fixed_R : R → Prop)
    (scalar_G : G → TauRat) (scalar_R : R → TauRat) where
  /-- The underlying bijection (II.T27's `Π : G ↔ R` at the
      type level). -/
  toEquiv : G ≃ R
  /-- (i) Tower coherence is preserved. -/
  preserves_tower : ∀ g : G, tower_coherent_G g ↔ tower_coherent_R (toEquiv g)
  /-- (ii) Finite spectral support |S_n| is preserved at every depth. -/
  preserves_spec_support : ∀ (g : G) (n : Nat),
    spec_support_G g n = spec_support_R (toEquiv g) n
  /-- (iv) σ-fixedness is preserved (paper Remark
      `rem:sigma-bipolar-key`: σ = bipolar swap, so (iii) and (iv)
      coincide). -/
  preserves_sigma_fixed : ∀ g : G, sigma_fixed_G g ↔ sigma_fixed_R (toEquiv g)
  /-- (v) Scalar values are preserved (paper II.T40(e)
      calibration preservation). -/
  preserves_scalar : ∀ g : G, scalar_G g = scalar_R (toEquiv g)

-- ============================================================
-- PART 2: G-side / R-side universal-property predicates
-- ============================================================

/-- **G-side minimality predicate** (paper §7.5 Step 1,
    universal property characterising `E_cl`).

    A G-side element `g : G` is "minimal" iff:
    - it is non-trivial (paper: not the identity advance),
    - it is tower-coherent (refinement-compatible),
    - it is σ-fixed (= bipolar-swap-fixed),
    - it has finite spectral support |S_n| = 1 at every
      depth (paper: single non-trivial channel),
    - its scalar readout equals the unit-normalised value
      (paper: smallest non-trivial amplitude = canonical unit).

    Paper §7.5 Step 1 rephrasing:

    > "`E_cl` is the unique bipolar-swap-fixed non-trivial
    > refinement-compatible ω-germ transformer on `H_τ(ω)`
    > with |S_n| = 1 at every finite stage n and
    > unit-normalised amplitude in the single non-trivial
    > channel."

    We render this as a `Prop`-valued predicate over five
    external classifiers (the same classifiers used in
    `BipolarPreservingBijection`).

    The `is_nontrivial` classifier is supplied as `G → Prop`
    (rather than baked into the bijection structure) so that
    non-triviality is a property of the *element*, not of the
    Π-equivalence.  This matches paper's Step 1 phrasing. -/
structure IsGSideMinimal
    (G : Type)
    (is_nontrivial_G : G → Prop)
    (tower_coherent_G : G → Prop)
    (sigma_fixed_G : G → Prop)
    (spec_support_G : G → Nat → Bool)
    (scalar_G : G → TauRat)
    (unit_value : TauRat)
    (g : G) : Prop where
  /-- Non-trivial (paper: not the identity advance). -/
  nontrivial : is_nontrivial_G g
  /-- Tower-coherent (refinement-compatible). -/
  tower : tower_coherent_G g
  /-- σ-fixed (= bipolar-swap-fixed). -/
  sigma_fixed : sigma_fixed_G g
  /-- |S_n| = 1 at every depth `n` (paper: single
      non-trivial channel). -/
  spec_support_one : ∀ n : Nat, spec_support_G g n = true
  /-- Scalar value equals the canonical unit. -/
  scalar_unit : scalar_G g = unit_value

/-- **R-side minimality predicate** (paper §7.5 Step 2,
    universal property characterising the ν-iterator's
    refinement tail).

    Structurally identical to `IsGSideMinimal` but over the
    R-side carrier; same five clauses with R-side classifiers.

    Paper §7.5 Step 2 rephrasing:

    > "The ν-iterator's refinement tail is the unique
    > bipolar-swap-fixed non-trivial tower-coherent sequence
    > in `Ẑ` with |S_n| = 1 at every stage k and
    > unit-normalised increment in the single non-trivial
    > channel."

    The same `unit_value` is used as on the G-side: paper
    §7.5 Step 3a establishes normalisation compatibility via
    II.T40(e), so the two sides share a single canonical
    unit. -/
structure IsRSideMinimal
    (R : Type)
    (is_nontrivial_R : R → Prop)
    (tower_coherent_R : R → Prop)
    (sigma_fixed_R : R → Prop)
    (spec_support_R : R → Nat → Bool)
    (scalar_R : R → TauRat)
    (unit_value : TauRat)
    (r : R) : Prop where
  /-- Non-trivial. -/
  nontrivial : is_nontrivial_R r
  /-- Tower-coherent. -/
  tower : tower_coherent_R r
  /-- σ-fixed. -/
  sigma_fixed : sigma_fixed_R r
  /-- |S_n| = 1 at every depth `n`. -/
  spec_support_one : ∀ n : Nat, spec_support_R r n = true
  /-- Scalar value equals the canonical unit. -/
  scalar_unit : scalar_R r = unit_value

-- ============================================================
-- PART 3: Yoneda-style transport — paper Lemma 7.15 abstract form
-- ============================================================

/-- **Bipolar-preserving bijections transport G-side
    minimality to R-side minimality** (paper §7.5 Step 4,
    Yoneda-style conclusion).

    Direct unfolding of the five preservation clauses
    against the five minimality clauses.  The
    `preserves_nontrivial` hypothesis carries the
    non-triviality preservation (paper: "Π is a bijection;
    E_cl is non-trivial; hence Π(E_cl) is non-trivial.").

    This is the **structural core** of paper Lemma 7.15:
    given that Π preserves the five identifying features,
    the G-side minimal element maps to an R-side minimal
    element under Π. -/
theorem BipolarPreservingBijection.preserves_minimality
    {G R : Type}
    {is_nontrivial_G : G → Prop} {is_nontrivial_R : R → Prop}
    {tower_coherent_G : G → Prop} {tower_coherent_R : R → Prop}
    {spec_support_G : G → Nat → Bool} {spec_support_R : R → Nat → Bool}
    {sigma_fixed_G : G → Prop} {sigma_fixed_R : R → Prop}
    {scalar_G : G → TauRat} {scalar_R : R → TauRat}
    {unit_value : TauRat}
    (P : BipolarPreservingBijection G R
          tower_coherent_G tower_coherent_R
          spec_support_G spec_support_R
          sigma_fixed_G sigma_fixed_R
          scalar_G scalar_R)
    (preserves_nontrivial : ∀ g : G,
      is_nontrivial_G g → is_nontrivial_R (P.toEquiv g))
    (g : G)
    (h_g : IsGSideMinimal G is_nontrivial_G tower_coherent_G
              sigma_fixed_G spec_support_G scalar_G unit_value g) :
    IsRSideMinimal R is_nontrivial_R tower_coherent_R
      sigma_fixed_R spec_support_R scalar_R unit_value
      (P.toEquiv g) where
  nontrivial := preserves_nontrivial g h_g.nontrivial
  tower := (P.preserves_tower g).mp h_g.tower
  sigma_fixed := (P.preserves_sigma_fixed g).mp h_g.sigma_fixed
  spec_support_one := fun n => by
    rw [← P.preserves_spec_support g n]
    exact h_g.spec_support_one n
  scalar_unit := by
    rw [← P.preserves_scalar g]
    exact h_g.scalar_unit

-- ============================================================
-- PART 4: Paper Lemma 7.15 (minimality-transport) in headline form
-- ============================================================

/-- **Paper Lemma 7.15 (`lem:minimality-transport`) — abstract
    form.**

    Given:
    - a bipolar-preserving bijection `Π : G ↔ R`,
    - a G-side minimal element `g` (witness for `E_cl`),
    - an R-side minimal element `r_min` (witness for the
      ν-iterator's refinement tail),
    - **R-side uniqueness** of minimal elements (the singleton
      character of the universal property),
    - preservation of non-triviality,

    we conclude `Π(g) = r_min`: the bijection sends the G-side
    minimal element to the unique R-side minimal element.

    Paper §7.5 Step 4 (Yoneda conclusion):

    > "Since Π(E_cl) is a well-defined element of R, we check
    > that it satisfies the R-side universal property of
    > Step 2: [..five clauses..].  Hence Π(E_cl) satisfies the
    > universal property that uniquely characterises the
    > ν-iterator's refinement tail (Step 2).  By uniqueness,
    > Π(E_cl) = the ν-iterator's refinement tail."

    The Lean rendering captures the uniqueness clause as a
    hypothesis `r_unique`; concrete instances supplying the
    bijection and the universal-property witnesses also
    supply the uniqueness witness.

    **Note**: paper labels the R-side witness `the ν-iterator's
    refinement tail`; in this abstract scaffold it is simply
    `r_min`, the R-side minimal element supplied by the
    consumer. -/
theorem minimality_transport_lemma
    {G R : Type}
    {is_nontrivial_G : G → Prop} {is_nontrivial_R : R → Prop}
    {tower_coherent_G : G → Prop} {tower_coherent_R : R → Prop}
    {spec_support_G : G → Nat → Bool} {spec_support_R : R → Nat → Bool}
    {sigma_fixed_G : G → Prop} {sigma_fixed_R : R → Prop}
    {scalar_G : G → TauRat} {scalar_R : R → TauRat}
    {unit_value : TauRat}
    (P : BipolarPreservingBijection G R
          tower_coherent_G tower_coherent_R
          spec_support_G spec_support_R
          sigma_fixed_G sigma_fixed_R
          scalar_G scalar_R)
    (preserves_nontrivial : ∀ g : G,
      is_nontrivial_G g → is_nontrivial_R (P.toEquiv g))
    (g : G) (r_min : R)
    (h_g : IsGSideMinimal G is_nontrivial_G tower_coherent_G
              sigma_fixed_G spec_support_G scalar_G unit_value g)
    (_h_r : IsRSideMinimal R is_nontrivial_R tower_coherent_R
              sigma_fixed_R spec_support_R scalar_R unit_value r_min)
    (r_unique : ∀ r₁ r₂ : R,
      IsRSideMinimal R is_nontrivial_R tower_coherent_R
        sigma_fixed_R spec_support_R scalar_R unit_value r₁ →
      IsRSideMinimal R is_nontrivial_R tower_coherent_R
        sigma_fixed_R spec_support_R scalar_R unit_value r₂ →
      r₁ = r₂) :
    P.toEquiv g = r_min :=
  r_unique (P.toEquiv g) r_min
    (P.preserves_minimality preserves_nontrivial g h_g) _h_r

-- ============================================================
-- PART 5: Paper Theorem 7.16 — abstract structural form
-- ============================================================

/-- **Paper Theorem 7.16 (`thm:oq5-unconditional`) — structural
    form.**

    Records the paper's headline claim:

    > GerE = e_ν   (structurally, not merely numerically)

    at the abstract scaffold level: under the same hypotheses
    as `minimality_transport_lemma`, the G-side minimal
    element's image under Π *is* the R-side minimal element.

    This is the **structural identification** content of
    paper Theorem 7.16: `Π(E_cl) = ν-iterator's refinement tail`.
    The structural form is the foundation; the numerical
    coincidence `GerE = e_ν = e ≈ 2.71828` is the scalar-readout
    promotion in `boundary_interior_scalar_identification` below.

    Paper §7.5 line 2640: "All v1–v2 open structural questions
    on the coupling identity are now closed." -/
theorem boundary_interior_identification
    {G R : Type}
    {is_nontrivial_G : G → Prop} {is_nontrivial_R : R → Prop}
    {tower_coherent_G : G → Prop} {tower_coherent_R : R → Prop}
    {spec_support_G : G → Nat → Bool} {spec_support_R : R → Nat → Bool}
    {sigma_fixed_G : G → Prop} {sigma_fixed_R : R → Prop}
    {scalar_G : G → TauRat} {scalar_R : R → TauRat}
    {unit_value : TauRat}
    (P : BipolarPreservingBijection G R
          tower_coherent_G tower_coherent_R
          spec_support_G spec_support_R
          sigma_fixed_G sigma_fixed_R
          scalar_G scalar_R)
    (preserves_nontrivial : ∀ g : G,
      is_nontrivial_G g → is_nontrivial_R (P.toEquiv g))
    (g : G) (r_min : R)
    (h_g : IsGSideMinimal G is_nontrivial_G tower_coherent_G
              sigma_fixed_G spec_support_G scalar_G unit_value g)
    (h_r : IsRSideMinimal R is_nontrivial_R tower_coherent_R
              sigma_fixed_R spec_support_R scalar_R unit_value r_min)
    (r_unique : ∀ r₁ r₂ : R,
      IsRSideMinimal R is_nontrivial_R tower_coherent_R
        sigma_fixed_R spec_support_R scalar_R unit_value r₁ →
      IsRSideMinimal R is_nontrivial_R tower_coherent_R
        sigma_fixed_R spec_support_R scalar_R unit_value r₂ →
      r₁ = r₂) :
    P.toEquiv g = r_min :=
  minimality_transport_lemma P preserves_nontrivial g r_min h_g h_r r_unique

/-- **Paper Theorem 7.16 promoted to scalar readout** — the
    boundary scalar readout coincides with the interior
    scalar readout.

    Under the identification of `Π(g)` with `r_min` (paper
    Theorem 7.16 structural form), and using Π's scalar
    preservation (clause v / II.T40(e)), the G-side scalar
    `scalar_G g` equals the R-side scalar `scalar_R r_min`:

       `scalar_G g = scalar_R (Π g) = scalar_R r_min`.

    Paper §7.5 boxed identity:

    > GerE = e_ν = lim_{k → ∞}(1 + 1/p_{k+1})^{p_{k+1}}
    >        = e ≈ 2.71828.

    The scalar identification at the readout level — once both
    sides are exhibited as minimal witnesses — is paper's
    headline structural identity, promoted from "structural
    identification" to "scalar equality" via II.T40(e). -/
theorem boundary_interior_scalar_identification
    {G R : Type}
    {is_nontrivial_G : G → Prop} {is_nontrivial_R : R → Prop}
    {tower_coherent_G : G → Prop} {tower_coherent_R : R → Prop}
    {spec_support_G : G → Nat → Bool} {spec_support_R : R → Nat → Bool}
    {sigma_fixed_G : G → Prop} {sigma_fixed_R : R → Prop}
    {scalar_G : G → TauRat} {scalar_R : R → TauRat}
    {unit_value : TauRat}
    (P : BipolarPreservingBijection G R
          tower_coherent_G tower_coherent_R
          spec_support_G spec_support_R
          sigma_fixed_G sigma_fixed_R
          scalar_G scalar_R)
    (preserves_nontrivial : ∀ g : G,
      is_nontrivial_G g → is_nontrivial_R (P.toEquiv g))
    (g : G) (r_min : R)
    (h_g : IsGSideMinimal G is_nontrivial_G tower_coherent_G
              sigma_fixed_G spec_support_G scalar_G unit_value g)
    (h_r : IsRSideMinimal R is_nontrivial_R tower_coherent_R
              sigma_fixed_R spec_support_R scalar_R unit_value r_min)
    (r_unique : ∀ r₁ r₂ : R,
      IsRSideMinimal R is_nontrivial_R tower_coherent_R
        sigma_fixed_R spec_support_R scalar_R unit_value r₁ →
      IsRSideMinimal R is_nontrivial_R tower_coherent_R
        sigma_fixed_R spec_support_R scalar_R unit_value r₂ →
      r₁ = r₂) :
    scalar_G g = scalar_R r_min := by
  rw [P.preserves_scalar g,
      boundary_interior_identification P preserves_nontrivial
        g r_min h_g h_r r_unique]

/-- **Both sides agree at the canonical unit value** — a
    direct corollary of the scalar identification combined
    with the minimality clauses.

    Both `scalar_G g` and `scalar_R r_min` equal the shared
    `unit_value`, so this is immediate from the two scalar
    clauses.  The corollary is stated to make the paper's
    "GerE = e_ν = e (= unit value)" three-way coincidence
    explicit at the abstract scaffold level.

    No `Π` is needed here — the unit equality follows from
    the two universal-property witnesses alone. -/
theorem minimal_witnesses_share_unit_value
    {G R : Type}
    {is_nontrivial_G : G → Prop} {is_nontrivial_R : R → Prop}
    {tower_coherent_G : G → Prop} {tower_coherent_R : R → Prop}
    {spec_support_G : G → Nat → Bool} {spec_support_R : R → Nat → Bool}
    {sigma_fixed_G : G → Prop} {sigma_fixed_R : R → Prop}
    {scalar_G : G → TauRat} {scalar_R : R → TauRat}
    {unit_value : TauRat}
    {g : G} {r_min : R}
    (h_g : IsGSideMinimal G is_nontrivial_G tower_coherent_G
              sigma_fixed_G spec_support_G scalar_G unit_value g)
    (h_r : IsRSideMinimal R is_nontrivial_R tower_coherent_R
              sigma_fixed_R spec_support_R scalar_R unit_value r_min) :
    scalar_G g = scalar_R r_min := by
  rw [h_g.scalar_unit, h_r.scalar_unit]

-- ============================================================
-- PART 6: Identity-bijection sanity check (toy instance)
-- ============================================================

/-- **The identity bijection on a single type is bipolar-preserving
    for any classifier triple** — a sanity check that the
    `BipolarPreservingBijection` structure compiles and the
    five clauses are reflexively dischargeable when `G = R` and
    `Π = id`.

    Paper context: this is the trivial case where the boundary
    and interior types are literally the same; the identity
    bijection is automatically a (bipolar-preserving)
    isomorphism.  The toy carrier `Unit` is too small to host
    any non-trivial spectral or σ-structure, so we use it
    here only to confirm the scaffold compiles. -/
def identityBipolarPreservingBijection
    {G : Type}
    (tower_coherent : G → Prop)
    (spec_support : G → Nat → Bool)
    (sigma_fixed : G → Prop)
    (scalar : G → TauRat) :
    BipolarPreservingBijection G G
      tower_coherent tower_coherent
      spec_support spec_support
      sigma_fixed sigma_fixed
      scalar scalar where
  toEquiv := Equiv.refl G
  preserves_tower := fun _ => Iff.rfl
  preserves_spec_support := fun _ _ => rfl
  preserves_sigma_fixed := fun _ => Iff.rfl
  preserves_scalar := fun _ => rfl

/-- **Sanity check: identity bijection transports
    minimality reflexively.**

    On the identity bijection, `Π.toEquiv g = g`, so the
    preserved minimality witness is the same element with the
    same minimality data (G-side and R-side coincide). -/
theorem identityBipolarPreservingBijection_preserves_minimality
    {G : Type}
    {is_nontrivial : G → Prop}
    {tower_coherent : G → Prop}
    {spec_support : G → Nat → Bool}
    {sigma_fixed : G → Prop}
    {scalar : G → TauRat}
    {unit_value : TauRat}
    {g : G}
    (h_g : IsGSideMinimal G is_nontrivial tower_coherent
              sigma_fixed spec_support scalar unit_value g) :
    IsRSideMinimal G is_nontrivial tower_coherent sigma_fixed
      spec_support scalar unit_value g :=
  (identityBipolarPreservingBijection tower_coherent spec_support
    sigma_fixed scalar).preserves_minimality
    (fun _ h => h) g h_g

end Tau.Boundary
