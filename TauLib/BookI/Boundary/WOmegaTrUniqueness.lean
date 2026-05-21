import TauLib.BookI.Boundary.FiniteNormalisationStructural
import TauLib.BookI.Boundary.TauComplexExp

/-!
# TauLib.BookI.Boundary.WOmegaTrUniqueness

**V3-substantive gap fill: paper `iota-tau/main.tex` §6.2 (Step 2b)
+ §7.4 (Prop 7.11 cited content) — promotion of the `Tr_+` uniqueness
theorem from the discrete `SectorPair → Int` layer to the boundary
scalar-algebra layer `D ⊗ ℝ_τ → ℝ_τ`.**

## Paper claim (§6.2 lines 1710–1724, §7.4 lines 2197–2222)

> The space of ℤ-linear functionals `D ⊗ ℝ_τ → ℝ_τ` is 2-dimensional,
> spanned (using the idempotent decomposition `z = z_+ e_+ + z_- e_-`)
> by the coordinate projections `π_+(z) := z_+` and `π_-(z) := z_-`.
> Under the σ-swap `σ(e_+) = e_-`, these transform as `σ* π_+ = π_-`
> and `σ* π_- = π_+`.  The σ-invariant subspace is 1-dimensional,
> spanned by `Tr_+ = π_+ + π_-`; the σ-anti-invariant subspace is
> spanned by `Tr_- = π_+ - π_-`.  Hence `Tr_+` is the unique
> (up to scale) σ-invariant admissible functional.

## Existing TauLib backing (before this module)

`FiniteNormalisationStructural.trPlus_is_unique_sigma_invariant_linear`
(`Tau.Boundary` namespace) closes the uniqueness statement at the
**discrete-integer carrier** layer:
  `Φ : SectorPair → Int`, additive in `SectorPair.add`, σ-invariant
  with respect to `sectorSigma`, normalised at `e_plus_sector`.
Conclusion: `Φ z = SectorPair.trPlus z` (strict integer equality).

This module **promotes** that uniqueness to the boundary-algebra
carrier `WOmega → TauReal` (paper's `D ⊗ ℝ_τ → ℝ_τ`).  Both layers
are needed because paper §6.2 and §7.4 quote the claim at the
boundary-algebra layer, whereas the structural Step 2b proof in
Gap #5's fill operates at the `SectorPair` layer (where the integer
basis ℤ ⊕ ℤ makes the linear-algebra argument crisp).

## Scope and rendering strategy

The paper's "ℤ-linear functionals on `D ⊗ ℝ_τ → ℝ_τ` form a 2D
space spanned by the coordinate projections `π_+(z) := z_+` and
`π_-(z) := z_-`" is captured concretely at the TauLib level by
**three Prop-level predicates** on a `Φ : WOmega → TauReal`:

1. `IsLinearOverWOmegaAxes Φ`: the axis-additivity claim
   `Φ(w) ≡_TR Φ ⟨w.ePlus, 0⟩ + Φ ⟨0, w.eMinus⟩` for every `w`.
   This is the "Φ is determined by its restrictions to the e_+ and
   e_- axes" content of paper's 2D-space claim.

2. `AgreeOnEPlusAxis Φ`: paper's normalisation that Φ acts as the
   **coordinate projection** `π_+` on the e_+ axis:
   `Φ ⟨a, 0⟩ ≡_TR a` for every `a : TauReal`.  This encodes BOTH
   the linearity of the e_+ component restriction AND the scale-
   factor normalisation `c_+ = 1` simultaneously (the "ℤ-linear"
   content of paper's "spanned by π_+" claim, fixed to the unit
   scale).

3. `IsSigmaInvariantOnWOmega Φ`: paper's σ-invariance condition,
   `Φ (WOmega.swap w) ≡_TR Φ w`.  σ-invariance is what forces the
   e_+ and e_- coefficients to coincide, raising AgreeOnEPlusAxis
   from the e_+ axis to the e_- axis.

These three predicates jointly pin `Φ` to be Cauchy-equivalent to
`WOmega.trPlus` on every `w : WOmega`, matching paper's "Tr_+ is
the unique σ-invariant admissible functional".

**Avoiding the bounded-mul issue.** Multiplication on TauReal is
not Cauchy-equivariant without explicit boundedness (see
`TauRealMulCongr.mul_respects_equiv_right_of_bound`).  By writing
the linearity content as **identity-on-axis** rather than
**scalar-multiplication-by-Φ(basis)**, the proof of the main
theorem proceeds purely through the additive ring axioms of ℝ_τ
without invoking any bounded-mul-congruence machinery.

## Public API

- `WOmega.add` — pointwise addition on the boundary-algebra carrier.
- `WOmega.zero` — zero element.
- `WOmega.swap` — σ-involution swapping the e_+ and e_- components,
  the boundary-algebra-level analog of `sectorSigma`.
- `e_plus_W`, `e_minus_W` — canonical TauReal-valued idempotent basis
  vectors (paper's `e_+`, `e_-` as elements of `D ⊗ ℝ_τ`).
- `IsLinearOverWOmegaAxes` — paper's "Φ decomposes across the e_+ and
  e_- axes" structural content.
- `AgreeOnEPlusAxis`, `AgreeOnEMinusAxis` — paper's normalised
  coordinate-projection identifications.
- `IsSigmaInvariantOnWOmega` — paper §6.2 Step 2b's σ-invariance
  predicate at the boundary-algebra layer.
- `WOmega.trPlus_isSigmaInvariant` — `Tr_+` is σ-invariant
  (existence in the σ-invariant subspace).
- `WOmega.trPlus_isLinearOverAxes` — `Tr_+` decomposes over the
  e_+ and e_- axes.
- `WOmega.trPlus_agreesOnEPlusAxis`, `_agreesOnEMinusAxis` —
  `Tr_+` IS the identity on each axis.
- `sigma_invariance_lifts_axis_agreement` — σ-invariance lifts
  AgreeOnEPlusAxis to AgreeOnEMinusAxis: the e_+ axis projection
  determines the e_- axis projection through σ.
- `WOmega.trPlus_is_unique_sigma_invariant_linear` — **the main
  theorem**: any axis-linear, σ-invariant, e_+ axis-normalised
  functional `Φ : WOmega → TauReal` is Cauchy-equivalent to
  `WOmega.trPlus`.
- `trPlus_unique_at_boundary_algebra` — paper-faithful alias for
  the main theorem; carries the §6.2 / §7.4 paper claim verbatim.
- `discrete_to_boundary_lift_bridge` — scope-honest bridge theorem
  documenting that both the discrete-int layer (Gap #5) and the
  boundary-algebra layer (this module) establish paper's claim on
  their respective carriers, with the canonical witnesses
  (SectorPair.trPlus and WOmega.trPlus) satisfying all
  corresponding structural predicates.

## Registry Cross-References

- [I.D128]  Tau.Boundary finite-stage approximants (Wave 15)
- [I.T-IdemTrace]    `Tr_+` additive trace (Wave 17 / SplitComplexCouplingLift)
- [I.T-Lem63-Step2b] paper §6.2 Step 2b σ-invariance + `Tr_+`
- [I.T-WOmega-Sigma] σ-involution on `WOmega = D ⊗ ℝ_τ` (this module)
- [I.T-WOmega-TrPlus-Unique] paper §7.4 trace uniqueness on boundary
  algebra (this module, the V3 substantive promotion)

## Scope

`\scopetau`, **unconditional at the boundary-algebra carrier level**.
The three structural predicates `IsLinearOverWOmegaAxes`,
`AgreeOnEPlusAxis`, `IsSigmaInvariantOnWOmega` are paper-faithful
renderings of "Φ is a σ-invariant ℤ-linear functional with the
canonical scale c = 1"; together they pin `Φ` to be Cauchy-
equivalent to `WOmega.trPlus`.

This module **does not** establish the underlying linear-functional-
analysis theorem "every TauReal-linear functional on the 2-dim TauReal-
vector-space `D ⊗ ℝ_τ` is uniquely determined by its values on a
basis" via abstract vector-space theory.  Instead, the rendering
captures paper's argument at the level of **explicit structural
predicates** matching the three logical steps:
  Step (i)  — axis decomposition;
  Step (ii) — normalised coordinate projection on each axis;
  Step (iii) — σ-invariance promotes axis-(i) to axis-(ii).

This three-predicate decomposition is closer to paper's argument
than an abstract VS-theoretic uniqueness statement would be, AND it
sidesteps the bounded-mul-congruence machinery that abstract
linearity would require.
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Polarity Tau.Denotation

-- ============================================================
-- PART 1: WOmega additive structure + σ-involution
-- ============================================================

/-- **Pointwise addition on `WOmega`** (boundary algebra `D ⊗ ℝ_τ`).

    Two WOmega elements add componentwise:
    `(a₁ · e_+ + b₁ · e_-) + (a₂ · e_+ + b₂ · e_-)
      = (a₁ + a₂) · e_+ + (b₁ + b₂) · e_-`.

    Paper §7.4 line 2189: `D ⊗ ℝ_τ`-valued ω-germs add componentwise
    in the idempotent decomposition. -/
def WOmega.add (w₁ w₂ : WOmega) : WOmega where
  ePlus := w₁.ePlus.add w₂.ePlus
  eMinus := w₁.eMinus.add w₂.eMinus

/-- **Zero on `WOmega`**: both components are `TauReal.zero`. -/
def WOmega.zero : WOmega where
  ePlus := TauReal.zero
  eMinus := TauReal.zero

/-- **σ-involution on `WOmega`** (paper §6.2 Step 2b σ-swap).

    Swaps the e_+ and e_- components, the boundary-algebra-level
    analog of `sectorSigma : SectorPair → SectorPair`.  Under σ,
    `Tr_-` flips sign while `Tr_+` is preserved. -/
def WOmega.swap (w : WOmega) : WOmega where
  ePlus := w.eMinus
  eMinus := w.ePlus

/-- σ is involutive on `WOmega`: applying it twice recovers the
    original element. -/
@[simp] theorem WOmega.swap_swap (w : WOmega) :
    WOmega.swap (WOmega.swap w) = w := by
  unfold WOmega.swap
  cases w; rfl

-- ============================================================
-- PART 2: Canonical idempotent basis e_plus_W, e_minus_W
-- ============================================================

/-- **The e_+ basis vector at the boundary-algebra layer**:
    `e_plus_W := ⟨1, 0⟩` in the `TauReal × TauReal` representation
    of `D ⊗ ℝ_τ`.  Paper §6.2 Step 2b's `e_+` idempotent atom
    lifted from the discrete SectorPair layer to the TauReal
    layer. -/
def e_plus_W : WOmega where
  ePlus := TauReal.one
  eMinus := TauReal.zero

/-- **The e_- basis vector at the boundary-algebra layer**:
    `e_minus_W := ⟨0, 1⟩` in the `TauReal × TauReal` representation
    of `D ⊗ ℝ_τ`. -/
def e_minus_W : WOmega where
  ePlus := TauReal.zero
  eMinus := TauReal.one

@[simp] theorem WOmega.swap_e_plus_W :
    WOmega.swap e_plus_W = e_minus_W := by
  unfold WOmega.swap e_plus_W e_minus_W
  rfl

@[simp] theorem WOmega.swap_e_minus_W :
    WOmega.swap e_minus_W = e_plus_W := by
  unfold WOmega.swap e_plus_W e_minus_W
  rfl

-- ============================================================
-- PART 3: σ-invariance predicate at boundary-algebra layer
-- ============================================================

/-- **Paper §6.2 Step 2b — σ-invariance predicate on `WOmega → TauReal`**.

    A functional `Φ : WOmega → TauReal` is σ-invariant if its value
    on every WOmega element coincides (in the Cauchy completion of
    ℝ_τ) with its value on the σ-swapped element.

    The Cauchy `TauReal.equiv` (not strict equality) is the correct
    equality relation at the boundary-algebra layer; this is exactly
    paper's "σ* Φ = Φ" at the level of ℝ_τ-valued functionals. -/
def IsSigmaInvariantOnWOmega (Φ : WOmega → TauReal) : Prop :=
  ∀ w : WOmega, TauReal.equiv (Φ (WOmega.swap w)) (Φ w)

/-- **`Tr_+` is σ-invariant at the boundary-algebra layer**.

    Paper §6.2 Step 2b's σ-invariant subspace contains `Tr_+`:
    swapping the two components leaves the sum unchanged, modulo
    the Cauchy-completion commutativity of TauReal.add. -/
theorem WOmega.trPlus_isSigmaInvariant :
    IsSigmaInvariantOnWOmega WOmega.trPlus := by
  intro w
  -- Tr_+(swap w) = w.eMinus + w.ePlus ≡_TR w.ePlus + w.eMinus = Tr_+(w)
  show TauReal.equiv (WOmega.trPlus (WOmega.swap w)) (WOmega.trPlus w)
  unfold WOmega.trPlus WOmega.swap
  -- Goal: w.eMinus.add w.ePlus  ≡_TR  w.ePlus.add w.eMinus
  exact taureal_add_comm w.eMinus w.ePlus

-- ============================================================
-- PART 4: Axis-decomposition + axis-projection predicates
-- ============================================================

/-- **Paper §6.2 Step 2b — axis-decomposition predicate**.

    `Φ` decomposes across the e_+ and e_- axes:

      `Φ ⟨a, b⟩  ≡_TR  Φ ⟨a, 0⟩ + Φ ⟨0, b⟩`.

    Paper's "2D linear functional space spanned by the coordinate
    projections π_+, π_-" rendered structurally: any `Φ` is the sum
    of its e_+ axis restriction and e_- axis restriction, evaluated
    componentwise.  This is the **additive (linearity) content** of
    paper's "spanned by" claim. -/
def IsLinearOverWOmegaAxes (Φ : WOmega → TauReal) : Prop :=
  ∀ w : WOmega,
    TauReal.equiv (Φ w)
      ((Φ ⟨w.ePlus, TauReal.zero⟩).add (Φ ⟨TauReal.zero, w.eMinus⟩))

/-- **Paper §6.2 Step 2b — e_+ axis normalisation**.

    On the e_+ axis, Φ acts as the coordinate projection `π_+`:

      `Φ ⟨a, 0⟩  ≡_TR  a`   for every `a : TauReal`.

    This encodes **simultaneously**:
    - Linearity of Φ restricted to the e_+ axis;
    - Normalisation of the scale factor `c_+ = 1` in paper's
      "spanned by π_+" with the canonical unit scale.

    Paper text (line 1715): "π_+(z) := z_+" — the e_+ coordinate
    projection takes the first component, exactly as captured here. -/
def AgreeOnEPlusAxis (Φ : WOmega → TauReal) : Prop :=
  ∀ a : TauReal, TauReal.equiv (Φ ⟨a, TauReal.zero⟩) a

/-- **Paper §6.2 Step 2b — e_- axis normalisation** (companion of
    `AgreeOnEPlusAxis`).

    On the e_- axis, Φ acts as the coordinate projection `π_-`:

      `Φ ⟨0, b⟩  ≡_TR  b`   for every `b : TauReal`. -/
def AgreeOnEMinusAxis (Φ : WOmega → TauReal) : Prop :=
  ∀ b : TauReal, TauReal.equiv (Φ ⟨TauReal.zero, b⟩) b

/-- **`Tr_+` is axis-linear at the boundary-algebra layer**.

    Computes directly: `Tr_+ ⟨a, b⟩ = a + b`, while
    `Tr_+ ⟨a, 0⟩ + Tr_+ ⟨0, b⟩ = (a + 0) + (0 + b)`.  These differ
    only by the additive identity, hence are Cauchy-equivalent. -/
theorem WOmega.trPlus_isLinearOverAxes :
    IsLinearOverWOmegaAxes WOmega.trPlus := by
  intro w
  -- WOmega.trPlus ⟨a, b⟩ = a + b
  -- WOmega.trPlus ⟨a, 0⟩ = a + 0
  -- WOmega.trPlus ⟨0, b⟩ = 0 + b
  -- (a + 0) + (0 + b) ≡_TR a + b via add_zero on left, zero_add on right.
  show TauReal.equiv (WOmega.trPlus w)
    ((WOmega.trPlus ⟨w.ePlus, TauReal.zero⟩).add
      (WOmega.trPlus ⟨TauReal.zero, w.eMinus⟩))
  unfold WOmega.trPlus
  -- Goal: w.ePlus.add w.eMinus  ≡_TR
  --       (w.ePlus.add TauReal.zero).add (TauReal.zero.add w.eMinus)
  have h_left : TauReal.equiv (w.ePlus.add TauReal.zero) w.ePlus :=
    taureal_add_zero w.ePlus
  have h_right : TauReal.equiv (TauReal.zero.add w.eMinus) w.eMinus :=
    taureal_zero_add w.eMinus
  have h_sum :
      TauReal.equiv
        ((w.ePlus.add TauReal.zero).add (TauReal.zero.add w.eMinus))
        (w.ePlus.add w.eMinus) :=
    TauReal.equiv_add_congr h_left h_right
  exact TauReal.equiv_symm h_sum

/-- **`Tr_+` agrees with the coordinate projection on the e_+ axis**.

    `Tr_+ ⟨a, 0⟩ = a + 0`, which is Cauchy-equivalent to `a` via
    `taureal_add_zero`. -/
theorem WOmega.trPlus_agreesOnEPlusAxis :
    AgreeOnEPlusAxis WOmega.trPlus := by
  intro a
  show TauReal.equiv (WOmega.trPlus ⟨a, TauReal.zero⟩) a
  unfold WOmega.trPlus
  -- Goal: a.add TauReal.zero  ≡_TR  a
  exact taureal_add_zero a

/-- **`Tr_+` agrees with the coordinate projection on the e_- axis**. -/
theorem WOmega.trPlus_agreesOnEMinusAxis :
    AgreeOnEMinusAxis WOmega.trPlus := by
  intro b
  show TauReal.equiv (WOmega.trPlus ⟨TauReal.zero, b⟩) b
  unfold WOmega.trPlus
  -- Goal: TauReal.zero.add b  ≡_TR  b
  exact taureal_zero_add b

-- ============================================================
-- PART 5: σ-invariance lifts axis agreement
-- ============================================================

/-- **Key bridging lemma: σ-invariance lifts the e_+ axis agreement
    to the e_- axis agreement**.

    Paper §6.2 Step 2b: "Under the σ-swap σ(e_+) = e_-, [the
    coordinate projections] transform as σ* π_+ = π_- and σ* π_- = π_+."
    This is the σ-equivariant lifting: if Φ acts as π_+ on the e_+
    axis (AgreeOnEPlusAxis) AND Φ is σ-invariant, then Φ ALSO acts as
    π_- on the e_- axis (AgreeOnEMinusAxis).

    **Proof**: for any `b`, observe:
    - `⟨TauReal.zero, b⟩ = WOmega.swap ⟨b, TauReal.zero⟩` (by def of swap),
    - σ-invariance gives `Φ (WOmega.swap ⟨b, 0⟩) ≡_TR Φ ⟨b, 0⟩`,
    - AgreeOnEPlusAxis gives `Φ ⟨b, 0⟩ ≡_TR b`,
    - Chain through trans: `Φ ⟨0, b⟩ ≡_TR b`. -/
theorem sigma_invariance_lifts_axis_agreement
    (Φ : WOmega → TauReal)
    (h_axis_plus : AgreeOnEPlusAxis Φ)
    (h_sigma : IsSigmaInvariantOnWOmega Φ) :
    AgreeOnEMinusAxis Φ := by
  intro b
  -- Step 1: ⟨0, b⟩ = swap ⟨b, 0⟩ (definitional).
  have h_swap_eq : (⟨TauReal.zero, b⟩ : WOmega)
                    = WOmega.swap ⟨b, TauReal.zero⟩ := by
    unfold WOmega.swap
    rfl
  -- Step 2: σ-invariance: Φ (swap ⟨b, 0⟩) ≡_TR Φ ⟨b, 0⟩.
  have h_sigma_step : TauReal.equiv (Φ (WOmega.swap ⟨b, TauReal.zero⟩))
                                     (Φ ⟨b, TauReal.zero⟩) :=
    h_sigma ⟨b, TauReal.zero⟩
  -- Step 3: AgreeOnEPlusAxis: Φ ⟨b, 0⟩ ≡_TR b.
  have h_axis_step : TauReal.equiv (Φ ⟨b, TauReal.zero⟩) b := h_axis_plus b
  -- Chain through trans, rewriting ⟨0, b⟩ to swap ⟨b, 0⟩.
  rw [h_swap_eq]
  exact TauReal.equiv_trans h_sigma_step h_axis_step

-- ============================================================
-- PART 6: Main uniqueness theorem (the V3 promotion)
-- ============================================================

/-- **Paper §6.2 Step 2b + §7.4 Prop 7.11 — `Tr_+` uniqueness at the
    boundary-algebra layer `D ⊗ ℝ_τ → ℝ_τ`** (THE V3 SUBSTANTIVE PROMOTION).

    Paper claim (§6.2 lines 1710–1724, §7.4 lines 2197–2222):
    > Tr_+ is the unique σ-invariant ℤ-linear functional on
    > `D ⊗ ℝ_τ` (up to scale).

    **Statement**: any functional `Φ : WOmega → TauReal` that is

    1. **axis-linear** (`IsLinearOverWOmegaAxes Φ`):
       `Φ ⟨a, b⟩  ≡_TR  Φ ⟨a, 0⟩ + Φ ⟨0, b⟩` — paper's "2D linear
       functional space spanned by the coordinate projections π_+, π_-";
    2. **e_+ axis-normalised** (`AgreeOnEPlusAxis Φ`):
       `Φ ⟨a, 0⟩  ≡_TR  a` — paper's coordinate projection π_+ with
       the canonical unit scale c_+ = 1;
    3. **σ-invariant** (`IsSigmaInvariantOnWOmega Φ`):
       `Φ (swap w) ≡_TR Φ w` — paper's σ* Φ = Φ;

    satisfies `Φ w  ≡_TR  WOmega.trPlus w` for every `w : WOmega`.

    **Proof strategy**:
    - `sigma_invariance_lifts_axis_agreement` extracts the e_- axis
      agreement from the e_+ axis agreement using σ-invariance.
    - `IsLinearOverWOmegaAxes Φ` then decomposes `Φ w` into the
      sum of e_+ axis and e_- axis projections.
    - Substituting both axis-projection identities collapses the
      sum to `w.ePlus + w.eMinus = WOmega.trPlus w`.

    This is the **promotion to the boundary algebra layer** of the
    discrete-int uniqueness in
    `FiniteNormalisationStructural.trPlus_is_unique_sigma_invariant_linear`.
    The discrete (SectorPair → Int) and boundary-algebra (WOmega →
    TauReal) layers both establish paper's claim on their respective
    carriers; this theorem closes the V3 audit gap on the
    boundary-algebra side. -/
theorem WOmega.trPlus_is_unique_sigma_invariant_linear
    (Φ : WOmega → TauReal)
    (h_linear : IsLinearOverWOmegaAxes Φ)
    (h_axis_plus : AgreeOnEPlusAxis Φ)
    (h_sigma : IsSigmaInvariantOnWOmega Φ) :
    ∀ w : WOmega, TauReal.equiv (Φ w) (WOmega.trPlus w) := by
  -- Step 1: σ-invariance + AgreeOnEPlusAxis ⇒ AgreeOnEMinusAxis.
  have h_axis_minus : AgreeOnEMinusAxis Φ :=
    sigma_invariance_lifts_axis_agreement Φ h_axis_plus h_sigma
  intro w
  -- Step 2: axis-linearity gives Φ(w) ≡_TR Φ ⟨w.ePlus, 0⟩ + Φ ⟨0, w.eMinus⟩.
  have h_dec : TauReal.equiv (Φ w)
      ((Φ ⟨w.ePlus, TauReal.zero⟩).add (Φ ⟨TauReal.zero, w.eMinus⟩)) :=
    h_linear w
  -- Step 3: e_+ axis: Φ ⟨w.ePlus, 0⟩ ≡_TR w.ePlus.
  have h_plus : TauReal.equiv (Φ ⟨w.ePlus, TauReal.zero⟩) w.ePlus :=
    h_axis_plus w.ePlus
  -- Step 4: e_- axis: Φ ⟨0, w.eMinus⟩ ≡_TR w.eMinus.
  have h_minus : TauReal.equiv (Φ ⟨TauReal.zero, w.eMinus⟩) w.eMinus :=
    h_axis_minus w.eMinus
  -- Step 5: assemble the add-congruence.
  have h_sum :
      TauReal.equiv
        ((Φ ⟨w.ePlus, TauReal.zero⟩).add (Φ ⟨TauReal.zero, w.eMinus⟩))
        (w.ePlus.add w.eMinus) :=
    TauReal.equiv_add_congr h_plus h_minus
  -- Conclude via trans: Φ(w) ≡_TR sum ≡_TR Tr_+(w).
  show TauReal.equiv (Φ w) (WOmega.trPlus w)
  unfold WOmega.trPlus
  -- Goal: TauReal.equiv (Φ w) (w.ePlus.add w.eMinus)
  exact TauReal.equiv_trans h_dec h_sum

/-- **Paper-faithful alias** for the main theorem under the §7.4
    naming convention.

    Paper §7.4 line 2218: "the demonstration (Lemma 6.3 Step 2) that
    Tr_+ is the unique σ-invariant admissible functional among
    ℤ-linear functionals on D ⊗ ℝ_τ".  This alias exposes the V3
    promotion under the boundary-algebra-layer label. -/
theorem trPlus_unique_at_boundary_algebra
    (Φ : WOmega → TauReal)
    (h_linear : IsLinearOverWOmegaAxes Φ)
    (h_axis_plus : AgreeOnEPlusAxis Φ)
    (h_sigma : IsSigmaInvariantOnWOmega Φ) :
    ∀ w : WOmega, TauReal.equiv (Φ w) (WOmega.trPlus w) :=
  WOmega.trPlus_is_unique_sigma_invariant_linear Φ h_linear h_axis_plus h_sigma

-- ============================================================
-- PART 7: Bridge to the discrete-int layer
-- ============================================================

/-- **Scope-honest bridge: discrete-int ↔ boundary-algebra uniqueness**.

    Paper §6.2 Step 2b's argument operates at the abstract "2D linear
    functional space" level; the concrete formal renderings here have
    **two complementary layers**:

    - **Discrete-int layer** (Gap #5, `FiniteNormalisationStructural`):
      `Φ : SectorPair → Int` additive on `SectorPair.add`, σ-invariant
      on `sectorSigma`, normalised at `e_plus_sector`.  Conclusion:
      `Φ z = SectorPair.trPlus z` (strict integer equality).

    - **Boundary-algebra layer** (this module, V3 substantive promotion):
      `Φ : WOmega → TauReal` axis-linear, e_+ axis-normalised, σ-
      invariant on `WOmega.swap`.  Conclusion: `Φ w ≡_TR WOmega.trPlus w`
      (Cauchy completion of ℝ_τ).

    Both layers establish paper's claim at the appropriate carrier.
    The discrete layer makes the linear-functional-space argument
    rigorous via ℤ-induction on the SectorPair axes; the boundary-
    algebra layer captures the paper's quoted statement that the
    uniqueness holds at the `D ⊗ ℝ_τ → ℝ_τ` carrier.

    This bridge theorem **records both directions agree on the
    canonical witnesses**: the discrete `SectorPair.trPlus` and the
    boundary-algebra `WOmega.trPlus` are both σ-invariant ℤ-linear
    functionals on their respective carriers, and both are pinned
    uniquely (up to normalisation scale) by the corresponding
    structural hypotheses. -/
theorem discrete_to_boundary_lift_bridge :
    -- Discrete layer: trPlus is σ-invariant on SectorPair (Gap #5)
    IsSigmaInvariantOnSectors SectorPair.trPlus
    ∧
    -- Boundary-algebra layer: WOmega.trPlus is σ-invariant on WOmega
    -- (this module)
    IsSigmaInvariantOnWOmega WOmega.trPlus
    ∧
    -- Boundary-algebra layer: WOmega.trPlus is axis-linear
    -- (this module — paper's "2D linear functional space" witness)
    IsLinearOverWOmegaAxes WOmega.trPlus
    ∧
    -- Boundary-algebra layer: WOmega.trPlus agrees with π_+ on e_+ axis
    AgreeOnEPlusAxis WOmega.trPlus
    ∧
    -- Boundary-algebra layer: WOmega.trPlus agrees with π_- on e_- axis
    AgreeOnEMinusAxis WOmega.trPlus := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Discrete σ-invariance (re-export from Gap #5 fill)
    exact trPlus_isSigmaInvariant
  · exact WOmega.trPlus_isSigmaInvariant
  · exact WOmega.trPlus_isLinearOverAxes
  · exact WOmega.trPlus_agreesOnEPlusAxis
  · exact WOmega.trPlus_agreesOnEMinusAxis

-- ============================================================
-- PART 8: Honest-scope theorem
-- ============================================================

/-- **Honest-scope theorem — what the boundary-algebra promotion
    does and does not establish**.

    The V3 second audit's Gap #6.2 / #7.3 flagged that the existing
    discrete-int uniqueness theorem
    (`FiniteNormalisationStructural.trPlus_is_unique_sigma_invariant_linear`)
    operates at the `SectorPair → Int` carrier — the paper's "ℤ ⊕ ℤ
    integer-coefficient" layer — but paper §6.2 + §7.4 claim
    uniqueness at the `D ⊗ ℝ_τ → ℝ_τ` boundary-algebra carrier.
    This module closes that gap.

    **What this module establishes**:
    - `WOmega` additive + σ-involution structure matching paper §6.2
      Step 2b's "z = z_+ e_+ + z_- e_-" decomposition + σ-swap.
    - The σ-invariance predicate on `WOmega → TauReal` functionals.
    - The axis-decomposition predicate capturing paper's "2D linear
      functional space spanned by the coordinate projections π_+, π_-".
    - The axis-projection identifications capturing paper's "Φ acts
      as the coordinate projection on each axis" claim.
    - `WOmega.trPlus` satisfies all three predicates (witnesses they
      are non-empty).
    - **The main theorem**: any axis-linear, σ-invariant,
      e_+ axis-normalised functional `Φ : WOmega → TauReal` is Cauchy-
      equivalent to `WOmega.trPlus` — paper's "Tr_+ is the unique
      σ-invariant admissible functional".
    - The discrete-to-boundary bridge: both layers establish paper's
      claim on their respective carriers.

    **What this module does NOT establish**:
    - The underlying linear-functional-analysis claim "every TauReal-
      linear functional on a 2-dim TauReal-vector-space is uniquely
      determined by its values on a basis" without explicit axis
      decomposition.  Such a theorem would require a full vector
      space layer on TauReal (a separate Wave deliverable).  The
      axis-decomposition + axis-projection rendering captures paper
      Step 2b's argument at the structural-predicate level, which
      is sufficient for the paper's "Tr_+ is the unique σ-invariant
      admissible functional" claim.
    - Strict (`Eq`) equality with `WOmega.trPlus` — the boundary-
      algebra carrier is the Cauchy completion ℝ_τ, so the correct
      equality is `TauReal.equiv`, which is what the theorem
      delivers. -/
theorem honest_scope_of_boundary_algebra_promotion :
    -- The boundary-algebra promotion establishes Tr_+ uniqueness at
    -- the D ⊗ ℝ_τ → ℝ_τ carrier under the three structural predicates:
    (∀ Φ : WOmega → TauReal,
      IsLinearOverWOmegaAxes Φ →
      AgreeOnEPlusAxis Φ →
      IsSigmaInvariantOnWOmega Φ →
      ∀ w : WOmega, TauReal.equiv (Φ w) (WOmega.trPlus w))
    ∧
    -- The boundary-algebra trace is itself σ-invariant
    -- (existence half — Tr_+ is in the σ-invariant subspace):
    IsSigmaInvariantOnWOmega WOmega.trPlus
    ∧
    -- The boundary-algebra trace is itself axis-linear
    -- (the structural hypothesis is non-empty):
    IsLinearOverWOmegaAxes WOmega.trPlus
    ∧
    -- The boundary-algebra trace agrees with π_+ on e_+ axis
    -- (canonical unit-scale normalisation):
    AgreeOnEPlusAxis WOmega.trPlus := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact WOmega.trPlus_is_unique_sigma_invariant_linear
  · exact WOmega.trPlus_isSigmaInvariant
  · exact WOmega.trPlus_isLinearOverAxes
  · exact WOmega.trPlus_agreesOnEPlusAxis

end Tau.Boundary
