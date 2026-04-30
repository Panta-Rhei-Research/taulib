# Primitive Linking-Class Selection Rule for `d_top = 1` Contraction

**Author:** Specialist δ, Wave R8a Wave 1 of the V.T-NEW-5 sprint (April 2026).

**Mission:** settle the (0,1) bottleneck vs (1,0) dominant question for the primitive linking class in `d_top = 1` quasi-isothermal contraction. This question gates the V.T-LRD-1B headline `log₁₀ M_BH^max`.

**TL;DR (decision-grade summary).** Selection rule resolves **definitively to (0,1)** as the unique primitive linking class admissible under V.T40 + V.T-NEW-5. Wave R7 headline `log₁₀ M_BH^max ≈ 6.54 ± 0.10` **stands**. **R1 NOT triggered. R4 NOT triggered.** The (1,0) alternative is forbidden because the dominant-cycle reading requires a `J = J(M)` constitutive relation incompatible with V.T40 base/fiber asymmetry.

---

## 1. The two candidate selection rules

The `LinkingClass` struct ([BHBirthTopology.lean:110-117](../TauLib/BookV/Cosmology/BHBirthTopology.lean)) carries `(a, b : Int)` with `nontrivial : a ≠ 0 ∨ b ≠ 0`. The fiber-shape encoding ([BHBirthTopology.lean:273-284](../TauLib/BookV/Cosmology/BHBirthTopology.lean)) identifies:

- **`a` (γ-circle, radius `R = ℓ_τ`)** — the EM-sector / gravity-aligned cycle.
- **`b` (η-circle, radius `r = ι_τ · ℓ_τ`)** — the Strong-sector / transverse cycle.

A *primitive* linking class is one whose components are coprime (`gcd(|a|, |b|) = 1`) and minimal in the V.T110 quotient.

**Candidate (0,1) — "Bottleneck / transport-limited" (E's R7 reading):**
- Mechanism: η-cycle saturates first because its smaller radius gives the smaller transport cross-section per coherence-tick.
- Implied bound: `J_max^{T²} = ι_τ √κ_D · GM²/c ≈ 0.277 · GM²/c`.
- Headline: `log₁₀(M_BH^max/M_⊙) ≈ 6.54` at `z = 11`.

**Candidate (1,0) — "Dominant cycle / equilibrium-selected":**
- Mechanism: γ-cycle holds the most J-budget at equilibrium.
- Implied bound: `J_max^{T²} = √(κ_D(1 + (3/4)ι_τ²)) · GM²/c ≈ 0.847 · GM²/c`.
- Headline: `log₁₀(M_BH^max/M_⊙) ≈ 7.0` — a +0.46 dex shift from (0,1), squarely **R1 risk-gate territory**.

---

## 2. Selection rule from V.T40 + V.T-NEW-5

Take Specialist α's V.T-NEW-5 statement as given. The combined V.T40 + V.T-NEW-5 selector is a **two-clause filter:**
1. (V.T-NEW-5 existence) Admit only primitive `ℓ` for which the J-budget extends to a global Killing co-vector.
2. (V.T40 consistency) Reject any `ℓ` whose J-budget would force a defect cost `S_def > 0` on a non-decreasing-mass evolution.

### 2.1 V.T40 / V.T114 base/fiber asymmetry, restated

The `MatureBlackHole` struct ([NoShrinkExtended.lean:72-89](../TauLib/BookV/Cosmology/NoShrinkExtended.lean)) carries `defect_zero : Bool := true` and the `no_shrink_theorem` ([NoShrinkExtended.lean:131](../TauLib/BookV/Cosmology/NoShrinkExtended.lean)) gives `mass_n_plus_1 ≥ mass_n`. The structural content is asymmetric:

- **Base direction (mass / γ-cycle / `a`-component).** Monotonically non-decreasing under ρ (V.T40). Defect cost is *one-sided*: `dM/dn < 0` is forbidden.
- **Fiber direction (J / η-cycle / `b`-component).** No analogous monotonicity. The η-cycle is the *transport channel*.

This asymmetry is exactly Specialist G's coherence projection `Π_coh` killing `ω_η` at the level of the *budget functional*, but **not** at the level of *transport*. G's projection acts on coherent-budget cohomology; the η-cycle remains the active transport channel even though its budget contribution vanishes after projection. This distinction is **load-bearing** for resolving the (0,1) vs (1,0) question.

### 2.2 V.T-NEW-5 admissibility for each candidate

**(1,0) test.** Asserts γ-cycle carries the entire primitive J-budget. The τ-Kerr extension must promote `∂_θ` (η-cycle generator) to a Killing vector with *trivial* action on the J-functional. But V.T110 fiber structure gives `r/R = ι_τ ≠ 0`, so the η-cycle has finite radius and any Killing extension along `∂_θ` carries non-trivial Lie-derivative on the metric volume form, hence on the J-current. The Killing extension is *not* trivial — it is V.T110-fixed at `ι_τ`. So (1,0) requires the J-functional to ignore non-trivial Killing data, which V.T-NEW-5 forbids.

Equivalently: (1,0) produces a J-budget formula `J = √(κ_D(1 + (3/4)ι_τ²)) · GM²/c` mixing both Killing directions on equal footing. This is the *generic* T²-Kerr reading without V.T40's asymmetry. V.T-NEW-5 rules it out by demanding the unique extension *be* the asymmetric one.

**(0,1) test.** η-cycle carries the J-budget *as the rate-limiting transport channel*; γ-cycle's contribution is V.T40-locked into the M-direction. The τ-Kerr extension promotes `∂_θ` along the η-cycle direction with `r/R = ι_τ`, giving the `ι_τ`-prefactor; `√κ_D` from V.T109 threshold-survival. Result: `J_max^{T²} = ι_τ √κ_D · GM²/c` — exactly the rigid extension demanded by V.T-NEW-5 + V.T40.

### 2.3 V.T40 consistency check (the decisive step)

Consider a candidate evolution under (1,0): γ-cycle holds the J-budget, so `J = J_γ(M)` constitutively. V.T40 forces `dM/dn ≥ 0` everywhere. But the J-budget under (1,0) is *not* a one-sided functional — symmetric in `(a, b)`-rotations of the primitive class. Any J-shedding event must be balanced by an opposite-sign perturbation. Since (1,0) deactivates the η-cycle as transport channel, *any* J-shedding must come at the cost of `dM_γ/dn < 0` on the γ-budget — **contradicting V.T40**.

Under (0,1): J-shedding flows through η-cycle, which is *not* the mass-carrying cycle. V.T40 preserved trivially.

**Conclusion: only (0,1) survives both filters. Selection definitively (0,1).**

---

## 3. Confidence interval on J_max^{T²}

$$\boxed{J_{\max}^{T^2} = \iota_\tau\sqrt{\kappa_D}\,GM^2/c \approx 0.277\,GM^2/c}$$

$$\boxed{\log_{10}(M_{\rm BH}^{\max}/M_\odot) \approx 6.54 \pm 0.10 \text{ at } z = 11}$$

**Confidence interval rationale:** ±0.10 dex envelope from Wave R7 preserved unchanged. The (0,1) vs (1,0) ambiguity contributed *zero* dex (both are point-estimates). Remaining sources (Mo-Mao-White λ̄, f_cool, f_b, multi-stage η_J ≈ 0.08) unchanged.

---

## 4. R-flag dispositions

- **R1 (β/E vs γ/G divergence > 0.5 dex on J_max^{T²}):** **NO TRIGGER.** Numerical shift 0.000 dex. The 0.46 dex shift to log₁₀M_BH^max ≈ 7.0 that would have triggered pause is precluded.
- **R2 (linking-class unresolvable):** **NOT APPLICABLE.** V.T-NEW-5 is a categorical uniqueness statement; no degree of freedom for sub-region heterogeneity in the linking-class assignment.
- **R4 (selection rule contradicts V.T40):** **NOT TRIGGERED.** (0,1) does NOT force `J = 0`; γ-cycle still carries Kerr-like centrifugal `√κ_D · GM²/c` as a *non-quantised* J-component. η-cycle carries the *quantised* primitive holonomy. Total `J_max^{T²} = ι_τ · √κ_D · GM²/c`.

---

## 5. Lean formalisation hints (for Specialist ε's T2KerrUniqueness.lean)

Five candidate definitions/theorems, ordered by build-priority:

1. **`PrimitiveLinkingClass`** (def, ~15 lines) — refines `LinkingClass` with `Int.gcd a.natAbs b.natAbs = 1`. Export `bottleneck := ⟨0, 1, _⟩` and `dominant := ⟨1, 0, _⟩`.
2. **`JBudgetFunctional`** (def, ~20 lines) — two-channel J-budget carrier; depends on Phase 0.5 `TauRealSqrt.lean` for √κ_D.
3. **`selection_rule_from_v_t40_v_t_new_5`** (theorem, ~40 lines) — headline: under V.T-NEW-5 uniqueness + V.T40 no-shrink, BH's linking class is forced to (0,1). Proof: case-split, dispatch (1,0) by V.T40 contradiction, conclude (0,1) by elimination.
4. **`j_max_T2_bottleneck`** (theorem, ~25 lines) — once §3 fixes linking class to (0,1), delivers the `J_max^{T²} = ι_τ √κ_D · GM²/c` formula. Depends on `TauRealSqrt.lean`.
5. **`dominant_reading_violates_v_t40`** (theorem/counterexample, ~30 lines) — witness theorem that (1,0) is incompatible with V.T40. Pair with §3 so the uniqueness reads as "(0,1) survives, (1,0) does not".

---

## 6. v2.3 LRD paper headline disposition

**No change required.** `M_BH^max ≈ 10^{6.54 ± 0.10} M_⊙ at z = 11` survives unchanged into v2.3.

Recommended editorial note for v2.3 §7 Gap 6 (V.T-NEW-5 deferred-promotion entry): "The (0,1) bottleneck vs (1,0) dominant primitive linking-class question raised in v2.1 §7 Gap 6 is resolved definitively to (0,1) by Specialist δ's Wave R8a derivation (`taulib/research-notes/LinkingClassSelection.md`). The resolution combines V.T-NEW-5 categorical uniqueness with V.T40 No-Shrink: under (1,0), V.T40 is contradicted; under (0,1), V.T40 is preserved trivially. The Wave R7 headline cutoff `log₁₀M_BH^max ≈ 6.54 ± 0.10` survives unchanged."

---

**End of selection-rule derivation note. Wave R8a Wave 1 deliverable.**
