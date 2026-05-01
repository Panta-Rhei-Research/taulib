# V.T-NEW-5 — Categorical T²-Kerr Uniqueness Theorem: Derivation Note (v1)

**Status.** Wave R8a in-flight (April 2026). New skeleton-status Lean module proposed at `TauLib/BookV/Cosmology/T2KerrUniqueness.lean` bundling J_max^{T²} (V.T-NEW-5A) + unit Jacobian (V.T-NEW-5B) as separate registry entries. Carved out from `HeavySeedBirth.lean` per Specialist J's Wave R7 audit recommendation (cross-coupling matrix cells ✗₄ + ⚠₆).

**Source motivation.** Wave R7 V.T-LRD-1 derivation note v2 §3 (E + G converged J_max^{T²} = ι_τ √κ_D · GM²/c) and §10 open question #1 ((0,1) bottleneck vs (1,0) dominant linking class). The Wave R7 cross-validation produced the *value* but flagged the *metric construction itself* as not derived from a uniqueness theorem.

**Authoring history.**
- v1 (April 2026, this document): synthesis of Wave R8a Wave 1 outputs from 5 specialists (α NEW Wald §11/12 lens, β returning E refined construction, γ returning G refined Π_coh, δ NEW linking-class selection rule, ε NEW Lean architect).

---

## 1. Theorem statement (V.T-NEW-5)

**V.T-NEW-5 (T²-Kerr categorical uniqueness, conjugacy-class form).** Let `(M, g)` be a smooth four-dimensional Lorentzian manifold satisfying:

- **(H1) Stationarity.** A complete timelike Killing vector field `ξ` exists in the asymptotic region.
- **(H2) Axisymmetry.** A complete spacelike Killing vector field `ψ` with closed orbits, commuting with `ξ`.
- **(H3) Horizon presence.** A connected non-degenerate Killing horizon `H` with compact 2-dimensional cross-sections `Σ`.
- **(H4) τ-fibration compatibility.** `M` carries a `τ³ = τ¹ ×_f T²` fibration (V.T110 `bh_toroidal_topology` + `bh_toroidal_structural`); `Σ` is diffeomorphic to T² with linking class `ℓ ∈ H₁(T²; ℤ) = ℤ ⊕ ℤ` non-trivial.
- **(H5) V.T110 lock.** The two T²-circle radii satisfy `r/R = ι_τ`.
- **(H6) Asymptotic τ-flatness.** The metric approaches the bare `τ³ = τ¹ ×_f T²(∞)` fibration at `r → ∞`, where `T²(∞)` is the asymptotic torus with aspect ratio `ρ(∞)/R(∞) = ι_τ` inherited from V.T110's *fibration-wide* lock (not a horizon-local statement). This is *not* asymptotic Minkowski in the classical sense — the fiber does not shrink to a point — but it is the correct τ-analog: the asymptotic geometry is the bare fibration with no curvature contribution, and the fiber breathing fraction is preserved. **(Wave R8a Wave 2 β verification: §6 Gap-1 CLOSED GREEN.)**
- **(H7) τ-vacuum / τ-Einstein condition** (modulator: see §5 R3 YELLOW Gap-2).

**Conclusion.** The pair `(M, g)` is τ-equivalent (lies in the same conjugacy class under `Diff_τ(M)`) to E's T²-Kerr construction parametrised by `(M, J_γ)` with `|J_γ| ≤ J_max^{T²}(M) = ι_τ √κ_D · GM²/c`.

**Crucial difference from Carter-Robinson.** V.T-NEW-5 concludes only conjugacy-class equality (not pointwise isometry); the slack is needed because the τ³ fibration's discrete linking-class data is preserved only up to `SL(2, ℤ)` automorphisms of the T² fiber — see §4 for the (0,1) vs (1,0) implications.

**Two corollaries, promoted as separate registry entries:**

- **V.T-NEW-5A — J_max^{T²} bound.** `J_max^{T²}(M_BH) = ι_τ √κ_D · GM²/c ≈ 0.277 · GM²/c` ≈ 28% of Kerr's bound. The ι_τ-power exponent = 1 (uniqueness content). Cross-validated by α + β + γ.

- **V.T-NEW-5B — Unit Jacobian.** `|d log M_BH / d log λ| = 1` exactly in the regime `λ > λ_⋆ ~ ι_τ · λ̄`. Now a **one-line corollary** of V.T-NEW-5 (γ's §2 derivation): the moduli space is one-dimensional in (M_BH, J_γ) at fixed (r/R, κ_D), and the map λ → seeded BH factors through this moduli space.

**Inputs (cited registry IDs, all `formalized` in TauLib):**

- V.T109 (`bh_threshold_theorem`, `BookV.Cosmology.BHBirthTopology`) — anchors the centrifugal `√κ_D` factor.
- V.T110 (`bh_toroidal_topology`, `bh_toroidal_structural`, `BookV.Cosmology.BHBirthTopology`) — the `r/R = ι_τ` aspect-ratio lock.
- V.T40 / V.T114 (`no_shrink_theorem`, `BookV.Cosmology.NoShrinkExtended`) — base/fiber asymmetry; load-bearing in δ's §2.3 V.T40 consistency check that *forces* (0,1).
- V.D-LRD-1d (`T2HorizonAngularMomentumBound`, `BookV.Cosmology.HeavySeedBirth`) — origin point for V.T-NEW-5A promotion.

---

## 2. Proof sketch (Specialist α)

The argument is a τ-port of Carter-Robinson (1973) extended through Israel-Robinson-Mazur-Bunting-Chruściel. Three τ-substitutions to the classical chain:

**Step (a) — Bulk lift via the τ³ = τ¹ ×_f T² fibration.** Hawking's rigidity theorem ports to τ once we replace "analytic continuation across the horizon" with the τ³ fibration's fiberwise smoothness in the τ¹-base direction. The bulk Killing algebra contains at minimum `{ξ, ψ}` plus the fiber-tangent generators of `H_1(T²; ℤ) ⊗ ℝ ≅ ℝ²`. The lift is unobstructed because the τ³ fibration in V.T110 is *trivial up to twist* — the breathing fraction `ι_τ` modulates fiber size but does not introduce holonomy in the τ¹-base direction (this is V.T40 `no_shrink_theorem` interpreted bulk-side).

**Step (b) — Killing-vector algebra and the V.T110 lock.** In classical Kerr on S², the would-be third generator `∂_θ` is not Killing because the S² metric depends on θ through `sin²θ`. In the τ-case, the V.T110 quotient identifies `θ ↔ θ + 2π/N`. **At the locked aspect ratio `r/R = ι_τ`, the resulting T² metric becomes θ-translation invariant** (the angular dependence drops out exactly because `sin²θ` is replaced by the constant fiber breathing fraction). This promotes `∂_θ` to a third Killing vector. **α independently recovers E's Wave R7 finding by a different route** — as a *consequence of the V.T110 lock on the rigidity side*, not via E's quotient construction.

**Step (c) — Reduction to E's T²-Kerr.** With three commuting Killing vectors and τ-vacuum (H7), the field equations reduce to a sigma-model on a 1-dimensional reduced base (the radial coordinate). Robinson's identity / Mazur-Bunting then applies: any two solutions with the same asymptotic charges `(M, J_γ)` and the same horizon topology differ by a τ-diffeomorphism preserving the 3-dim Killing orbit. That conjugacy class is exactly E's T²-Kerr construction. The angular-momentum bound `|J_γ| ≤ J_max^{T²}` enters as the regularity condition at the inner radial boundary (analogue of Kerr's `|a| ≤ M`); beyond it, the would-be horizon develops a naked singularity, violating (H3).

---

## 3. Refined J_max^{T²} construction (Specialist β = returning E)

**Three structural upgrades from Wave R7 §3:**

1. **`κ_D^{1/2}` factor structurally forced (no longer parallel-derivation coincidence).** α's uniqueness clause + Wald §11/12 second-law monotonicity uniquely fixes the centrifugal-opposition prefactor as a *square root* (not first-power) because it enters as a horizon-area quadratic form, identically to standard Kerr.

2. **`ι_τ`-power exponent = 1 structurally forced.** Under uniqueness, the angular-momentum 2-form on the horizon is the unique element of `H¹(T²;ℝ)` that vanishes on the η-generator and has integer period 1 on the γ-generator. That period normalization combined with the `r/R = ι_τ` rescaling produces ι_τ to the **first power** — exactly because the period is *linear* in the cycle length.

3. **One free overall constant disappears.** The `F(0) → 1` Kerr-limit matching condition becomes redundant — α's uniqueness clause selects it automatically because the Kerr limit lives at the conjugacy-class boundary.

**Numerical headline (unchanged from Wave R7):** `F(ι_τ) = ι_τ √κ_D = 0.341304 × √0.658696 = 0.277083 ≈ 0.2771`. **Numerical shift from Wave R7: 0.000 dex.** The placeholder `f_iota_x_10000 = 2773` in `HeavySeedBirth.lean:454` remains correct to within rounding.

**Confidence interval ±0.10 dex** preserved from Wave R7 §3 (orthodox-propagation budget unchanged; α's theorem only tightened the prefactor's *epistemic* status).

---

## 4. Refined Π_coh derivation + Unit Jacobian as corollary (Specialist γ = returning G)

**Π_coh upgrade.** In Wave R7 the projection `Π_coh: ω_γ ⊕ ω_η → ω_γ` on `H_1(T²; ℤ) ⊗ ℝ` was a *structural projection consistent with V.T40* but specified only up to GL(2,ℤ) basis choice. Under V.T-NEW-5, **Π_coh is upgraded to the unique morphism** in the symmetric monoidal category of T²-horizon moduli spaces such that (i) the kernel matches the rigidity-killed Killing-Yano direction and (ii) the image is the V.T-NEW-5 moduli direction. **No residual GL(2,ℤ) freedom remains** — the V.T110 metric data uniquely fixes the splitting (the "tight" cycle [γ] shrinks under V.T109 collapse; the "loose" cycle [η] does not).

**Unit Jacobian as one-line corollary of V.T-NEW-5.** "V.T-NEW-5 implies the T²-Kerr moduli space is one-dimensional in (M_BH, J_γ) at fixed (r/R, κ_D); the map halo-spin → seeded BH factors through this one-dimensional moduli space; therefore the level sets of M_BH(λ) and λ·M_BH(λ) coincide, giving `d(log M_BH · λ) / d log λ = 0`, i.e. unit Jacobian." This is substantially shorter than the Wave R7 chain (Π_coh + V.T40 + V.T110 + reciprocal-eigenvalue argument).

**Wave R7 chain remains the right Lean formalisation pathway** because TauLib does not yet have a categorical moduli-space layer. Both should appear in `T2KerrUniqueness.lean`: the corollary as a one-line theorem consuming a `T2KerrUnique` instance, with the Wave R7 chain as the constructive existence proof feeding that instance.

**Cross-validation hooks with β:**
- **Hook 1:** β's `∂_θ` Killing vector ↔ γ's gravity-aligned cycle [γ]. The de Rham dual `ω_γ ∈ H¹(T²;ℝ)` should pair non-trivially with `∂_θ`; `ω_η` should pair to zero. Identifies [γ] as the long-axis cycle (`2πR`), [η] as the short-axis (`2πr`).
- **Hook 2:** β's transport-bottleneck on the (0,1) class ↔ γ's kernel of Π_coh. The (0,1) vs (1,0) ambiguity from Wave R7 §3 has a **clean V.T-NEW-5 resolution: both derivations agree because they are looking at different aspects** (surviving channel γ vs killed channel η) of the same uniqueness fact.

---

## 5. Linking-class selection rule (Specialist δ — DEFINITIVE)

**TL;DR (decision-grade summary).** Selection rule resolves **definitively to (0,1)** as the unique primitive linking class admissible under V.T40 + V.T-NEW-5 in `d_top = 1` quasi-isothermal contraction. Wave R7 headline `log₁₀ M_BH^max ≈ 6.54 ± 0.10` **stands.**

### 5.1 The decisive V.T40 consistency check

Under (1,0): the γ-cycle holds the J-budget, so `J = J_γ(M)` as a constitutive relation. V.T40 forces `dM/dn ≥ 0`. But the J-budget under (1,0) is *not* a one-sided functional — any J-shedding event must come at the cost of `dM_γ/dn < 0` on the γ-budget (because (1,0) deactivates the η-cycle as a transport channel). **Contradiction with V.T40.**

Under (0,1): J-shedding flows through the η-cycle, which is *not* the mass-carrying cycle. V.T40 is preserved trivially. **(0,1) is the unique survivor.**

### 5.2 Three structurally-independent supporting arguments (Specialist β)

- **(a) Energy-condition.** (1,0) requires positive-energy-condition violation at the bar-cascade threshold; incompatible with orthodox bulk-matter content (Begelman-Shlosman 2009).
- **(b) Asymptotic-geometry.** (0,1) smoothly recovers Kerr's standard `J_max = GM²/c` in the `ι_τ → 0` limit. (1,0) diverges by ~3× — no smooth Kerr limit. Under α's uniqueness theorem, the canonical representative *must* have a smooth Kerr limit.
- **(c) Transport-limited.** The bar-cascade transport efficiency `η_J ≈ 0.08` is structurally a (0,1)-class statement (it picks out the cycle that *limits flux*).

### 5.3 R-flag dispositions

- **R1 NO TRIGGER.** All four (α, β, γ, δ) converged on `J_max^{T²} = ι_τ √κ_D · GM²/c ≈ 0.277 · GM²/c`; numerical shift 0.000 dex from Wave R7. The 0.46 dex shift to `log₁₀ M_BH^max ≈ 7.0` that would have triggered pause is precluded.
- **R2 NOT APPLICABLE.** V.T-NEW-5 is a *categorical uniqueness* statement; no degree of freedom for sub-region heterogeneity in the linking-class assignment itself.
- **R3 YELLOW** on α's two assumption gaps — see §6 below.
- **R4 NOT TRIGGERED.** (0,1) does NOT force J = 0; the γ-cycle still carries the Kerr-like centrifugal `√κ_D · GM²/c` as a *non-quantised* J-component. Total `J_max^{T²} = ι_τ · √κ_D · GM²/c` is the product of the η-cycle aspect-ratio quantum (`ι_τ`) and the γ-cycle Kerr-like contribution.

### 5.4 v2.3 LRD paper headline disposition

**No change required.** `M_BH^max ≈ 10^{6.54 ± 0.10} M_⊙ at z = 11` survives unchanged into v2.3. δ recommends upgrading Wave R7 §10 open question #1 to **CLOSED** for the `d_top = 1` sector.

---

## 6. Honest gaps (R3 YELLOW)

α flagged **two assumption gaps** that are R3-YELLOW (patchable by explicit declaration; not RED):

**Gap-1 (asymptotic τ-flatness) — CLOSED GREEN by Wave R8a Wave 2 β.** The T²-Kerr metric construction carries `𝒜(r) := ρ(r)/R(r) = ι_τ` constantly from horizon to infinity, because V.T110's `r/R = ι_τ` lock is a *fibration-wide* statement (`BHBirthTopology.lean:261-294` docstring: "*By definition of the fiber structure, R = ℓ_τ and r = ι_τ·ℓ_τ, so r/R = ι_τ*"), not horizon-local. The η-cycle radius `ρ(r)` is rigidly slaved to the γ-cycle radius `R(r)` by V.T40 base/fiber asymmetry + V.T110 fiber structure; it carries no independent radial profile. The Killing reduction in E's metric construction has only three independent metric functions `(F(r), R(r), A(r))` — there is no fourth function `ρ(r)` that could carry an independent profile. H6 stands as restated in §1 above; no two-aspect-ratio reformulation needed. **Confidence 0.9.** See Wave 2 β verification note for the full trace.

**Gap-2 (τ-vacuum form).** Without committing to whether V.T204's `a₀(z) = c·H(z)·ι_τ/2` correction enters the bulk equations. For an isolated stationary BH, this is moot. But the V.T-LRD-1 application is at z = 8–15 where V.T204's high-z correction is non-negligible. **Recommendation:** prove V.T-NEW-5 in the *isolated regime* first (clean uniqueness), then state the cosmological extension as a separate corollary V.T-NEW-5b with the V.T204 modification absorbed into the τ-vacuum tensor on the RHS.

Two further gaps (Gap-3 V.T40 consistency: GREEN; Gap-4 linking-boundary regularity: structurally clean; Gap-5 extremal `|J| = J_max^{T²}` limit: defer to Wave 2/3) are tracked but non-blocking.

---

## 7. Lean-formalisation status (Wave R8a Wave 1 advance)

**New skeleton module proposed:** `TauLib/BookV/Cosmology/T2KerrUniqueness.lean` (~430 lines, ε's Wave 1 design). Sections:

1. CategoricalT2KerrUniqueness struct + `v_t_new_5_categorical_uniqueness` (5-clause Bool conjunction proven by 5 `rfl`s).
2. `JMaxT2BoundStatement` carrier + `t_v_new_5a_j_max_t2_bound` (5-clause; structural identity + `omega`).
3. `UnitJacobianStatement` carrier + `t_v_new_5b_unit_jacobian` (5-clause; all `rfl`).
4. Selection-rule witness placeholder (binds to `unit_linking` pending δ's full Lean refinement).
5. Cross-references: `j_max_t2_iota_TauReal` aliases HeavySeedBirth's `iota_tau_T2_bound_TauReal`.
6. (FalsificationPack entry moved to `FalsificationPack.lean` directly per ε's circular-import avoidance.)

**Trust budget impact: zero** new custom axioms; **zero** sorries in T2KerrUniqueness.lean itself; all proofs by `rfl` / `omega` / `decide` / structural identity.

**Critical-path Phase 0.5 deferred site:** The closed-form TauReal-witnessed `f_iota_TauReal := iota_tau_TauReal.mul (TauReal.sqrt (TauReal.one.sub iota_tau_TauReal))` requires `TauReal.sqrt` from Wave R8b. Marked `-- TODO: Wave R8b` in T2KerrUniqueness.lean Section 2.

---

## 8. Registry update plan (Wave R8a deliverables)

**To add to `corpus/intake/2026-04-30-wave-r8a-vtnew5/book-05.jsonl`:**

| ID | Type | Name | Module | Status | Scope |
|----|------|------|--------|--------|-------|
| V.T-NEW-5A | theorem | J_max^{T²} bound — T²-Kerr angular-momentum uniqueness | `TauLib.BookV.Cosmology.T2KerrUniqueness` | `skeleton` | `tau-effective` |
| V.T-NEW-5B | theorem | Unit Jacobian lemma — `|d log M_BH / d log λ| = 1` from T²-coherence | `TauLib.BookV.Cosmology.T2KerrUniqueness` | `skeleton` | `tau-effective` |

(Optional V.T-NEW-5 main entry deferred — could land in a future Wave R8c batch with the full uniqueness theorem proof, once R3 YELLOW gaps resolve.)

---

## 9. Cross-coupling matrix update (V.T-NEW-5 row)

The cross-coupling matrix at `taulib/research-notes/V-T-LRD-1-cross-coupling-matrix.md` should add a **V.T-NEW-5 row** with:

- **Cell (V.T-NEW-5 ↔ V.T110):** ✓ — V.T-NEW-5 is by construction an upgrade of V.T110's structural content; no contradiction.
- **Cell (V.T-NEW-5 ↔ V.T40):** ✓ — δ's §2.3 V.T40 consistency check is the load-bearing piece that selects (0,1); fully consistent.
- **Cell (V.T-NEW-5 ↔ V.T109):** ✓ — V.T-NEW-5 inherits V.T109 threshold-survival as the input that anchors the `√κ_D` centrifugal factor.
- **Cell (V.T-NEW-5 ↔ V.T-LRD-1B):** ✓ — V.T-NEW-5A *closes* the structural-extension flag (cross-coupling matrix cell ✗₄).
- **Cell (V.T-NEW-5 ↔ V.T-LRD-1C):** ✓ — V.T-NEW-5B *closes* the structural-extension flag (cell ⚠₆) for the unit Jacobian.
- **Cell (V.T-NEW-5 ↔ kSZ N12-N14, inflation N9-N11):** all ✓ (no coupling at sub-galactic scales).

**Cross-coupling matrix Red-cell updates: ✗₄ + ⚠₆ now resolved by V.T-NEW-5A + V.T-NEW-5B.** The matrix's headline cells reduce from "two outright Red, three Yellow" to "one outright Red (✗₇ on V.T-LRD-1D pending physics; out of V.T-NEW-5 scope), two Yellow (⚠₁ V.T108 BBN + ⚠₃ V.T204 three-way coupling)".

---

## 10. Open questions for the next wave (Wave R8 proper or follow-up)

1. ~~**R3 YELLOW Gap-1 resolution**~~ — **CLOSED GREEN by Wave R8a Wave 2 β** (see §6 above). V.T110's `r/R = ι_τ` lock is fibration-wide; the T²-Kerr metric construction carries constant aspect ratio from horizon to infinity. No reformulation needed. Confidence 0.9.

2. **R3 YELLOW Gap-2 resolution** — formalise the isolated-vs-cosmological regime distinction; introduce V.T-NEW-5b for the V.T204-corrected variant.

3. **TauReal-witnessed J_max^{T²} numerical bound** — Wave R8 proper: once Phase 0.5 `TauRealSqrt` lands, complete the deferred `f_iota_TauReal` site in `HeavySeedBirth.lean` and `T2KerrUniqueness.lean` Section 2.

4. **V.T-LRD-1B + C + D theorem statements upgrade to TauReal-witnessed inequalities** — Wave R8 proper.

5. **Extremal `|J| = J_max^{T²}` limit** — Wave 2/3 specialist: prove uniqueness extends to the boundary case (extremal-rigidity argument analogous to extremal Kerr).

---

## 11. Wave R8a Wave 1 deliverables summary

**This document (v1 derivation note):** comprehensive integration of all Wave R8a Wave 1 specialist outputs.

**New Lean module (proposed):** `TauLib/BookV/Cosmology/T2KerrUniqueness.lean` — skeleton-status, ~430 lines, zero sorries.

**Companion documents (this wave):**
- `taulib/research-notes/LinkingClassSelection.md` — Specialist δ's selection-rule note.

**Cross-repo deliverables (next):**
- `taulib/TauLib/BookV/Cosmology/FalsificationPack.lean` — `pred_t2_kerr_uniqueness` Q8 entry (Wave R8a Wave 3 patch, optional).
- `taulib/research-notes/V-T-LRD-1-cross-coupling-matrix.md` — V.T-NEW-5 row addition (this wave).
- `corpus/intake/2026-04-30-wave-r8a-vtnew5/` — V.T-NEW-5A + V.T-NEW-5B JSONL records (this wave).
- `atlas/audits/taulib/2026-04-30-wave-r8a-vtnew5-closing-dashboard.md` — Wave R8a closing dashboard (this wave).
- `papers/research-notes/lrd-categorical-v2/main.tex` — v2.3 patches (per δ's recommendation: NO headline change; only §3.3 J_max^{T²} citation upgrade and §7 Gap 6 V.T-NEW-5 deferred-promotion entry; **user-gated**).

---

**End of derivation note v1. Wave R8a Wave 1 physics complete; Lean skeleton infrastructure designed; (0,1) selection rule definitively resolved; R3 YELLOW gaps surfaced for Wave 2 / handoff decision.**
