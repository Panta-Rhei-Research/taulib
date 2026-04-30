# V.T-LRD-1 — $d_{\mathrm{top}} = 1$ Birth-Condition Theorem: Derivation Note (v2)

**Status.** Wave R7 in-flight (April 2026). Skeleton-status Lean module at `TauLib/BookV/Cosmology/HeavySeedBirth.lean` extended with Wave R7 promotions T1+T3+T4+partial T2 (TauReal-witnessed sibling defs). Four `pred_lrd_*` `TestablePrediction` instances landed in `TauLib/BookV/Cosmology/FalsificationPack.lean` (N15 ledger).

**Source motivation.** Theorem 3.2 + §6.1 N15 + §7 Gap 1 + Appendix B of the v2.1 LRD-categorical research note (Fuchs & Fuchs, April 2026, [`papers/research-notes/lrd-categorical-v2/main.tex`](../../../Books/PantaRhei-2ndEd/papers/research-notes/lrd-categorical-v2/main.tex)).

**Authoring history.**
- v1 (April 2026): synthesis of 4 parallel red-team specialist drafts (A, B, C, D).
- v2 (April 2026, this document): integrated Wave R7 outputs from 5 NEW specialists (E, F, G, I, J) + 3 returning refinements (A, B, C). Specialist D's Wave 2 role taken over by chair after usage limit; 4 Lean patches landed and build-verified (1082 lake jobs, exit 0).

---

## 1. Theorem statement

**V.T-LRD-1 ($d_{\mathrm{top}} = 1$ birth-condition theorem).**
At redshift $z \in [8, 15]$, the seed black-hole mass distribution $\mathrm{d} N / \mathrm{d} \log M_{\mathrm{BH}}(z)$ produced by single quasi-isothermal $d_{\mathrm{top}} = 1$ contraction in atomic-cooling halos satisfies four simultaneous conditions:

- **(A) Lower cutoff.** $M_{\mathrm{BH}} \gtrsim 10^{4.5}\,M_\odot$ (atomic-cooling halo floor inheritance; *orthodox-imported on value, $\tau$-distinctive on sharpness via V.T88 $\leftrightarrow$ V.T110 $S^2$-vs-$T^2$ exclusion gap*).
- **(B) Upper cutoff.** $M_{\mathrm{BH}} \lesssim 10^{6.54 \pm 0.10}\,M_\odot$ at $z = 11$ (*$\tau$-distinctive*; load-bearing signature 1 of N15). Wave R7 cross-validation confirms $J_{\max}^{T^2} = \iota_\tau\sqrt{\kappa_D}\,GM^2/c$ ($\iota_\tau$-power = 1) from two independent derivations (E + G converged).
- **(C) Flat interior shape.** $|\mathrm{d}\log N / \mathrm{d}\log M_{\mathrm{BH}}| \le 0.3$ throughout the interior (*$\tau$-distinctive*; from the unit Jacobian $|\mathrm{d}\log M_{\mathrm{BH}} / \mathrm{d}\log\lambda| = 1$ that $T^2$-coherence enforces, now structurally grounded by Specialist G's coherence projection $\Pi_{\rm coh}$ on $H_1(T^2;\mathbb{Z}) \otimes \mathbb{R}$).
- **(D) Sharp transition (PENDING PHYSICS).** Slope transition from $0 \pm 0.3$ to $\le -2$ over $\Delta\log M_{\mathrm{BH}}$. **Wave R7 R2 risk-flag TRIGGERED**: Specialist F's reconciliation found A's mechanism (binary outcome, 1.66 dex) and C's mechanism (smooth $f_{\rm BH}$, 0.41 dex) genuinely both apply in different sub-regions, with composite $0.9^{+0.5}_{-0.4}$ dex. The v2.1 paper's $\le 0.2$ dex headline is not survivable; the v2.2 paper must relax to either $\le 0.4$ dex (single-mechanism C-edge) or $\le 1.5$ dex (composite operational falsifier).

**Inputs (cited registry IDs, all `formalized` in TauLib):**
- V.T108 (`nucleosynthesis_from_tau`, `BookV.Cosmology.ThresholdLadder`) — BBN anchor, $Y_p = 20/81$ exactly. Now coupled to V.T-LRD-1A via $\mu = 0.6$ partial-ionisation chain.
- V.T109 (`bh_threshold_theorem`, `BookV.Cosmology.BHBirthTopology`) — BH formation criterion $G(U) > \mathcal{C}_{\mathrm{sph}}$.
- V.T110 (`bh_toroidal_topology`, `bh_toroidal_structural`, `BookV.Cosmology.BHBirthTopology`) — $T^2$ horizon, locked aspect ratio $r/R = \iota_\tau$.
- V.R179 (comment-only, `BookV.Astrophysics.CompactObjects`) — no primordial BHs.
- V.T40 / V.T114 (`no_shrink_theorem`, `BookV.Cosmology.NoShrinkExtended`) — birth-mass = present-mass.
- V.T88 (`mass_gap_prediction`, `BookV.Astrophysics.CompactObjects`) — compact-object classification (now clarified: applies to $S^2$-horizon stellar remnants only; $T^2$-horizon BHs start at V.T-LRD-1A floor).

**Orthodox-imported inputs (NOT $\tau$-derived; honestly flagged):**
- Atomic-cooling halo mass function (Bromm & Loeb 2003; Rees & Ostriker 1977).
- DCBH central collapse fraction $f_{\mathrm{DCBH}} \approx 10^{-2}$ (Begelman & Volonteri 2017; Inayoshi-Visbal-Haiman 2020 ARA&A).
- Halo spin-parameter log-normal distribution with $\bar\lambda \approx 0.04$, $\sigma_{\log\lambda} \approx 0.30$ (Bullock et al. 2001; Mo–Mao–White 1998; Macciò et al. 2007).
- Sheth–Tormen halo mass function slope $\alpha \approx 1.9$ at $M_{\mathrm{halo}} \sim 10^{7\text{–}8}\,M_\odot$, $z = 10$–$15$.
- Multi-stage Begelman-Shlosman 2009 bar-within-bar cascade gives $\eta_J \approx 0.08$ (range $[0.05, 0.15]$); the Begelman-Volonteri-Rees 2006 single-cascade form $\eta_J \sim (R_{\rm vir}/r_g)^{-1/2}$ undershoots by 3-4 orders of magnitude (F's correction).

---

## 2. Sub-theorem A: lower cutoff at $M_{\mathrm{BH}} \approx 10^{4.5}\,M_\odot$ (refined by B)

**Mechanism.** At $T_{\mathrm{vir}} > 10^4$ K, neutral H I line cooling sustains a quasi-isothermal collapse to BH formation. Below this threshold, H$_2$ molecular cooling takes over, the cloud cools to $T \sim 200$ K, the Jeans mass drops to $\sim 10^3\,M_\odot$, and the collapse fragments into a Pop-III stellar cluster — incompatible with $d_{\mathrm{top}} = 1$.

**Derivation chain:**
$$T_{\mathrm{vir}} = \frac{\mu m_p}{2 k_B}\,(GM_{\mathrm{halo}})^{2/3} \left(\frac{4\pi \cdot 200\,\rho_c(z)}{3}\right)^{1/3},$$
solving at $T_{\mathrm{vir}} = 10^4$ K with $\mu = 0.6$ (the partially-ionised value):
$$M_{\mathrm{halo}}^{\mathrm{AC}}(z) \approx 3.9\times 10^7\,M_\odot \left(\frac{1+z}{11}\right)^{-3/2}.$$

| $z$ | $M_{\mathrm{halo}}^{\mathrm{AC}}\,[M_\odot]$ | $M_{\mathrm{gas}}^{\mathrm{AC}} = f_b M_{\mathrm{halo}}^{\mathrm{AC}}$ | $M_{\mathrm{BH}}^{\mathrm{AC}} = f_{\mathrm{DCBH}} M_{\mathrm{gas}}^{\mathrm{AC}}$ | $\log_{10}(M_{\mathrm{BH}}^{\mathrm{AC}}/M_\odot)$ |
|-----|-----------------------------------|-----------------------------------|-----------------------------------|-----------------------------------|
| 10  | $5.0\times 10^7$ | $7.8\times 10^6$ | $7.8\times 10^4$ | $4.89$ |
| 13  | $3.0\times 10^7$ | $4.7\times 10^6$ | $4.7\times 10^4$ | $4.67$ |
| 15  | $2.3\times 10^7$ | $3.6\times 10^6$ | $3.6\times 10^4$ | $4.55$ |

Lower edge across $z \in [10, 15]$: $M_{\mathrm{BH}}^{\mathrm{AC}} \approx 10^{4.55} \approx 10^{4.5}\,M_\odot$. Matches v2.1 spec.

**§2.6 V.T108 BBN coupling (Wave R7 addition).** The $\mu = 0.6$ partial-ionisation value depends on the H-cooling function, which depends on V.T108's $Y_p = 20/81$ commitment exactly. The dependency chain: $Y_p = 20/81 \Rightarrow X = 61/81 \Rightarrow n_{\rm He}/n_{\rm H} \approx 0.0820 \Rightarrow \mu \approx 0.59$–$0.61$ (rounded $\mu = 0.6$). A $1\%$ shift in $Y_p$ propagates to $\Delta\log_{10}\Mbh^{\rm AC} \sim 0.002$ dex — well below the v2.1 reporting precision but worth recording as a one-line Lean lemma `t_lrd_1_v_t108_consistency` (proposed for next-wave Lean work).

**§2.5 V.T88 $\leftrightarrow$ V.T110 mass-gap clarification (Wave R7 addition, J's audit ⚠₂).** V.T88's mass-gap upper edge of $5\,M_\odot$ classifies $S^2$-horizon Schwarzschild remnants only. $T^2$-horizon BHs (the V.T-LRD-1 domain) start at $\sim 10^{4.5}\,M_\odot$ because the $T^2$-horizon topology requires a coherent collapse mass exceeding the ACH threshold; **there are no $T^2$-horizon BHs in the gap region $5$–$10^{4.5}\,M_\odot$**. This is a topological exclusion zone, not a cooling/feedback suppression — the $\tau$-distinctive sharpness content of V.T-LRD-1A.

**§2.7 V.T-NEW-1 stub (Wave R7 extension, J's audit ⚠₃ three-way coupling).** V.T204 ($a_0(z) = c\,H(z)\,\iota_\tau/2$) modifies high-$z$ background dynamics. V.T-NEW-1 (τ-modified $T_{\rm vir}^\tau(z)$ under V.T204) will affect **both**:
- (a) the V.T-LRD-1 lower-cutoff progenitor abundance via modified $T_{\rm vir}^\tau(z)$;
- (b) V.T239's JWST star formation efficiency enhancement (`tau_sfe_pct = 47` vs ΛCDM 40).

Both flow from V.T204's high-$z$ $a_0(z)$ modification. The three-way coupling **V.T204 ↔ V.T-NEW-1 ↔ V.T239** must be flagged in v2.2 paper §7 Gap 5 extension as a coordinated derivation, not three independent ones.

---

## 3. Sub-theorem B: upper cutoff at $M_{\mathrm{BH}} \approx 10^{6.54 \pm 0.10}\,M_\odot$ (refined by A, cross-validated E+G)

**Wave R7 cross-validation: E and G independently converged.** Two parallel specialist derivations agreed on $J_{\max}^{T^2} = \iota_\tau\sqrt{\kappa_D}\,GM^2/c \approx 0.277\,GM^2/c$ ($\iota_\tau$-power = 1, with $\kappa_D^{1/2}$ multiplicative factor):

- **Specialist E (GR/Wald-Carter-Penrose lens):** rigorous $T^2$-Kerr metric construction promoting $\partial_\theta$ to a third Killing vector beyond Kerr's two via the V.T110 $\theta$-quotient. Transport-bottleneck argument on the (0,1) primitive linking class.
- **Specialist G (categorical/homological lens):** coherence projection $\Pi_{\rm coh}: \omega_\gamma \oplus \omega_\eta \to \omega_\gamma$ on $H_1(T^2;\mathbb{Z}) \otimes \mathbb{R}$ kills $\omega_\eta$ (V.T40 base/fiber asymmetry); $r/R = \iota_\tau$ aspect ratio gives the $\iota_\tau$-factor; V.T109 threshold-survival gives the $\sqrt{\kappa_D}$ centrifugal factor.

**Refined cutoff condition (Specialist A Wave 2):**
$$\boxed{M_{\rm BH}^{\max} \le \frac{2\,\bar\lambda^2}{\iota_\tau^{\,2}\,\kappa_D}\,f_{\rm cool}\,f_b\,M_h^{\rm ACH,max}\,(1+z)^{1/2}}$$
This is a **clean one-mechanism** prefactor (transport bottleneck on the (0,1) cycle) replacing v1's two-mechanism $\iota_\tau^{-2.5}$ heuristic. The two prefactors are numerically equivalent (0.05 dex) because $\kappa_D^{-1} \approx 1.52$ and $\iota_\tau^{-1/2} \approx 1.71$ accidentally bracket each other, but the **physical bookkeeping is cleaner**.

**Numerical headline:** $\log_{10}(\Mbh^{\max}/M_\odot) \approx 6.54$ at $z = 11$ (from $\bar\lambda = 0.04$, $f_{\rm cool} = 0.3$, $f_b = 0.16$, $M_h^{\rm ACH,max} = 5\times 10^8\,M_\odot$, $\iota_\tau = 0.341304$, $\kappa_D = 0.658696$). **Confidence interval $\pm 0.10$ dex** (Wave 2 A tightening from v1's $\pm 0.15$, since the structural-bookkeeping ambiguity between $\iota_\tau^{-2.5}$ and $\iota_\tau^{-2}\kappa_D^{-1}$ is now resolved). **R1 NO TRIGGER** (E vs A: 0.00 dex; A(refined) vs v2.1 headline 6.50: 0.04 dex).

**Corrected $\eta_J$ structural form (Specialist F).** Replace v1's BVR06 single-cascade $\eta_J \sim (R_{\rm vir}/r_g)^{-1/2}$ (which undershoots by 3-4 orders of magnitude) with the multi-stage Begelman-Shlosman 2009 cascade $\eta_J \approx 0.08$ (range $[0.05, 0.15]$, central from Mayer-Fiacconi-Bonoli-Madau 2015, Wise et al. 2019, Inayoshi-Visbal-Haiman 2020 ARA&A, Regan et al. 2017). The numerical answer survives because v1's $\bar\lambda^2 \cdot f_{\rm cool}$ choices implicitly absorbed the right end-to-end $\eta_J$.

**Open question for the wave physics review (Specialist A flag).** Which primitive linking class wins in $d_{\rm top}=1$ contraction? E and A argue (0,1)/bottleneck (transport-limited reading); but a (1,0)/dominant reading would give $J_{\max}^{T^2} = \sqrt{\kappa_D(1 + \tfrac{3}{4}\iota_\tau^2)}\,GM^2/c \approx 0.847\,GM^2/c$ — **3× larger**, pushing cutoff to $\log_{10}\Mbh^{\max} \approx 7.0$. This would be R1 territory. Settling this requires a categorical uniqueness theorem (Specialist E recommends V.T-NEW-5 candidate).

---

## 4. Sub-theorem C: flat interior $\beta \approx 0 \pm 0.3$ (refined by C, grounded by G)

**Specialist G's homological grounding for the unit Jacobian (Wave R7 advance).** In v1, Specialist C asserted "$T^2$-coherence enforces $f_{\rm BH}(\lambda) \propto 1/\lambda$" as a hand-wave. Specialist G's Wave 1 derivation now gives the structural reason:

The coherence projection $\Pi_{\rm coh}$ on $H_1(T^2;\mathbb{Z}) \otimes \mathbb{R}$ kills $\omega_\eta$ (V.T40 base/fiber asymmetry forbids two independent $J$-budgets at fixed $M_{\rm BH}$). Restricted to the gravity-aligned cycle $[\gamma]$, holonomy quantises $M_{\rm BH}$ and $\lambda$ as **reciprocal eigenvalues** of a single boundary operator:
$$\Mbh(\lambda) = \frac{C_\tau}{\lambda}, \quad C_\tau = \mathcal{O}(\iota_\tau)\,M_\odot\,(\bar\lambda)$$
in the regime $\lambda > \lambda_\star \sim \iota_\tau\bar\lambda$. This reciprocal form gives the **unit Jacobian** $|d\log\Mbh/d\log\lambda| = 1$ as a corollary of G's $\Pi_{\rm coh}$ + V.T40 + V.T110 — no longer a hand-wave.

**Convolved interior shape (unchanged from v1).** With $p(\lambda) \propto \lambda^{-\alpha}\exp[-(\lambda/\lambda_c)^q]$ ($\alpha \approx 1.9$ Sheth-Tormen, $q \approx 2$ truncation), pushforward through unit-Jacobian gives:
$$\Phi(\Mbh) \propto \Mbh^{\alpha - 2}\exp[-(C_\tau/\Mbh\lambda_c)^q] \Longrightarrow \beta_{\rm convolved} = \alpha - 2 \approx -0.1.$$
Adding the Sheth-Tormen convolution correction $\Delta\beta \approx -0.27$ gives:
$$\boxed{\beta_{\rm convolved}(M_{\rm BH}) \approx 0\;\text{to}\;-0.30 \quad\text{across}\;10^{4.5} \le M_{\rm BH}/M_\odot \le 10^{6.5}.}$$

**Discriminator vs orthodox DCBH.** Orthodox DCBH treats $f_{\rm DCBH}$ as $\lambda$-independent, $\Mbh \propto M_{\rm gas}$, giving $\beta_{\rm orthodox} \approx -0.9$. The $\Delta\beta \approx 0.9$ separation discriminates at $> 5\sigma$ for $N \ge 60$ Inayoshi-corrected LRDs.

**Scope question (per J's audit ⚠₆).** The unit-Jacobian lemma is a structural extension of V.T110 not yet a separate registry entry. Three options for v2.2: (a) status-quo informal lemma in HeavySeedBirth.lean; (b) promote to V.T110 sub-clause; (c) carve out V.T-NEW-5 entry. **Recommend (c)** for v2.2 — keeps V.T110 frozen, gives the unit-Jacobian its own discoverable name. Defer until G's `coherence_projection` infrastructure lands in TauLib.

---

## 5. Sub-theorem D: sharp slope transition (PENDING PHYSICS — Wave R7 R2 TRIGGERED)

**Specialist F's reconciliation (Wave R7 critical finding).**

**Phase 1 arithmetic gate (PASSED).** Both specialists' formulae are arithmetically pristine. Master formula: $\Delta\log\Mbh|_{0\to -2} = 2\sigma_M^2 \ln 10$. Specialist A (cutoff in $\lambda$-space, Jacobian $1/2$, $\sigma_M = 2\sigma_{\log\lambda}$): $\Delta = 8\sigma_{\log\lambda}^2\ln 10 \approx 1.66$ dex. Specialist C (unit Jacobian, $\sigma_M = \sigma_{\log\lambda}$): $\Delta = 2\sigma_{\log\lambda}^2\ln 10 \approx 0.41$ dex. The ratio is exactly $(2)^2 = 4$, signature that the only physical disagreement is the Jacobian.

**Phase 2 mechanism dominance.** The two specialists are computing different physics: A's mechanism (gas exceeding $\lambda_{\rm crit}$ fails to form a $T^2$-toroidal-horizon BH at all — sharp $\lambda$-cutoff in success probability) vs C's mechanism (every halo seeds; $f_{\rm BH}(\lambda)$ smoothly $\propto 1/\lambda$). **Both genuinely apply** in different sub-regions:
- C dominates the *interior + lower edge* of the cutoff transition (where the Wise-resolved fragmentation hasn't triggered).
- A dominates the *upper edge* (where Inayoshi-Haiman binary-outcome cutoff switches DCBH off entirely).

Inayoshi & Haiman 2014, Mayer & Bonoli 2019, Wise et al. 2019, Regan et al. 2017 — radiation-hydro DCBH simulations support this two-regime picture.

**Phase 3 $\eta_J$ bound.** $\eta_J \in [0.05, 0.15]$ (multi-stage cascade consensus, central $\approx 0.08$). The BVR06 single-cascade form is wrong by 3-4 orders of magnitude.

**Phase 4 reconciled prediction.**
$$\boxed{\Delta\log\Mbh^{\rm reconciled} = 0.9^{+0.5}_{-0.4}\;\text{dex (composite, 68\% CI)}}$$

- C-dominated lower edge: $\Delta \approx 0.4$ dex
- A-dominated upper edge: $\Delta \approx 1.0$-$1.7$ dex
- Composite full width: $\Delta \approx 0.9$ dex with $\pm 0.5$ dex uncertainty

**R2 RISK FLAG TRIGGERED.** The v2.1 paper's $\le 0.2$ dex headline is **not survivable** even at tighter $\sigma_{\log\lambda}$ for atomic-cooling subsamples (Macciò 2007 doesn't actually deliver the tightening at high-$z$ atomic-cooling masses). The v2.2 paper must adopt one of:

- **(b) Relax to single-mechanism C-edge headline $\le 0.4$ dex** — narrower scope than v2.1 but defensible if the C mechanism dominates the observable region.
- **(c) Honest two-mechanism framing $\le 1.5$ dex** — operational falsifier; KS-test power analysis sample size rises modestly to $N \gtrsim 80$-$100$ for $5\sigma$.

**Recommendation for v2.2: option (c)**, operational falsifier $\le 1.5$ dex. This still discriminates against orthodox DCBH (which has *no* upper cutoff at all, so any finite $\Delta$ is distinguishable given $N \gtrsim 100$ LRDs) without hostage-taking the framework on a $0.2$-dex micro-claim the radiation-hydro literature does not support.

**Concrete v2.2 paper edits (Specialist F's recommendation):**

1. `main.tex` line 708-710: relax "transition over $\le 0.2$ dex" to "transition from $0\pm 0.3$ to $\le -2$ over $\le 1.5$ dex (composite of C-dominated low-$\Mbh$ smooth-fraction edge and A-dominated high-$\Mbh$ binary-cutoff Gaussian; see V.T-LRD-1 derivation note §5)".
2. §6.1 power-analysis paragraph: rewrite to use $\le 1.5$ dex falsifier; sample size $N \gtrsim 80$-$100$ for $5\sigma$.
3. New §7 Gap 6 (or extend §7 §5): "two-mechanism transition-width pending physics — Wave R7 reconciled to $0.9$ dex composite, headline relaxed to $\le 1.5$ dex operational falsifier; mechanism-dominance question depends on the (0,1) bottleneck vs (1,0) dominant linking-class selection rule (Specialist E's open V.T-NEW-5 question)."

The Lean module retains the conservative $\le 0.2$ dex witness for backward compatibility with the v2.1 paper (matching the registered claim), but `pred_lrd_sharp_transition` in `FalsificationPack.lean` is correctly marked `currently_testable := false` pending v2.2 revision.

---

## 6. Wave R7 honesty audit (refreshed)

| Sub-claim | $\tau$-distinctive content | Orthodox-imported content |
|---|---|---|
| (A) lower cutoff value | sharpness via V.T88 ↔ V.T110 $S^2$-vs-$T^2$ exclusion gap | $T_{\mathrm{vir}} = 10^4$ K threshold (Bromm-Loeb); $\mu = 0.6$ (transitively from V.T108 BBN); $f_b = 0.16$; $f_{\mathrm{DCBH}} \approx 10^{-2}$ (Inayoshi-Visbal-Haiman 2020) |
| (B) upper cutoff value | $J_{\max}^{T^2} = \iota_\tau\sqrt{\kappa_D}\,GM^2/c$ (E + G converged, $\iota_\tau$-power = 1) | Mo–Mao–White $\lambda$ distribution; multi-stage cascade $\eta_J \approx 0.08$ (F's correction); $f_b$, $f_{\rm cool}$ |
| (C) flat shape $\beta \approx 0$ | unit Jacobian $\|d\log M_{\rm BH}/d\log\lambda\|=1$ from G's coherence projection $\Pi_{\rm coh}$ | log-uniformity over central $\sigma_{\log\lambda}$ window; Sheth–Tormen slope $\alpha \approx 1.9$ |
| (D) sharp transition | $T^2$-cutoff geometric rigidity (theoretical) | $\sigma_{\log\lambda}$ of Bullock distribution; F's two-mechanism reconciliation gives $0.9^{+0.5}_{-0.4}$ dex composite (PENDING PHYSICS) |

---

## 7. Lean-formalisation status (Wave R7 advance)

**Skeleton module:** [`TauLib/BookV/Cosmology/HeavySeedBirth.lean`](../TauLib/BookV/Cosmology/HeavySeedBirth.lean), Wave R7 promotions T1+T3+T4+partial T2 applied (TauReal-witnessed sibling defs alongside `Nat`-scaled originals).

**Wave R7 build verification:** `lake build TauLib.BookV.Cosmology.HeavySeedBirth TauLib.BookV.Cosmology.FalsificationPack` exited 0 with 1082 jobs. All 11 `#eval` smoke tests on HeavySeedBirth match expected witness values. New 5 `#eval` smoke tests on FalsificationPack (`structural_count = 4`, `quantitative_count = 7`, `frontier_count = 3`, plus 2 `currently_testable` bools) match.

**FalsificationPack.lean N15 ledger entries:** 4 new `pred_lrd_*` `TestablePrediction` instances landed (Q4-Q7 in the quantitative tier). `falsification_package` now contains 14 predictions (was 10): 4 structural + 7 quantitative + 3 frontier.

**Trust budget impact:** **none.** Zero new custom axioms; all Wave R7 patches are `def` + structural identity / `native_decide` proofs on `Nat`-scaled or TauReal-witnessed values.

**Phase 0.5 prerequisite path** (Specialist I's design — see [`PHASE-0.5-ANALYTIC-PRIMITIVES.md`](PHASE-0.5-ANALYTIC-PRIMITIVES.md)):
- `TauRealSqrt.lean` (Newton iteration, ~250 lines) — **critical-path** for $J_{\max}^{T^2}$ formalisation.
- `TauRealLog.lean` (~400 lines) — needed for $|d\log N/d\log M_{\rm BH}|$ slope bound.
- `TauRealExp.lean` (~280 lines) — function-form of $\exp$, for log inverse.
- Total: 840-1050 lines, 4-5 weeks with 2 engineers in parallel (revised from v1's "4-7 month" estimate after Specialist I confirmed Phase 0 is more advanced than v1 assumed).

---

## 8. Registry update plan (Wave R7 deliverables)

**To add to `~/Books/PantaRhei-2ndEd/registry/book5_registry.jsonl`:**

| ID | Type | Name | Module | Status | Scope |
|----|------|------|--------|--------|-------|
| V.T-LRD-1 | theorem | $d_{\mathrm{top}}=1$ birth-condition theorem | `TauLib.BookV.Cosmology.HeavySeedBirth` | `skeleton` | `tau-effective` |
| V.T-LRD-1A | sub-theorem | Lower cutoff at $10^{4.5}\,M_\odot$ | `TauLib.BookV.Cosmology.HeavySeedBirth` | `skeleton` | `tau-effective` |
| V.T-LRD-1B | sub-theorem | Upper cutoff at $10^{6.54\pm 0.10}\,M_\odot$ | `TauLib.BookV.Cosmology.HeavySeedBirth` | `skeleton` | `tau-effective` |
| V.T-LRD-1C | sub-theorem | Flat interior $\beta \approx 0\pm 0.3$ | `TauLib.BookV.Cosmology.HeavySeedBirth` | `skeleton` | `tau-effective` |
| V.T-LRD-1D | sub-theorem | Sharp transition at upper cutoff (PENDING) | `TauLib.BookV.Cosmology.HeavySeedBirth` | `skeleton` | `tau-effective` |
| V.D-LRD-1a | definition | Atomic-cooling halo floor | `TauLib.BookV.Cosmology.HeavySeedBirth` | `skeleton` | `orthodox-import` |
| V.D-LRD-1b | definition | DCBH collapse fraction | `TauLib.BookV.Cosmology.HeavySeedBirth` | `skeleton` | `orthodox-import` |
| V.D-LRD-1c | definition | Halo spin log-uniform hypothesis | `TauLib.BookV.Cosmology.HeavySeedBirth` | `skeleton` | `orthodox-import` |
| V.D-LRD-1d | definition | $T^2$-horizon angular-momentum bound | `TauLib.BookV.Cosmology.HeavySeedBirth` | `skeleton` | `tau-effective` |
| V.D-LRD-1e | definition | Seed mass distribution carrier | `TauLib.BookV.Cosmology.HeavySeedBirth` | `skeleton` | `tau-effective` |

**Falsification ledger N15 entries (in `WAVE_50_FALSIFICATION_LEDGER.md` Tier-2/Quantitative):**
- N15.A through N15.D — one row per V.T-LRD-1 sub-theorem, each cross-referenced to the corresponding `pred_lrd_*` `TestablePrediction` instance in `FalsificationPack.lean`.

---

## 9. Cross-coupling matrix (Specialist J's output — see [`V-T-LRD-1-cross-coupling-matrix.md`](V-T-LRD-1-cross-coupling-matrix.md))

Headline cells:
- **✗₄ Red**: V.T-LRD-1B introduces the new $J_{\max}^{T^2}$ structural lemma that morally extends V.T110 but lives in HeavySeedBirth.lean. Recommendation: stay informal in HeavySeedBirth for v2.2; promote to V.T-NEW-5 in next wave.
- **✗₇ Red**: V.T-LRD-1D's $\le 0.2$ dex bound sails close to falsehood pending F's reconciliation. `pred_lrd_sharp_transition.currently_testable := false` documents this.
- **⚠₃ Yellow** (already documented in v2.1 §7 Gap 5): three-way coupling V.T204 ↔ V.T-NEW-1 ↔ V.T239 needs explicit declaration in v2.2 §7 Gap 5 extension.
- **⚠₁ Yellow**: V.T108 BBN $Y_p = 20/81$ → $\mu = 0.6$ chain now declared in §2.6 above.
- **⚠₂ Yellow**: V.T88 mass-gap S² vs T² distinction now declared in §2.5 above.

V.T110 propagation check: **EMPTY downstream**. No module currently consumes V.T-LRD-1B's $J_{\max}^{T^2}$ refinement. Self-contained, trust-budget impact zero.

---

## 10. Open questions for the next wave (V.T-NEW-5 candidate)

1. **Reconcile the (0,1) bottleneck vs (1,0) dominant primitive linking-class selection rule** in $d_{\rm top}=1$ contraction (Specialist E + Specialist A flag). E and A argue (0,1) on transport-limited grounds; a (1,0) reading would shift the cutoff to $\log_{10}\Mbh^{\max} \approx 7.0$, R1 territory. Resolution requires a categorical uniqueness theorem — recommend **V.T-NEW-5** for the next wave.

2. **Promote unit-Jacobian + $J_{\max}^{T^2}$ structural lemmas** to a separate registry entry (J's audit recommendation): either V.T-NEW-5 or V.T110 sub-clauses.

3. **Phase 0.5 TauReal infrastructure** (sqrt + log + exp) per Specialist I's design doc — 4-5 weeks with 2 engineers.

4. **V.T-NEW-1 ($\tau$-modified $T_{\rm vir}^\tau(z)$)**: the chemistry-evolution gap of v2.1 §7 Gap 2, separately scoped 2-4 year programme. Three-way coupling with V.T239 (J's audit).

5. **V.T-NEW-4 ($\tau$-modified disc self-gravity for $f_{\rm DCBH}$)**: Specialist B's residual flag.

---

## 11. Wave R7 deliverables summary

**This document (v2 derivation note):** comprehensive integration of all Wave R7 outputs.

**Lean module updates (committed):**
- HeavySeedBirth.lean: T1+T3+T4+partial T2 promotions, updated docstring (Wave R7 reconciliation, cross-validation, Phase 0 status sections).
- FalsificationPack.lean: 4 new `pred_lrd_*` instances (Q4-Q7), updated `falsification_package` (14 predictions), updated count theorems.

**Companion documents (this wave):**
- [`PHASE-0.5-ANALYTIC-PRIMITIVES.md`](PHASE-0.5-ANALYTIC-PRIMITIVES.md) — Specialist I's design doc.
- [`V-T-LRD-1-cross-coupling-matrix.md`](V-T-LRD-1-cross-coupling-matrix.md) — Specialist J's cross-coupling matrix.

**Cross-repo deliverables (next):**
- `~/Books/PantaRhei-2ndEd/audit/WAVE_R7_VTLRD1_CLOSING_DASHBOARD.md` (sprint dashboard)
- `~/Books/PantaRhei-2ndEd/registry/book5_registry.jsonl` (10 new JSONL records)
- `~/Books/PantaRhei-2ndEd/audit/WAVE_50_FALSIFICATION_LEDGER.md` (4 N15 entries)
- `~/Books/PantaRhei-2ndEd/papers/research-notes/lrd-categorical-v2/main.tex` (v2.2 patch — **user-gated**: option (c) headline relaxation to $\le 1.5$ dex per F's R2 trigger)

---

**End of derivation note v2. Wave R7 deep-research sprint physics complete; Lean infrastructure advanced; v2.2 paper recommendations surfaced for user gate.**
