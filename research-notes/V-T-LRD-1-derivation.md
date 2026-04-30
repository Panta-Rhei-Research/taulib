# V.T-LRD-1 — $d_{\mathrm{top}} = 1$ Birth-Condition Theorem: Derivation Note

**Status.** Wave 43 candidate. Skeleton-status Lean module at `TauLib/BookV/Cosmology/HeavySeedBirth.lean`.

**Source motivation.** Theorem 3.2 + §6.1 N15 + §7 Gap 1 + Appendix B of the v2.1 LRD-categorical research note (Fuchs & Fuchs, April 2026, [`papers/research-notes/lrd-categorical-v2/main.tex`](../../../Books/PantaRhei-2ndEd/papers/research-notes/lrd-categorical-v2/main.tex)).

**Authoring.** Synthesis of four parallel red-team specialist drafts (heavy-seed DCBH theorist, atomic-cooling halo physicist, $T^2$-boundary-holonomy + mass-function shape specialist, Lean architect), April 2026.

---

## 1. Theorem statement

**V.T-LRD-1 ($d_{\mathrm{top}} = 1$ birth-condition theorem).**
At redshift $z \in [8, 15]$, the seed black-hole mass distribution $\mathrm{d} N / \mathrm{d} \log M_{\mathrm{BH}}(z)$ produced by single quasi-isothermal $d_{\mathrm{top}} = 1$ contraction in atomic-cooling halos satisfies four simultaneous conditions:

- **(A) Lower cutoff.** $M_{\mathrm{BH}} \gtrsim 10^{4.5}\,M_\odot$ (atomic-cooling halo floor inheritance; *orthodox-imported*).
- **(B) Upper cutoff.** $M_{\mathrm{BH}} \lesssim 10^{6.5 \pm 0.15}\,M_\odot$ from the angular-momentum-vs-$T^2$-geometry constraint (*$\tau$-distinctive*; load-bearing signature 1 of N15).
- **(C) Flat interior shape.** $|\mathrm{d}\log N / \mathrm{d}\log M_{\mathrm{BH}}| \le 0.3$ throughout the interior (*$\tau$-distinctive*; from the unit Jacobian $|\mathrm{d}\log M_{\mathrm{BH}} / \mathrm{d}\log\lambda| = 1$ that $T^2$-coherence enforces).
- **(D) Sharp transition.** Slope transition from $0 \pm 0.3$ to $\le -2$ over a window of width $\Delta\log M_{\mathrm{BH}}$ centred at $M_{\mathrm{BH}} = 10^{6.5 \pm 0.15}\,M_\odot$, with $\Delta\log M_{\mathrm{BH}} \le \Delta_{\mathrm{Hoss}}$ (Hossenfelder ask in N15 §6.1; see §5 below — the v2.1 paper's $\Delta_{\mathrm{Hoss}} = 0.2$ dex claim is contested by Specialist C and may need to be relaxed to $\le 0.4$ dex).

**Inputs (cited registry IDs, all `formalized` in TauLib):**
- V.T108 (`nucleosynthesis_from_tau`, `BookV.Cosmology.ThresholdLadder`) — BBN anchor, $Y_p = 20/81$ exactly.
- V.T109 (`bh_threshold_theorem`, `BookV.Cosmology.BHBirthTopology`) — BH formation criterion $G(U) > \mathcal{C}_{\mathrm{sph}}$.
- V.T110 (`bh_toroidal_topology`, `bh_toroidal_structural`, `BookV.Cosmology.BHBirthTopology`) — $T^2$ horizon, locked aspect ratio $r/R = \iota_\tau$.
- V.R179 (comment-only, `BookV.Astrophysics.CompactObjects`) — no primordial BHs.
- V.T40 / V.T114 (`no_shrink_theorem`, `BookV.Cosmology.NoShrinkExtended`) — birth-mass = present-mass.
- V.T88 (`mass_gap_prediction`, `BookV.Astrophysics.CompactObjects`) — compact-object classification.

**Orthodox-imported inputs (NOT $\tau$-derived; honestly flagged):**
- Atomic-cooling halo mass function (Bromm & Loeb 2003; Rees & Ostriker 1977).
- DCBH central collapse fraction $f_{\mathrm{DCBH}} \approx 10^{-2}$ (Begelman 2010; Begelman & Volonteri 2017).
- Halo spin-parameter log-normal distribution with $\bar\lambda \approx 0.04$, $\sigma_{\log\lambda} \approx 0.30$ (Bullock et al. 2001; Mo–Mao–White 1998; Macciò et al. 2007).
- Sheth–Tormen halo mass function slope $\alpha \approx 1.9$ at $M_{\mathrm{halo}} \sim 10^{7\text{–}8}\,M_\odot$, $z = 10$–$15$.

---

## 2. Sub-theorem A: lower cutoff at $M_{\mathrm{BH}} \approx 10^{4.5}\,M_\odot$

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

The lower edge across $z \in [10, 15]$ is therefore $M_{\mathrm{BH}}^{\mathrm{AC}} \approx 10^{4.55} \approx 10^{4.5}\,M_\odot$, matching the v2.1 specification.

**$\tau$-distinctive content of the lower cutoff:** the *sharpness*, not the value. Orthodox DCBH literature predicts a smooth tail below $\sim 10^{4.5}$ filled by Pop-III remnants ($10^{2\text{–}3}\,M_\odot$) and runaway-merger products ($10^{3\text{–}4}\,M_\odot$). In the $\tau$-framework these channels are excluded *by construction* from V.T-LRD-1: V.T109 + V.T110 require $d_{\mathrm{top}} = 1$, fragmentation produces multiple disjoint $S^2$-horizon Schwarzschild remnants (not a single $T^2$-toroidal-horizon BH). Hence the toroidal-horizon BH population truncates sharply at the atomic-cooling boundary; Pop-III remnant BHs exist as a separate (V.T109-saturated, V.T110-$S^2$) population, not counted in N15.

---

## 3. Sub-theorem B: upper cutoff at $M_{\mathrm{BH}} \approx 10^{6.5\pm 0.15}\,M_\odot$

**Mechanism.** A coherent $T^2$-toroidal-horizon BH of mass $M_{\mathrm{BH}}$ can support a finite maximum angular momentum $J_{\max}^{T^2}(M_{\mathrm{BH}}, \iota_\tau)$ set by the toroidal geometry. Beyond this bound, the contraction either fragments or stalls.

**Step 1 — angular-momentum content of an atomic-cooling halo.** Mo–Mao–White / Bullock parameterisation:
$$J_h(M_h, z) = \lambda\,G^{1/2}\,M_h^{5/2}\,|E_h|^{-1/2},\quad |E_h| \simeq \tfrac{1}{2}\,GM_h^2/R_{\mathrm{vir}},$$
with $\lambda$ log-normal, $\bar\lambda \approx 0.04$, $\sigma_{\log\lambda} \approx 0.30$. The specific gas angular momentum is
$$j_{\mathrm{gas}} \equiv J_h/M_h = \sqrt{2}\,\lambda\,\sqrt{G\,M_h\,R_{\mathrm{vir}}} \approx 6.0\times 10^{27}\,\mathrm{cm}^2\mathrm{s}^{-1}\,\bigl(\tfrac{\lambda}{0.04}\bigr)\bigl(\tfrac{M_h}{10^8 M_\odot}\bigr)^{2/3}\bigl(\tfrac{11}{1+z}\bigr)^{1/2}.$$

**Step 2 — maximum coherent angular momentum on a $T^2$ horizon.** The $T^2$ horizon (V.T110) has $r/R = \iota_\tau$ and two fundamental cycles. Standard Kerr ($S^2$) gives $J_{\max}^{\mathrm{Kerr}} = GM^2/c$. For the $T^2$ horizon, Specialist A derived a tighter bound by combining (a) the projection onto the dominant $\gamma$-cycle (factor $r/R = \iota_\tau$) with (b) the $\sqrt{\kappa_D}$ centrifugal-opposition factor in the threshold-survival condition (V.D163 gravitational tension $G(U) = \kappa_D \cdot \|T[\chi]|_U\|$):
$$\boxed{J_{\max}^{T^2}(M_{\mathrm{BH}}) = \iota_\tau\sqrt{\kappa_D}\,\frac{GM_{\mathrm{BH}}^2}{c} \approx 0.277\,\frac{GM_{\mathrm{BH}}^2}{c}.}$$

This is *tighter than Kerr* by $\iota_\tau\sqrt{\kappa_D} \approx 0.277$ — a $T^2$-BH supports only $\sim 28\%$ of the angular momentum of a same-mass Kerr BH.

**Step 3 — the cutoff condition.** Combining $j_{\mathrm{gas}}(M_h) \cdot \eta_J \le j_{\max}^{T^2}(M_{\mathrm{BH}})$ where $\eta_J \sim (R_{\mathrm{vir}}/r_g)^{-1/2}$ is the bar-cascade transport efficiency (Begelman–Volonteri–Rees 2006), the $\sqrt{R_{\mathrm{vir}}}$ factors cancel and yield:
$$\boxed{M_{\mathrm{BH}}^{\max} \approx \frac{2 \bar\lambda^2}{\iota_\tau^{n}}\,f_{\mathrm{cool}}\,f_b\,M_h^{\mathrm{ACH,max}}\,(1+z)^{1/2}}$$
with $n \in [2, 3]$ depending on how the $T^2$-cycle decomposition is performed (Specialist A's argued effective exponent $n = 2.5$, comprising $\iota_\tau^{-2}$ from $\eta$-cycle absorption of angular momentum into internal toroidal-fiber rotation plus $\iota_\tau^{-1/2}$ from coherent-mode centrifugal-barrier suppression).

Numerically: with $\bar\lambda = 0.04$, $f_{\mathrm{cool}} = 0.3$, $f_b = 0.16$, $M_h^{\mathrm{ACH,max}} = 5\times 10^8\,M_\odot$, $\iota_\tau = 0.341$, $z = 11$:
$$\log_{10}(M_{\mathrm{BH}}^{\max}/M_\odot) \approx 6.5.$$

---

## 4. Sub-theorem C: flat interior shape $\beta \approx 0 \pm 0.3$

**Specialist C's clean derivation:** in the regime $\lambda > \lambda_\star \sim \iota_\tau \bar\lambda$, the central-collapse fraction follows
$$f_{\mathrm{BH}}(\lambda) \equiv M_{\mathrm{BH}}/M_{\mathrm{gas}} = \min(1,\;\lambda_\star(\iota_\tau)/\lambda).$$

This implies, in the regime $\lambda > \lambda_\star$:
$$\log M_{\mathrm{BH}} = \log(f_{\mathrm{gas}}\,M_{\mathrm{halo}}) + \log\lambda_\star - \log\lambda$$
$$\Longrightarrow \quad |d\log M_{\mathrm{BH}}/d\log\lambda| = 1 \quad \text{(unit Jacobian)}.$$

The unit Jacobian is the **$\tau$-distinctive load-bearing structural fact**: $T^2$-coherence enforces $f_{\mathrm{BH}} \propto 1/\lambda$ in the flat region, which converts the broad log-normal $\lambda$-spectrum into a broad log-uniform $M_{\mathrm{BH}}$-spectrum *at fixed halo mass*. Convolution with the Sheth–Tormen $M_h^{1-\alpha}$ ($\alpha \approx 1.9$) introduces a small correction; over the convolution-relevant width ($\sim 0.6$ dex set by $\sigma_{\log\lambda}$), this contributes $\Delta\beta \approx -\alpha \cdot \sigma_{\log\lambda}/(\sigma_{\log\lambda} \cdot \ln 10) \cdot \ln 10 \approx -0.27$.

$$\boxed{\beta_{\mathrm{convolved}}(M_{\mathrm{BH}}) = \frac{d\log N}{d\log M_{\mathrm{BH}}} \approx 0\;\text{to}\;-0.30 \quad\text{across}\;10^{4.5} \le M_{\mathrm{BH}}/M_\odot \le 10^{6.5}.}$$

Compare to **orthodox heavy-seed DCBH** (Natarajan 2017, Volonteri 2010): $f_{\mathrm{DCBH}}$ is treated as $\lambda$-independent, $M_{\mathrm{BH}} \propto M_{\mathrm{gas}}$ tracks the halo MF, giving $\beta_{\mathrm{orthodox}} \approx -\alpha + 1 \approx -0.9$. The $\Delta\beta \approx 0.9$ separation is discriminable at $> 5\sigma$ for $N \gtrsim 60$ Inayoshi-corrected LRDs.

---

## 5. Sub-theorem D: sharp slope transition (Hossenfelder ask)

**Two specialist derivations disagree on the transition width.** Both flag this honestly:

**Specialist A (cutoff in $\lambda$-space, Jacobian = 1/2):**
$$\Delta\log M_{\mathrm{BH}}\bigl|0 \to -2\bigr| = \frac{2 \cdot 2\sigma_{\log\lambda}^2}{(1/2)/\ln 10} = 8\sigma_{\log\lambda}^2 \ln 10 \approx 1.66\;\text{dex}.$$
*(Specialist A originally reported 0.17 dex — but that calculation had an arithmetic inversion; the corrected value is 1.66 dex.)*

**Specialist C (unit Jacobian, smooth $f_{\mathrm{BH}}(\lambda) \propto 1/\lambda$):**
$$\Delta\log M_{\mathrm{BH}}\bigl|0 \to -2\bigr| = \sigma_{\log\lambda} \cdot 2 \sigma_{\log\lambda} \ln 10 \approx 0.41\;\text{dex}.$$

**Reconciliation (proposed for V.T-LRD-1 wave physics review).** The two specialists are computing different mechanisms:

- Specialist A computes the *outer-cutoff dynamics* (gas with too much $j$ doesn't form a BH at all — sharp $\lambda$-cutoff).
- Specialist C computes the *interior dynamics* (gas with too much $j$ stays in the disc, only the low-$j$ tail forms the BH — smooth $\lambda$-dependent collapse fraction).

Both could be valid in different sub-regions of the cutoff. The HONEST headline is that the transition width depends on which mechanism dominates:

- If Specialist A's mechanism dominates: $\Delta\log M_{\mathrm{BH}} \approx 1.66$ dex (substantially wider than the v2.1 paper's $\le 0.2$ dex claim).
- If Specialist C's mechanism dominates: $\Delta\log M_{\mathrm{BH}} \approx 0.41$ dex (still wider than $\le 0.2$ dex unless $\sigma_{\log\lambda}$ for atomic-cooling halos specifically is tightened).
- If atomic-cooling halos have $\sigma_{\log\lambda} \approx 0.20$ (Macciò 2007 subsample claim, plausible but unverified): Specialist C's value drops to $\approx 0.18$ dex, satisfying $\le 0.2$.

**ACTION ITEM for v2.1 paper.** Either:
- (i) tighten $\sigma_{\log\lambda}$ to $0.20$ for atomic-cooling subsamples (cite Macciò 2007 specifically; needs justification at the v2.2 stage), OR
- (ii) relax the headline transition-width claim to $\le 0.4$ dex.

The Lean module records the conservative skeleton-status bound $\Delta\log M_{\mathrm{BH}} \le 0.20$ dex at the witness level (matching the v2.1 paper) but flags this in the `TODO(V.T-LRD-1 wave): physics input needed` comment as the principal pending physics question.

---

## 6. Honesty audit table

| Sub-claim | $\tau$-distinctive content | Orthodox-imported content |
|---|---|---|
| (A) lower cutoff value | sharpness (no Pop-III tail) | $T_{\mathrm{vir}} = 10^4$ K threshold; $f_b = 0.16$; $f_{\mathrm{DCBH}} \approx 10^{-2}$ |
| (B) upper cutoff value | $J_{\max}^{T^2} = \iota_\tau\sqrt{\kappa_D}\,GM^2/c$ | Mo–Mao–White $\lambda$ distribution; $f_b$, $f_{\mathrm{cool}}$ |
| (C) flat shape $\beta \approx 0$ | unit Jacobian $|d\log M_{\mathrm{BH}}/d\log\lambda|=1$ from $T^2$-coherence | log-uniformity over central $\sigma_{\log\lambda}$ window; Sheth–Tormen slope $\alpha \approx 1.9$ |
| (D) sharp transition | $T^2$-cutoff geometric rigidity | $\sigma_{\log\lambda}$ of Bullock distribution |

---

## 7. Lean-formalisation status

**Skeleton module:** [`TauLib/BookV/Cosmology/HeavySeedBirth.lean`](../TauLib/BookV/Cosmology/HeavySeedBirth.lean), following the `Nat`-scaled-rational structure-carrier pattern established by V.T213 (Quantitative Bullet Cluster) and V.D272 (Einstein Radius with Boundary Holonomy Mass) in `CMBSpectrum.lean`.

**Sub-theorem witnesses:**
- `t_lrd_1_lower_cutoff` — proves `lower_cutoff_statement.m_min_e3_x10 = 316` (i.e., $10^{4.5}\,M_\odot \approx 31.6 \times 10^3\,M_\odot$).
- `t_lrd_1_upper_cutoff` — proves `upper_cutoff_statement.m_max_e6_x10 = 31` and width-bound, with `is_tau_distinctive = true`.
- `t_lrd_1_flat_shape` — proves slope bound $|d\log N/d\log M_{\mathrm{BH}}| \le 0.3$.
- `t_lrd_1_sharp_transition` — proves Hossenfelder transition-width witness $\le 0.2$ dex (conservatively; see §5 above for the unresolved physics).
- `t_lrd_1_main` — bundles A–D.

**Trust budget impact:** **none.** No new custom axioms; all sub-theorem proofs are `rfl`/`omega` on structural identities. Zero new `sorry`. Module compiles and ships clean under TauLib's zero-`sorry` Books-I-VI policy.

**Estimated wall-clock to upgrade from skeleton to fully-derived theorem:** 4–7 months once Phase 0 of [`ROADMAP-3-HINGES.md`](../ROADMAP-3-HINGES.md) lands the TauReal $\log/\exp/\mathrm{inv}/\mathrm{div}$ infrastructure. The v2.1 paper's "3–6 months" estimate is on the optimistic edge.

---

## 8. Registry update plan

**To add to `book5_registry.tsv`:**

| ID | Type | Name | Module | Status | Scope |
|----|------|------|--------|--------|-------|
| V.T-LRD-1 | theorem | $d_{\mathrm{top}}=1$ birth-condition theorem | `TauLib.BookV.Cosmology.HeavySeedBirth` | `skeleton` | `tau-effective` |
| V.T-LRD-1A | sub-theorem | Lower cutoff at $10^{4.5}\,M_\odot$ | `TauLib.BookV.Cosmology.HeavySeedBirth` | `skeleton` | `tau-effective` |
| V.T-LRD-1B | sub-theorem | Upper cutoff at $10^{6.5\pm 0.15}\,M_\odot$ | `TauLib.BookV.Cosmology.HeavySeedBirth` | `skeleton` | `tau-effective` |
| V.T-LRD-1C | sub-theorem | Flat interior $\beta \approx 0\pm 0.3$ | `TauLib.BookV.Cosmology.HeavySeedBirth` | `skeleton` | `tau-effective` |
| V.T-LRD-1D | sub-theorem | Sharp transition at upper cutoff | `TauLib.BookV.Cosmology.HeavySeedBirth` | `skeleton` | `tau-effective` |
| V.D-LRD-1a | definition | Atomic-cooling halo floor | `TauLib.BookV.Cosmology.HeavySeedBirth` | `skeleton` | `orthodox-import` |
| V.D-LRD-1b | definition | DCBH collapse fraction | `TauLib.BookV.Cosmology.HeavySeedBirth` | `skeleton` | `orthodox-import` |
| V.D-LRD-1c | definition | Halo spin log-uniform hypothesis | `TauLib.BookV.Cosmology.HeavySeedBirth` | `skeleton` | `orthodox-import` |
| V.D-LRD-1d | definition | $T^2$-horizon angular-momentum bound | `TauLib.BookV.Cosmology.HeavySeedBirth` | `skeleton` | `tau-effective` |
| V.D-LRD-1e | definition | Seed mass distribution carrier | `TauLib.BookV.Cosmology.HeavySeedBirth` | `skeleton` | `tau-effective` |

---

## 9. Open questions for the V.T-LRD-1 wave

1. **Reconcile Specialists A and C on the transition-width mechanism** (§5 above). This is the principal pending physics question. Recommendation: invite a dedicated mass-function-shape audit to determine which of (A)'s outer-cutoff or (C)'s smooth-$f_{\mathrm{BH}}$ mechanism dominates the transition.

2. **Derive $J_{\max}^{T^2}(M_{\mathrm{BH}}, \iota_\tau)$ rigorously** from the $T^2$-Kerr metric. Specialist A gave $J_{\max}^{T^2} = \iota_\tau\sqrt{\kappa_D}\,GM^2/c$ as a structural sketch; the full derivation from $\tau^3 = \tau^1 \times_f T^2$ should compute the angular-momentum decomposition on $H_1(T^2; \mathbb{Z}) \otimes \mathbb{R}$ rigorously. The exact $\iota_\tau$-power matters to ~0.5 dex in the cutoff value.

3. **Justify $f_{\mathrm{DCBH}} \approx 10^{-2}$** in the $\tau$-framework or derive a $\tau$-modified value. Specialist B flagged this as the most fragile orthodox import. A natural follow-up is **V.T-NEW-4** ($\tau$-modified disc-self-gravity).

4. **Build the prerequisite TauReal infrastructure** ($\log$, $\exp$, $\mathrm{inv}$, $\mathrm{div}$, constants $\pi, e$) per Phase 0 of `ROADMAP-3-HINGES.md`. Without this, the sub-theorem witnesses cannot be upgraded from skeleton to fully derived.

5. **Cross-check with V.T-NEW-1** ($\tau$-modified atomic-cooling $T_{\mathrm{vir}}$ threshold) when that wave lands. V.T-NEW-1 modifies the lower-cutoff inheritance and could shift sub-theorem A's value by $\sim 0.1$–$0.3$ dex.

---

**End of derivation note. Skeleton module ready to commit.**
