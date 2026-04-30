# V.T-LRD-1 Cross-Coupling Matrix

**Author:** Specialist J ($\tau$-cosmology cross-coupling specialist), Wave R7 V.T-LRD-1 sprint.

**Mission:** Audit V.T-LRD-1 outputs against existing $\tau$-cosmology theorems and companion research notes for **contradiction or under-coupling**.

**Bottom line:** Two outright Red cells (✗₄ J_max^{T²} as V.T110 extension; ✗₇ sub-theorem D pending physics), three Yellow-flagged under-couplings (⚠₁ V.T108 BBN; ⚠₂ V.T88 mass-gap distinction; ⚠₃ V.T204 ↔ V.T-NEW-1 ↔ V.T239 three-way coupling). All resolution paths documented in derivation note v2 §§2.5-2.7, §§3-5, §10.

---

## 1. The matrix

Rows: V.T-LRD-1 sub-theorems and V.D-LRD-1a–e definitions.
Columns: existing audit targets (V.T-* theorems + N9-N14 companion-note falsification entries).
Cells: **Green ✓** (independent), **Yellow ⚠** (under-coupled), **Red ✗** (contradiction or strong cross-coupling requiring action).

| | V.T108 BBN | V.T109 BH thresh | V.T110 T² horizon | V.T40/T114 No-Shrink | V.T88 mass gap | V.T98 Wilson skel. | V.T204 BTFR/$a_0(z)$ | V.T213 cluster-lensing | V.T239 SFE/$E_z$ | kSZ N12 | kSZ N13 | kSZ N14 | inflation N9 | inflation N10 | inflation N11 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| **A: lower cutoff $10^{4.5}$** | ⚠₁ | ✓ (input) | ✓ (input) | ✓ (input) | ⚠₂ | ✓ | ⚠₃ | ✓ | ⚠₃ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| **B: upper cutoff $10^{6.54}$** | ✓ | ✓ (input) | **✗₄** | ✓ | ⚠₅ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ⚠₁₀ |
| **C: flat shape $\beta\le 0.3$** | ✓ | ✓ | ⚠₆ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| **D: sharp transition (PENDING)** | ✓ | ✓ | **✗₇** | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| **D-LRD-1a (ACH floor)** | ⚠₁ | ✓ | ✓ | ✓ | ✓ | ✓ | ⚠₃ | ✓ | ⚠₃ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| **D-LRD-1b ($f_{DCBH}$)** | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| **D-LRD-1c (Bullock spin)** | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ⚠₃ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| **D-LRD-1d ($J_{\max}^{T^2}$)** | ✓ | ✓ | **✗₄** | ✓ | ✓ | ⚠₈ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| **D-LRD-1e (seed MF carrier)** | ✓ | ✓ | ✓ | ✓ | ✓ | ⚠₈ | ⚠₃ | ✓ | ⚠₃ | ✓ | ⚠₉ | ✓ | ✓ | ✓ | ⚠₁₀ |

---

## 2. Cell-by-cell findings

### ⚠₁ (V.T108 ↔ A, D-LRD-1a) — V.T108 BBN coupling

V.T108 commits to $Y_p = 20/81$ exactly. The V.T-LRD-1A lower-cutoff derivation uses $\mu = 0.6$ (partial-ionisation regime at the ACH cooling boundary), which depends on $Y_p$ via the chain:
$$Y_p = 20/81 \Rightarrow X = 61/81 \Rightarrow n_{\rm He}/n_{\rm H} \approx 0.082 \Rightarrow \mu \approx 0.59\text{-}0.61.$$
A 1% shift in $Y_p$ propagates to $\Delta\log_{10}\Mbh^{\rm AC} \sim 0.002$ dex — well below v2.1 reporting precision. v2.1 §6.1 already declares V.T108 a separately-falsifiable anchor ("framework-coupled BBN handle").

**Resolution:** declared as §2.6 of derivation note v2; proposed Lean lemma `t_lrd_1_v_t108_consistency` for next-wave Lean work (not blocking).

### ⚠₂ (V.T88 ↔ A) — V.T88 mass-gap S²-vs-T² distinction

V.T88's mass-gap upper edge of $5\,M_\odot$ classifies $S^2$-horizon Schwarzschild remnants only. V.T-LRD-1's lower cutoff at $\sim 10^{4.5}\,M_\odot$ describes $T^2$-horizon BHs only. The gap region $5$–$10^{4.5}\,M_\odot$ is a topological exclusion zone, not a cooling/feedback suppression. This makes V.T-LRD-1A's sharpness genuinely $\tau$-distinctive.

**Resolution:** declared as §2.5 of derivation note v2 (sharpness = $\tau$-distinctive content via V.T88 ↔ V.T110 distinction). The Lean module already has `t_lrd_1_above_mass_gap` sanity check at `HeavySeedBirth.lean:918` proving `mass_gap_upper < 31600`.

### ⚠₃ (V.T204/V.T239 ↔ A, D-LRD-1a, D-LRD-1c, D-LRD-1e) — Three-way high-$z$ coupling

V.T204 ($a_0(z) = c \cdot H(z) \cdot \iota_\tau / 2$) at $z = 10$-$13$ has **two downstream consequences**:
- (a) LRD-progenitor abundance via modified $T_{\rm vir}^\tau(z)$ (V.T-NEW-1 future work; signature 5 of N15 in v2.1 paper).
- (b) JWST star formation efficiency enhancement V.T239 (`tau_sfe_pct = 47` vs ΛCDM 40).

The v2.1 paper §7 Gap 5 already documents the V.T204 ↔ BTFR √ι_τ deficit ↔ signature 5 cross-coupling at the BTFR axis but **misses the V.T239 axis**.

**Resolution:** declared as derivation note v2 §2.7 ("V.T-NEW-1 stub"). v2.2 paper §7 Gap 5 should be **extended to a three-way coupling** V.T204 ↔ V.T-NEW-1 ↔ V.T239 (concrete edit recommended below).

### ✗₄ (V.T110 ↔ B, D-LRD-1d) — RED: $J_{\max}^{T^2}$ as a V.T110 structural extension

V.T-LRD-1B introduces an entirely new structural lemma:
$$J_{\max}^{T^2}(M_{\rm BH}) = \iota_\tau\sqrt{\kappa_D}\,GM^2/c \approx 0.277\,J_{\max}^{\rm Kerr}.$$
Cross-validated by Specialists E (Wald-Carter-Penrose lens) and G (categorical/homological lens) independently — both arrived at $\iota_\tau$-power = 1. This is a *de facto upgrade* to V.T110: previously V.T110 only stated `bh_toroidal_topology` ("BH horizon topology is T²") and `bh_toroidal_structural` (linking class non-trivial). It said *nothing* about angular-momentum bounds.

**Resolution options:**
- **(a) Status quo (RECOMMENDED for v2.2)**: keep the lemma informally inside `HeavySeedBirth.lean` as `iota_tau_T2_bound_TauReal` (Wave R7 partial T2 promotion, landed). Cite from G's `coherence_projection` and V.T110.
- **(b) Promote to V.T110 sub-clause**: extend V.T110's statement to include the unit Jacobian + $J_{\max}^{T^2}$ as part of its conclusion. Cleanest categorical fit but mutates a locked theorem; defer.
- **(c) Carve out V.T-NEW-5**: register `J_max_T2_bound` and `t_lrd_1_unit_jacobian` as their own theorem with V.T110 + V.T40 + G's $\Pi_{\rm coh}$ as hypotheses. **Recommended for next wave** (post Phase 0.5 + Wave R8).

### ⚠₅ (V.T88 ↔ B) — Mass-gap upper-edge for $T^2$-horizon BHs

The upper cutoff $10^{6.54}\,M_\odot$ is the *load-bearing N15 signature 1 falsifier*. V.T88 (compact-object classification) does not currently encode an upper-mass classification cutoff for $T^2$-horizon BHs. **Open question**: does V.T88 need a third tier (super-massive $T^2$-horizon BHs above $10^{6.54}\,M_\odot$, formed by post-V.T-LRD-1 *accretion* from below the cutoff)? If yes, V.T88 needs a comment-only remark.

**Resolution**: defer to V.T88 documentation update (low-priority hygiene; not blocking).

### ⚠₆ (V.T110 ↔ C) — Unit Jacobian as V.T110 structural extension

The unit Jacobian $|d\log\Mbh/d\log\lambda| = 1$ is now structurally grounded by Specialist G's coherence projection $\Pi_{\rm coh}$ on $H_1(T^2;\mathbb{Z}) \otimes \mathbb{R}$. This is another structural extension of V.T110 living in HeavySeedBirth.lean.

**Resolution**: same as ✗₄ — recommend V.T-NEW-5 candidate for next wave bundling both the unit-Jacobian lemma and the $J_{\max}^{T^2}$ bound.

### ✗₇ (V.T110 ↔ D) — RED: Sub-theorem D PENDING PHYSICS

The sharp-transition $\le 0.2$ dex bound is sailing close to falsehood pending Specialist F's reconciliation. Wave R7 found:
- A's mechanism: 1.66 dex outer-cutoff binary mechanism.
- C's mechanism: 0.41 dex unit-Jacobian smooth-fraction.
- Both apply in different sub-regions; composite $0.9^{+0.5}_{-0.4}$ dex.

**Resolution (Wave R7 LANDED)**: `pred_lrd_sharp_transition.currently_testable := false` correctly documents the pending-physics status. The v2.2 paper headline must relax (recommendation: option (c) honest two-mechanism framing $\le 1.5$ dex).

### ⚠₈ (V.T98 ↔ D-LRD-1d, D-LRD-1e) — Wilson-skeleton high-bias node count

V.T98 (Wilson-skeleton cosmic web) is cited in v2.1 §7 Gap 3 ("LRDs sit at Wilson-skeleton high-bias nodes per V.T98"). The V.D-LRD-1e seed-mass distribution carrier and the comoving number density of LRDs *should* connect to V.T98's high-bias node count, but v2.1 §7 Gap 3 explicitly states "the cosmological supply chain has no parameter-free closed-form τ-derivation."

**Resolution**: no action needed beyond v2.1 §7 Gap 3 acknowledgement; Wave R7 outputs do not implicitly close Gap 3 (the angular-momentum-cutoff derivation does not constrain the *abundance*, only the *seed mass distribution shape*).

### ⚠₉ (kSZ N13 ↔ D-LRD-1e) — Boundary-holonomy mass mechanism

N13 (pairwise-kSZ amplitude consistency) commits to consistency with $M_{\rm eff} = M_{\rm pt}(1 + M_{\rm pa}/M_{\rm pt})$, $M_{\rm eff}/M_{\rm pt} \le 6.65$. LRDs at $z = 5$-$7$ have $M_{\rm BH} \in [10^{4.5}, 10^{6.5}]\,M_\odot$ — well below cluster scale. The two predictions don't directly cross-couple, but the boundary-holonomy-mass mechanism that gives 6.65 at cluster scales also operates at sub-galactic scales (V.T213 + V.D272), and signature 3 of N15 is *aperture saturation at LRD scales* anchored on V.T213 + V.D272.

**Resolution**: v2.2 paper §6.1 N15 signature 3 should declare cross-reference to N13/N14 (concrete edit recommended below).

### ⚠₁₀ (inflation N11 ↔ B, D-LRD-1e) — $A_s$ → $\sigma_8$ → $M_h^{\rm ACH,max}$

N11 ($A_s = (121/225)\iota_\tau^{18}(1 - \iota_\tau^3/3)$ consistency) directly sets $\sigma_8$ and the halo MF normalisation that V.T-LRD-1's atomic-cooling halo abundance inherits via $M_h^{\rm ACH,max} = 5\times 10^8\,M_\odot$ (derivation §3 step 3). If $A_s$ is significantly off the inflation-note central value, halo MF normalisation shifts, and $M_h^{\rm ACH,max}$ shifts proportionally, which feeds into the upper cutoff value. Logarithmic dependence is weak ($\le 0.1$ dex per dex shift in $A_s$), but should be documented.

**Resolution**: v2.2 paper §6.1 framework-coupled handles paragraph should add cross-reference to N11 (concrete edit recommended below).

---

## 3. V.T110 propagation check

Downstream consumers of `bh_toroidal_topology` and `bh_toroidal_structural` per `grep -rn`:

1. `Tour/GuidedTour/BookV.lean:168, 178, 195` — guided-tour exposition only. **Unaffected** by V.T-LRD-1.
2. `BookV/Cosmology/HeavySeedBirth.lean:58, 725, 768` — V.T-LRD-1 itself. Self-consistent.
3. `BookV/Cosmology/BHBipolarFusion.lean` — imports `BHBirthTopology` but `grep` finds no `J_max`, `JMax`, `jmax` consumers. Bipolar-fusion module reuses V.T110's $T^2$-horizon structural property but does not consume the angular-momentum bound. **Unaffected.**

**Net: propagation surface is empty downstream of HeavySeedBirth.lean.** V.T-LRD-1 introduces a structural lemma that lives self-contained within its own module. **Trust budget impact zero**, no other module needs updating.

---

## 4. Companion-note N-series cross-checks

### N9 (inflation: $r = \iota_\tau^4 \approx 0.014$) and N10 (inflation: $n_s = 1 - 2/57 \approx 0.965$)

V.T-LRD-1 operates at $z \in [8, 15]$ via the atomic-cooling halo abundance, which depends on the *small-scale* primordial $P(k)$ at $k \sim 0.1$-$1\,\mathrm{Mpc}^{-1}$. $n_s$ tilts $P(k)$ at small scales: $\Delta n_s \sim 0.005$ shifts $P(k = 1\,\mathrm{Mpc}^{-1})$ by $\sim 5\%$, hence the high-$z$ atomic-cooling halo abundance by $\sim 30\%$ at the high-mass tail. However, the *spectrum* of LRD-progenitor halos itself does **not** independently test inflationary $n_s$ informatively: the LRD-progenitor halo abundance has a $\sim 1$ dex prior envelope per v2.1 §7 Gap 3, much larger than the $n_s$-tilt induced shift. $r$ does not enter at all (tensors don't affect halo abundance).

**Net: minor cross-coupling, not testable. No N15 sub-entry needs to reference N9/N10.**

### N11 (inflation: $A_s$ consistency)

See ⚠₁₀ above. v2.2 paper should add a one-sentence cross-reference.

### N12 (kSZ: force-law index $n = 2$ on cluster–cluster scales)

No direct cross-coupling: V.T-LRD-1 operates at sub-galactic scales (LRD half-light radii $\lesssim 100$ pc, host-halo virial radii $\sim$ kpc), well below the 30-230 Mpc cluster–cluster regime where $n = 2$ is tested.

**Green.**

### N13/N14 (kSZ: pairwise-kSZ amplitude consistency / 5-cluster $M_{\rm eff}/M_{\rm pt} = 6.65$)

See ⚠₉ above. Cross-reference recommended.

### Critical cross-check: signature 5 / V.T204 / BTFR √ι_τ deficit

V.T-LRD-1's signature 5 is the high-$z$ side ($z = 10$-$13$) of V.T204; the kSZ note's BTFR √ι_τ deficit (ksz §17.4 line 1574) is the $z = 0$ side. The v2.1 §7 Gap 5 already documents this. **Verification:** the documentation is **sufficient as written**, but the V.T239 axis (⚠₃) is missing — recommended Gap 5 extension to three-way coupling.

### N15 slot confirmation

N15 is the correct next slot. N9-N11 (inflation), N12-N14 (kSZ), N15 (LRD). **Confirmed safe.** Wave R7 split N15 into A-D sub-entries matching V.T-LRD-1's four sub-theorems (4 `pred_lrd_*` instances landed in `FalsificationPack.lean`).

---

## 5. v2.2 LRD paper concrete edits (recommended)

Based on the audit, the v2.2 LRD paper should incorporate:

1. **§3.3 (derivation chain)**: add explicit citation of derivation note v2 §3 step 2 for the $J_{\max}^{T^2} = \iota_\tau\sqrt{\kappa_D}\,GM^2/c$ bound, with honest disclaimer: "this bound is a structural extension of V.T110 not yet promoted to a separate registry entry; see V.D-LRD-1d in `HeavySeedBirth.lean`." (Cell ✗₄.)

2. **§5 (sharp transition / Hossenfelder ask)**: relax the headline transition-width claim. Recommend option (c) honest two-mechanism framing with $\le 1.5$ dex composite operational falsifier. The conservative $\le 0.2$ dex Lean witness stays for backward compatibility but is no longer the v2.2 headline. (Cell ✗₇, F's R2 trigger.)

3. **§6.1 N15 framework-coupled handles**: add one-sentence cross-references to:
   - inflation N11 ($A_s$ consistency for $M_h^{\rm ACH,max}$ normalisation; ⚠₁₀);
   - V.T239 (JWST SFE enhancement at $z = 10$ for the high-$z$ V.T204 axis; ⚠₃).

4. **§6.1 N15 signature 3**: declare cross-reference to ksZ N13/N14 (V.T213 saturation mechanism is independently tested at cluster scale; ⚠₉).

5. **§7 Gap 5 (cross-coupling)**: **extend to a three-way coupling**: V.T204 → {LRD signature 5 high-z, BTFR √ι_τ deficit z=0, V.T239 JWST SFE enhancement z=10}. Current Gap 5 only covers the first two; ⚠₃.

6. **§7 add new Gap 6** (recommended): "V.T-LRD-1 introduces structural lemmas ($J_{\max}^{T^2}$ via V.D-LRD-1d, unit Jacobian via the C interior shape) that strengthen V.T110 but are not yet separate registry entries. Promotion to V.T-NEW-5 itemised in next-wave roadmap." (Cells ✗₄ + ⚠₆.)

7. **App. B (Wave 43 specification)**: update to reflect actual specialist outputs: derivation note v2 §5 honestly records the Specialist A vs C disagreement; Wave 43 specification should not promise $\le 0.2$ dex sharp transition without the Macciò-2007 caveat (which Specialist F demonstrated cannot save the headline anyway).

---

## 6. Action items for D (FalsificationPack)

**Wave R7 LANDED**: 4 `TestablePrediction` instances added to `FalsificationPack.lean` (lines 172-254). All cross-coupling references included in the description fields per J's specs:

- `pred_lrd_lower_cutoff` (Q4): describes V.T108 BBN H-cooling + V.T88 mass gap distinction cross-coupling. `currently_testable := false`.
- `pred_lrd_upper_cutoff` (Q5): describes E + G converged cross-validation; inflation N11 cross-coupling; new structural lemma flagged. `currently_testable := true`.
- `pred_lrd_flat_shape` (Q6): describes G's coherence projection grounding; V.T110 extension. `currently_testable := true`.
- `pred_lrd_sharp_transition` (Q7): describes F's reconciliation, R2 trigger, pending v2.2 paper revision. `currently_testable := false` — correctly flagged not-testable until physics resolution.

`falsification_package` updated from 10 to 14 predictions. Build verified (1082 lake jobs, exit 0).

---

**End of cross-coupling matrix. All Yellow and Red cells have documented resolution paths in derivation note v2 or are flagged for v2.2 paper edits / V.T-NEW-5 future wave.**
