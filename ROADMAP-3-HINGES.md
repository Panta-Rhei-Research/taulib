# TauLib Refactoring Roadmap — Three Hinge Theorems

**Status:** Phases 0 & 4 closed; Phases 2A & 2B partial; **Workstream B1 COMPLETE** ✅. **Workstream B2.alg in progress** — W0 (namespace rename) + W1 (Algebra TauRatQ TauRealQ) + W2 (TauAlgReal real algebraics) + W4 (TauAlgComplex ℚ̄) + W5 (TauAlgComplex bridge to Mathlib's AlgebraicClosure ℚ) all SHIPPED ✅; W3, W3b queued. **Dossier Part 7.2 ACHIEVED for both topology equality AND TauAlgComplex** (dual-path verification handles for both canonical anchoring decisions)
**Version:** v1.0 (2026-04-21); v2.0c status update (2026-05-04) — B2.alg W5 canonical bridge landed
**Authors:** Thorsten Fuchs & Anna-Sophie Fuchs (via collaborative planning session)

> **2026-05-04 update v2.0c (B2.alg W5 — canonical bridge for
> TauAlgComplex landed):**
>
> **W5** (TauLib PR #144 → admin-merge pending) ships the
> **canonical-anchoring verification handle** for `TauAlgComplex`:
>
> ```lean
> noncomputable def tauAlgComplexEquivAlgClosureQ :
>     TauAlgComplex ≃ₐ[TauRatQ] AlgebraicClosure ℚ :=
>   IsAlgClosure.equiv TauRatQ TauAlgComplex (AlgebraicClosure ℚ)
> ```
>
> The τ-native ℚ̄ is provably AlgEquiv to Mathlib's canonical
> AlgebraicClosure ℚ. **Dossier Part 7.2 verification handle
> ACHIEVED for TauAlgComplex** (analogous to B1.4c.5b's II.T10
> cross-check for the topology equality).
>
> ## Cleaner-than-expected discovery
>
> Initially planned manual construction of `Algebra TauRatQ
> (AlgebraicClosure ℚ)` + manual `IsScalarTower TauRatQ ℚ
> (AlgebraicClosure ℚ)`. Discovered Mathlib's
> `AlgebraicClosure.lean` (lines 138 + 141) already auto-derives
> BOTH from any base `Algebra R k`. So we only define `Algebra
> TauRatQ ℚ` (manual via `RingHom.toAlgebra
> ringEquivRat.toRingHom`); Mathlib provides everything else
> automatically. Manual construction would have created instance
> diamonds.
>
> ## Algebraicity transports up the tower
>
> Via `Algebra.IsAlgebraic.trans` (transitivity from
> `Mathlib/RingTheory/Algebraic/Integral.lean:323`):
> 1. `Algebra.IsAlgebraic TauRatQ ℚ` — every q : ℚ algebraic
>    via `isAlgebraic_algebraMap`
> 2. `Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ)` — Mathlib auto
> 3. ⟹ `Algebra.IsAlgebraic TauRatQ (AlgebraicClosure ℚ)`
>
> Then `IsAlgClosure TauRatQ (AlgebraicClosure ℚ)` synthesizes,
> and `IsAlgClosure.equiv` ships the canonical AlgEquiv.
>
> ## Updated Workstream B2.alg structure
>
> | Wave | Status | Content |
> |------|--------|---------|
> | **W0** | **✅ SHIPPED** | Namespace rename (PR #141) |
> | **W1** | **✅ SHIPPED** | `Algebra TauRatQ TauRealQ` (PR #142) |
> | **W2** | **✅ SHIPPED** | `TauAlgReal` IntermediateField (PR #142) |
> | W3 | QUEUED | Bridge `TauAlgReal ≃ algebraicClosure ℚ ℝ` (needs TauRealQ →+* ℝ Cauchy bridge first) |
> | W3b | QUEUED | `LinearOrderedField TauAlgReal` (real-closed transport) |
> | **W4** | **✅ SHIPPED** | `TauAlgComplex` = τ-native ℚ̄ (PR #139) |
> | **W5** | **✅ SHIPPED** | `TauAlgComplex ≃ₐ[TauRatQ] AlgebraicClosure ℚ` bridge (PR #144) |
>
> ## Dossier Part 7.2 verification handles ACHIEVED ✅
>
> Both major canonical-anchoring decisions are now verified via
> dual-path proofs:
>
> 1. **Topology equality** (B1.4c): bidirectional inclusion
>    (B1.4c.3) + II.T10 uniqueness via Continuous.homeoOfEquivCompactToT2
>    (B1.4c.5b)
> 2. **TauAlgComplex = ℚ̄** (B2.alg.W4 + W5): τ-native
>    AlgebraicClosure TauRatQ + canonical bridge to Mathlib's
>    AlgebraicClosure ℚ via IsAlgClosure.equiv

> **2026-05-04 update v2.0b (B2.alg W0 + W1 + W2 landed —
> τ-native real algebraic numbers):**
>
> Three more sub-PRs landed today (after the W4 TauAlgComplex
> opener), substantially extending the algebraic-completion
> bridge:
>
> - **W0** (TauLib PR #141 → `38ad2d9`): namespace rename
>   resolving the pre-existing `Tau.Boundary.toRat_inv` /
>   `Tau.Boundary.TauRat.inv` collision between
>   `TauRatQuotient.lean` and `TauRatInv.lean`. Renamed the
>   (newer) unconditional Quotient versions to `_total` suffix,
>   preserving the manuscript-aligned conditional originals.
>   Single-file rename with internal-reference updates; no
>   external TauLib breakage. **User-authorized refactor**.
>
> - **W1 + W2** (TauLib PR #142 → admin-merge pending):
>   bundled two-wave shipping the τ-native real algebraic numbers:
>   - **W1** (`TauRatRealAlgebraTower.lean`): `Algebra TauRatQ
>     TauRealQ` instance via Mathlib's canonical `algebraMap ℚ
>     TauRealQ` (auto-derived from Field + IsStrictOrderedRing
>     → CharZero via `IsStrictOrderedRing.toCharZero`)
>   - **W2** (`TauAlgReal.lean`): `TauAlgReal := algebraicClosure
>     TauRatQ TauRealQ` as `IntermediateField`. Inherits Field
>     + Algebra + IsAlgebraic from Mathlib's canonical
>     `algebraicClosure F E` construction.
>
> ## Updated Workstream B2.alg structure
>
> | Wave | Status | Content |
> |------|--------|---------|
> | **W0** | **✅ SHIPPED** | Namespace rename (PR #141) |
> | **W1** | **✅ SHIPPED** | `Algebra TauRatQ TauRealQ` (PR #142) |
> | **W2** | **✅ SHIPPED** | `TauAlgReal` IntermediateField (PR #142) |
> | W3 | QUEUED | Bridge `TauAlgReal ≃ algebraicClosure ℚ ℝ` (needs TauRealQ →+* ℝ Cauchy bridge first) |
> | W3b | QUEUED | `LinearOrderedField TauAlgReal` (real-closed transport) |
> | **W4** | **✅ SHIPPED** | `TauAlgComplex` = τ-native ℚ̄ (PR #139) |
> | W5 | QUEUED | Bridge `TauAlgComplex ≃ₐ[TauRatQ] AlgebraicClosure ℚ` (needs IsScalarTower setup) |
>
> ## What this enables
>
> The τ-framework now reaches **two algebraic-completion
> targets**:
> - **`TauAlgComplex`** (W4): the τ-native algebraic complex
>   numbers (ℚ̄), with `Field` + `IsAlgClosed`
> - **`TauAlgReal`** (W2): the τ-native real algebraic numbers,
>   with `Field` (sitting strictly between TauRatQ and TauRealQ)
>
> Both are constructively clean (countable extensions of ℚ),
> sidestepping the Markov-principle wall that blocks full Cauchy
> completion to ℝ.
>
> ## What's queued
>
> - **W3** + **W5** (canonical-anchoring verification handles
>   to Mathlib's `algebraicClosure ℚ ℝ` and `AlgebraicClosure ℚ`):
>   require additional substrate (TauRealQ →+* ℝ Cauchy bridge
>   for W3; IsScalarTower setup for W5). Multi-iteration
>   follow-up work; queued.
> - **B2.alg.5** (LinearOrderedField TauAlgReal via Sturm
>   sequences or transport): substantial; queued.

> **2026-05-04 update v2.0a (Workstream B2.alg OPENED — W4
> TauAlgComplex landed 🚀):**
>
> **The "lap of honor" sprint after B1 completion**: extend the
> τ-framework's bridge layer **into the algebraic numbers**.
>
> **Strategic motivation** (per
> `atlas/insights/2026-04-29-constructive-real-cardinality-boundary.md`):
> the Cauchy completion of ℚ blocks at `LinearOrderedField`
> (Markov-principle wall, Wave 41), but the **algebraic completion**
> is constructively tractable — algebraic numbers are countable
> (countable union of finite root sets per polynomial). The
> algebraic-completion tier sits **strictly between ℚ and ℂ** and
> is the largest constructively-clean scalar extension.
>
> ## What landed today (W4)
>
> - **W4 — `TauAlgComplex`** (TauLib PR #139 → admin-merge pending):
>   the τ-native algebraic complex numbers (ℚ̄), defined as
>   `AlgebraicClosure TauRatQ`. Inherits **`Field`**, **`Algebra
>   TauRatQ`**, **`Algebra.IsAlgebraic`**, and **`IsAlgClosed`**
>   from Mathlib's canonical construction. Four `noncomputable
>   example` declarations serve as machine-checked verification
>   handles. Build cost: 2553 jobs (+786 from FieldTheory.AlgebraicClosure
>   imports), 0 errors, 0 sorry, axioms=3 unchanged.
>
> ## Workstream B2.alg structure (per the approved plan)
>
> | Wave | Status | Content |
> |------|--------|---------|
> | W1 | **BLOCKED** | `Algebra TauRatQ TauRealQ` algebra tower |
> | W2 | **BLOCKED** | `TauAlgReal` (algebraic reals as IntermediateField in TauRealQ) |
> | W3 | **BLOCKED** | Bridge `TauAlgReal ≃ algebraicClosure ℚ ℝ` |
> | **W4** | **✅ SHIPPED** | `TauAlgComplex` = τ-native ℚ̄ |
> | W5 | **QUEUED** | Bridge `TauAlgComplex ≃ₐ[TauRatQ] AlgebraicClosure ℚ` via `IsAlgClosure.equiv` |
>
> ## ⚠️ W1 + W2 + W3 BLOCKED on namespace tech debt
>
> While attempting W1 (the `Algebra TauRatQ TauRealQ` algebra
> tower), discovered a **pre-existing namespace collision**:
> both `TauLib/BookI/Boundary/Bridge/TauRatQuotient.lean` (line
> 186) and `TauLib/BookI/Boundary/TauRatInv.lean` (line 93)
> define `Tau.Boundary.toRat_inv` in the same namespace:
>
> - `TauRatInv.toRat_inv (q : TauRat) (h : q.is_nonzero) : ...`
>   (conditional form, original)
> - `TauRatQuotient.toRat_inv (q : TauRat) : ...` (unconditional
>   form, total — handles 0 → 0 case)
>
> No existing TauLib module imports BOTH (verified via grep).
> W1 is the first module to need the combination (TauRatQuotient
> for `ringEquivRat`, TauRealQuotientField for `Field TauRealQ`
> which transitively pulls TauRatInv via TauRealInv). Hence the
> conflict surfaced for the first time today.
>
> **Resolution path** (queued as a focused tech-debt PR, B2.alg.W0):
> rename `TauRatQuotient.toRat_inv` to `toRat_inv_total` (or
> similar) to disambiguate. Single-file rename + one internal
> reference update at line 254. Once landed, W1 → W2 → W3 unblock
> sequentially.
>
> **Strict-discipline note**: per the discipline of "respect
> pre-existing structures", the rename was NOT applied as part of
> W1 itself; flagged here as a separate sub-PR (B2.alg.W0) for
> user authorization before touching foundational Wave 40 code.
>
> ## What W4 unlocks (without W1+W2+W3)
>
> - `TauAlgComplex` is fully usable as the τ-native algebraic
>   closure of ℚ — a `Field` + `IsAlgClosed` carrier
> - Polynomial roots, splitting fields, number-theoretic
>   constructions over `TauRatQ` can immediately use
>   `TauAlgComplex` as their target
> - The pattern for future algebraic-extension waves (number
>   fields, cyclotomic extensions, Galois groups) is established
>
> ## What W5 will add (queued)
>
> The canonical-anchoring verification handle:
> `TauAlgComplex ≃ₐ[TauRatQ] AlgebraicClosure ℚ`. Constructed via
> `IsAlgClosure.equiv` once we set up `Algebra TauRatQ
> (AlgebraicClosure ℚ)` via the existing `TauRatQ ≃+* ℚ` bridge.
>
> ## Future opportunities (post-B2.alg)
>
> - **B2.alg.5** (real algebraics via algebraicClosure ℚ ℝ):
>   ship `TauAlgReal` directly via Mathlib's
>   `algebraicClosure ℚ ℝ` (sidestepping the W1 algebra-tower
>   block), with the bridge `TauAlgReal ≃ₐ[TauRatQ] algebraicClosure
>   ℚ ℝ` derived from the `TauRatQ ≃+* ℚ` Wave 40 bridge alone
> - Number-theoretic extensions, Galois groups, cyclotomic
>   constructions — all now have `TauAlgComplex` as the natural
>   ambient algebraic-closure target

> **2026-05-04 update v1.0n (Workstream B1 COMPLETE 🎉):**

> **2026-05-04 update v1.0n (Workstream B1 COMPLETE 🎉):**
>
> The entire B1.4c + B1.5c workstream is now landed on origin/main.
> **τ³ is formally compact + canonically anchored with dual-path
> topology equality verification** in Lean 4.
>
> **Final session deliverables**:
>
> - **PR #133** (`fa4f0b0`): structural fix `coeff_zero` sentinel
>   on `OmegaInverseLimit` (root-cause depth-0 fix). Unblocks the
>   compactness workstream.
>
> - **B1.5c.4** (PR #134 → `9bf5861`): König chain construction
>   substrate — `chain : (k : ℕ) → ChainElement U k` via
>   `chainBase` + `chainStepZero` + `chainStepSucc`. Plus
>   `univ_eq_cylinder_one_union`, `pigeonhole_step_zero`,
>   `chain_compat_succ`. ~227 LOC.
>
> - **B1.5c.5 + B1.5c.6** (PR #135 → `f1e27ac`):
>   - `chain_compat_general`: full coherence for `1 ≤ k ≤ l` via
>     `Nat.le_induction` + `Nat.mod_mod_of_dvd` + `primorial_dvd`
>   - `chainLimit`, `chainLimitTauProfinite`: assemble chain into
>     TauProfinite element via `OmegaInverseLimit`
>   - `chainLimit_proj` verification handle
>   - **`instance : CompactSpace TauProfinite`** via Mathlib's
>     `compactSpace_generateFrom` (Alexander's subbasis theorem)
>     applied to `cylinderBasis`
>   - **= manuscript Theorem II.T07 (τ³ is compact)** ✅
>   ~168 LOC.
>
> - **B1.4c.5b** (PR #136 → `25854f7`): II.T10 Topology Uniqueness
>   cross-check — new module `TauProfiniteTopologyUniqueness.lean`:
>   - `id_continuous_cylinder_to_metric`
>   - `idHomeoCylinderToMetric : Homeomorph (X, T_cyl) (X, T_met)`
>     via Mathlib's `Continuous.homeoOfEquivCompactToT2`
>   - `cylinder_topology_eq_metric_topology_via_uniqueness`:
>     **second proof** of topology equality via the manuscript's
>     II.T10 uniqueness path (compact-Hausdorff bijection is a
>     homeomorphism)
>   - **= manuscript Theorem II.T10 (Topology Uniqueness)** ✅
>   ~159 LOC.
>
> **Dossier Part 7.2 verification handle ACHIEVED**: the canonical
> anchoring is provably equivalent across two distinct proof paths
> (bidirectional inclusion B1.4c.3 + uniqueness B1.4c.5b),
> cross-validating the formalization's correctness.
>
> ## Complete B1.4c + B1.5c sub-PR sequence
>
> | Wave | Content | PR |
> |------|---------|-----|
> | B1.4 | MetricSpace TauProfinite (canonical-anchored) | (prior) |
> | B1.4b | metric_ball ⊆ cylinder forward | #119 |
> | B1.4c.1+2 | depth-0 + reverse direction (cyl ∩ cyl ⊆ ball) | #121 |
> | B1.4c.3a | every cylinder is metric-open | #125 |
> | B1.4c.3b+3+4 | reverse + full equality + canonical instance (def) | #126 |
> | B1.4c.5 | instance migration (eliminate diamond) | #128 |
> | Structural | coeff_zero sentinel (depth-0 fix) | #133 |
> | B1.5b PART 3 | proj_mod_primorial substrate | (prior) |
> | B1.5c.1 | validSubcylinderCenters Finset | #123 |
> | B1.5c.1b+2 | upper bound + Finset partition equality | #130 |
> | B1.5c.3 | n-ary pigeonhole step | #131 |
> | B1.5c.4 | König chain construction | #134 |
> | B1.5c.5+6 | limit + **CompactSpace TauProfinite** | #135 |
> | **B1.4c.5b** | **II.T10 uniqueness cross-check** | **#136** |
>
> **Full library**: 1767 jobs, 0 errors, 0 sorry, axioms=3
> (unchanged throughout). Strict-discipline 0-sorry policy upheld
> across the entire workstream.
>
> ## Manuscript theorems formally verified ✅
>
> - **II.T07** (τ³ is compact) — via König chain + Alexander
> - **II.T10** (Topology Uniqueness) — via compact-Hausdorff
>   homeomorphism
> - **II.D13** (canonical ultrametric distance) — anchored in B1.4
> - **II.T05** (ultrametric inequality) — B1.4
> - **II.D12** (first disagreement depth) — B1.3.5
> - **II.D11** (cylinder clopen basis) — Wave 51
> - **II.D10** (stage-k cylinder) — Wave 50
> - **II.P03** (cylinder complement is finite union) — Wave 51
> - **II.P04** (cylinders ARE balls) — formalized via topology
>   equality at three levels: basic-set, full-topology, canonical
>   instance, dual-proof-path

> **2026-05-05 update v1.0m (B1.5c.1b+2+3 landed; depth-0 structural
> issue surfaced):**
> Three more sub-PRs landed on origin/main today, advancing the
> compactness substrate substantially:
>
> - **B1.5c.1b + B1.5c.2** (TauLib PR #130 → `b544e67`):
>   - `validSubcylinderCenters_lt`: the queued upper-bound lemma
>     (working `calc`-chain proof avoiding the prior tactic
>     unification issues)
>   - `cylinder_eq_finset_iUnion_subcylinders`: the **finite,
>     Finset-indexed** partition equality (refactor of B1.5b's
>     subtype-indexed version)
>   - Helper `proj_lt_primorial` (every projection bounded by its
>     stage's primorial, for k ≥ 1)
>
> - **B1.5c.3** (TauLib PR #131 → `d682ce0`):
>   - `pigeonhole_step`: the inductive step — if `cylinder k c` has
>     no finite subcover, then SOME refining `cylinder (k+1) c'`
>     (with `c' ∈ validSubcylinderCenters k c`) also has no finite
>     subcover. Proof via `Classical.choose` + `Finset.biUnion`
>     witness-Finset assembly.
>
> Three substantive sub-PRs landed in this session, in addition to
> B1.4c.5 + ROADMAP v1.0l (PRs #128, #129) earlier.
>
> ## ⚠️ Structural depth-0 issue surfaced
>
> While drafting B1.5c.4 (the recursive `Classical.choose` chain),
> I discovered a structural issue that **blocks B1.5c.4-6 + B1.4c.5b
> from proceeding without a resolution**:
>
> **Problem**: `OmegaInverseLimit.compat` requires `1 ≤ k ≤ l`,
> leaving `coeff 0` UNCONSTRAINED. So `TauProfinite`-as-defined
> contains elements `{x_n | n ∈ ℕ}` where each `x_n.coeff 0 = n`
> and `x_n.coeff k = 0` for `k ≥ 1`. These are pairwise distinct,
> live in different `cylinder 0 n`, and the cover
> `{cylinder 0 n | n ∈ ℕ}` covers `TauProfinite` with **NO finite
> subcover**.
>
> Therefore `TauProfinite` (as currently defined) is **NOT compact**
> in the cylinder topology. The proposed `CompactSpace TauProfinite`
> instance (B1.5c.6) cannot be proven against the current
> definition.
>
> **Manuscript context**: per
> `book-02/part01/ch06-tau3-fibration.tex` Def II.D07, τ³ is the
> fibered product τ¹ ×_f T². Theorem II.T07 asserts τ³ is compact.
> The Lean encoding via `OmegaInverseLimit` is intended to model
> this, but the unconstrained `coeff 0` introduces "spurious"
> non-canonical elements that break compactness. Per the canonical
> embedding `nat_to_inverse_limit`, the IMAGE has `coeff 0 = 0`
> always (since `n % primorial 0 = n % 1 = 0`).
>
> **Resolution paths** (require user decision):
>
> 1. **Constrain `coeff 0`** in the `OmegaInverseLimit` structure
>    (add `coeff_zero : coeff 0 = 0` field). Cleanest mathematically
>    but a breaking change requiring downstream consumer audit.
>
> 2. **Define a sub-structure** `TauProfinite₀ := {x : TauProfinite
>    | x.proj 0 = 0}` and prove `CompactSpace TauProfinite₀`. Then
>    the II.T10 cross-check applies to this canonical subspace.
>
> 3. **Coarsen the cylinder topology** to omit depth-0 cylinders
>    from the basis (use only `{cylinder k c | k ≥ 1}`). Changes
>    the topology — would need to revisit Wave 50/51 + B1.4c
>    proofs.
>
> 4. **Quotient** `TauProfinite` by "differs only in `coeff 0`",
>    making the canonical class the carrier of compactness.
>
> ## What's queued
>
> - **B1.4c.5b**: BLOCKED on B1.5c.6 (CompactSpace), itself blocked
>   on the structural decision above.
> - **B1.5c.4 + B1.5c.5 + B1.5c.6**: BLOCKED on the structural
>   decision. The pigeonhole inductive step (B1.5c.3) is shipped,
>   but the chain construction can't conclude in compactness without
>   resolving the depth-0 issue.
>
> All other prior queued items (B1.4c.5b, etc.) remain queued.

> **2026-05-05 update v1.0l (B1.4c.5 — instance migration landed):**
> One more sub-PR landed on origin/main today, completing the
> MetricSpace instance unification:
>
> - **B1.4c.5** (TauLib PR #128 → `e6782d2`): instance migration
>   eliminating the MetricSpace diamond. Modifies
>   `TauProfiniteMetricSpaceCanonical.lean` (~10-line change):
>
>   ```lean
>   attribute [-instance] TauProfinite.instMetricSpace
>
>   noncomputable instance instMetricSpaceCanonical : MetricSpace TauProfinite :=
>     TauProfinite.instMetricSpace.replaceTopology
>       cylinder_topology_eq_metric_topology
>   ```
>
>   B1.4's `instMetricSpace` (with auto-derived TopologicalSpace) is
>   removed from the global instance pool but remains a callable
>   named `def`. The canonical version (with topology component
>   definitionally equal to Wave 50's cylinder topology via
>   `replaceTopology`) is now the **official** `MetricSpace
>   TauProfinite` instance. **Result**: a single, unambiguous
>   instance with NO diamond.
>
>   **Backward compatibility preserved**: code that explicitly
>   references `TauProfinite.instMetricSpace` (e.g., the
>   `cylinder_topology_eq_metric_topology` theorem statement, the
>   canonical instance's `replaceTopology` call itself) continues
>   to work. Only typeclass resolution is redirected.
>
>   **Verification handle 7.1 preserved**: `dist x y =
>   ultrametricDistanceReal x y` still holds by `rfl` (the
>   `instMetricSpaceCanonical_dist` theorem confirms — unchanged).
>
> **Audit findings** (Phase 1 exploration before migration):
> - Zero direct references to `TauProfinite.instMetricSpace` by name
>   across TauLib code → migration risk LOW.
> - Implicit consumers via `[MetricSpace TauProfinite]` typeclass
>   resolution (Separation, Compactness, etc.) now see the canonical
>   instance — full library builds cleanly (1765 jobs, 0 errors).
>
> **B1.4c.5b status**: explicitly QUEUED (per user decision in
> session). The cross-check proof of
> `cylinder_topology_eq_metric_topology` via Theorem **II.T10**
> uniqueness ("compact-Hausdorff bijection is a homeomorphism")
> remains BLOCKED on `CompactSpace TauProfinite` (queued as B1.5b/c,
> ~300-500 LOC of multi-iteration substrate work). T2Space +
> TotallyDisconnectedSpace already shipped (Wave 51); Mathlib
> homeomorphism lemma `isHomeomorph_iff_continuous_bijective`
> available; only `CompactSpace` is missing. When unblocked,
> B1.4c.5b is ~30 LOC of assembly.

> **2026-05-05 update v1.0k (B1.4c.3a+3b+3+4 — full topology
> equality + canonical instance landed):**
> Two more sub-PRs landed on origin/main today, completing the
> entire B1.4c topology agreement workstream:
>
> - **B1.4c.3a** (TauLib PR #125 → `a494ab9`): forward direction —
>   `cylinder_isOpen_in_metric_topology` (every cylinder is
>   metric-open). ~38 LOC, 1 named theorem. Case-splits on `k = 0`
>   vs `k ≥ 1` and applies B1.4b/B1.4c.1's subset lemma to find a
>   metric ball at each cylinder point.
>
> - **B1.4c.3b + B1.4c.3 + B1.4c.4** (TauLib PR #126 → `c3882cf`):
>   bundled three-wave completion of the topology agreement story:
>
>   - **B1.4c.3b**: reverse direction —
>     `metric_ball_isOpen_in_cylinder_topology` (every metric ball
>     is cylinder-open). Proof uses the **Archimedean property**
>     (`pow_unbounded_of_one_lt`) to find `k ≥ 1` with `1/2^k <
>     ε - dist y x`, then invokes B1.4c.2's `cylinder_inter_subset_ball`
>     plus the triangle inequality. ~60 LOC.
>
>   - **B1.4c.3**: full topology equality —
>     `cylinder_topology_eq_metric_topology` proves
>     `TauProfinite.instTopologicalSpace = ...metric topology`.
>     `le_antisymm` proof using B1.4c.3a + B1.4c.3b directly:
>     - `cylinder ≤ metric` via `Metric.isOpen_iff` + B1.4c.3b
>     - `metric ≤ cylinder` via
>       `TopologicalSpace.le_generateFrom_iff_subset_isOpen`
>       + B1.4c.3a
>     ~50 LOC.
>
>   - **B1.4c.4** (new module
>     `TauProfiniteMetricSpaceCanonical.lean`): canonical
>     MetricSpace via `MetricSpace.replaceTopology` —
>     `instMetricSpaceCanonical` whose auto-generated topology
>     component is **definitionally** equal to Wave 50's cylinder
>     topology. Verification handle preserved:
>     `instMetricSpaceCanonical_dist : dist = ultrametricDistanceReal`
>     by `rfl`. Shipped as `noncomputable def` (not `instance`) to
>     avoid instance-resolution diamond with B1.4's existing
>     `instMetricSpace`. ~121 LOC.
>
> **Manuscript context (Wave R7 research sprint)**: per
> `book-02/part02/ch10-ultrametric-depth.tex` Prop II.P04
> (ll. 302-321), cylinders ARE balls (`C_k(x) = closed-ball(x,
> 2^(-k)) = open-ball(x, 2^(-(k-1)))`). The manuscript treats
> cylinder + metric as ONE topology with two characterizations,
> NOT as two separate topologies proven equal. B1.4c.3 + B1.4c.4
> together make this identification formal at both the topology
> level and the canonical-instance level.
>
> **B1.4c.5 queued**: the actual instance migration — replacing
> B1.4's `instance` declaration with the canonical version.
> Requires an audit of downstream `MetricSpace TauProfinite`
> consumers to avoid breakage. Not blocking; can land whenever
> downstream-audit work is convenient.
>
> **B1.4c.5b queued** (cross-check, post-B1.5c.6): when
> `CompactSpace TauProfinite` lands, ship a SECOND proof of
> topology equality via Theorem **II.T10** (Topology Uniqueness,
> `book-02/part03/ch14-topology-invariant.tex` ll. 135-197) — the
> slick `compact-Hausdorff bijection is homeomorphism` argument.
> This would be a clean cross-check that the canonical anchoring
> is correct (per dossier Part 7 verification handle 7.2:
> provable equivalence).
>
> **B1.5c.1b+ queued (still)**: upper-bound lemma + partition
> equality + n-ary pigeonhole + recursive Classical.choose chain
> + limit extraction + Alexander subbasis assembly. All needed
> for the full `CompactSpace TauProfinite` instance, which is
> needed to unlock Path B (II.T10 uniqueness) for the topology
> equality cross-check.

> **2026-05-05 update (B1.4c.1+2 + B1.5c.1 substrate landed):**
> Two more sub-PRs landed on origin/main today, continuing the
> strict-discipline incremental progression:
>
> - **B1.4c.1+2** (TauLib PR #121 → `eacf615`): completes the
>   bidirectional cylinder-ball correspondence via
>   `metric_ball_one_subset_cylinder_zero` (depth-0 forward) +
>   `cylinder_inter_subset_ball` (the reverse direction:
>   `cylinder 0 (x.proj 0) ∩ cylinder k (x.proj k) ⊆ Metric.ball x (1/2^k)`).
>   ~97 LOC, 2 named theorems.
>
> - **B1.5c.1** (TauLib PR #123 → `3a4c1da`): named anchor for the
>   Finset-indexed cylinder partition —
>   `validSubcylinderCenters k c : Finset TauIdx` enumerates
>   stage-(k+1) refining centers, plus `validSubcylinderCenters_mod`
>   (coherence with parent: `c' % primorial k = c`). ~110 LOC,
>   1 def + 1 named theorem.
>
> **Strict-discipline observations from this session**:
> - The CI `--expected-sorry 0` correctly blocked an exploratory
>   sorry write during B1.5c.1 setup.
> - The companion upper-bound lemma `validSubcylinderCenters_lt`
>   was attempted but hit repeated tactic-elaboration issues
>   (`ring` failed on `Nat`; `linarith`/`trans_le` couldn't unify
>   multiplication terms). Honestly queued as B1.5c.1b.
> - Same pattern: ship what builds 0-sorry; queue the rest.
>
> **B1.4c.3+ queued**: the topology equality lemma
> (`cylinder_topology_eq_metric_topology`) + the
> `MetricSpace.replaceTopology`-wrapped instance. The bidirectional
> correspondence (B1.4b + B1.4c.1+2) is the substrate; lifting to
> topology equality + applying `replaceTopology` is the work.
>
> **B1.5c.1b+ queued**: upper-bound lemma + partition equality +
> n-ary pigeonhole + recursive Classical.choose chain + limit
> extraction + Alexander subbasis assembly. All needed for the
> full `CompactSpace TauProfinite` instance. Substantial focused
> follow-up work, multi-iteration.

> **2026-05-05 update (B1.4b forward topology-agreement substrate
> landed):** TauLib PR #119 (commit `55ef51f`) ships the **forward
> direction** of the metric/cylinder topology agreement in
> `BookI/Boundary/Bridge/TauProfiniteMetricSpaceTopologyAgreement.lean`
> (~110 LOC, 1 named theorem):
> - `metric_ball_subset_cylinder` — for `k ≥ 1` and any `x`,
>   `Metric.ball x (1/2^k) ⊆ cylinder k (x.proj k)`. Proof traces
>   through B1.4's `dist_eq_ultrametricDistanceReal` →
>   B1.3.5's `ultrametricDistance` and `firstDisagreementDepth`,
>   honoring the canonical-anchoring discipline.
>
> **B1.4c queued**: the **reverse direction**
> (`cylinder ⊆ Metric.ball` for appropriate radius) and the full
> `MetricSpace.replaceTopology`-wrapped instance. The reverse is
> more involved because depth 0 needs special handling:
> `OmegaInverseLimit.compat` only constrains depths `1 ≤ k ≤ l`,
> so `cylinder k (x.proj k)` for `k ≥ 1` doesn't force depth-0
> agreement. The actual correspondence is
> `Metric.ball x (1/2^k) = cylinder 0 (x.proj 0) ∩ cylinder k (x.proj k)`,
> not a direct cylinder equality. Documenting in the module
> docstring + queueing as a focused follow-up wave. Not blocking
> any consumer.
>
> **B1.5c queued (still)**: the full `CompactSpace TauProfinite`
> instance via the recursive `Classical.choose` chain + Finset-indexed
> partition + limit-point extraction + Alexander subbasis assembly
> (Steps 3-6 of Remark `[II.R01]`). The Finset-indexed partition
> alone requires substantial number-theoretic substrate work
> (cylinder partition into `nth_prime (k+1)` subcylinders via
> `primorial (k+1) / primorial k = nth_prime (k+1)`), and the
> chain construction requires sigma-typed `Nat.rec` + `Classical.choose`
> orchestration. Estimated total ~300-500 LOC of careful Lean —
> better as a dedicated multi-iteration wave with no time pressure.
> The strict discipline (no temporary sorrys) means we ship what
> builds 0-sorry today and queue the rest honestly.

> **2026-05-05 update (B1.5b PART 3 substrate landed):** TauLib
> module `BookI/Boundary/Bridge/TauProfiniteCompactness.lean` ships
> the **PART 3 substrate** for the τ-native pigeonhole proof:
> - `proj_mod_primorial` — projection compatibility lifted from
>   `OmegaInverseLimit.compat`, the foundation for cylinder nesting
>   and chain coherence.
> - `cylinder_subset_of_proj_mod_eq` — cylinder nesting (depth-(k+1)
>   subcylinder ⊆ depth-k parent when centers are coherent).
> - `cylinder_eq_iUnion_subcylinders` — the cylinder partition
>   (every depth-k cylinder = union of depth-(k+1) subcylinders),
>   currently parameterized by a `TauProfinite`-subtype indexing.
>
> **B1.5c queued**: the full `CompactSpace TauProfinite` instance
> via the recursive chain construction + limit-point extraction +
> Alexander subbasis assembly (Steps 3-6 of Remark `[II.R01]`).
> Implementing this requires:
> 1. Refactoring the partition lemma to a **finite** `Finset`-indexed
>    form (so n-ary pigeonhole has a concrete finite index set).
> 2. The recursive `Classical.choose` chain construction (~100-200
>    LOC).
> 3. The limit-point extraction via `OmegaInverseLimit.mk`.
> 4. The Alexander subbasis orchestration via `isCompact_generateFrom`.
>
> Per the strict discipline, B1.5b ships only the parts that build
> 0-sorry today; the chain construction is a focused B1.5c follow-up.

> **2026-05-05 update (B1.5a substrate scaffolding landed):** TauLib
> module `BookI/Boundary/Bridge/TauProfiniteCompactness.lean` ships
> the named substrate for the τ-native König-like pigeonhole proof
> of `CompactSpace TauProfinite`:
> - `FinitelyCoverable` predicate — the contradiction lever the
>   pigeonhole proof propagates through the chain.
> - `not_finitelyCoverable_of_union` — the binary pigeonhole helper
>   (if `S ∪ T` not finitely coverable, then `S` or `T` is not).
> - `univ_subset_iUnion_cylinder` — the depth-`k` cylinder cover of
>   `Set.univ` that the proof refines.
> - 4 supporting lemmas (`finitelyCoverable_empty`,
>   `finitelyCoverable_of_subset`, two `_of_union_left/right`).
> - All proofs land **0 sorry** (the strict CI invariant correctly
>   rejected an earlier scaffolding attempt that included a
>   placeholder `sorry`).
>
> **B1.5b queued**: the full `CompactSpace TauProfinite` instance
> via the recursive `Classical.choose` chain of non-coverable
> subcylinders + tower-coherence + limit-point extraction
> (Steps 3-6 of Remark `[II.R01]`). Estimated ~200-300 LOC of
> careful Lean — better as a focused dedicated wave than a rushed
> single-PR push. The B1.5a substrate provides all the named anchors
> B1.5b will compose.

> **2026-05-05 update (B1.4.5 canonical compactness spec landed):**
> Atlas dossier
> [`audits/taulib/2026-05-05-canonical-compactness-spec.md`](https://github.com/Panta-Rhei-Research/atlas/blob/main/audits/taulib/2026-05-05-canonical-compactness-spec.md)
> (commit `92cb479`) extracts the canonical compactness construction
> from Book II Part 03 ch13 (`[II.T07]` Compactness Theorem with both
> Tychonoff primary and τ-native pigeonhole proofs from Remark
> `[II.R01]`), Book II Part 09 ch52 (`[II.T42]` Categoricity step 3:
> "K2 forces compactness"), and Book I axiom K2
> (`ρ(ω) = ω`, the architectural anchor for inherent compactness).
> - **B1.5 will follow Path B** (τ-native König-like pigeonhole proof
>   per Remark `[II.R01]`) rather than classical Tychonoff via
>   product embedding. Constructively cleaner (countable dependent
>   choice only) and honors the canonical-anchoring discipline.
> - Headline finding: τ³'s **global compactness is unusual** —
>   most ultrametric spaces (`ℚ_p`, `ℤ_p`) are only locally compact.
>   τ³ is globally compact because (a) the primorial tower (K1)
>   gives finite-at-each-stage structure, and (b) ω (K2) is already
>   in the domain — no external compactification needed. The
>   manuscript calls this **inherent compactness**.
> - The dossier ships 5-clause anti-spec (no Tychonoff-via-product,
>   no external compactification, no boundary readouts, no
>   LocallyCompact fallback, no SequentialCompact shortcut) and
>   6-clause verification handles for the B1.5 PR.

> **2026-05-04 update (B1.4 canonical MetricSpace landed):** TauLib
> PR #112 (commit `a1f0a0d`) ships the canonical
> `MetricSpace TauProfinite` instance in
> `BookI/Boundary/Bridge/TauProfiniteMetricSpace.lean` (~280 LOC, 4
> parts), anchored to `TauProfinite.ultrametricDistance` from
> B1.3.5. The `dist` field is **definitionally equal** to
> `ultrametricDistanceReal` (verifiable by `rfl`), satisfying the
> dossier Part 7.1 verification handle.
> - PART 2 ships the **first formal Lean proof of `[II.T05]`** —
>   the ultrametric inequality
>   `d(x, z) ≤ max(d(x, y), d(y, z))` — the manuscript ch10
>   ll. 246-269 proof formalised via `Nat.find` reasoning on the
>   disagreement set.
> - This is the **strongest possible** Mathlib metric bridge: the
>   metric is forced by `[II.T10]` Topology Uniqueness +
>   `[II.T42]` Categoricity, not just "TauProfinite happens to be
>   metrizable".
> - **B1.4b queued**: formal topology-agreement proof via
>   `MetricSpace.replaceTopology` — the metric topology and Wave 50's
>   cylinder topology coincide as a mathematical fact, but Lean
>   currently sees two independent `TopologicalSpace TauProfinite`
>   instances. B1.4b would unify via `replaceTopology`. Not blocking
>   any consumer.
> - **B1.5 deferred**: `CompactSpace TauProfinite` via Tychonoff +
>   `Profinite` categorical wrap was originally planned to land in
>   parallel with B1.4 but requires substantive work
>   (~200-400 LOC for the closed embedding into
>   `(k : ℕ) → Fin (primorial k)`). Better suited to a dedicated
>   follow-up wave. Not blocking B1.4's MetricSpace consumer.

> **2026-05-04 update (B1.3.5 prep wave):** Canonical topology +
> geometry **anchoring spec** landed for the upcoming B1.4 + B1.5
> waves:
> - New atlas dossier
>   [`audits/taulib/2026-05-04-canonical-topology-geometry-spec.md`](https://github.com/Panta-Rhei-Research/atlas/blob/main/audits/taulib/2026-05-04-canonical-topology-geometry-spec.md)
>   extracts the canonical ultrametric topology (Book II Part 03 +
>   Topology Uniqueness Theorem `[II.T10]`) and the canonical Tarski
>   geometry (Book II Part 04 + Categoricity Theorem `[II.T42]`) from
>   the monograph manuscript sources, and pins them as the binding
>   anchoring spec for B1.4 / B1.5 / future Mathlib geometry bridges.
> - New TauLib module
>   `BookI/Boundary/Bridge/TauProfiniteUltrametric.lean` ships the
>   named anchor functions: `firstDisagreementDepth` (the canonical δ
>   per `[II.D12]`) and `ultrametricDistance` (= 2^(-δ) per `[II.D13]`).
>   B1.4's `MetricSpace TauProfinite` instance must wrap these.
> - Anti-spec (Part 6 of dossier): no boundary scalar readouts
>   (`OrthodoxBridge`), no defect-germ readouts
>   (`DefectInverseSystem`), no Cauchy-completion approximation
>   depths, no discrete metric, no boundary-conformal metrics.
>
> **2026-05-03 update:** Five Workstream B1 waves landed yesterday on
> origin/main:
> - **B1.0a + B1.0b** (Phase 0): callsite audit + asymptotic
>   Cauchy-stability bridge (`TauReal.iota_tau_isCauchy`).
> - **B1.1** (Phase 4): concrete-K numerical certificate at K=50,
>   ε=1/1000 (`TauReal.iota_tau_numerical_certificate`).
> - **B1.2** (Phase 2A partial): hyperfactorization (B,C,D)
>   ∃!-form conditional uniqueness
>   (`hyperfactorization_uniqueness_BCD`). A-uniqueness queued as B1.2c.
> - **B1.3** (Phase 2B partial): prime polarity Prop-level dichotomy +
>   Bool↔Prop bridges (6 theorems in new `LegendreClassifier.lean`).
>   Full Dirichlet density `1/2` queued as B1.3c (requires Mathlib
>   analytic-NT bridge).
>
> See §4 status block + the B1 dossier
> [`atlas/audits/taulib/2026-05-03-foundations-bridges-state-of-the-union.md`](https://github.com/Panta-Rhei-Research/atlas/blob/main/audits/taulib/2026-05-03-foundations-bridges-state-of-the-union.md)
> for the current state and the proposed 9-wave continuation.

---

## 1. Executive Summary

This document plans the porting of the three hinge theorems of the Panta
Rhei τ-framework from their LaTeX proof form (three research papers,
completed April 2026) into Lean 4 / TauLib formal proofs:

1. **Hyperfactorization** (Book I Theorem I.T04)
   — unique tower-atom decomposition
2. **Prime Polarity** (Book I Theorem I.T05)
   — B/C prime split and Dirichlet density $R_B = 1/2$
3. **Master Constant** (Book I Chapter 41, corrected via ERRATUM-004)
   — structural derivation of $\iota_\tau = 2/(\pi + e)$

The overarching goal: **replace fiat definitions with structural ones**.
Most critically, $\iota_\tau$ should cease to be a hardcoded
`Nat/Nat` pair in `BookI/Boundary/Iota.lean` and instead be defined
as the scalar readout of the crossing-point defect $\omega$-germ,
with the numerical identity $\iota_\tau = 2/(\pi+e) \approx 0.341304$
appearing as a theorem.

Estimated total effort: **~3000-4000 Lean lines, ~18 weeks elapsed
(or 6-8 weeks with 3 engineers in parallel)**.

---

## 2. Current State Assessment

### 2.1 TauLib overall state

- **125,771 LOC, 450 modules, 4,332 theorems, 3,542 definitions**
- **Only 3 `sorry`** — all in Book VII (methodological, not structural)
- Books I–VI: **zero `sorry`**
- Build system: Lake; mathlib allowed for **tactics only** (no
  mathematical content)
- `autoImplicit = false` — every variable explicit

### 2.2 Three hinge theorems — current state

All three exist as **computable Boolean verifiers with narrative
docstrings**, but the Prop-level structural theorems the papers
prove are **not yet present**.

| Theorem | Current state | Gap |
|---|---|---|
| **ι_τ master constant** | `iota_tau_numer : Nat := 341304` (fiat, `Iota.lean:41`) | No link to π, e; no formal theorem of the identity |
| **Prime Polarity** | `partition_check : Bool` (L220 Polarity.lean) | No density theorem, no Legendre-symbol classifier |
| **Hyperfactorization** | `hyperfact_check : Bool` (L61 Hyperfact.lean) | No Prop-level `∃!` theorem |

### 2.3 Substrate readiness

The **foundation is sufficient**:

| Substrate | Module | Status |
|---|---|---|
| `SplitComplex` (j² = +1) | `BookI/Polarity/BipolarAlgebra.lean` + `Boundary/SplitComplex.lean` | **Complete** — full ring axioms proved |
| `AlgebraicLemniscate` | `BookI/Polarity/Lemniscate.lean` | **Complete structurally** — σ-involution, canonical construction |
| σ involution / polarity swap | `BookI/Polarity/BipolarAlgebra.lean` | Proved |
| `OmegaTail` (finite-depth ω-germs) | `BookI/Polarity/OmegaGerms.lean` | **Present but computational** — needs `InverseLimit` extension |
| `TauReal` (Cauchy-style reals) | `BookI/Boundary/ConstructiveReals.lean` | **Partial** — see §2.4 below |

### 2.4 TauReal audit finding (critical for Phase 0)

TauReal **exists** but is a simplified "sequence of TauRat
approximations" wrapper (structure with `approx : Nat → TauRat`),
**not a true Cauchy-quotient completion**.

**Present:**
- `TauReal.add, mul, sub, negate, fromTauRat, fromNat`
- Ring axioms (proved as `taureal_*` theorems, bundled in
  `taureal_ring_axioms`)
- `taureal_archimedean_embedding` (injective embedding from ℕ)

**Missing (critical for refactor):**
- `TauReal.inv`, `TauReal.div` — **cannot form `2/(π+e)` today**
- `TauReal.lt, le, abs` (ordering, absolute value)
- `TauReal.lim` / `Cauchy.toReal` / any limit-taking operation
- `TauReal.pi` — does not exist
- `TauReal.exp 1` — does not exist
- No mathlib bridge (by design — TauLib's policy is
  mathlib tactics only, not content)

---

## 3. Strategic Approach

### 3.1 Phase map

| Phase | Scope | Lines | Weeks | Parallel? |
|---|---|---:|---:|:-:|
| **Phase 0** | TauReal extensions + structural ι_τ refactor | ~200 | 2 | No (blocks all) |
| **Phase 1** | Shared foundations (Lemniscate, ω-germs, Read, PolarityLattice, BipolarSwap) | 400-500 | 2 | No |
| **Phase 2A** | Hyperfactorization uniqueness | 500-700 | 3-4 | Yes |
| **Phase 2B** | Prime Polarity (Route B) | 500-600 | 3-4 | Yes |
| **Phase 2C** | iota-tau Steps 1-10 | ~1280 | 6-8 | Yes |
| **Phase 3** | Integration + iota-tau Step 11 (split-complex lift) | 200-300 | 2 | No |
| **Phase 3'** | iota-tau Step 12 (Saturation, Enrich^4=Enrich^3) | 120-400 | 2-4 | Gated |
| **Phase 4** | Numerical evaluation + `#eval` certificate | 50-100 | 0.5 | No |

### 3.2 Dependency analysis

**iota-tau is the capstone paper** (1280 core lines + extensions) but
**does NOT structurally depend** on Hyperfactorization or Prime Polarity
as completed theorems. Cross-paper references are thematic only.
Consequence: Phases 2A, 2B, 2C can run in parallel after Phase 1
foundations.

**Hyperfactorization is the lowest-risk starter** — most pieces already
in `BookI/Coordinates/*.lean` (`no_tie`, `Descent`, `ABCD`); needs only
elevation from Boolean verifier to Prop-level uniqueness via strong
induction.

**Prime Polarity Route B is explicitly independent of Hyperfactorization
I.T04** (paper §1760, "Route B's entire pipeline lives at the
CRT-idempotent level without invoking hyperfactorization"). This
breaks a potential circular dependency.

---

## 4. Phase 0 — Detailed Plan (based on TauReal audit)

> **Status update (2026-05-03, Workstream B1):**
> Phase 0 is **closed in two halves** — see
> [`atlas/audits/taulib/2026-05-03-foundations-bridges-state-of-the-union.md`](https://github.com/Panta-Rhei-Research/atlas/blob/main/audits/taulib/2026-05-03-foundations-bridges-state-of-the-union.md)
> and the B1 atlas dossier.
>
> - **B1.0a** ✓ — Callsite audit + dual-representation pattern documented.
>   Atlas: [`audits/taulib/2026-05-03-iota-tau-callsite-audit.md`](https://github.com/Panta-Rhei-Research/atlas/blob/main/audits/taulib/2026-05-03-iota-tau-callsite-audit.md).
>   TauLib PR #103 (commit `8bd68ce`) — docstring enrichment on
>   `Iota.lean` ↔ `TauRealIotaTau.lean` documenting that the **fiat**
>   form (`iota_tau_numer/iota_tau_denom`, 162 callsites) and the
>   **structural** form (`TauReal.iota_tau := 2/(π+e)`) coexist by
>   design — not a fiat-to-replace migration.
> - **B1.0b** ✓ — Asymptotic bridge theorem
>   `TauReal.iota_tau_isCauchy` (TauLib PR #104) certifying that
>   the structural form is a well-defined element of the TauReal
>   Cauchy completion. Pure composition of existing IsCauchy
>   infrastructure (`IsCauchy_mul`, `IsCauchy_inv`, `IsCauchy_add`,
>   `pi_isCauchy`, `e_isCauchy`, `pi_plus_e_boundedAwayFromZero`).
>   No partial-sum evaluation; no new sorry / axioms.
> - **B1.1** ✓ — Concrete-K numerical certificate
>   `TauReal.iota_tau_numerical_certificate` (TauLib PR following
>   B1.0b). At witness depth `K = 50`, the structural form is within
>   `1/1000` of the fiat decimal — discharged via a single
>   `native_decide` call on the unfolded `TauRat.lt` inequality
>   (50 Leibniz-pair partial-sum terms in `pi_partial 50` + 50
>   factorial terms in `e_partial 50`, composed through `mul`/`inv`/
>   `add` and reduced at the C-compiled byte-code level).
> - **B1.1c** queued (opt-in) — Tighten the certificate to either
>   `|iota_tau.approx K − 341304/1000000| < 1/10⁶` (would need
>   `K ≥ 30 000` for Leibniz pairs, stressing `native_decide`'s
>   reduction budget) or to the dossier's original `1/10¹²` target
>   (unreachable with Leibniz pairs; needs Machin / Wallis /
>   Chudnovsky π series acceleration, ~200–500 LOC of new
>   infrastructure). **Not currently blocking** any downstream
>   consumer — per the B1.0a audit, all 162 `decide`/`native_decide`
>   callsites use the fiat `Nat/Nat` directly. Pick up only when a
>   downstream theorem actually needs the tighter formal bound.
>
> The structural `TauReal.pi`, `TauReal.e`, `TauReal.iota_tau`
> definitions and the defining identity
> `iota_tau · (π+e) ≡ 2` (`TauReal.iota_tau_mul_pi_plus_e_eq_two`)
> were all delivered in Waves 3b/3c/3d/4 of the TauReal infrastructure
> refactor (origin/main, pre-B1.0). The detailed P0.1–P0.4 sub-task
> structure below was the v1.0 strategic plan; the actual landings
> took a slightly different shape (Cauchy machinery instead of
> direct-sequence avoidance), but achieve the same end state.

### 4.1 Goal

Replace `iota_tau : Nat/Nat` fiat definition with a structural
`iota_tau : TauReal` derived from the defect-germ scalar readout, and
prove `iota_tau = 2/(π + e)` as a theorem in TauReal.

### 4.2 Sub-tasks

**P0.1 — Extend ConstructiveReals.lean with pi, e constants** (~45 lines)

Add two standalone definitions of TauReal constants using the
*direct-sequence* idiom (no quotient, no Cauchy machinery):

```lean
-- In BookII/Transcendentals/PiEarned.lean (extend)
-- Leibniz / Archimedes-polygon series (already scaled integer in pi_scaled)
noncomputable def TauReal.pi : TauReal where
  approx n := ⟨⟨pi_scaled n, 0⟩, 10^n, pow_pos_of_two ..⟩

-- In BookII/Transcendentals/EEarned.lean (extend)
noncomputable def TauReal.e : TauReal where
  approx n := ⟨⟨e_factorial_scaled n, 0⟩, fact_denom n, fact_denom_pos ..⟩
```

Estimated: **~20 lines per constant + 5 lines for the denominator
positivity lemmas = ~45 lines total**.

**P0.2 — Add TauReal.two** (~1 line)

```lean
noncomputable def TauReal.two : TauReal := TauReal.fromNat 2
```

**P0.3 — Direct-sequence definition of ι_τ avoiding division** (~10 lines)

Since `TauReal.inv` / `TauReal.div` don't exist yet, define ι_τ as a
direct sequence matching `2 * 10^n / (pi_scaled n + e_scaled n)`:

```lean
-- In BookI/Boundary/Iota.lean (rewrite)
noncomputable def iota_tau : TauReal where
  approx n := ⟨⟨2 * 10^n, 0⟩, pi_scaled n + e_scaled n, pi_plus_e_pos ..⟩
```

This is the **structural** definition: a canonical sequence
earned from the paper's construction. The Nat/Nat fiat becomes a
**derived bound**:

```lean
-- Preserved for backward compatibility (~50 downstream callsites)
def iota_tau_numer : Nat := 341304  -- now: derived bound
def iota_tau_denom : Nat := 1000000
lemma iota_tau_bound :
  TauReal.approx iota_tau 7 = ⟨⟨iota_tau_numer * 10, 0⟩, iota_tau_denom * 10, _⟩ := by
  native_decide
```

**P0.4 — The numerical identity theorem** (~40 lines, the hard step)

Prove the pointwise-TauRat identity linking the ι_τ sequence to
the 2/(π+e) sequence. This requires adding `TauRat.inv` with a
nonzero hypothesis:

```lean
-- New in TauRat.lean (~30 lines)
noncomputable def TauRat.inv (q : TauRat) (h : q.num ≠ 0) : TauRat := ...
-- Prove basic properties: inv_mul_self, inv_nonzero, etc.

-- In Iota.lean
theorem iota_tau_eq_two_over_pi_plus_e_pointwise :
  ∀ n, TauRat.equiv
    (iota_tau.approx n)
    (TauRat.two.mul (TauRat.inv ((TauReal.pi.approx n).add (TauReal.e.approx n)) _)) := by
  intro n
  -- direct algebraic manipulation on TauRat
  ...
```

From this pointwise identity, `iota_tau = 2/(π_τ + e_τ)` at the
TauReal-equiv level follows by `TauReal.equiv` unfolding.

**P0.5 — Reconcile backward compatibility** (~20 lines, audit-driven)

Audit the ~50 downstream callsites of `iota_tau_numer` /
`iota_tau_denom` (identified in `BookIV/MassDerivation/BreathingModes.lean:92`,
`BookV/GravityField/NonlinearEinstein.lean:435`, etc.). Ensure the
new structural definition preserves these as derived bounds so no
callsite proof breaks.

### 4.3 Phase 0 deliverables

At the end of Phase 0:

1. `TauReal.pi` and `TauReal.e` exist as canonical sequences (not via
   Cauchy quotient, but as direct sequence approximants — sufficient
   for current needs).
2. `TauReal.two` is a named constant.
3. `TauRat.inv` with nonzero hypothesis is implemented with basic
   properties.
4. `iota_tau : TauReal` is the structural definition in `Iota.lean`.
5. `iota_tau_eq_two_over_pi_plus_e` is a proven theorem.
6. `iota_tau_numer` / `iota_tau_denom` remain as derived bounds;
   downstream callsites continue to compile.
7. `BookI/Boundary/Iota.lean` docstring updated:
   old: *"iota_tau is NOT defined as a real number (deferred to Book II)"*
   → new: *"iota_tau is the canonical scalar readout of the
   crossing-point defect germ; the numerical identity
   `iota_tau = 2/(π + e)` is Theorem `iota_tau_eq_two_over_pi_plus_e`."*

### 4.4 Phase 0 estimated effort

**~200 Lean lines** (45 + 1 + 10 + 40 + 30 + 20 + proofs), **2 weeks
for one engineer**. No mathlib bridge required. No full Cauchy-quotient
TauReal rewrite required (that's a separate wave if desired).

### 4.5 Phase 0 risks

**R0.1 — TauRat.inv complexity.** If `TauRat` lacks a `num_ne_zero`
witness field, adding `inv` may require restructuring TauRat itself.
Mitigation: spot-check TauRat.lean first (before starting P0.4) and
scope the inv extension.

**R0.2 — pi_scaled / e_factorial_scaled numerical precision.** The
existing Leibniz / factorial series produce *integer approximations*
— need to verify they converge accurately enough for the identity
theorem's pointwise bound to hold. Mitigation: if precision is
insufficient, add improved series (e.g., Machin-like π formula,
faster-converging e series) — estimated +50 lines.

**R0.3 — Downstream callsite breakage.** ~50 files reference
`iota_tau_numer` / `iota_tau_denom`. Mitigation: preserve these as
derived bounds with same Nat values (Phase 0 maintains exact
numerical compatibility).

---

## 5. Phases 1-4 — High-Level Plan

### 5.1 Phase 1 — Shared Foundations (~400-500 lines, 2 weeks)

Build once, reuse three times:

- `BookI/Polarity/Lemniscate.lean` extension — σ-involution on
  $\mathbb{L} = S^1 \vee S^1$ as wedge, crossing point $\omega_\times$
- `BookI/Polarity/OmegaGerms.lean` — full `InverseLimit` type
  (upgrade from finite-depth tuples)
- `BookI/Boundary/Read.lean` (**new**) — `ReadF_n`, `ReadF = invLim`,
  `ReadOrth` functor (using Phase 0's TauReal.pi, TauReal.e)
- `BookI/Polarity/PolarityLattice.lean` — $\Lambda[n]$ with labeled
  classes (B / C / ×)
- `BookI/Polarity/BipolarSwap.lean` — universal lobe-swap API

### 5.2 Phase 2 — Per-paper cores (parallelisable)

Each phase delivers the Prop-level theorems replacing the current
Boolean verifiers.

> **Status update (2026-05-03, Workstream B1):**
> Phase 2A and Phase 2B are **partially closed** via B1.2 + B1.3
> respectively (see header status block + the B1 atlas dossier).
>
> - **B1.2** ✓ — TauLib PR #108 (commit `512bf66`):
>   `hyperfactorization_uniqueness_BCD : ∃! bcd, IsHyperfactWitness x a bcd.1 bcd.2.1 bcd.2.2 v`
>   in `BookI/Coordinates/HyperfactProp.lean`. Closes the
>   **conditional uniqueness** half of paper I.T04 — given
>   `(x, a, v)` is fixed, `(B, C, D)` is uniquely determined.
> - **B1.3** ✓ — TauLib PR #107 (commit `bbef12e`): new
>   `BookI/Polarity/LegendreClassifier.lean` with 6 named theorems
>   (Prop-level dichotomy `prime_polarity_dichotomy` + Bool↔Prop
>   bridges `partition_check_iff` / `b_class_witness_iff` /
>   `c_class_witness_iff` + disjointness + exhaustiveness).
> - **B1.2c** queued — A-uniqueness (proving `A` = `largest_prime_divisor x`)
>   requires interaction with `largest_prime_divisor`, ~150-300 LOC.
>   Not currently blocking any consumer — Wave 6's `IsHyperfactWitness`
>   already pins (A, V) pre-condition for all uses.
> - **B1.3c** queued — full Dirichlet density `1/2` theorem
>   (`b_density_one_half`) requires Mathlib analytic-NT bridge;
>   policy decision pending per dossier §4.5 + §B1.4.

**Phase 2A — Hyperfactorization** (~500-700 lines):
- `theorem hyperfactorization : ∀ x ≥ 2, ∃! abcd, ValidABCD x abcd`
- Uses existing `no_tie` + `Descent` + strong induction
- Deliverable module: `BookI/Coordinates/Hyperfact.lean` upgrade
- **2026-05-03 status**: B1.2 (above) closes the conditional-on-(A,V)
  half; full unconditional `∃! abcd` queued as B1.2c.

**Phase 2B — Prime Polarity Route B** (~500-600 lines):
- New `BookI/Polarity/LegendreClassifier.lean` (mod-8 classifier)
- Dichotomy theorem (Prop-level, replacing `partition_check` Bool)
- Density theorem (partial — density = 1/2 via Dirichlet-in-AP from
  mathlib; density→ι_τ identification deferred to Phase 3)
- **2026-05-03 status**: B1.3 (above) closes the dichotomy +
  Bool↔Prop bridge half; full Dirichlet density queued as B1.3c.

**Phase 2C — iota-tau Steps 1-10** (~1280 lines):
- Crossing-point defect germ construction (Steps 4-5)
- Non-polarity + ω-approach halves (Steps 6a-6b)
- Intersection + universality (Steps 6c-7)
- Coupling identity (Step 9 — depends on Phase 0's TauReal.pi, e)
- Numerical readout (Step 10 — this promotes Phase 0's
  pointwise-TauRat identity to the full scalar-algebra theorem)

### 5.3 Phase 3 — Integration (~200-300 lines, 2 weeks)

- **Step 11**: split-complex lift via Book II ch.47 idempotent
  decomposition — `BookI/IotaTau/SplitComplex.lean` or equivalent
- Cross-paper consistency: Prime Polarity's χ character agrees with
  iota-tau's split-complex χ̃ lift
- Capstone theorem module `BookI/IotaTau/NumericalIdentity.lean`:
  the final `iota_tau_eq_two_over_pi_plus_e` with full chain

### 5.4 Phase 3' — Saturation (gated on Book VII ch.48)

- iota-tau Step 12: `Enrich^4(τ) = Enrich^3(τ)` saturation theorem
- Blocked until Book VII chapter 48 (self-enrichment tower)
  is formalised
- **Recommendation**: ship 3-hinge refactor WITHOUT Phase 3', add
  later when Book VII matures

### 5.5 Phase 4 — Numerical evaluation (~50-100 lines, 0.5 week)

- Interval-arithmetic proof: `|ReadOrth iota_tau - 0.341304238875| < 10^{-12}`
- Optional `#eval` certificate via `native_decide` on bounded
  rational approximation
- Verification against the 2nd-Ed locked constant
  (CLAUDE.md: 0.341304238875... as of 2026-02-18)

---

## 6. Key Open Decisions

### D1. Mathlib content policy

**Current**: Lakefile allows mathlib **tactics only**, not content.

**Question**: Can we import `Mathlib.Data.Real.Basic` + `Real.pi` +
`Real.exp` for the Phase 4 numerical cross-verification? This would
enable a bridge theorem `TauReal.pi ≈ Real.pi` to within
proven error bounds.

**Impact**: If **yes**, Phase 4 is straightforward (~50 lines).
If **no**, Phase 4 requires native TauReal interval arithmetic
(~100 lines, more work but keeps mathlib-free purity).

**Recommendation**: start with **no mathlib content** policy
(preserves TauLib's purity claim), revisit if Phase 4 blockers
emerge.

### D2. Backward compatibility strategy

**Current plan**: preserve `iota_tau_numer` / `iota_tau_denom` as
derived bounds so ~50 downstream callsites compile unchanged.

**Alternative**: rewrite all callsites to use the new structural
`iota_tau : TauReal` directly, removing the Nat/Nat intermediate.

**Recommendation**: derived-bounds strategy (safer, preserves
momentum, downstream can migrate incrementally).

### D3. Sprint parallelisation

**Sequential** (1 engineer): ~18 weeks total
**Parallel** (3 engineers on Phases 2A/2B/2C after Phase 1): ~6-8
weeks total

**Recommendation**: start sequential (build momentum, confirm
patterns work); parallelise Phase 2 once Phase 1 foundations are
proven.

### D4. Phase 3' (Saturation / Enrich^4 = Enrich^3) gating

**Option A**: Ship 3-hinge refactor without Step 12. Add later as
Book VII matures.
**Option B**: Delay release until Book VII ch.48 is formalised
(unknown timeline).

**Recommendation**: **Option A** — the three hinges stand on their
own; Step 12 is a structural bonus, not a prerequisite.

### D5. Cauchy-quotient TauReal upgrade

Current TauReal is a simplified "sequence wrapper" with pointwise-equiv
semantics. A proper Cauchy-quotient construction would be more
mathematically honest but is a separate ~200-300 line wave.

**Recommendation**: **keep simplified TauReal for now** (Phase 0
works with existing semantics); schedule Cauchy-quotient upgrade as
a separate wave after 3-hinge refactor completes.

---

## 7. Progress Tracking

### 7.1 Milestone ledger

| Milestone | Phase | Status | Target date |
|---|---|---|---|
| M0: TauReal audit complete | 0 | ✅ Done (2026-04-21) | — |
| M1: Strategy doc ratified | — | 🟡 In review | 2026-04-21 |
| M2: TauReal.pi, TauReal.e, TauReal.two | 0 | ⬜ Pending | +2 days |
| M3: TauRat.inv + nonzero hypothesis | 0 | ⬜ Pending | +3 days |
| M4: Structural iota_tau + numerical theorem | 0 | ⬜ Pending | +1 week |
| M5: Phase 0 complete (Iota.lean refactor) | 0 | ⬜ Pending | +2 weeks |
| M6: Phase 1 foundations | 1 | ⬜ Pending | +4 weeks |
| M7: First hinge theorem ported (2A recommended) | 2A | ⬜ Pending | +7-8 weeks |
| M8: All three hinges ported | 2A-2C | ⬜ Pending | +14-16 weeks |
| M9: Numerical evaluation certificate | 4 | ⬜ Pending | +16-18 weeks |

### 7.2 Risk register

| ID | Risk | Severity | Mitigation |
|---|---|---|---|
| R0.1 | TauRat.inv complexity | Medium | Audit TauRat before P0.4 |
| R0.2 | pi_scaled / e_scaled precision | Low | Add improved series if needed |
| R0.3 | Callsite breakage | Low | Preserve derived bounds |
| R1.1 | OmegaGerms InverseLimit type refactor | Medium | Prototype in spike branch first |
| R2C.1 | Novel σ-equivariant holomorphic transformer API | High | Spike early, pair with paper author |
| R3'.1 | Book VII ch.48 dependency | High | Gate Phase 3', ship without if needed |

---

## 8. Appendices

### A. Key file paths (repo-relative)

**Upstream papers (LaTeX source, in the Panta Rhei book repo, not TauLib):**
- `papers/iota-tau/main.tex` (v2.9, 33 pages)
- `papers/prime-polarity/main.tex`
- `papers/hyperfactorization/main.tex`

**TauLib primary refactor targets (paths below are relative to TauLib repo root):**
- `TauLib/BookI/Boundary/Iota.lean`
- `TauLib/BookI/Boundary/ConstructiveReals.lean`
- `TauLib/BookI/Polarity/Polarity.lean`
- `TauLib/BookI/Coordinates/Hyperfact.lean`

**TauLib shared infrastructure:**
- `BookI/Polarity/Lemniscate.lean`, `BipolarAlgebra.lean`, `OmegaGerms.lean`, `PolarizedGerms.lean`, `Spectral.lean`
- `BookI/Coordinates/NoTie.lean`, `Descent.lean`, `ABCD.lean`
- `BookI/Boundary/SplitComplex.lean`
- `BookII/Hartogs/BndLift.lean`, `EvolutionOperator.lean`, `MutualDetermination.lean`
- `BookII/CentralTheorem/CentralTheorem.lean`, `ExtensionsOmegaGerms.lean`

### B. Paper cross-references

| Paper | Lean section label | Line range |
|---|---|---|
| iota-tau | `sec:lean-plan` | 2975-3058 |
| prime-polarity | `sec:lean-plan` | 1694-1795 |
| hyperfactorization | `sec:lean-plan` | 1340-1428 |

### C. Historical context

- **2026-02-18**: ι_τ corrected to 0.341304238875... (was 0.341459 in
  1st Ed) — locked in Book II, not yet reflected in Iota.lean
- **2026-04-21 (this session)**: Three hinge papers completed to
  v2.9 / v1 structural rigour; TauLib refactor roadmap drafted

### D. Companion documents

- `RELEASE_NOTES.md` — TauLib release tracking (will be updated
  per phase)
- `ATLAS.md` — registry-to-Lean cross-reference (to be updated as
  hinge theorems are ported)

---

## Change Log

- **v1.0 (2026-04-21)**: Initial strategy document. Based on parallel
  reconnaissance reports covering (a) Lean roadmaps across all three
  papers and (b) TauLib kernel audit including TauReal substrate
  status. Phase 0 plan detailed; Phases 1-4 high-level.

- **v1.1 (2026-04-21)**: Phase 0 expanded into a **full 4-wave TauReal
  infrastructure build** (replaces minimal `direct-sequence avoidance`
  approach). New scope: ~900 lines instead of ~200. Decision: walk the
  hard way and build proper Cauchy semantics, ordering, field
  operations, and standard constants natively in TauLib.

  | Wave | Scope | Lines | Module |
  |---|---|---:|---|
  | 1 | TauRat field & order (`equiv_trans`, `toRat`, `lt/le/abs/inv/div`) | ~250 | `TauRatField.lean` (new) |
  | 2 | TauReal Cauchy semantics + ordering | ~300 | `TauRealCauchy.lean` (new) |
  | 3 | TauReal constants (π, e via Cauchy series) | ~200 | extend `PiEarned.lean`, `EEarned.lean` |
  | 4 | Structural ι_τ + numerical identity | ~150 | refactor `Iota.lean` |

- **v1.2 (2026-04-21)**: **Tactical-constraint audit complete.**
  Discovered that `Mathlib.Tactic.FieldSimp` and `Mathlib.Tactic.Linarith`
  are **NOT in TauLib's effective tactic budget** because their
  discharger sub-modules pull in `Mathlib.Algebra.Field.*`,
  `Mathlib.Algebra.Order.*`, `Mathlib.Algebra.Group.Nat.Defs`,
  `Mathlib.Logic.Basic` — all mathematical content forbidden by lakefile
  policy.  Effective budget: `ring`, `ring_nf`, `linear_combination`,
  `norm_num`, `push_cast`, `omega`, `decide`, `native_decide`, plus
  Lean core types (`Rat`, `Int`, `Nat`) with their built-in operations.

  **Strategy: Option B1 + selective B3.**  Push through with manual
  tactical work, building TauLib-internal helper lemmas opportunistically
  as patterns recur.  Wave 1 split into 4 sub-waves for compile-time
  isolation:

  | Sub-wave | Scope | Lines | Module | Status |
  |---|---|---:|---|---|
  | 1a | `equiv_trans`, `toRat` bridge, homomorphisms, `is_nonzero` | 223 | `TauRatField.lean` | ✅ DELIVERED |
  | 1b | Ordering (`lt`, `le`, transitivity, trichotomy) | ~80 | `TauRatOrder.lean` | next |
  | 1c | Absolute value (`abs` + properties) | ~100 | `TauRatAbs.lean` | pending |
  | 1d | Inverse + division (`inv`, `div` with nonzero hypotheses) | ~150-200 | `TauRatInv.lean` | pending |

  **Revised estimates** (factoring 2-3× tactical-work overhead):
  Wave 1 ~600 lines, Wave 2 ~600 lines, Wave 3 ~250 lines, Wave 4 ~200
  lines.  Total ~1650 lines (was 900).

- **v1.3 (2026-04-21)**: **Wave 1a delivered and compiling.**  223
  lines.  TauRat now has `equiv_trans` (the missing piece in
  NumberTower), `toRat` semantic bridge, full set of homomorphism
  properties (`toRat_add/mul/negate/sub/zero/one`), and `is_nonzero`
  predicate with equiv preservation.  Smoke tests passing.
