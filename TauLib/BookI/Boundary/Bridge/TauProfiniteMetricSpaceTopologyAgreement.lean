import TauLib.BookI.Boundary.Bridge.TauProfiniteMetricSpace
import TauLib.BookI.Boundary.Bridge.TauProfiniteCompactness
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# TauLib.BookI.Boundary.Bridge.TauProfiniteMetricSpaceTopologyAgreement

**Workstream B1.4b — substrate for metric/cylinder topology agreement**.

B1.4 (`TauProfiniteMetricSpace.lean`) shipped the canonical
`MetricSpace TauProfinite` instance anchored to
`ultrametricDistance`, but Mathlib's `MetricSpace` typeclass
auto-generates a `TopologicalSpace` from `dist` — distinct from
Wave 50's cylinder topology.

This module ships the **forward direction substrate**:
`Metric.ball x (1/2^k) ⊆ cylinder k (x.proj k)`. Combined with its
counterpart (queued: `cylinder k (x.proj k) ⊆ Metric.ball x ε` for
appropriate ε, complicated by depth-0 considerations), this would
yield the full topology agreement and the
`MetricSpace.replaceTopology`-wrapped instance.

## Mathematical content

**Forward lemma** (`metric_ball_subset_cylinder`): for `k ≥ 1` and
any `x : TauProfinite`,

```
Metric.ball x (1/2^k) ⊆ cylinder k (x.proj k)
```

**Proof**: if `dist x y < 1/2^k`, then by definition of
`ultrametricDistance` as `2^(-firstDisagreementDepth)`, we have
`firstDisagreementDepth y x > k`. By `proj_mod_primorial`
(B1.5b PART 3), this implies `y.proj k = x.proj k`, i.e.
`y ∈ cylinder k (x.proj k)`.

## Why depth 0 complicates the reverse direction

Wave 50's `cylinder` is defined for any depth k, including k = 0.
But `OmegaInverseLimit.compat` only constrains depths `1 ≤ k ≤ l`
— at depth 0, `coeff 0` is unconstrained. The `ultrametricDistance`
metric distinguishes elements that disagree at depth 0
(via `firstDisagreementDepth = 0 → distance = 1`), so the metric
topology distinguishes such elements. The cylinder topology also
does (via `cylinder 0 c`), so the topologies agree, but the
correspondence isn't `cylinder k (x.proj k) = Metric.ball x ε`
directly — it's `cylinder 0 (x.proj 0) ∩ cylinder k (x.proj k) =
Metric.ball x (1/2^k)`. The full equivalence proof is queued as
**B1.4c** along with the `MetricSpace.replaceTopology`
orchestration.

## Registry Cross-References

- [II.D12]               First disagreement depth (B1.3.5)
- [II.D13]               Canonical ultrametric distance (B1.3.5)
- [II.T05]               Ultrametric inequality (B1.4)
- [II.T10]               Topology Uniqueness Theorem (canonicity)
- [I.T-B1.4b-BallSubsetCylinder] `Metric.ball ⊆ cylinder` (this module)

## Cross-references

- B1.4 `TauProfiniteMetricSpace.lean`
- B1.5b PART 3 `TauProfiniteCompactness.lean` — `proj_mod_primorial`
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation Tau.Polarity

namespace TauProfinite

/-- **Metric ball is contained in the cylinder**: for `k ≥ 1` and any
    `x : TauProfinite`, the metric ball of radius `1/2^k` around `x`
    lies inside the depth-`k` cylinder centered at `x.proj k`.

    This is the **forward direction** of the topology agreement
    (every metric ball is open in the cylinder topology). The
    reverse direction requires handling depth-0 agreement
    separately and is queued as **B1.4c**. -/
theorem metric_ball_subset_cylinder {k : ℕ} (_hk : 1 ≤ k) (x : TauProfinite) :
    Metric.ball x ((1 : ℝ) / 2 ^ k) ⊆ cylinder k (x.proj k) := by
  intro y hy
  rw [Metric.mem_ball, dist_eq_ultrametricDistanceReal] at hy
  -- hy : ultrametricDistanceReal y x < 1/2^k
  rw [mem_cylinder]
  -- Goal: y.proj k = x.proj k
  unfold ultrametricDistanceReal ultrametricDistance firstDisagreementDepth at hy
  -- After unfolding, hy uses `firstDisagreementDepth y x`, which has body
  -- `∃ k, y.proj k ≠ x.proj k`
  open Classical in
  by_cases h_diff : ∃ j : ℕ, y.proj j ≠ x.proj j
  · rw [dif_pos h_diff] at hy
    -- hy: ((1 : ℚ) / 2 ^ Nat.find h_diff : ℝ) < 1/2^k
    -- Need: y.proj k = x.proj k
    -- By contradiction: if y.proj k ≠ x.proj k, then Nat.find h_diff ≤ k
    by_contra h_ne
    have h_find_le : Nat.find h_diff ≤ k := Nat.find_le h_ne
    -- Show 1/2^k ≤ 1/2^(Nat.find h_diff), contradicting hy
    have h_pow_le : (2 : ℝ) ^ Nat.find h_diff ≤ 2 ^ k := by
      apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h_find_le
    have h_pow_pos_k : (0 : ℝ) < 2 ^ k := by positivity
    have h_pow_pos_N : (0 : ℝ) < 2 ^ Nat.find h_diff := by positivity
    have h_inv : (1 : ℝ) / 2 ^ k ≤ 1 / 2 ^ Nat.find h_diff := by
      rw [div_le_div_iff₀ h_pow_pos_k h_pow_pos_N]
      linarith
    push_cast at hy
    linarith
  · -- h_diff : ¬ ∃ j, y.proj j ≠ x.proj j
    -- Then y = x by ext_proj, so y.proj k = x.proj k trivially
    push_neg at h_diff
    -- h_diff : ∀ j, y.proj j = x.proj j
    have h_eq : y = x := ext_proj h_diff
    rw [h_eq]

-- ============================================================
-- PART 2 (B1.4c.1): Depth-0 forward inclusion
-- ============================================================

/-- **Depth-0 counterpart of B1.4b**: the metric ball of radius 1
    around `x` lies inside the depth-0 cylinder centered at
    `x.proj 0`.

    This handles the `k = 0` case that B1.4b's
    `metric_ball_subset_cylinder` (which requires `1 ≤ k`) doesn't
    cover. Same proof shape, with `1/2^0 = 1`. -/
theorem metric_ball_one_subset_cylinder_zero (x : TauProfinite) :
    Metric.ball x (1 : ℝ) ⊆ cylinder 0 (x.proj 0) := by
  intro y hy
  rw [Metric.mem_ball, dist_eq_ultrametricDistanceReal] at hy
  rw [mem_cylinder]
  unfold ultrametricDistanceReal ultrametricDistance firstDisagreementDepth at hy
  open Classical in
  by_cases h_diff : ∃ j : ℕ, y.proj j ≠ x.proj j
  · rw [dif_pos h_diff] at hy
    -- hy: ((1 : ℚ) / 2 ^ Nat.find h_diff : ℝ) < 1
    -- Need: y.proj 0 = x.proj 0
    -- By contradiction: if y.proj 0 ≠ x.proj 0, then Nat.find h_diff = 0
    by_contra h_ne
    have h_find_le : Nat.find h_diff ≤ 0 := Nat.find_le h_ne
    have h_find_zero : Nat.find h_diff = 0 := Nat.le_zero.mp h_find_le
    -- distance = 1/2^0 = 1, but hy says < 1, contradiction
    rw [h_find_zero] at hy
    push_cast at hy
    norm_num at hy
  · push_neg at h_diff
    have h_eq : y = x := ext_proj h_diff
    rw [h_eq]

-- ============================================================
-- PART 3 (B1.4c.2): Reverse direction — cylinder intersection ⊆ ball
-- ============================================================

/-- **Reverse direction of topology agreement**: the intersection of
    the depth-0 and depth-k cylinders centered at `x`'s projections
    is contained in the metric ball of radius `1/2^k` around `x`
    (for `k ≥ 1`).

    This is the **converse** to B1.4b's `metric_ball_subset_cylinder`:
    together they establish the topology equivalence at the basic-open
    level. The depth-0 cylinder is needed because
    `OmegaInverseLimit.compat` only constrains depths `1 ≤ k ≤ l` —
    depth 0 needs to be specified separately to force full
    metric-distance closeness. -/
theorem cylinder_inter_subset_ball {k : ℕ} (_hk : 1 ≤ k) (x : TauProfinite) :
    cylinder 0 (x.proj 0) ∩ cylinder k (x.proj k) ⊆
      Metric.ball x ((1 : ℝ) / 2 ^ k) := by
  intro y ⟨hy0, hyk⟩
  rw [mem_cylinder] at hy0 hyk
  -- hy0 : y.proj 0 = x.proj 0
  -- hyk : y.proj k = x.proj k
  rw [Metric.mem_ball, dist_eq_ultrametricDistanceReal]
  unfold ultrametricDistanceReal ultrametricDistance firstDisagreementDepth
  open Classical in
  by_cases h_diff : ∃ j : ℕ, y.proj j ≠ x.proj j
  · rw [dif_pos h_diff]
    -- Goal: ((1 : ℚ) / 2 ^ Nat.find h_diff : ℝ) < 1/2^k
    -- Strategy: show Nat.find h_diff > k, hence 1/2^Nat.find < 1/2^k
    have h_find_gt : Nat.find h_diff > k := by
      by_contra h_le
      push_neg at h_le
      -- h_le : Nat.find h_diff ≤ k
      have h_disag := Nat.find_spec h_diff
      -- h_disag : y.proj (Nat.find h_diff) ≠ x.proj (Nat.find h_diff)
      -- We need to show y.proj (Nat.find h_diff) = x.proj (Nat.find h_diff),
      -- contradicting h_disag.
      -- Case split on whether Nat.find h_diff = 0 or ≥ 1.
      rcases Nat.eq_zero_or_pos (Nat.find h_diff) with h_zero | h_pos
      · rw [h_zero] at h_disag
        exact h_disag hy0
      · -- 1 ≤ Nat.find h_diff ≤ k, use compat
        have h_y_compat : y.proj k % primorial (Nat.find h_diff) = y.proj (Nat.find h_diff) :=
          proj_mod_primorial y h_pos h_le
        have h_x_compat : x.proj k % primorial (Nat.find h_diff) = x.proj (Nat.find h_diff) :=
          proj_mod_primorial x h_pos h_le
        rw [hyk] at h_y_compat
        rw [h_x_compat] at h_y_compat
        exact h_disag h_y_compat.symm
    -- Now derive distance < 1/2^k
    have h_pow_lt : (2 : ℝ) ^ k < 2 ^ Nat.find h_diff := by
      apply pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 2)
      omega
    have h_pow_pos_k : (0 : ℝ) < 2 ^ k := by positivity
    have h_pow_pos_N : (0 : ℝ) < 2 ^ Nat.find h_diff := by positivity
    push_cast
    rw [div_lt_div_iff₀ h_pow_pos_N h_pow_pos_k]
    linarith
  · rw [dif_neg h_diff]
    -- y agrees with x at every depth → distance is 0 → in ball
    push_cast
    positivity

-- ============================================================
-- PART 4 (B1.4c.3a): Forward direction — cylinders are metric-open
-- ============================================================

/-- **Every cylinder is open in the metric topology**.

    This is the **forward direction** of the topology agreement.
    Combined with B1.4b's `metric_ball_subset_cylinder` (and
    B1.4c.1's `metric_ball_one_subset_cylinder_zero`), this lemma
    shows the cylinder topology is contained in the metric topology
    (every cylinder-open is metric-open).

    The reverse direction (every metric ball is open in cylinder
    topology, requiring an Archimedean argument to find `k` with
    `1/2^k < ε`) and the final `MetricSpace.replaceTopology`
    instance application are queued as **B1.4c.3b + B1.4c.4**.

    **Proof**: split on whether `k = 0` or `k ≥ 1`. Use the
    appropriate subset lemma (B1.4b or B1.4c.1) to find a metric
    ball at each point of the cylinder. -/
theorem cylinder_isOpen_in_metric_topology (k c : TauIdx) :
    @IsOpen TauProfinite
      TauProfinite.instMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      (cylinder k c) := by
  rw [@Metric.isOpen_iff TauProfinite TauProfinite.instMetricSpace.toPseudoMetricSpace]
  intro y hy
  rw [mem_cylinder] at hy
  rcases Nat.eq_zero_or_pos k with hk_zero | hk_pos
  · -- k = 0 case: use B1.4c.1 with ε = 1
    refine ⟨1, by norm_num, ?_⟩
    subst hk_zero
    rw [← hy]
    exact metric_ball_one_subset_cylinder_zero y
  · -- k ≥ 1 case: use B1.4b with ε = 1/2^k
    refine ⟨(1 : ℝ) / 2 ^ k, by positivity, ?_⟩
    rw [← hy]
    exact metric_ball_subset_cylinder hk_pos y

end TauProfinite

end Tau.Boundary
