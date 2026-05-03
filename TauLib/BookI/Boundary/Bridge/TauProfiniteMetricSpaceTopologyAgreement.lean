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

end TauProfinite

end Tau.Boundary
