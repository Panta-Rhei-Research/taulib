import TauLib.BookI.Boundary.Bridge.TauProfiniteMetricSpaceTopologyAgreement

/-!
# TauLib.BookI.Boundary.Bridge.TauProfiniteMetricSpaceCanonical

**Workstream B1.4c.4 — `MetricSpace.replaceTopology`-wrapped canonical
instance**.

B1.4 (`TauProfiniteMetricSpace.lean`) shipped the canonical
`MetricSpace TauProfinite` instance anchored to
`ultrametricDistance`, but Mathlib's `MetricSpace` typeclass
auto-generates a `TopologicalSpace` from `dist` — distinct from
Wave 50's cylinder topology (`generateFrom cylinderBasis`).

B1.4c.3 (`TauProfiniteMetricSpaceTopologyAgreement.lean` PART 6)
shipped the topology equality proof:

```
cylinder_topology_eq_metric_topology :
  TauProfinite.instTopologicalSpace =
    TauProfinite.instMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
```

This module ships the **canonical wrapping**:
`TauProfinite.instMetricSpaceCanonical`, the
`MetricSpace.replaceTopology`-wrapped MetricSpace whose
auto-generated TopologicalSpace component is **definitionally**
`TauProfinite.instTopologicalSpace` (the Wave 50 cylinder topology).

## Why a `def` (not an `instance`)

We ship `TauProfinite.instMetricSpaceCanonical` as a `noncomputable
def`, not as an `instance`. Reasoning:

1. **Avoid instance diamond**: B1.4's `TauProfinite.instMetricSpace`
   is already a `MetricSpace TauProfinite` instance. Adding a
   second instance would create a diamond Lean would have to
   resolve, with potential downstream breakage.

2. **Migration handle**: downstream consumers can opt into the
   canonical instance explicitly via
   `TauProfinite.instMetricSpaceCanonical`, while existing code
   continues to use B1.4's `TauProfinite.instMetricSpace`
   unchanged.

3. **Future cleanup** (queued as **B1.4c.5**): when downstream
   consumers are audited and updated, B1.4's
   `instance` declaration can be replaced with this canonical
   version, retiring the auto-generated topology entirely.

## Manuscript context (Wave R7 research sprint)

Per `book-02/part02/ch10-ultrametric-depth.tex` Prop II.P04
(ll. 302-321), cylinders ARE balls: the manuscript treats cylinder
+ metric as ONE topology with two characterizations. This canonical
instance makes that identification operationally cohesive in Lean —
the MetricSpace's underlying topology IS the cylinder topology, by
definitional equality (after `replaceTopology`).

## Registry Cross-References

- [II.D12]               First disagreement depth (B1.3.5)
- [II.D13]               Canonical ultrametric distance (B1.3.5)
- [II.T05]               Ultrametric inequality (B1.4)
- [II.T10]               Topology Uniqueness Theorem (canonicity)
- [I.T-B1.4c.4-CanonicalMetricSpace] `instMetricSpaceCanonical`
                                       (this module)

## Cross-references

- B1.4 `TauProfiniteMetricSpace.lean`
- B1.4c.3 `TauProfiniteMetricSpaceTopologyAgreement.lean` —
  `cylinder_topology_eq_metric_topology`
- Atlas dossier
  `atlas/audits/taulib/2026-05-04-canonical-topology-geometry-spec.md`
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

namespace TauProfinite

-- ============================================================
-- B1.4c.5: Instance migration — eliminate the diamond
-- ============================================================
--
-- B1.4's `TauProfinite.instMetricSpace` (in
-- `TauProfiniteMetricSpace.lean`) is the original MetricSpace
-- declaration with an auto-generated TopologicalSpace component
-- distinct from Wave 50's cylinder topology. With the topology
-- equality now formally proven (B1.4c.3), we can eliminate the
-- instance diamond by:
--
-- 1. Removing B1.4's `instMetricSpace` from the global instance
--    pool (it remains a named `noncomputable def`, callable
--    explicitly, but no longer participates in typeclass
--    resolution).
-- 2. Promoting `instMetricSpaceCanonical` (this module) from
--    `noncomputable def` to a real `noncomputable instance`.
--
-- Result: a single, unambiguous `MetricSpace TauProfinite`
-- instance whose underlying `TopologicalSpace` component is
-- definitionally Wave 50's cylinder topology — no diamond.
--
-- Downstream code that explicitly references
-- `TauProfinite.instMetricSpace` (e.g., the
-- `cylinder_topology_eq_metric_topology` theorem statement, this
-- module's `replaceTopology` call, etc.) continues to work
-- because the name is still bound; only typeclass resolution is
-- redirected.

attribute [-instance] TauProfinite.instMetricSpace

/-- **Canonical `MetricSpace TauProfinite`** — the official
    instance, with topology component definitionally equal to
    Wave 50's cylinder topology
    (`TauProfinite.instTopologicalSpace`).

    This is the `MetricSpace.replaceTopology`-wrapped version of
    B1.4's `TauProfinite.instMetricSpace`, applying the
    `cylinder_topology_eq_metric_topology` proof to fuse the two
    a-priori-distinct topologies (Wave 50's cylinder topology vs.
    B1.4's auto-generated metric topology) into ONE canonical
    structure.

    **Definitional equality preserved**: `dist` still equals
    `ultrametricDistanceReal` by `rfl` (B1.4 verification handle 7.1
    preserved), since `replaceTopology` only replaces the topology
    component, not the distance function. See
    `instMetricSpaceCanonical_dist` below.

    **Instance migration (B1.4c.5)**: this is now the **official**
    `MetricSpace TauProfinite` instance. B1.4's
    `TauProfinite.instMetricSpace` was demoted via
    `attribute [-instance]` (above) to eliminate the instance
    diamond. The original `instMetricSpace` remains a named
    `noncomputable def` callable by explicit reference, but no
    longer participates in typeclass resolution. -/
noncomputable instance instMetricSpaceCanonical : MetricSpace TauProfinite :=
  TauProfinite.instMetricSpace.replaceTopology
    cylinder_topology_eq_metric_topology

/-- **Verification handle**: the canonical metric-space's `dist`
    field is still definitionally `ultrametricDistanceReal`,
    preserving B1.4's verification handle (dossier Part 7.1) under
    the `replaceTopology` wrapping. -/
theorem instMetricSpaceCanonical_dist (x y : TauProfinite) :
    instMetricSpaceCanonical.dist x y = ultrametricDistanceReal x y :=
  rfl

end TauProfinite

end Tau.Boundary
