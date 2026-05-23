# G8 Lane A A1.6 Compact Resolvent Proof Map

Status: private operator-theory memo for the selected floor-normalized Ch.23
route.  This note does not claim RH, A2 point-spectrum provenance, A3 actual-xi
membership, or standard-mode equality.

## Goal

The A1.5 reverse-inclusion/maximality route closes selected-carrier
self-adjointness for the Kirchhoff graph Laplacian.  A1.6 must now prove:

```text
selected compact Ch.23 graph
  + selected Kirchhoff Hilbert/domain source
  + maximal self-adjoint graph Laplacian
  + compact operator-domain embedding
  + compact resolvent
  + discrete point-spectrum consequence
  -> G8BookIIILemniscateCompactResolventSource
```

The existing raw `G8BookIIILemniscateCompactResolventSource` still consumes the
older `LemniscateOperatorDomain` surface.  Therefore the selected A1.6 theorem
must be exported through an explicit legacy transport bridge; it is not
silently identified with the raw carrier.

## Proof Stones

1. Selected self-adjoint adapter.
   The closed A1.3-A1.5 route gives the selected graph Laplacian, boundary-form
   cancellation, and maximal Kirchhoff self-adjointness.  This is now surfaced
   by `G8BookIIICh23FloorNormalizedA16SelectedSelfAdjointOperatorSource`.

2. Compact embedding.
   Prove the compact graph Rellich theorem: bounded graph/operator-domain norm
   controls edgewise `H2` data on the two compact lobes, finite lobe compactness
   gives precompactness in `L2`, and the Kirchhoff constraints are closed.  The
   exact source is
   `G8BookIIICh23FloorNormalizedA16RellichCompactEmbeddingSource`.

3. Coercive resolvent regularity.
   Use the safe resolvent point `-1`.  Prove existence of `(H_L + 1)^{-1}`,
   its map from `L2` into the selected operator domain, and a graph-norm bound.
   The exact source is
   `G8BookIIICh23FloorNormalizedA16CoerciveResolventRegularitySource`.

4. Compact resolvent.
   Factor the safe resolvent through the compact operator-domain embedding.
   The exact source is
   `G8BookIIICh23FloorNormalizedA16ResolventCompactnessSource`.

5. Discrete point spectrum.
   Apply the self-adjoint compact-resolvent spectral theorem: finite
   multiplicities, eigenvalue escape to infinity, and no continuous spectral
   residue for the Lane A predicate.  The exact source is
   `G8BookIIICh23FloorNormalizedA16DiscretePointSpectrumSource`.

6. Legacy export.
   Export to `G8BookIIILemniscateCompactResolventSource` only through
   `G8BookIIICh23FloorNormalizedA16LegacySelfAdjointOperatorAdapterSource` and
   `G8BookIIICh23FloorNormalizedA16CompactResolventDiscreteSpectrumAssemblySource`.

## Current Lean Split

The A1.6 implementation intentionally lands source surfaces first:

```text
G8BookIIICh23FloorNormalizedA16SelfAdjointOperatorSourceAdapter
G8BookIIICh23FloorNormalizedA16CompactEmbedding
G8BookIIICh23FloorNormalizedA16RellichCompactEmbeddingRoute
G8BookIIICh23FloorNormalizedA16CompactEmbeddingConstruction
G8BookIIICh23FloorNormalizedA16ResolventCompactness
G8BookIIICh23FloorNormalizedA16ResolventCompactnessConstruction
G8BookIIICh23FloorNormalizedA16DiscretePointSpectrum
G8BookIIICh23FloorNormalizedA16DiscretePointSpectrumConstruction
```

The selected self-adjoint source is theorem-backed from A1.5.  The Rellich
route has now been split and closed on the selected-carrier corridor:
graph-norm `H2` control, finite two-lobe Rellich compactness, closed
Kirchhoff-subspace stability, and compact-embedding assembly are theorem-backed
in `G8BookIIICh23FloorNormalizedA16CompactEmbeddingConstruction`.  This closes
the selected compact-embedding source without using A2, A3, finite `n^2`
diagnostics, or RH-facing downstream modules.

The safe `-1` resolvent regularity and compact-resolvent factorization stones
are now closed on the selected-carrier corridor in
`G8BookIIICh23FloorNormalizedA16ResolventCompactnessConstruction`: the selected
weak coercive shift, resolvent mapping into the selected operator domain,
graph-norm bound, edgewise elliptic regularity, and factorization through the
compact embedding are theorem-backed from the closed A1.1-A1.6 selected route.

The discrete point-spectrum consequence is now closed on the selected-carrier
corridor in
`G8BookIIICh23FloorNormalizedA16DiscretePointSpectrumConstruction`: compact
self-adjoint resolvent spectral-theorem input, finite multiplicities,
eigenvalue escape, no continuous spectral residue, spectral resolution, and
the selected discrete point-spectrum source are theorem-backed from the closed
selected self-adjoint and compact-resolvent route.  This does not assert
standard `n^2` mode equality.  The legacy raw-carrier export remains explicit
if a downstream surface needs the older `LemniscateOperatorDomain` carrier.

## Guardrails

- Do not use finite `n^2` checks to prove compact resolvent or discreteness.
- Do not use A2 point-spectrum reality, A3 actual-xi membership, final RH
  handoffs, accepted coverage, O3, determinant transfer, completion uniqueness,
  or divisor transfer.
- Do not identify the selected floor-normalized carrier with the older raw
  `LemniscateCarrier` without the explicit legacy transport bridge.
- Keep direct Mathlib imports out of downstream G8 bridge modules; add any
  needed compact-operator/spectral imports only through the established
  low-level gateway.
