import TauLib.BookI.Boundary.Bridge.TauProfiniteSeparation
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Bases
import Mathlib.Tactic.Linarith

/-!
# TauLib.BookI.Boundary.Bridge.TauProfiniteCompactness

**Workstream B1.5a — Substrate for the τ-native compactness proof
of TauProfinite (Remark `[II.R01]`)**.

This module ships the **substrate scaffolding** that the τ-native
König-like pigeonhole proof of `CompactSpace TauProfinite` will
build on. The full instance landing is the B1.5b follow-up wave.

Per the binding spec dossier
[`atlas/audits/taulib/2026-05-05-canonical-compactness-spec.md`](https://github.com/Panta-Rhei-Research/atlas/blob/main/audits/taulib/2026-05-05-canonical-compactness-spec.md)
(Part 5 Lean target API), the full B1.5 deliverable is the
`CompactSpace TauProfinite` instance proven via the τ-native
pigeonhole proof from Remark `[II.R01]`. That full proof requires
a recursive `Classical.choose` chain of non-coverable subcylinders
plus tower-coherence + limit-point extraction — substantial Lean
work that warrants its own focused wave.

This first slice (B1.5a) lands the **named substrate**:

1. `FinitelyCoverable` predicate — the proof's central
   contradiction lever.
2. The full-space iUnion-of-cylinders lemma — the basis cover the
   pigeonhole works on.
3. Two helper lemmas about `FinitelyCoverable` that the pigeonhole
   chain construction will use directly.

No `sorry`, no incomplete instance — all definitions and lemmas
are fully proven. The headline `CompactSpace TauProfinite`
instance lands in **B1.5b**, anchored to this substrate.

## Mathematical content

Manuscript Remark `[II.R01]` (`book-02/part03/ch13-stone-space.tex`
ll. 159-213) — the τ-native König-like proof:

1. Refine any open cover to a cover `V` by cylinders.
2. Suppose `V` has no finite subcover. Derive a contradiction.
3. **Stage 1**: τ³ partitions into finitely many stage-1 cylinders.
   By pigeonhole, at least one cannot be finitely covered.
4. **Stage k inductive**: refine a non-coverable stage-(k-1)
   cylinder; pigeonhole gives a non-coverable stage-k subcylinder.
5. The chain `(r_k)_{k≥1}` is tower-coherent and defines a unique
   limit point `x* ∈ τ³` via `OmegaInverseLimit.mk`.
6. Some basis cylinder of the cover contains `x*`, contradicting
   the non-coverable assumption at that depth.

This module covers the framework lemmas (`FinitelyCoverable` +
`univ_subset_iUnion_cylinder`) needed for Steps 1-2; B1.5b will
add the chain construction (Steps 3-4), the limit extraction
(Step 5), and the contradiction (Step 6).

## Registry Cross-References

- [I.K2]                 ω fixed-point axiom (architectural cause)
- [II.T07]               Compactness Theorem (statement)
- [II.R01]               τ-native pigeonhole proof (the route taken)
- [II.T42]               Categoricity Theorem step 3 (global warrant)
- [I.T-B1.5a-Substrate]  Substrate for `CompactSpace TauProfinite`
                          (this module)
- [I.T-B1.5b-CompactSpace] `CompactSpace TauProfinite` instance
                          (B1.5b follow-up, queued)

## Cross-references

- B1.4.5 dossier `atlas/audits/taulib/2026-05-05-canonical-compactness-spec.md`
- `BookI/Boundary/Bridge/TauProfiniteTopology.lean` (Wave 50) —
  cylinder topology
- `BookI/Boundary/Bridge/TauProfiniteSeparation.lean` (Wave 51) —
  T2Space + TotallyDisconnectedSpace + `exists_separating_depth`
- `BookI/Boundary/Bridge/TauProfiniteUltrametric.lean` (B1.3.5) —
  canonical δ + d (used by B1.4 metric, not directly here)
- `BookI/Boundary/Bridge/TauProfiniteMetricSpace.lean` (B1.4) —
  canonical metric instance (intentionally not imported here; the
  τ-native compactness route is independent of the metric route per
  dossier Part 6 anti-spec clause 6.5)
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

namespace TauProfinite

-- ============================================================
-- PART 1: THE FinitelyCoverable PREDICATE
-- ============================================================

/-- **`FinitelyCoverable P S`**: the set `S ⊆ TauProfinite` admits a
    finite subcover from the family `P` of subsets.

    The negation `¬ FinitelyCoverable P S` is what the τ-native
    König-like pigeonhole proof propagates through the chain of
    refining cylinders (Step 4 of Remark `[II.R01]`).

    Definitionally identical to the standard "compact iff every cover
    has a finite subcover" formulation, packaged as a named predicate
    so chain-construction lemmas can refer to it cleanly. -/
def FinitelyCoverable (P : Set (Set TauProfinite)) (S : Set TauProfinite) : Prop :=
  ∃ Q : Finset (Set TauProfinite), ↑Q ⊆ P ∧ S ⊆ ⋃₀ ↑Q

/-- The empty set is trivially finitely coverable by any family
    (the empty subcover suffices). -/
theorem finitelyCoverable_empty (P : Set (Set TauProfinite)) :
    FinitelyCoverable P ∅ := by
  refine ⟨∅, ?_, ?_⟩
  · intro x hx; exact absurd hx (Finset.notMem_empty _)
  · intro x hx; exact absurd hx (Set.notMem_empty x)

/-- Subset monotonicity: if `S ⊆ T` and `T` is finitely coverable
    by `P`, so is `S`. -/
theorem finitelyCoverable_of_subset {P : Set (Set TauProfinite)}
    {S T : Set TauProfinite} (h_sub : S ⊆ T)
    (h_fc : FinitelyCoverable P T) : FinitelyCoverable P S := by
  obtain ⟨Q, hQP, hT_sub⟩ := h_fc
  exact ⟨Q, hQP, h_sub.trans hT_sub⟩

/-- Pigeonhole-style helper: if a binary union `S ∪ T` is finitely
    coverable, then both `S` and `T` are (each by the same finite
    subcover, restricted by `subset_of_subset`).

    Used by the contrapositive in Step 3 / 4 of Remark `[II.R01]`:
    if `S ∪ T` is **not** finitely coverable, then at least one of
    `S` or `T` is not finitely coverable. (See
    `not_finitelyCoverable_of_union` below.) -/
theorem finitelyCoverable_of_union_left {P : Set (Set TauProfinite)}
    {S T : Set TauProfinite}
    (h_fc : FinitelyCoverable P (S ∪ T)) :
    FinitelyCoverable P S :=
  finitelyCoverable_of_subset Set.subset_union_left h_fc

theorem finitelyCoverable_of_union_right {P : Set (Set TauProfinite)}
    {S T : Set TauProfinite}
    (h_fc : FinitelyCoverable P (S ∪ T)) :
    FinitelyCoverable P T :=
  finitelyCoverable_of_subset Set.subset_union_right h_fc

/-- **The pigeonhole step (binary version)**: if `S ∪ T` is **not**
    finitely coverable by `P`, then at least one of `S, T` is not
    finitely coverable by `P`.

    This is the contrapositive packaging of the union-coverable
    lemmas — exactly the shape the König-like pigeonhole step
    (Remark `[II.R01]` Step 3-4) needs at each refinement level
    where two adjacent subcylinders are considered. -/
theorem not_finitelyCoverable_of_union
    {P : Set (Set TauProfinite)} {S T : Set TauProfinite}
    (h_not_fc : ¬ FinitelyCoverable P (S ∪ T)) :
    ¬ FinitelyCoverable P S ∨ ¬ FinitelyCoverable P T := by
  by_contra h_both
  push_neg at h_both
  obtain ⟨h_fc_S, h_fc_T⟩ := h_both
  -- Both `S` and `T` are finitely coverable; combine to cover `S ∪ T`.
  -- Finset union over `Set TauProfinite` requires `DecidableEq`,
  -- which is supplied classically (the proof is `noncomputable`).
  classical
  obtain ⟨QS, hQS_sub, hS_sub⟩ := h_fc_S
  obtain ⟨QT, hQT_sub, hT_sub⟩ := h_fc_T
  apply h_not_fc
  refine ⟨QS ∪ QT, ?_, ?_⟩
  · intro x hx
    rw [Finset.coe_union, Set.mem_union] at hx
    rcases hx with hx | hx
    · exact hQS_sub hx
    · exact hQT_sub hx
  · intro x hx
    rcases hx with hxS | hxT
    · obtain ⟨U, hU_in, hxU⟩ := hS_sub hxS
      refine ⟨U, ?_, hxU⟩
      rw [Finset.coe_union, Set.mem_union]
      exact Or.inl hU_in
    · obtain ⟨U, hU_in, hxU⟩ := hT_sub hxT
      refine ⟨U, ?_, hxU⟩
      rw [Finset.coe_union, Set.mem_union]
      exact Or.inr hU_in

-- ============================================================
-- PART 2: SPACE-LEVEL CYLINDER COVER
-- ============================================================

/-- The whole `TauProfinite` space is covered by depth-`k` cylinders
    centered at every point's own depth-`k` projection.

    This is the cover that Step 1 of Remark `[II.R01]` refines from
    the input open cover, and the basis for the pigeonhole partition
    in Steps 3-4.

    Note: this iUnion is over all of `TauProfinite` (uncountably many
    centers), but the **range** of `proj k` is `Fin (primorial k)`
    (a finite set), so the effective cover has only `primorial k`
    distinct cylinders. Reducing to that finite cover is a B1.5b
    refinement step. -/
theorem univ_subset_iUnion_cylinder (k : TauIdx) :
    (Set.univ : Set TauProfinite) ⊆
      ⋃ x : TauProfinite, cylinder k (x.proj k) := by
  intro x _
  refine Set.mem_iUnion.mpr ⟨x, ?_⟩
  rw [mem_cylinder]

/-- Companion: every `TauProfinite` element belongs to its own
    depth-`k` cylinder. -/
@[simp] theorem self_mem_own_cylinder (x : TauProfinite) (k : TauIdx) :
    x ∈ cylinder k (x.proj k) := by
  rw [mem_cylinder]

end TauProfinite

end Tau.Boundary
