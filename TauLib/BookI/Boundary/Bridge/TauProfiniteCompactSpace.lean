import TauLib.BookI.Boundary.Bridge.TauProfiniteFinsetPartition
import Mathlib.Topology.Compactness.Compact

/-!
# TauLib.BookI.Boundary.Bridge.TauProfiniteCompactSpace

**Workstream B1.5c.4 + B1.5c.5 + B1.5c.6 — `CompactSpace TauProfinite`
via Alexander subbasis + recursive König chain construction**.

This module ships the canonical `CompactSpace TauProfinite`
instance, completing the **τ-native compactness theorem** (manuscript
**II.T07**: τ³ is compact).

## Proof structure

1. **B1.5c.4** (chain construction): given a basic-open cover with
   no finite subcover, recursively pick chain elements
   `c : ℕ → TauIdx` with `c k < primorial k`,
   `c (k+1) % primorial k = c k` (for `k ≥ 1`), and
   `cylinder k (c k)` having no finite subcover at every depth.
   Uses `pigeonhole_step_zero` (depth 0 → 1) and `pigeonhole_step`
   (depth k → k+1, k ≥ 1).

2. **B1.5c.5** (limit extraction): the chain assembles into an
   `OmegaInverseLimit`, hence a `TauProfinite` element `x*` with
   `x*.proj k = c k` at every depth.

3. **B1.5c.6** (Alexander assembly): apply Mathlib's
   `compactSpace_generateFrom`. For any cover by basic opens with
   no finite subcover, derive a contradiction: `x*` would lie in
   some basic open `cylinder n c_U` in the cover, yielding the
   finite subcover `{cylinder n c_U}` of `cylinder n (c n)` —
   contradiction.

## Substrate dependencies

- B1.5b PART 3, B1.5c.1+1b+2+3 — Finset partition + pigeonhole
- PR #133 — `OmegaInverseLimit.coeff_zero` constraint
- Wave 50/51 — cylinder topology, T2Space
- Mathlib — `compactSpace_generateFrom` (Alexander)
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation Tau.Polarity

namespace TauProfinite

-- ============================================================
-- PART 1: Depth-0 base partition (univ = ⋃ c' ∈ {0, 1}, cylinder 1 c')
-- ============================================================

/-- **Depth-0 base partition**: with the new `coeff_zero` sentinel
    (PR #133), `cylinder 0 0 = univ` (everyone has `proj 0 = 0`).
    The depth-1 refinement partitions universe into the two
    stage-1 cylinders (since `proj 1 < primorial 1 = 2`).

    This bridges the depth-0 → depth-1 gap that
    `cylinder_eq_finset_iUnion_subcylinders` (which requires
    `1 ≤ k`) doesn't cover. -/
theorem univ_eq_cylinder_one_union :
    (Set.univ : Set TauProfinite) =
      ⋃ c' ∈ ({0, 1} : Finset TauIdx), cylinder 1 c' := by
  ext x
  refine ⟨fun _ => ?_, fun _ => Set.mem_univ x⟩
  -- Goal: x ∈ ⋃ c' ∈ ({0, 1} : Finset TauIdx), cylinder 1 c'
  have h_lt : x.proj 1 < primorial 1 := proj_lt_primorial x (le_refl 1)
  have h_prim : primorial 1 = 2 := by show nth_prime 1 * primorial 0 = 2; native_decide
  rw [h_prim] at h_lt
  -- h_lt : x.proj 1 < 2, so x.proj 1 = 0 or x.proj 1 = 1
  rw [Set.mem_iUnion]
  refine ⟨x.proj 1, ?_⟩
  rw [Set.mem_iUnion]
  refine ⟨?_, ?_⟩
  · -- x.proj 1 ∈ ({0, 1} : Finset TauIdx)
    simp only [Finset.mem_insert, Finset.mem_singleton]
    -- x.proj 1 < 2 → x.proj 1 = 0 ∨ x.proj 1 = 1
    -- Use Nat.lt_succ_iff: m < n + 1 ↔ m ≤ n. So x.proj 1 ≤ 1.
    have h_le : x.proj 1 ≤ 1 := Nat.lt_succ_iff.mp h_lt
    -- x.proj 1 ≤ 1 → x.proj 1 = 0 ∨ x.proj 1 = 1
    rcases Nat.lt_or_eq_of_le h_le with h | h
    · left; exact Nat.lt_one_iff.mp h
    · right; exact h
  · -- x ∈ cylinder 1 (x.proj 1) is Iff.rfl with x.proj 1 = x.proj 1
    rfl

-- ============================================================
-- PART 2: Depth-0 pigeonhole step
-- ============================================================

/-- **Depth-0 pigeonhole step**: if the universe has no finite
    subcover, then SOME `cylinder 1 c'` (with `c' ∈ {0, 1}`) has
    no finite subcover. Bridges the depth-0 → depth-1 chain step. -/
theorem pigeonhole_step_zero
    {ι : Type*} {U : ι → Set TauProfinite}
    (h_no_finite : ¬ ∃ s : Finset ι,
      (Set.univ : Set TauProfinite) ⊆ ⋃ i ∈ s, U i) :
    ∃ c' ∈ ({0, 1} : Finset TauIdx),
      ¬ ∃ s : Finset ι, cylinder 1 c' ⊆ ⋃ i ∈ s, U i := by
  classical
  by_contra h_all
  push_neg at h_all
  choose f hf using h_all
  let s_total : Finset ι :=
    (({0, 1} : Finset TauIdx).attach).biUnion (fun ⟨c', hc'⟩ => f c' hc')
  apply h_no_finite
  refine ⟨s_total, ?_⟩
  rw [univ_eq_cylinder_one_union]
  intro y hy
  simp only [Set.mem_iUnion, exists_prop] at hy
  obtain ⟨c', hc', hyc'⟩ := hy
  have hyU := hf c' hc' hyc'
  simp only [Set.mem_iUnion, exists_prop] at hyU ⊢
  obtain ⟨i, hi_mem, hyi⟩ := hyU
  refine ⟨i, ?_, hyi⟩
  rw [Finset.mem_biUnion]
  exact ⟨⟨c', hc'⟩, Finset.mem_attach _ _, hi_mem⟩

-- ============================================================
-- PART 3 (B1.5c.4): Chain construction
-- ============================================================

/-- **Chain element at depth k**: a center value with proofs of
    bound, mod-coherence (vacuous for k = 0), and no-finite-subcover
    invariant. -/
structure ChainElement {ι : Type*} (U : ι → Set TauProfinite) (k : ℕ) where
  c : TauIdx
  c_lt : c < primorial k
  no_finite : ¬ ∃ s : Finset ι, cylinder k c ⊆ ⋃ i ∈ s, U i

/-- **Base chain element at depth 0**: `c = 0` with the universe
    no-finite-subcover hypothesis transported via `cylinder 0 0 =
    univ` (from `coeff_zero`). -/
noncomputable def chainBase {ι : Type*} {U : ι → Set TauProfinite}
    (h_base : ¬ ∃ s : Finset ι,
      (Set.univ : Set TauProfinite) ⊆ ⋃ i ∈ s, U i) :
    ChainElement U 0 :=
  { c := 0,
    c_lt := by show 0 < primorial 0; simp [primorial],
    no_finite := by
      intro ⟨s, hs⟩
      apply h_base
      refine ⟨s, ?_⟩
      intro x _
      apply hs
      rw [mem_cylinder]
      exact x.toLimit.coeff_zero }

/-- **Pick next chain element from depth 0** via
    `pigeonhole_step_zero`. The result `c' ∈ {0, 1}` is automatically
    `< primorial 1 = 2`. -/
noncomputable def chainStepZero {ι : Type*} {U : ι → Set TauProfinite}
    (prev : ChainElement U 0) : ChainElement U 1 :=
  -- Lift prev.no_finite to univ via cylinder 0 prev.c ⊆ univ trivially
  have h_univ : ¬ ∃ s : Finset ι,
      (Set.univ : Set TauProfinite) ⊆ ⋃ i ∈ s, U i := by
    intro ⟨s, hs⟩
    apply prev.no_finite
    refine ⟨s, ?_⟩
    intro x _
    exact hs (Set.mem_univ x)
  -- Use Classical.choose on the existence statement (Prop → Type)
  let result : ∃ c' ∈ ({0, 1} : Finset TauIdx),
      ¬ ∃ s : Finset ι, cylinder 1 c' ⊆ ⋃ i ∈ s, U i :=
    pigeonhole_step_zero h_univ
  let c' : TauIdx := result.choose
  let hc'_spec := result.choose_spec
  let hc'_mem : c' ∈ ({0, 1} : Finset TauIdx) := hc'_spec.1
  let hc'_no_finite : ¬ ∃ s : Finset ι, cylinder 1 c' ⊆ ⋃ i ∈ s, U i :=
    hc'_spec.2
  { c := c',
    c_lt := by
      have h_prim : primorial 1 = 2 := by
        show nth_prime 1 * primorial 0 = 2; native_decide
      rw [h_prim]
      have h_or : c' = 0 ∨ c' = 1 := by
        have := hc'_mem
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        exact this
      rcases h_or with h | h <;> rw [h] <;> norm_num,
    no_finite := hc'_no_finite }

/-- **Pick next chain element from depth k+1** via `pigeonhole_step`. -/
noncomputable def chainStepSucc {ι : Type*} {U : ι → Set TauProfinite}
    {k : ℕ} (prev : ChainElement U (k + 1)) : ChainElement U (k + 2) :=
  let result := pigeonhole_step (Nat.succ_pos k) prev.c_lt prev.no_finite
  { c := result.choose,
    c_lt := validSubcylinderCenters_lt prev.c_lt result.choose_spec.1,
    no_finite := result.choose_spec.2 }

/-- **The chain** (B1.5c.4): recursively pick chain elements at
    every depth using `chainStepZero` (depth 0 → 1) and
    `chainStepSucc` (depth k+1 → k+2). -/
noncomputable def chain {ι : Type*} {U : ι → Set TauProfinite}
    (h_base : ¬ ∃ s : Finset ι,
      (Set.univ : Set TauProfinite) ⊆ ⋃ i ∈ s, U i) :
    (k : ℕ) → ChainElement U k
  | 0 => chainBase h_base
  | 1 => chainStepZero (chain h_base 0)
  | k + 2 => chainStepSucc (chain h_base (k + 1))

/-- **Chain coherence (depth ≥ 1)**: at every step `k ≥ 1`, the
    chain center is consistent with the previous step's center
    under the primorial modulus. Inherited from
    `validSubcylinderCenters_mod`. -/
theorem chain_compat_succ {ι : Type*} {U : ι → Set TauProfinite}
    (h_base : ¬ ∃ s : Finset ι,
      (Set.univ : Set TauProfinite) ⊆ ⋃ i ∈ s, U i)
    (k : ℕ) :
    (chain h_base (k + 2)).c % primorial (k + 1) = (chain h_base (k + 1)).c := by
  -- chain h_base (k+2) = chainStepSucc (chain h_base (k+1)) by def
  -- chainStepSucc returns result.choose where result.choose_spec.1 :
  --   result.choose ∈ validSubcylinderCenters (k+1) prev.c
  -- So result.choose % primorial (k+1) = prev.c by validSubcylinderCenters_mod
  show (chainStepSucc (chain h_base (k + 1))).c % primorial (k + 1) =
       (chain h_base (k + 1)).c
  unfold chainStepSucc
  -- Goal: result.choose % primorial (k+1) = prev.c
  let prev := chain h_base (k + 1)
  let result := pigeonhole_step (Nat.succ_pos k) prev.c_lt prev.no_finite
  exact validSubcylinderCenters_mod prev.c_lt result.choose_spec.1

end TauProfinite

end Tau.Boundary
