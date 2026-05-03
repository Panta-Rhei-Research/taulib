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

/-- **Chain coherence at successive depths (l ≥ 1)**: the
    successor-step coherence
    `(chain (l+1)).c % primorial l = (chain l).c`
    for any `l ≥ 1`. Decomposes via cases on `l`:
    - `l = 0`: vacuous (`hl : 1 ≤ 0` impossible)
    - `l = l' + 1`: directly `chain_compat_succ`. -/
theorem chain_compat_step {ι : Type*} {U : ι → Set TauProfinite}
    (h_base : ¬ ∃ s : Finset ι,
      (Set.univ : Set TauProfinite) ⊆ ⋃ i ∈ s, U i)
    (l : ℕ) (hl : 1 ≤ l) :
    (chain h_base (l + 1)).c % primorial l = (chain h_base l).c := by
  cases l with
  | zero => omega
  | succ l' => exact chain_compat_succ h_base l'

-- ============================================================
-- PART 4 (B1.5c.5): Generalized chain coherence + limit extraction
-- ============================================================

/-- **Generalized chain coherence**: for `1 ≤ k ≤ l`,
    `(chain l).c % primorial k = (chain k).c`. Proof by induction
    on `l ≥ k` using `chain_compat_step` + `Nat.mod_mod_of_dvd`
    (with `primorial k ∣ primorial l`). -/
theorem chain_compat_general {ι : Type*} {U : ι → Set TauProfinite}
    (h_base : ¬ ∃ s : Finset ι,
      (Set.univ : Set TauProfinite) ⊆ ⋃ i ∈ s, U i)
    (k l : ℕ) (hk : 1 ≤ k) (hkl : k ≤ l) :
    (chain h_base l).c % primorial k = (chain h_base k).c := by
  induction l, hkl using Nat.le_induction with
  | base =>
    -- l = k case: (chain k).c % primorial k = (chain k).c
    exact Nat.mod_eq_of_lt (chain h_base k).c_lt
  | succ l hkl ih =>
    -- ih : (chain l).c % primorial k = (chain k).c
    -- chain_compat_step (with hl : 1 ≤ l from hk ≤ hkl):
    --   (chain (l+1)).c % primorial l = (chain l).c
    have hl : 1 ≤ l := le_trans hk hkl
    have h_step : (chain h_base (l + 1)).c % primorial l = (chain h_base l).c :=
      chain_compat_step h_base l hl
    -- primorial k ∣ primorial l (since k ≤ l)
    have h_dvd : primorial k ∣ primorial l := primorial_dvd hkl
    -- Nat.mod_mod_of_dvd : c ∣ b → a % b % c = a % c
    have h_mod : (chain h_base (l + 1)).c % primorial l % primorial k =
                 (chain h_base (l + 1)).c % primorial k :=
      Nat.mod_mod_of_dvd _ h_dvd
    rw [h_step] at h_mod
    -- h_mod : (chain l).c % primorial k = (chain (l+1)).c % primorial k
    rw [← h_mod]
    exact ih

/-- **Chain limit element**: the chain `(c_k)_{k≥0}` assembles into
    an `OmegaInverseLimit`, hence a `TauProfinite` element `x*`
    with `x*.proj k = c_k` for every `k`.

    Uses the generalized chain coherence (`chain_compat_general`)
    for the `compat` field; the `coeff_zero` field follows
    definitionally from `chainBase.c = 0`. -/
noncomputable def chainLimit {ι : Type*} {U : ι → Set TauProfinite}
    (h_base : ¬ ∃ s : Finset ι,
      (Set.univ : Set TauProfinite) ⊆ ⋃ i ∈ s, U i) :
    OmegaInverseLimit where
  coeff := fun k => (chain h_base k).c
  coeff_zero := by show (chain h_base 0).c = 0; rfl
  compat := chain_compat_general h_base

/-- **Chain limit as a TauProfinite element**. -/
noncomputable def chainLimitTauProfinite {ι : Type*} {U : ι → Set TauProfinite}
    (h_base : ¬ ∃ s : Finset ι,
      (Set.univ : Set TauProfinite) ⊆ ⋃ i ∈ s, U i) :
    TauProfinite :=
  { toLimit := chainLimit h_base }

/-- **Verification handle**: the chain limit's projection at depth `k`
    is the chain center at depth `k`. By definition of `chainLimit`. -/
theorem chainLimit_proj {ι : Type*} {U : ι → Set TauProfinite}
    (h_base : ¬ ∃ s : Finset ι,
      (Set.univ : Set TauProfinite) ⊆ ⋃ i ∈ s, U i)
    (k : ℕ) :
    (chainLimitTauProfinite h_base).proj k = (chain h_base k).c := rfl

-- ============================================================
-- PART 5 (B1.5c.6): CompactSpace TauProfinite via Alexander
-- ============================================================

/-- **`CompactSpace TauProfinite`** (B1.5c.6 — manuscript Theorem
    II.T07: τ³ is compact).

    **Proof via Alexander's subbasis theorem
    (`compactSpace_generateFrom`)**: it suffices to show every cover
    by basic-open cylinders admits a finite subcover. Suppose not;
    by König-style chain construction (B1.5c.4) build a coherent
    descending chain of cylinders, each without a finite subcover.
    The chain assembles into a `TauProfinite` limit element `x*`
    (B1.5c.5). Since the cover is exhaustive, `x* ∈ V` for some
    cylinder `V = cylinder n c_U` in the cover. By the chain's
    projection identity, `cylinder n (chain n).c = V`, so `{V}` is
    a finite subcover of `cylinder n (chain n).c` —
    contradicting the chain's invariant. -/
noncomputable instance : CompactSpace TauProfinite := by
  classical
  apply compactSpace_generateFrom (rfl : TauProfinite.instTopologicalSpace =
    TopologicalSpace.generateFrom cylinderBasis)
  intro P hP_sub h_cover
  -- P ⊆ cylinderBasis, ⋃₀ P = univ; want ∃ Q ⊆ P, Q.Finite ∧ ⋃₀ Q = univ
  by_contra h_no_finite_subcover
  push_neg at h_no_finite_subcover
  -- h_no_finite_subcover : ∀ Q ⊆ P, Q.Finite → ⋃₀ Q ≠ univ
  -- Convert P to indexed form: ι := P, U : P → Set TauProfinite, U ⟨V, hV⟩ := V
  let ι := P
  let U : ι → Set TauProfinite := fun p => p.val
  -- Translate "no finite subcover" into our form
  have h_base : ¬ ∃ s : Finset ι,
      (Set.univ : Set TauProfinite) ⊆ ⋃ i ∈ s, U i := by
    intro ⟨s, hs⟩
    -- s : Finset ι (where ι := P), so s.image Subtype.val : Finset (Set TauProfinite) ⊆ P
    apply h_no_finite_subcover (SetLike.coe (s.image Subtype.val))
    · -- (s.image Subtype.val).toSet ⊆ P
      intro V hV
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hV
      obtain ⟨p, _, hp_eq⟩ := hV
      rw [← hp_eq]
      exact p.prop
    · exact (Finset.finite_toSet _)
    · -- ⋃₀ (s.image Subtype.val).toSet = univ
      ext x
      simp only [Set.mem_sUnion, Finset.coe_image, Set.mem_image,
        Finset.mem_coe, Set.mem_univ, iff_true]
      have hx : x ∈ (Set.univ : Set TauProfinite) := Set.mem_univ x
      have hx_in_iUnion := hs hx
      simp only [Set.mem_iUnion, exists_prop] at hx_in_iUnion
      obtain ⟨i, hi_mem, hi⟩ := hx_in_iUnion
      refine ⟨i.val, ⟨i, hi_mem, rfl⟩, hi⟩
  -- Build the König chain
  let chn := chain h_base
  -- Build the limit element
  let xStar := chainLimitTauProfinite h_base
  -- xStar ∈ univ ⊆ ⋃₀ P, so xStar ∈ V for some V ∈ P
  have hxStar_univ : xStar ∈ (Set.univ : Set TauProfinite) := Set.mem_univ _
  rw [← h_cover] at hxStar_univ
  obtain ⟨V, hV_mem_P, hxStar_V⟩ := hxStar_univ
  -- V ∈ P ⊆ cylinderBasis, so V is some cylinder n c_U
  have hV_basis : V ∈ cylinderBasis := hP_sub hV_mem_P
  obtain ⟨n, c_U, hV_eq⟩ := hV_basis
  -- xStar ∈ V = cylinder n c_U, so xStar.proj n = c_U
  rw [hV_eq] at hxStar_V
  rw [mem_cylinder] at hxStar_V
  -- hxStar_V : xStar.proj n = c_U
  -- chainLimit_proj : xStar.proj n = (chn n).c
  have h_proj : xStar.proj n = (chn n).c := chainLimit_proj h_base n
  -- So (chn n).c = c_U, hence cylinder n (chn n).c = V
  have h_chn_eq : (chn n).c = c_U := h_proj.symm.trans hxStar_V
  -- Construct the singleton finite subcover {⟨V, hV_mem_P⟩} of cylinder n (chn n).c
  apply (chn n).no_finite
  refine ⟨{⟨V, hV_mem_P⟩}, ?_⟩
  intro x hx
  rw [mem_cylinder] at hx
  -- hx : x.proj n = (chn n).c = c_U
  rw [h_chn_eq] at hx
  -- hx : x.proj n = c_U
  -- Goal: x ∈ ⋃ i ∈ {⟨V, hV_mem_P⟩}, U i
  simp only [Set.mem_iUnion, exists_prop, Finset.mem_singleton]
  refine ⟨⟨V, hV_mem_P⟩, rfl, ?_⟩
  -- Goal: x ∈ U ⟨V, hV_mem_P⟩ = V = cylinder n c_U
  show x ∈ V
  rw [hV_eq]
  rw [mem_cylinder]
  exact hx

end TauProfinite

end Tau.Boundary
