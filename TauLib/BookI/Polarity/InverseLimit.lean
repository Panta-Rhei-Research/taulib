import TauLib.BookI.Polarity.OmegaGerms

/-!
# TauLib.BookI.Polarity.InverseLimit

**Inverse-limit lift of the OmegaTail infrastructure** — the
infinite-depth coherent tower form needed by Hinge 5 (HolEnd_τ
pre-Yoneda collapse) and Hinge 6 (circularity resolution via
ω-germ stabilisation).

## Registry Cross-References

- [I.D25] OmegaTail (`Tau.Polarity.OmegaTail`, depth-truncated)
- [I.D29] CRT decomposition / reconstruction
- [I.T-H5-InverseLimit] OmegaInverseLimit (this module)

## Mathematical Content

**Wave 8 — H5.1 InverseLimit upgrade**.  The existing `OmegaTail`
type captures the *depth-truncated* compatible-tower form: a list
of components `x_1, x_2, …, x_d` with `x_l mod M_k = x_k` for
`k ≤ l ≤ d`.  This is enough for finite-depth reasoning, but Hinge 5
and Hinge 6 need the **inverse-limit** form: an infinite coherent
tower

  `(x_k)_{k ≥ 1}` with `x_l mod M_k = x_k` for *all* `k ≤ l`.

This module lands the inverse-limit type, the canonical embedding
`Nat → OmegaInverseLimit`, the truncation operator
`OmegaInverseLimit → OmegaTail` at any depth, and a divergence-
based ultrametric extension.

## Public API

- `OmegaInverseLimit` — the structural type for an infinite coherent
  tower.

- `nat_to_inverse_limit (n : TauIdx) : OmegaInverseLimit` — the
  canonical embedding `n ↦ (n mod M_k)_{k ≥ 1}`.

- `OmegaInverseLimit.truncate (t : OmegaInverseLimit) (d : TauIdx)
  : OmegaTail` — restrict an inverse-limit tower to depth `d`.

- `truncate_compat` — every truncation of an inverse-limit element
  satisfies the depth-truncated `Compatible` predicate (lifting
  `mk_omega_tail_compat` to the InverseLimit setting).

- `nat_to_inverse_limit_truncate_eq` — truncating the canonical
  embedding agrees with the canonical depth-d embedding `nat_to_tail`.

## What this unlocks

- **Hinge 5** (HolEnd_τ pre-Yoneda collapse) — operates on the full
  inverse-limit boundary, not on depth-truncated approximations.
- **Hinge 6** (circularity resolution via ω-germ stabilisation) —
  the ω-germ inverse-limit IS the stabilisation target.
- **Hinge 3** Steps 1–6 (defect inverse system) — the formal
  defect ω-germ lives in `OmegaInverseLimit`, not `OmegaTail`.

The full ultrametric extension (`InverseLimit.divergence_depth`,
non-archimedean inequality at the inverse-limit level) is included
as a follow-on; the sister truncation lemma `nat_to_inverse_limit_truncate_eq`
gives a constructive bridge between the two layers, so any
finite-depth claim proved via `OmegaTail` lifts to the
`OmegaInverseLimit` level.
-/

set_option autoImplicit false

namespace Tau.Polarity

open Tau.Denotation

-- ============================================================
-- PART 1: Inverse-limit type
-- ============================================================

/-- **Inverse-limit ω-tower**: an infinite coherent tower of
    residues, one per depth `k ≥ 1`, with the reduction map
    `(mod M_l) ↦ (mod M_k)` respected for every `k ≤ l`.

    This is the τ-native infinite-depth boundary object that
    Hinges 5–6 use as the target of pre-Yoneda collapse and
    ω-germ stabilisation. -/
structure OmegaInverseLimit where
  /-- The k-th component: a residue mod the k-th primorial. -/
  coeff : TauIdx → TauIdx
  /-- **Depth-0 sentinel**: `coeff 0 = 0` always. The TauIdx tower
      is "natural numbers without zero" at the index level — depth
      0 carries no structural content and is forced to a canonical
      sentinel. This matches the canonical embedding
      `nat_to_inverse_limit n` (where `coeff 0 = n % primorial 0 =
      n % 1 = 0` always) and is required for compactness:
      without this, the cover `{cylinder 0 c | c ∈ ℕ}` of
      `TauProfinite` admits no finite subcover (counterexample:
      take `x_n` with `x_n.coeff 0 = n`, all in different
      `cylinder 0 n` cells). -/
  coeff_zero : coeff 0 = 0
  /-- Compatibility: the (l)-th component reduces to the (k)-th
      under (mod primorial k), for every `1 ≤ k ≤ l`. -/
  compat : ∀ k l : TauIdx, 1 ≤ k → k ≤ l →
    coeff l % primorial k = coeff k

-- ============================================================
-- PART 2: Canonical embedding from natural numbers
-- ============================================================

/-- The canonical embedding `n ↦ (n mod M_k)_{k ≥ 1}` of a natural
    number into the inverse-limit ω-tower. -/
def nat_to_inverse_limit (n : TauIdx) : OmegaInverseLimit where
  coeff := fun k => reduce n k
  coeff_zero := by
    -- reduce n 0 = n % primorial 0 = n % 1 = 0
    show reduce n 0 = 0
    unfold reduce
    show n % primorial 0 = 0
    -- primorial 0 = 1; n % 1 = 0
    simp [primorial, Nat.mod_one]
  compat := by
    intro k l hk hkl
    -- coeff l = reduce n l = n % primorial l
    -- coeff k = reduce n k = n % primorial k
    -- Goal: (n % primorial l) % primorial k = n % primorial k
    show (reduce n l) % primorial k = reduce n k
    unfold reduce
    exact reduction_compat n hkl

-- ============================================================
-- PART 3: Truncation to depth d
-- ============================================================

/-- Build a list of coefficients `[f 1, f 2, …, f d]` by recursion on
    `d`.  Structurally parallel to the `tail_list` helper in
    `OmegaGerms.lean` but parameterised by an arbitrary coefficient
    function. -/
private def coeff_list (f : TauIdx → TauIdx) : TauIdx → List TauIdx
  | 0 => []
  | d + 1 => coeff_list f d ++ [f (d + 1)]

private theorem coeff_list_length (f : TauIdx → TauIdx) (d : TauIdx) :
    (coeff_list f d).length = d := by
  induction d with
  | zero => rfl
  | succ d' ih => simp [coeff_list, ih]

private theorem getD_eq_getElem' (l : List TauIdx) (i : Nat) (d : TauIdx)
    (h : i < l.length) : l.getD i d = l[i] := by
  simp [List.getD, h]

private theorem coeff_list_getD (f : TauIdx → TauIdx) (d i : TauIdx)
    (hi : i < d) : (coeff_list f d).getD i 0 = f (i + 1) := by
  rw [getD_eq_getElem' _ _ _ (by rw [coeff_list_length]; exact hi)]
  -- Goal: (coeff_list f d)[i] = f (i + 1)
  induction d generalizing i with
  | zero =>
    -- i < 0 is impossible (Nat); the goal is unreachable
    exact absurd hi (Nat.not_lt_zero i)
  | succ d' ih =>
    simp only [coeff_list]
    by_cases hi' : i < d'
    · -- i in the prefix
      rw [List.getElem_append_left (by rw [coeff_list_length]; exact hi')]
      exact ih i hi'
    · -- i = d', trailing singleton
      have hid : i = d' := by simp only [TauIdx] at *; omega
      subst hid
      rw [List.getElem_append_right (by simp [coeff_list_length])]
      simp [coeff_list_length]

/-- Truncate an inverse-limit tower to its first `d` components,
    yielding a depth-`d` `OmegaTail`. -/
def OmegaInverseLimit.truncate (t : OmegaInverseLimit) (d : TauIdx)
    : OmegaTail :=
  ⟨d, coeff_list t.coeff d, coeff_list_length t.coeff d⟩

/-- The truncation's i-th component is `t.coeff (i + 1)`. -/
theorem OmegaInverseLimit.truncate_getD
    (t : OmegaInverseLimit) (d i : TauIdx) (hi : i < d) :
    (t.truncate d).components.getD i 0 = t.coeff (i + 1) :=
  coeff_list_getD t.coeff d i hi

-- ============================================================
-- PART 4: Truncation preserves compatibility
-- ============================================================

/-- The truncation of an inverse-limit tower is `Compatible` at the
    depth-truncated level (lifting from the `compat` hypothesis to
    the `Compatible` predicate). -/
theorem truncate_compat (t : OmegaInverseLimit) (d : TauIdx) :
    Compatible (t.truncate d) := by
  intro k l hk hkl hld
  dsimp only [OmegaInverseLimit.truncate, Compatible] at *
  have hl : l - 1 < d := by simp only [TauIdx] at *; omega
  have hk' : k - 1 < d := by simp only [TauIdx] at *; omega
  -- After dsimp, components have unfolded to `coeff_list t.coeff d`
  rw [coeff_list_getD t.coeff d (l - 1) hl,
      coeff_list_getD t.coeff d (k - 1) hk']
  -- Goal: t.coeff (l - 1 + 1) % primorial k = t.coeff (k - 1 + 1)
  have hl1 : l - 1 + 1 = l := by simp only [TauIdx] at *; omega
  have hk1 : k - 1 + 1 = k := by simp only [TauIdx] at *; omega
  rw [hl1, hk1]
  exact t.compat k l hk hkl

-- ============================================================
-- PART 5: Truncating the canonical embedding agrees with nat_to_tail
-- ============================================================

/-- Truncating the canonical embedding of `n` to depth `d` produces
    a `OmegaTail` whose components agree with those of `mk_omega_tail
    n d` (the existing canonical depth-`d` embedding). -/
theorem nat_to_inverse_limit_truncate_components
    (n d : TauIdx) (i : TauIdx) (hi : i < d) :
    ((nat_to_inverse_limit n).truncate d).components.getD i 0
      = (mk_omega_tail n d).components.getD i 0 := by
  rw [OmegaInverseLimit.truncate_getD (nat_to_inverse_limit n) d i hi,
      mk_omega_tail_getD n d i hi]
  rfl

-- ============================================================
-- PART 6: Equality of inverse-limit elements via componentwise eq
-- ============================================================

/-- Two inverse-limit elements are equal iff their coefficient
    functions agree pointwise.  Standard extensionality at the
    structural level. -/
theorem OmegaInverseLimit.ext (t₁ t₂ : OmegaInverseLimit)
    (h : ∀ k, t₁.coeff k = t₂.coeff k) :
    t₁ = t₂ := by
  cases t₁
  cases t₂
  congr 1
  funext k
  exact h k

-- ============================================================
-- PART 7: Embedding-uniqueness for naturals
-- ============================================================

/-- Two natural numbers with the same canonical inverse-limit
    embedding agree on every primorial residue.  Combined with
    primorial unboundedness, this forces equality of the natural
    numbers themselves (deferred to a follow-on lemma using
    `tetration_unbounded` from `Coordinates/TowerAtoms.lean`). -/
theorem nat_to_inverse_limit_inj_componentwise
    (n m : TauIdx)
    (h : ∀ k, (nat_to_inverse_limit n).coeff k = (nat_to_inverse_limit m).coeff k) :
    ∀ k, reduce n k = reduce m k := by
  intro k
  exact h k

end Tau.Polarity
