import TauLib.BookI.Polarity.ModArith

/-!
# TauLib.BookI.Polarity.OmegaGerms

Omega-tails (compatible towers) and the divergence ultrametric.

## Registry Cross-References

- [I.D25] Omega-Tail — `OmegaTail`, `nat_to_tail`, `divergence_depth`

## Ground Truth Sources
- chunk_0155_M001710: Omega-tails, divergence ultrametric, coupling invariant

## Mathematical Content

An omega-tail is a compatible tower (x_k)_{k ≥ 1} where x_k ∈ Z/M_kZ
and the reduction maps are respected: x_ℓ mod M_k = x_k for k ≤ ℓ.

Every natural number n gives rise to an omega-tail via n ↦ (n mod M_k)_k.
The divergence depth d(t, t') = min{k : x_k ≠ x_k'} defines a canonical
ultrametric on the space of omega-tails.
-/

namespace Tau.Polarity

open Tau.Denotation

-- ============================================================
-- OMEGA-TAIL [I.D25]
-- ============================================================

/-- [I.D25] Truncated omega-tail up to depth d: components x_k for k = 1..d.
    Represented as a list of TauIdx values, where the k-th entry is x_k ∈ Z/M_kZ.
    Compatibility: x_k = x_ℓ mod M_k for k ≤ ℓ. -/
structure OmegaTail where
  depth : TauIdx
  components : List TauIdx
  depth_eq : components.length = depth
  deriving Repr

/-- Build omega-tail components for n at depths 1..d. -/
def nat_to_tail_go (n k d : Nat) (fuel : Nat) (acc : List TauIdx) : List TauIdx :=
  if fuel = 0 then acc
  else if k > d then acc
  else nat_to_tail_go n (k + 1) d (fuel - 1) (acc ++ [reduce n k])
termination_by fuel

/-- Canonical embedding: n ↦ (n mod M_1, n mod M_2, ..., n mod M_d). -/
def nat_to_tail_components (n d : TauIdx) : List TauIdx :=
  nat_to_tail_go n 1 d d []

/-- The canonical omega-tail of a natural number n, truncated at depth d. -/
def nat_to_tail (n d : TauIdx) : OmegaTail :=
  let comps := nat_to_tail_components n d
  ⟨comps.length, comps, rfl⟩

-- ============================================================
-- COMPONENT ACCESS
-- ============================================================

/-- Safe component access with default 0. -/
def OmegaTail.get (t : OmegaTail) (i : Nat) : TauIdx :=
  t.components.getD i 0

-- ============================================================
-- COMPATIBILITY CHECK
-- ============================================================

/-- Check compatibility at indices k ≤ l: component[l-1] mod M_k = component[k-1]. -/
def compat_inner (comps : List TauIdx) (k l : Nat) (fuel : Nat) : Bool :=
  if fuel = 0 then true
  else if k > l then true
  else
    let xk := comps.getD (k - 1) 0
    let xl := comps.getD (l - 1) 0
    (xl % primorial k == xk) && compat_inner comps (k + 1) l (fuel - 1)
termination_by fuel

/-- Check full compatibility of an omega-tail. -/
def compat_outer (comps : List TauIdx) (d k : Nat) (fuel : Nat) : Bool :=
  if fuel = 0 then true
  else if k > d then true
  else compat_inner comps k d d && compat_outer comps d (k + 1) (fuel - 1)
termination_by fuel

def compat_check (t : OmegaTail) : Bool :=
  compat_outer t.components t.depth 1 t.depth

-- ============================================================
-- PROP-LEVEL COMPATIBILITY [I.D25]
-- ============================================================

/-- Prop-level compatibility: for all k ≤ l within depth,
    the reduction map respects tower components. -/
def Compatible (t : OmegaTail) : Prop :=
  ∀ k l, 1 ≤ k → k ≤ l → l ≤ t.depth →
    t.components.getD (l - 1) 0 % primorial k = t.components.getD (k - 1) 0

-- ============================================================
-- CANONICAL EMBEDDING SOUNDNESS
-- ============================================================

/-- Clean specification list: [reduce n 1, reduce n 2, ..., reduce n d].
    Built recursively for clean inductive reasoning. -/
private def tail_list : Nat → Nat → List TauIdx
  | _, 0 => []
  | n, d + 1 => tail_list n d ++ [reduce n (d + 1)]

private theorem tail_list_length (n d : Nat) : (tail_list n d).length = d := by
  induction d with
  | zero => rfl
  | succ d' ih => simp [tail_list, ih]

/-- Omega-tail built from clean spec (for formal reasoning). -/
def mk_omega_tail (n d : TauIdx) : OmegaTail :=
  ⟨d, tail_list n d, tail_list_length n d⟩

-- Helper: getD at in-bounds index equals getElem
private theorem getD_eq_getElem (l : List TauIdx) (i : Nat) (d : TauIdx) (h : i < l.length) :
    l.getD i d = l[i] := by
  simp [List.getD, h]

private theorem tail_list_getD (n d i : Nat) (hi : i < d) :
    (tail_list n d).getD i 0 = reduce n (i + 1) := by
  rw [getD_eq_getElem _ _ _ (by rw [tail_list_length]; exact hi)]
  -- Goal: (tail_list n d)[i] = reduce n (i + 1)
  induction d generalizing i with
  | zero => omega
  | succ d' ih =>
    simp only [tail_list]
    by_cases hi' : i < d'
    · -- i in prefix
      rw [List.getElem_append_left (by rw [tail_list_length]; exact hi')]
      exact ih i hi'
    · -- i = d'
      have hid : i = d' := by omega
      subst hid
      rw [List.getElem_append_right (by simp [tail_list_length])]
      simp [tail_list_length]

/-- The clean-spec omega-tail is compatible: reduction maps compose.
    This is the Prop-level soundness theorem for the canonical embedding. -/
theorem mk_omega_tail_compat (n d : TauIdx) : Compatible (mk_omega_tail n d) := by
  intro k l hk hkl hld
  dsimp only [mk_omega_tail, Compatible] at *
  -- hld : l ≤ d (structure projection resolved)
  have hl : l - 1 < d := by simp only [TauIdx] at *; omega
  have hk' : k - 1 < d := by simp only [TauIdx] at *; omega
  rw [tail_list_getD n d (l - 1) hl, tail_list_getD n d (k - 1) hk']
  have hl1 : l - 1 + 1 = l := by simp only [TauIdx] at *; omega
  have hk1 : k - 1 + 1 = k := by simp only [TauIdx] at *; omega
  rw [hl1, hk1]
  exact reduction_compat n hkl

/-- Component accessor for mk_omega_tail: the i-th component is reduce n (i+1). -/
theorem mk_omega_tail_getD (n d i : Nat) (hi : i < d) :
    (mk_omega_tail n d).components.getD i 0 = reduce n (i + 1) :=
  tail_list_getD n d i hi

-- Verified: nat_to_tail and mk_omega_tail produce identical components
-- (for all standard smoke-test depths)
example : (nat_to_tail 42 5).components = (mk_omega_tail 42 5).components := by native_decide
example : (nat_to_tail 100 5).components = (mk_omega_tail 100 5).components := by native_decide
example : (nat_to_tail 7 10).components = (mk_omega_tail 7 10).components := by native_decide

-- ============================================================
-- TAIL EQUIVALENCE
-- ============================================================

/-- Pointwise equality check of two component lists up to depth d. -/
def equiv_go (c1 c2 : List TauIdx) (d i : Nat) (fuel : Nat) : Bool :=
  if fuel = 0 then true
  else if i ≥ d then true
  else
    let a := c1.getD i 0
    let b := c2.getD i 0
    (a == b) && equiv_go c1 c2 d (i + 1) (fuel - 1)
termination_by fuel

/-- Tail equivalence: two omega-tails agree on all shared components. -/
def tail_equiv (t1 t2 : OmegaTail) : Bool :=
  let d := min t1.depth t2.depth
  equiv_go t1.components t2.components d 0 d

-- ============================================================
-- DIVERGENCE DEPTH
-- ============================================================

/-- Find first disagreement index between two component lists. -/
def diverge_go (c1 c2 : List TauIdx) (d i : Nat) (fuel : Nat) : TauIdx :=
  if fuel = 0 then 0
  else if i ≥ d then 0
  else
    let a := c1.getD i 0
    let b := c2.getD i 0
    if a != b then i + 1
    else diverge_go c1 c2 d (i + 1) (fuel - 1)
termination_by fuel

/-- Divergence depth: first index k where the tails disagree.
    Returns 0 if tails are equivalent (up to shared depth). -/
def divergence_depth (t1 t2 : OmegaTail) : TauIdx :=
  let d := min t1.depth t2.depth
  diverge_go t1.components t2.components d 0 d

/-- Ultrametric distance: 0 if equivalent, k₀ = first disagreement index otherwise. -/
def ultra_dist (t1 t2 : OmegaTail) : TauIdx := divergence_depth t1 t2

-- ============================================================
-- ULTRAMETRIC PROPERTIES (formal + computable)
-- ============================================================

/-- Helper: diverge_go is symmetric in its list arguments. -/
private theorem diverge_go_comm (c1 c2 : List TauIdx) (d i fuel : Nat) :
    diverge_go c1 c2 d i fuel = diverge_go c2 c1 d i fuel := by
  induction fuel generalizing i with
  | zero => unfold diverge_go; rfl
  | succ n ih =>
    unfold diverge_go
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    split
    · rfl
    · -- Case split on equality of components
      by_cases h : List.getD c1 i 0 = List.getD c2 i 0
      · -- Equal: both bne checks false, recurse via IH
        simp_all
      · -- Unequal: both bne checks true, both return i + 1
        have h' : List.getD c2 i 0 ≠ List.getD c1 i 0 := Ne.symm h
        simp_all

/-- Ultrametric symmetry: d(t1,t2) = d(t2,t1). -/
theorem ultra_symmetric (t1 t2 : OmegaTail) :
    ultra_dist t1 t2 = ultra_dist t2 t1 := by
  unfold ultra_dist divergence_depth
  rw [show min t1.depth t2.depth = min t2.depth t1.depth
      from Nat.min_comm t1.depth t2.depth]
  exact diverge_go_comm t1.components t2.components _ 0 _

/-- Agreement transitivity: if c1[i] = c2[i] and c2[i] = c3[i], then c1[i] = c3[i]. -/
theorem agree_at_trans (c1 c2 c3 : List TauIdx) (i : Nat)
    (h12 : c1.getD i 0 = c2.getD i 0) (h23 : c2.getD i 0 = c3.getD i 0) :
    c1.getD i 0 = c3.getD i 0 := h12 ▸ h23

/-- Check symmetry: d(t1, t2) = d(t2, t1). -/
def ultra_symmetry_check (t1 t2 : OmegaTail) : Bool :=
  ultra_dist t1 t2 == ultra_dist t2 t1

/-- Check ultrametric strong triangle inequality (divergence-depth convention).
    In the raw divergence-depth convention (0 = identical, k = first disagreement
    at position k-1), the standard ultrametric triangle d(x,z) ≤ max(d(x,y), d(y,z))
    translates to: the first disagreement of (t1,t3) is at least as deep as
    the minimum of the first disagreements of the other two pairs.
    This holds for all non-identical pairs; when ultra_dist = 0 (identical),
    the pair is transparent (d(t1,t3) = d(t2,t3) when t1 ≡ t2). -/
def ultra_triangle_check (t1 t2 t3 : OmegaTail) : Bool :=
  -- For non-identical t1,t3: first-disagree(t1,t3) ≥ min of other two
  ultra_dist t1 t3 == 0 ||
  ultra_dist t1 t3 >= min (ultra_dist t1 t2) (ultra_dist t2 t3)

-- ============================================================
-- ULTRAMETRIC TRIANGLE (formal proof)
-- ============================================================

/-- Helper: diverge_go returns 0 or a value > i (the starting index). -/
private theorem diverge_go_zero_or_gt (c1 c2 : List TauIdx) (d i fuel : Nat) :
    diverge_go c1 c2 d i fuel = 0 ∨ diverge_go c1 c2 d i fuel > i := by
  induction fuel generalizing i with
  | zero => left; unfold diverge_go; rfl
  | succ n ih =>
    unfold diverge_go
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    split -- i ≥ d?
    · left; rfl
    · by_cases heq : c1.getD i 0 = c2.getD i 0
      · -- Equal: bne false, recurse
        have hne : c1.getD i 0 ≠ c2.getD i 0 → False := fun h => h heq
        simp_all
        rcases ih (i + 1) with h | h
        · left; exact h
        · right; exact Nat.lt_trans (Nat.lt_add_one i) h
      · -- Unequal: bne true, return i + 1
        have heq' : c2.getD i 0 ≠ c1.getD i 0 := Ne.symm heq
        simp_all

/-- Ultrametric triangle inequality for diverge_go (formal, universal proof).
    The first disagreement of (c1,c3) is either 0 (identical) or at least as deep
    as the minimum of the first disagreements of (c1,c2) and (c2,c3). -/
private theorem diverge_go_triangle (c1 c2 c3 : List TauIdx) (d i fuel : Nat) :
    diverge_go c1 c3 d i fuel = 0 ∨
    diverge_go c1 c3 d i fuel ≥
      Nat.min (diverge_go c1 c2 d i fuel) (diverge_go c2 c3 d i fuel) := by
  induction fuel generalizing i with
  | zero => left; unfold diverge_go; rfl
  | succ n ih =>
    unfold diverge_go
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    split -- i ≥ d?
    · left; rfl
    · rename_i hid
      -- Nested by_cases: derive third equality from first two to avoid contradictions
      by_cases h13 : c1.getD i 0 = c3.getD i 0
      · -- c1[i] = c3[i]: d13 recurses
        by_cases h12 : c1.getD i 0 = c2.getD i 0
        · -- c1[i] = c2[i] → c2[i] = c3[i], all recurse → IH
          have h23 : c2.getD i 0 = c3.getD i 0 := h12.symm.trans h13
          have h23' : c3.getD i 0 ≠ c2.getD i 0 → False := fun h => h h23.symm
          simp_all
        · -- c1[i] ≠ c2[i] → c2[i] ≠ c3[i], d12=i+1, d23=i+1
          have h23 : c2.getD i 0 ≠ c3.getD i 0 := fun heq => h12 (h13.trans heq.symm)
          have h12' : c2.getD i 0 ≠ c1.getD i 0 := Ne.symm h12
          have h23' : c3.getD i 0 ≠ c2.getD i 0 := Ne.symm h23
          simp_all
          rcases diverge_go_zero_or_gt c1 c3 d (i + 1) n with h | h
          · left; exact h
          · right; exact Nat.le_of_lt h
      · -- c1[i] ≠ c3[i]: d13 = i+1
        have h13' : c3.getD i 0 ≠ c1.getD i 0 := Ne.symm h13
        by_cases h12 : c1.getD i 0 = c2.getD i 0
        · -- c1[i] = c2[i] → c2[i] ≠ c3[i], d12 recurses, d23=i+1
          have h23 : c2.getD i 0 ≠ c3.getD i 0 := fun heq => h13 (h12.trans heq)
          have h23' : c3.getD i 0 ≠ c2.getD i 0 := Ne.symm h23
          simp_all; exact Nat.min_le_right _ _
        · -- c1[i] ≠ c2[i]: d12 = i+1
          have h12' : c2.getD i 0 ≠ c1.getD i 0 := Ne.symm h12
          by_cases h23 : c2.getD i 0 = c3.getD i 0
          · -- c2[i] = c3[i]: d23 recurses
            have h23' : c3.getD i 0 ≠ c2.getD i 0 → False := fun h => h h23.symm
            simp_all; exact Nat.min_le_left _ _
          · -- c2[i] ≠ c3[i]: d23 = i+1
            have h23' : c3.getD i 0 ≠ c2.getD i 0 := Ne.symm h23
            simp_all

/-- Ultrametric distance on same-depth tails reduces to diverge_go. -/
private theorem ultra_dist_eq_diverge (t1 t2 : OmegaTail) (d : TauIdx)
    (h1 : t1.depth = d) (h2 : t2.depth = d) :
    ultra_dist t1 t2 = diverge_go t1.components t2.components d 0 d := by
  simp only [ultra_dist, divergence_depth, h1, h2, Nat.min_self]

/-- Ultrametric triangle inequality (formal, universal) for equal-depth tails.
    d(t1,t3) = 0 or d(t1,t3) ≥ min(d(t1,t2), d(t2,t3)). -/
theorem ultra_triangle (t1 t2 t3 : OmegaTail)
    (h12 : t1.depth = t2.depth) (h13 : t1.depth = t3.depth) :
    ultra_dist t1 t3 = 0 ∨
    ultra_dist t1 t3 ≥ Nat.min (ultra_dist t1 t2) (ultra_dist t2 t3) := by
  rw [ultra_dist_eq_diverge t1 t3 t1.depth rfl (h13 ▸ rfl),
      ultra_dist_eq_diverge t1 t2 t1.depth rfl (h12 ▸ rfl),
      ultra_dist_eq_diverge t2 t3 t1.depth (h12 ▸ rfl) (h13 ▸ rfl)]
  exact diverge_go_triangle t1.components t2.components t3.components t1.depth 0 t1.depth

/-- Ultrametric triangle for mk_omega_tail (the most common use case). -/
theorem ultra_triangle_mk (n1 n2 n3 d : TauIdx) :
    ultra_dist (mk_omega_tail n1 d) (mk_omega_tail n3 d) = 0 ∨
    ultra_dist (mk_omega_tail n1 d) (mk_omega_tail n3 d) ≥
      Nat.min (ultra_dist (mk_omega_tail n1 d) (mk_omega_tail n2 d))
              (ultra_dist (mk_omega_tail n2 d) (mk_omega_tail n3 d)) :=
  ultra_triangle _ _ _ rfl rfl

-- ============================================================
-- ULTRAMETRIC TRIANGLE (native_decide verifications, kept as regression tests)
-- ============================================================

-- The divergence-depth convention uses 0 = "identical" and k = "first
-- disagreement at position k-1". The standard ultrametric triangle
-- d(x,z) ≤ max(d(x,y), d(y,z)) uses d = 2^(-first_disagree), where
-- larger first_disagree → smaller d. Translated to our convention:
--
--   For non-identical pairs: ultra_dist(t1,t3) ≥ min(ultra_dist(t1,t2), ultra_dist(t2,t3))
--
-- Verified by native_decide for concrete omega-tails below.

example : ultra_triangle_check (nat_to_tail 7 5) (nat_to_tail 42 5) (nat_to_tail 100 5)
    = true := by native_decide
example : ultra_triangle_check (nat_to_tail 1 5) (nat_to_tail 3 5) (nat_to_tail 7 5)
    = true := by native_decide
example : ultra_triangle_check (nat_to_tail 2 5) (nat_to_tail 8 5) (nat_to_tail 14 5)
    = true := by native_decide
example : ultra_triangle_check (nat_to_tail 10 5) (nat_to_tail 40 5) (nat_to_tail 100 5)
    = true := by native_decide
example : ultra_triangle_check (nat_to_tail 1 5) (nat_to_tail 1 5) (nat_to_tail 7 5)
    = true := by native_decide
example : ultra_triangle_check (nat_to_tail 30 5) (nat_to_tail 60 5) (nat_to_tail 90 5)
    = true := by native_decide

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Omega-tails of small numbers
#eval nat_to_tail 7 4      -- components at depths 1..4
#eval nat_to_tail 42 4
#eval nat_to_tail 100 5

-- Compatibility
#eval compat_check (nat_to_tail 7 5)     -- true
#eval compat_check (nat_to_tail 42 5)    -- true
#eval compat_check (nat_to_tail 100 5)   -- true

-- Tail equivalence
#eval tail_equiv (nat_to_tail 7 4) (nat_to_tail 7 4)     -- true
#eval tail_equiv (nat_to_tail 7 4) (nat_to_tail 37 4)    -- false

-- Divergence depth
#eval divergence_depth (nat_to_tail 7 5) (nat_to_tail 37 5)   -- some depth
#eval divergence_depth (nat_to_tail 7 5) (nat_to_tail 7 5)    -- 0 (identical)
#eval divergence_depth (nat_to_tail 7 5) (nat_to_tail 9 5)    -- first disagreement

-- Ultrametric properties
#eval ultra_symmetry_check (nat_to_tail 7 5) (nat_to_tail 42 5)    -- true
#eval ultra_triangle_check (nat_to_tail 7 5) (nat_to_tail 42 5) (nat_to_tail 100 5) -- true

end Tau.Polarity
