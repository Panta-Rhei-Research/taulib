import TauLib.BookI.Polarity.OmegaGerms

/-!
# TauLib.BookI.Polarity.OmegaRing

Stagewise ring operations on omega-tails with compatibility preservation.

## Registry Cross-References

- [I.D28] Boundary Local Ring — `mk_omega_tail_add`, `mk_omega_tail_mul`
- [I.D25] Omega-Tail — `Compatible_add`, `Compatible_mul`

## Ground Truth Sources
- chunk_0243_M002286: Boundary ring with levelwise addition/multiplication
- chunk_0314_M002691: Stagewise ring operations preserve compatibility

## Mathematical Content

The boundary ring ℤ̂_τ = lim Z/M_kZ carries componentwise ring operations:
- Addition: (x_k) + (y_k) = ((x_k + y_k) mod M_k)
- Multiplication: (x_k) · (y_k) = ((x_k · y_k) mod M_k)

Both operations preserve tower compatibility (the key structural theorem).
The proofs use: reduction_compat, Nat.add_mod / Nat.mul_mod, mod_mod_of_dvd.
-/

namespace Tau.Polarity

open Tau.Denotation

-- ============================================================
-- UTILITY: getD for List access
-- ============================================================

/-- Helper: getD at in-bounds index equals getElem. -/
private theorem getD_eq_getElem (l : List TauIdx) (i : Nat) (d : TauIdx) (h : i < l.length) :
    l.getD i d = l[i] := by
  simp [List.getD, h]

-- ============================================================
-- COMPONENTWISE ADDITION
-- ============================================================

/-- Componentwise addition list: [(n1+n2) mod M_1, ..., (n1+n2) mod M_d].
    Built recursively for clean inductive reasoning. -/
private def omega_add_list (n1 n2 : Nat) : Nat → List TauIdx
  | 0 => []
  | d + 1 => omega_add_list n1 n2 d ++ [(reduce n1 (d + 1) + reduce n2 (d + 1)) % primorial (d + 1)]

private theorem omega_add_list_length (n1 n2 d : Nat) : (omega_add_list n1 n2 d).length = d := by
  induction d with
  | zero => rfl
  | succ d' ih => simp [omega_add_list, ih]

/-- Omega-tail addition via canonical embedding. -/
def mk_omega_tail_add (n1 n2 d : TauIdx) : OmegaTail :=
  ⟨d, omega_add_list n1 n2 d, omega_add_list_length n1 n2 d⟩

private theorem omega_add_list_getD (n1 n2 d i : Nat) (hi : i < d) :
    (omega_add_list n1 n2 d).getD i 0 =
    (reduce n1 (i + 1) + reduce n2 (i + 1)) % primorial (i + 1) := by
  rw [getD_eq_getElem _ _ _ (by rw [omega_add_list_length]; exact hi)]
  induction d generalizing i with
  | zero => omega
  | succ d' ih =>
    simp only [omega_add_list]
    by_cases hi' : i < d'
    · rw [List.getElem_append_left (by rw [omega_add_list_length]; exact hi')]
      exact ih i hi'
    · have hid : i = d' := by omega
      subst hid
      rw [List.getElem_append_right (by simp [omega_add_list_length])]
      simp [omega_add_list_length]

/-- Bridge: componentwise addition equals global addition under reduce. -/
theorem omega_add_eq_reduce (n1 n2 d i : Nat) (hi : i < d) :
    (omega_add_list n1 n2 d).getD i 0 = reduce (n1 + n2) (i + 1) := by
  rw [omega_add_list_getD n1 n2 d i hi]
  simp only [reduce]
  exact (Nat.add_mod n1 n2 (primorial (i + 1))).symm

/-- Componentwise addition of canonical tails produces compatible towers. -/
theorem Compatible_add (n1 n2 d : TauIdx) : Compatible (mk_omega_tail_add n1 n2 d) := by
  intro k l hk hkl hld
  dsimp only [mk_omega_tail_add, Compatible] at *
  have hl : l - 1 < d := by simp only [TauIdx] at *; omega
  have hk' : k - 1 < d := by simp only [TauIdx] at *; omega
  rw [omega_add_eq_reduce n1 n2 d (l - 1) hl, omega_add_eq_reduce n1 n2 d (k - 1) hk']
  have hl1 : l - 1 + 1 = l := by simp only [TauIdx] at *; omega
  have hk1 : k - 1 + 1 = k := by simp only [TauIdx] at *; omega
  rw [hl1, hk1]
  exact reduction_compat (n1 + n2) hkl

-- ============================================================
-- COMPONENTWISE MULTIPLICATION
-- ============================================================

/-- Componentwise multiplication list: [(n1*n2) mod M_1, ..., (n1*n2) mod M_d]. -/
private def omega_mul_list (n1 n2 : Nat) : Nat → List TauIdx
  | 0 => []
  | d + 1 => omega_mul_list n1 n2 d ++ [(reduce n1 (d + 1) * reduce n2 (d + 1)) % primorial (d + 1)]

private theorem omega_mul_list_length (n1 n2 d : Nat) : (omega_mul_list n1 n2 d).length = d := by
  induction d with
  | zero => rfl
  | succ d' ih => simp [omega_mul_list, ih]

/-- Omega-tail multiplication via canonical embedding. -/
def mk_omega_tail_mul (n1 n2 d : TauIdx) : OmegaTail :=
  ⟨d, omega_mul_list n1 n2 d, omega_mul_list_length n1 n2 d⟩

private theorem omega_mul_list_getD (n1 n2 d i : Nat) (hi : i < d) :
    (omega_mul_list n1 n2 d).getD i 0 =
    (reduce n1 (i + 1) * reduce n2 (i + 1)) % primorial (i + 1) := by
  rw [getD_eq_getElem _ _ _ (by rw [omega_mul_list_length]; exact hi)]
  induction d generalizing i with
  | zero => omega
  | succ d' ih =>
    simp only [omega_mul_list]
    by_cases hi' : i < d'
    · rw [List.getElem_append_left (by rw [omega_mul_list_length]; exact hi')]
      exact ih i hi'
    · have hid : i = d' := by omega
      subst hid
      rw [List.getElem_append_right (by simp [omega_mul_list_length])]
      simp [omega_mul_list_length]

/-- Bridge: componentwise multiplication equals global multiplication under reduce. -/
theorem omega_mul_eq_reduce (n1 n2 d i : Nat) (hi : i < d) :
    (omega_mul_list n1 n2 d).getD i 0 = reduce (n1 * n2) (i + 1) := by
  rw [omega_mul_list_getD n1 n2 d i hi]
  simp only [reduce]
  exact (Nat.mul_mod n1 n2 (primorial (i + 1))).symm

/-- Componentwise multiplication of canonical tails produces compatible towers. -/
theorem Compatible_mul (n1 n2 d : TauIdx) : Compatible (mk_omega_tail_mul n1 n2 d) := by
  intro k l hk hkl hld
  dsimp only [mk_omega_tail_mul, Compatible] at *
  have hl : l - 1 < d := by simp only [TauIdx] at *; omega
  have hk' : k - 1 < d := by simp only [TauIdx] at *; omega
  rw [omega_mul_eq_reduce n1 n2 d (l - 1) hl, omega_mul_eq_reduce n1 n2 d (k - 1) hk']
  have hl1 : l - 1 + 1 = l := by simp only [TauIdx] at *; omega
  have hk1 : k - 1 + 1 = k := by simp only [TauIdx] at *; omega
  rw [hl1, hk1]
  exact reduction_compat (n1 * n2) hkl

-- ============================================================
-- GENERAL RING OPERATIONS ON ARBITRARY COMPATIBLE TAILS
-- ============================================================

/-- General componentwise addition of two omega-tails of equal depth. -/
def OmegaTail.add (t1 t2 : OmegaTail) (_hd : t1.depth = t2.depth) : OmegaTail where
  depth := t1.depth
  components := (List.range t1.depth).map (fun i =>
    (t1.components.getD i 0 + t2.components.getD i 0) % primorial (i + 1))
  depth_eq := by simp

/-- Helper: access components of OmegaTail.add. -/
private theorem add_getD (t1 t2 : OmegaTail) (hd : t1.depth = t2.depth)
    (i : Nat) (hi : i < t1.depth) :
    (t1.add t2 hd).components.getD i 0 =
    (t1.components.getD i 0 + t2.components.getD i 0) % primorial (i + 1) := by
  simp only [OmegaTail.add]
  rw [getD_eq_getElem _ _ _ (by simp [List.length_map, List.length_range]; exact hi)]
  simp [List.getElem_map, List.getElem_range]

/-- General compatibility preservation under addition. -/
theorem Compatible_add_general (t1 t2 : OmegaTail) (hd : t1.depth = t2.depth)
    (h1 : Compatible t1) (h2 : Compatible t2) :
    Compatible (t1.add t2 hd) := by
  intro k l hk hkl hld
  have hdepth : (t1.add t2 hd).depth = t1.depth := by simp [OmegaTail.add]
  have hld' : l ≤ t1.depth := by rw [← hdepth]; exact hld
  have hl : l - 1 < t1.depth := by simp only [TauIdx] at *; omega
  have hk' : k - 1 < t1.depth := by simp only [TauIdx] at *; omega
  have hl1 : l - 1 + 1 = l := by simp only [TauIdx] at *; omega
  have hk1 : k - 1 + 1 = k := by simp only [TauIdx] at *; omega
  rw [add_getD t1 t2 hd (l - 1) hl, add_getD t1 t2 hd (k - 1) hk']
  -- Normalize: primorial (l-1+1) → primorial l, primorial (k-1+1) → primorial k
  rw [hl1, hk1]
  -- Goal: ((x_l + y_l) % M_l) % M_k = (x_k + y_k) % M_k
  rw [mod_mod_of_dvd _ _ _ (primorial_dvd hkl)]
  -- Goal: (x_l + y_l) % M_k = (x_k + y_k) % M_k
  rw [Nat.add_mod (t1.components.getD (l-1) 0) (t2.components.getD (l-1) 0) (primorial k)]
  -- Goal: ((x_l % M_k) + (y_l % M_k)) % M_k = (x_k + y_k) % M_k
  rw [h1 k l hk hkl hld', h2 k l hk hkl (by rw [← hd]; exact hld')]

/-- General componentwise multiplication of two omega-tails of equal depth. -/
def OmegaTail.mul (t1 t2 : OmegaTail) (_hd : t1.depth = t2.depth) : OmegaTail where
  depth := t1.depth
  components := (List.range t1.depth).map (fun i =>
    (t1.components.getD i 0 * t2.components.getD i 0) % primorial (i + 1))
  depth_eq := by simp

/-- Helper: access components of OmegaTail.mul. -/
private theorem mul_getD (t1 t2 : OmegaTail) (hd : t1.depth = t2.depth)
    (i : Nat) (hi : i < t1.depth) :
    (t1.mul t2 hd).components.getD i 0 =
    (t1.components.getD i 0 * t2.components.getD i 0) % primorial (i + 1) := by
  simp only [OmegaTail.mul]
  rw [getD_eq_getElem _ _ _ (by simp [List.length_map, List.length_range]; exact hi)]
  simp [List.getElem_map, List.getElem_range]

/-- General compatibility preservation under multiplication. -/
theorem Compatible_mul_general (t1 t2 : OmegaTail) (hd : t1.depth = t2.depth)
    (h1 : Compatible t1) (h2 : Compatible t2) :
    Compatible (t1.mul t2 hd) := by
  intro k l hk hkl hld
  have hdepth : (t1.mul t2 hd).depth = t1.depth := by simp [OmegaTail.mul]
  have hld' : l ≤ t1.depth := by rw [← hdepth]; exact hld
  have hl : l - 1 < t1.depth := by simp only [TauIdx] at *; omega
  have hk' : k - 1 < t1.depth := by simp only [TauIdx] at *; omega
  have hl1 : l - 1 + 1 = l := by simp only [TauIdx] at *; omega
  have hk1 : k - 1 + 1 = k := by simp only [TauIdx] at *; omega
  rw [mul_getD t1 t2 hd (l - 1) hl, mul_getD t1 t2 hd (k - 1) hk']
  -- Normalize: primorial (l-1+1) → primorial l, primorial (k-1+1) → primorial k
  rw [hl1, hk1]
  -- Goal: ((x_l * y_l) % M_l) % M_k = (x_k * y_k) % M_k
  rw [mod_mod_of_dvd _ _ _ (primorial_dvd hkl)]
  -- Goal: (x_l * y_l) % M_k = (x_k * y_k) % M_k
  rw [Nat.mul_mod (t1.components.getD (l-1) 0) (t2.components.getD (l-1) 0) (primorial k)]
  -- Goal: ((x_l % M_k) * (y_l % M_k)) % M_k = (x_k * y_k) % M_k
  rw [h1 k l hk hkl hld', h2 k l hk hkl (by rw [← hd]; exact hld')]

-- ============================================================
-- RING IDENTITY ELEMENTS
-- ============================================================

/-- Zero omega-tail: all components are 0 mod M_k = 0. -/
def mk_omega_zero (d : TauIdx) : OmegaTail := mk_omega_tail 0 d

/-- One omega-tail: all components are 1 mod M_k = 1 (for k ≥ 1). -/
def mk_omega_one (d : TauIdx) : OmegaTail := mk_omega_tail 1 d

/-- Zero is compatible. -/
theorem omega_zero_compat (d : TauIdx) : Compatible (mk_omega_zero d) :=
  mk_omega_tail_compat 0 d

/-- One is compatible. -/
theorem omega_one_compat (d : TauIdx) : Compatible (mk_omega_one d) :=
  mk_omega_tail_compat 1 d

-- ============================================================
-- FORMAL RING IDENTITY PROOFS
-- ============================================================

/-- mk_omega_tail_add produces the same components as mk_omega_tail of the sum.
    This is the master bridge: componentwise addition = global addition. -/
theorem omega_add_components_eq (n1 n2 d : TauIdx) :
    (mk_omega_tail_add n1 n2 d).components = (mk_omega_tail (n1 + n2) d).components := by
  have hlen : (mk_omega_tail_add n1 n2 d).components.length =
              (mk_omega_tail (n1 + n2) d).components.length :=
    (mk_omega_tail_add n1 n2 d).depth_eq.trans (mk_omega_tail (n1 + n2) d).depth_eq.symm
  apply List.ext_getElem hlen
  intro i h1 h2
  have hi : i < d := by rw [(mk_omega_tail_add n1 n2 d).depth_eq] at h1; exact h1
  rw [← getD_eq_getElem _ i 0 h1, ← getD_eq_getElem _ i 0 h2]
  show (omega_add_list n1 n2 d).getD i 0 = (mk_omega_tail (n1 + n2) d).components.getD i 0
  rw [omega_add_eq_reduce n1 n2 d i hi, mk_omega_tail_getD (n1 + n2) d i hi]

/-- mk_omega_tail_mul produces the same components as mk_omega_tail of the product.
    This is the master bridge: componentwise multiplication = global multiplication. -/
theorem omega_mul_components_eq (n1 n2 d : TauIdx) :
    (mk_omega_tail_mul n1 n2 d).components = (mk_omega_tail (n1 * n2) d).components := by
  have hlen : (mk_omega_tail_mul n1 n2 d).components.length =
              (mk_omega_tail (n1 * n2) d).components.length :=
    (mk_omega_tail_mul n1 n2 d).depth_eq.trans (mk_omega_tail (n1 * n2) d).depth_eq.symm
  apply List.ext_getElem hlen
  intro i h1 h2
  have hi : i < d := by rw [(mk_omega_tail_mul n1 n2 d).depth_eq] at h1; exact h1
  rw [← getD_eq_getElem _ i 0 h1, ← getD_eq_getElem _ i 0 h2]
  show (omega_mul_list n1 n2 d).getD i 0 = (mk_omega_tail (n1 * n2) d).components.getD i 0
  rw [omega_mul_eq_reduce n1 n2 d i hi, mk_omega_tail_getD (n1 * n2) d i hi]

-- Ring identity corollaries (all universal, no native_decide)

/-- Additive identity: n + 0 = n (on omega-tails). -/
theorem omega_add_zero (n d : TauIdx) :
    (mk_omega_tail_add n 0 d).components = (mk_omega_tail n d).components := by
  rw [omega_add_components_eq, Nat.add_zero]

/-- Multiplicative identity: n * 1 = n (on omega-tails). -/
theorem omega_mul_one (n d : TauIdx) :
    (mk_omega_tail_mul n 1 d).components = (mk_omega_tail n d).components := by
  rw [omega_mul_components_eq, Nat.mul_one]

/-- Additive commutativity: n + m = m + n (on omega-tails). -/
theorem omega_add_comm (n1 n2 d : TauIdx) :
    (mk_omega_tail_add n1 n2 d).components = (mk_omega_tail_add n2 n1 d).components := by
  rw [omega_add_components_eq, omega_add_components_eq, Nat.add_comm n1 n2]

/-- Multiplicative commutativity: n * m = m * n (on omega-tails). -/
theorem omega_mul_comm (n1 n2 d : TauIdx) :
    (mk_omega_tail_mul n1 n2 d).components = (mk_omega_tail_mul n2 n1 d).components := by
  rw [omega_mul_components_eq, omega_mul_components_eq, Nat.mul_comm n1 n2]

/-- Additive associativity: (a + b) + c = a + (b + c) (on omega-tails). -/
theorem omega_add_assoc (n1 n2 n3 d : TauIdx) :
    (mk_omega_tail_add (n1 + n2) n3 d).components =
    (mk_omega_tail_add n1 (n2 + n3) d).components := by
  rw [omega_add_components_eq, omega_add_components_eq, Nat.add_assoc]

/-- Multiplicative associativity: (a * b) * c = a * (b * c) (on omega-tails). -/
theorem omega_mul_assoc (n1 n2 n3 d : TauIdx) :
    (mk_omega_tail_mul (n1 * n2) n3 d).components =
    (mk_omega_tail_mul n1 (n2 * n3) d).components := by
  rw [omega_mul_components_eq, omega_mul_components_eq, Nat.mul_assoc]

/-- Distributivity: a * (b + c) = a*b + a*c (on omega-tails). -/
theorem omega_left_distrib (n1 n2 n3 d : TauIdx) :
    (mk_omega_tail_mul n1 (n2 + n3) d).components =
    (mk_omega_tail_add (n1 * n2) (n1 * n3) d).components := by
  rw [omega_mul_components_eq, omega_add_components_eq, Nat.left_distrib]

-- ============================================================
-- RING IDENTITY CHECKS (native_decide)
-- ============================================================

/-- Check: n + 0 = n (additive identity). -/
def add_zero_check (n d : TauIdx) : Bool :=
  (mk_omega_tail_add n 0 d).components == (mk_omega_tail n d).components

/-- Check: n * 1 = n (multiplicative identity). -/
def mul_one_check (n d : TauIdx) : Bool :=
  (mk_omega_tail_mul n 1 d).components == (mk_omega_tail n d).components

/-- Check: n + m = m + n (additive commutativity). -/
def add_comm_check (n1 n2 d : TauIdx) : Bool :=
  (mk_omega_tail_add n1 n2 d).components == (mk_omega_tail_add n2 n1 d).components

/-- Check: n * m = m * n (multiplicative commutativity). -/
def mul_comm_check (n1 n2 d : TauIdx) : Bool :=
  (mk_omega_tail_mul n1 n2 d).components == (mk_omega_tail_mul n2 n1 d).components

-- ============================================================
-- NATIVE_DECIDE VERIFICATIONS
-- ============================================================

-- Additive identity
example : add_zero_check 7 5 = true := by native_decide
example : add_zero_check 42 5 = true := by native_decide
example : add_zero_check 100 5 = true := by native_decide

-- Multiplicative identity
example : mul_one_check 7 5 = true := by native_decide
example : mul_one_check 42 5 = true := by native_decide
example : mul_one_check 100 5 = true := by native_decide

-- Commutativity
example : add_comm_check 7 42 5 = true := by native_decide
example : add_comm_check 3 100 5 = true := by native_decide
example : mul_comm_check 7 42 5 = true := by native_decide
example : mul_comm_check 3 100 5 = true := by native_decide

-- Compatible_add for canonical tails matches nat_to_tail of sum
example : (mk_omega_tail_add 7 42 5).components = (mk_omega_tail 49 5).components := by native_decide
example : (mk_omega_tail_add 100 200 5).components = (mk_omega_tail 300 5).components := by native_decide

-- Compatible_mul for canonical tails matches nat_to_tail of product
example : (mk_omega_tail_mul 7 6 5).components = (mk_omega_tail 42 5).components := by native_decide
example : (mk_omega_tail_mul 10 10 5).components = (mk_omega_tail 100 5).components := by native_decide

-- General OmegaTail.add preserves compatibility (checked via compat_check)
example : compat_check ((mk_omega_tail 7 5).add (mk_omega_tail 42 5) rfl) = true := by native_decide
example : compat_check ((mk_omega_tail 100 5).add (mk_omega_tail 200 5) rfl) = true := by native_decide

-- General OmegaTail.mul preserves compatibility
example : compat_check ((mk_omega_tail 7 5).mul (mk_omega_tail 6 5) rfl) = true := by native_decide
example : compat_check ((mk_omega_tail 10 5).mul (mk_omega_tail 10 5) rfl) = true := by native_decide

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Addition
#eval mk_omega_tail_add 7 42 5          -- should match mk_omega_tail 49 5
#eval mk_omega_tail 49 5                -- reference

-- Multiplication
#eval mk_omega_tail_mul 7 6 5           -- should match mk_omega_tail 42 5
#eval mk_omega_tail 42 5                -- reference

-- Ring identities
#eval add_zero_check 42 5               -- true
#eval mul_one_check 42 5                -- true

-- Commutativity
#eval add_comm_check 7 42 5             -- true
#eval mul_comm_check 7 42 5             -- true

end Tau.Polarity
