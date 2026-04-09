import TauLib.BookI.Polarity.OmegaRing
import TauLib.BookI.Polarity.CRTBasis
import TauLib.BookI.Polarity.TeichmuellerLift

/-!
# TauLib.BookI.Boundary.Ring

Boundary ring negation and the full ring axiom suite for omega-tails.

## Registry Cross-References

- [I.D28] Boundary Local Ring — `BdryRing`, `mk_omega_tail_neg`

## Ground Truth Sources
- chunk_0243_M002286: Boundary ring with levelwise addition/multiplication
- chunk_0314_M002691: Negation, additive inverse, ring axiom collection

## Mathematical Content

The boundary ring Z_hat_tau = lim Z/M_kZ carries componentwise ring operations.
This module extends OmegaRing with:
- Negation: neg(x)_k = (M_k - x_k) mod M_k
- Additive inverse: x + neg(x) = 0
- Double negation: neg(neg(x)) = x
- Full ring axiom collection: add_comm, add_assoc, add_zero, add_neg,
  mul_comm, mul_assoc, mul_one, left_distrib
-/

namespace Tau.Boundary

open Tau.Denotation Tau.Polarity

-- ============================================================
-- TYPE ALIAS
-- ============================================================

/-- Boundary ring element: an omega-tail in the primorial tower. -/
abbrev BdryRing := OmegaTail

-- ============================================================
-- UTILITY
-- ============================================================

private theorem getD_eq_getElem (l : List TauIdx) (i : Nat) (d : TauIdx) (h : i < l.length) :
    l.getD i d = l[i] := by
  simp [List.getD, h]

-- ============================================================
-- CORE MODULAR NEGATION IDENTITY
-- ============================================================

/-- Helper: m * (c + 1) = m * c + m. Used to avoid non-linear omega goals. -/
private theorem mul_succ_eq (m c : Nat) : m * (c + 1) = m * c + m := by
  ring

/-- Helper: (m * c - a) % m = (m - a % m) % m when a ≤ m * c and m > 0.
    Proof by induction on c. -/
private theorem mul_sub_mod (m : Nat) (hm : m > 0) :
    ∀ (c a : Nat), a ≤ m * c → (m * c - a) % m = (m - a % m) % m := by
  intro c
  induction c with
  | zero =>
    intro a ha
    simp only [Nat.mul_zero, Nat.le_zero] at ha
    subst ha; simp
  | succ c' ih =>
    intro a ha
    by_cases ham : a ≤ m * c'
    · -- a ≤ m * c': strip one copy of m
      have h1 : m * (c' + 1) - a = m * c' - a + m := by
        have := mul_succ_eq m c'
        omega
      rw [h1, Nat.add_mod_right]
      exact ih a ham
    · -- a > m * c': a is in the last "block" [m*c', m*(c'+1)]
      push_neg at ham
      -- a - m*c' is in range (0, m]
      have h_diff_bound : a - m * c' ≤ m := by
        have := mul_succ_eq m c'; omega
      have h_diff_pos : a - m * c' > 0 := by omega
      -- m*(c'+1) - a = m - (a - m*c')
      have h_rhs : m * (c' + 1) - a = m - (a - m * c') := by
        have := mul_succ_eq m c'; omega
      rw [h_rhs]
      -- a % m = (a - m*c') % m because a = m*c' + (a - m*c')
      have hmod : a % m = (a - m * c') % m := by
        have ha_split : a = a - m * c' + m * c' := by omega
        conv_lhs => rw [ha_split]
        exact Nat.add_mul_mod_self_left (a - m * c') m c'
      rw [hmod]
      -- case split: a - m*c' = m or < m
      by_cases heq : a - m * c' = m
      · -- a - m*c' = m: both sides become 0
        rw [heq]
        -- Goal: (m - m) % m = (m - m % m) % m
        simp [Nat.mod_self]
      · have hlt : a - m * c' < m := by omega
        rw [Nat.mod_eq_of_lt hlt]

/-- Core identity: (M_d - n%M_d) % M_k = (M_k - n%M_k) % M_k when M_k | M_d.
    Proof: factor M_d = M_k * c, apply mul_sub_mod, then use mod_mod_of_dvd. -/
private theorem neg_mod_dvd (n : Nat) {k d : Nat} (hdvd : primorial k ∣ primorial d) :
    (primorial d - n % primorial d) % primorial k =
    (primorial k - n % primorial k) % primorial k := by
  have hpos_k : primorial k > 0 := primorial_pos k
  have hpos_d : primorial d > 0 := primorial_pos d
  have hn_lt : n % primorial d < primorial d := Nat.mod_lt n hpos_d
  obtain ⟨c, hc⟩ := hdvd
  -- Rewrite LHS using M_d = M_k * c
  rw [show primorial d = primorial k * c from hc] at hn_lt ⊢
  -- Goal: (M_k*c - n%(M_k*c)) % M_k = (M_k - n%M_k) % M_k
  rw [mul_sub_mod (primorial k) hpos_k c _ (Nat.le_of_lt hn_lt)]
  -- Goal: (M_k - (n%(M_k*c)) % M_k) % M_k = (M_k - n%M_k) % M_k
  rw [mod_mod_of_dvd n (primorial k) (primorial k * c) ⟨c, rfl⟩]

-- ============================================================
-- COMPONENTWISE NEGATION
-- ============================================================

private def omega_neg_list (n : Nat) : Nat -> List TauIdx
  | 0 => []
  | d + 1 => omega_neg_list n d ++ [(primorial (d + 1) - reduce n (d + 1)) % primorial (d + 1)]

private theorem omega_neg_list_length (n d : Nat) : (omega_neg_list n d).length = d := by
  induction d with
  | zero => rfl
  | succ d' ih => simp [omega_neg_list, ih]

/-- Omega-tail negation via canonical embedding. -/
def mk_omega_tail_neg (n d : TauIdx) : OmegaTail :=
  { depth := d
    components := omega_neg_list n d
    depth_eq := omega_neg_list_length n d }

private theorem omega_neg_list_getD (n d i : Nat) (hi : i < d) :
    (omega_neg_list n d).getD i 0 =
    (primorial (i + 1) - reduce n (i + 1)) % primorial (i + 1) := by
  rw [getD_eq_getElem _ _ _ (by rw [omega_neg_list_length]; exact hi)]
  induction d generalizing i with
  | zero => omega
  | succ d' ih =>
    simp only [omega_neg_list]
    by_cases hi' : i < d'
    · rw [List.getElem_append_left (by rw [omega_neg_list_length]; exact hi')]
      exact ih i hi'
    · have hid : i = d' := by omega
      subst hid
      rw [List.getElem_append_right (by simp [omega_neg_list_length])]
      simp [omega_neg_list_length]

/-- Negation reduces to standard negation: componentwise neg = global neg mod M_k. -/
private theorem omega_neg_eq_reduce (n d i : Nat) (hi : i < d) :
    (omega_neg_list n d).getD i 0 = reduce ((primorial d - n % primorial d) % primorial d) (i + 1) := by
  rw [omega_neg_list_getD n d i hi]
  simp only [reduce]
  rw [mod_mod_of_dvd _ _ _ (primorial_dvd (show i + 1 ≤ d by omega))]
  exact (neg_mod_dvd n (primorial_dvd (show i + 1 ≤ d by omega))).symm

-- ============================================================
-- NEGATION BRIDGE
-- ============================================================

/-- Bridge: componentwise negation produces the negation representative at each stage. -/
theorem omega_neg_components_eq (n d : TauIdx) :
    (mk_omega_tail_neg n d).components =
    (mk_omega_tail ((primorial d - n % primorial d) % primorial d) d).components := by
  have hlen : (mk_omega_tail_neg n d).components.length =
              (mk_omega_tail ((primorial d - n % primorial d) % primorial d) d).components.length :=
    (mk_omega_tail_neg n d).depth_eq.trans
      (mk_omega_tail ((primorial d - n % primorial d) % primorial d) d).depth_eq.symm
  apply List.ext_getElem hlen
  intro i h1 h2
  have hi : i < d := by rw [(mk_omega_tail_neg n d).depth_eq] at h1; exact h1
  rw [← getD_eq_getElem _ i 0 h1, ← getD_eq_getElem _ i 0 h2]
  show (omega_neg_list n d).getD i 0 = _
  rw [omega_neg_eq_reduce n d i hi, mk_omega_tail_getD _ d i hi]

-- ============================================================
-- COMPATIBILITY OF NEGATION
-- ============================================================

/-- Negation of canonical tails is compatible. -/
theorem Compatible_neg (n d : TauIdx) : Compatible (mk_omega_tail_neg n d) := by
  intro k l hk hkl hld
  dsimp only [mk_omega_tail_neg, Compatible] at *
  have hl : l - 1 < d := by simp only [TauIdx] at *; omega
  have hk' : k - 1 < d := by simp only [TauIdx] at *; omega
  rw [omega_neg_list_getD n d (l - 1) hl, omega_neg_list_getD n d (k - 1) hk']
  have hl1 : l - 1 + 1 = l := by simp only [TauIdx] at *; omega
  have hk1 : k - 1 + 1 = k := by simp only [TauIdx] at *; omega
  rw [hl1, hk1]
  simp only [reduce]
  rw [mod_mod_of_dvd _ _ _ (primorial_dvd hkl)]
  exact neg_mod_dvd n (primorial_dvd hkl)

-- ============================================================
-- NEGATION INVOLUTION
-- ============================================================

/-- Double negation on Nat mod: (M - (M - x%M)%M) % M = x%M. -/
private theorem double_neg_mod (x M : Nat) (hM : M > 0) :
    (M - (M - x % M) % M) % M = x % M := by
  have hxm : x % M < M := Nat.mod_lt x hM
  by_cases h0 : x % M = 0
  · rw [h0, Nat.sub_zero, Nat.mod_self, Nat.sub_zero, Nat.mod_self]
  · have hpos : x % M > 0 := Nat.pos_of_ne_zero h0
    have h1 : M - x % M < M := by omega
    rw [Nat.mod_eq_of_lt h1]
    have h2 : M - (M - x % M) = x % M := by omega
    rw [h2]
    exact Nat.mod_eq_of_lt hxm

/-- Double negation is identity: neg(neg(n)) has the same components as n. -/
theorem omega_neg_neg_eq (n d : TauIdx) :
    ∀ (i : Nat), i < d →
    (omega_neg_list ((primorial d - n % primorial d) % primorial d) d).getD i 0 =
    (mk_omega_tail n d).components.getD i 0 := by
  intro i hi
  rw [omega_neg_list_getD _ d i hi]
  rw [mk_omega_tail_getD n d i hi]
  unfold reduce
  have hidvd : primorial (i + 1) ∣ primorial d := primorial_dvd (show i + 1 ≤ d by omega)
  rw [mod_mod_of_dvd _ _ _ hidvd]
  rw [neg_mod_dvd n hidvd]
  exact double_neg_mod n (primorial (i + 1)) (primorial_pos (i + 1))

-- ============================================================
-- ADDITIVE INVERSE
-- ============================================================

/-- x + (M - x%M)%M = 0 (mod M). -/
private theorem add_neg_cancel_mod (x M : Nat) (hM : M > 0) :
    (x % M + (M - x % M) % M) % M = 0 := by
  have hxm : x % M < M := Nat.mod_lt x hM
  by_cases h0 : x % M = 0
  · rw [h0, Nat.sub_zero, Nat.mod_self, Nat.add_zero, Nat.zero_mod]
  · have hpos : x % M > 0 := Nat.pos_of_ne_zero h0
    have h1 : M - x % M < M := by omega
    rw [Nat.mod_eq_of_lt h1]
    have h2 : x % M + (M - x % M) = M := by omega
    rw [h2]
    exact Nat.mod_self M

/-- Additive inverse: n + neg(n) = 0 (on components). -/
theorem omega_add_neg_cancel (n d : TauIdx) :
    ∀ (i : Nat), i < d →
    (mk_omega_tail_add n ((primorial d - n % primorial d) % primorial d) d).components.getD i 0 =
    (mk_omega_zero d).components.getD i 0 := by
  intro i hi
  have h_add := omega_add_components_eq n ((primorial d - n % primorial d) % primorial d) d
  rw [show (mk_omega_tail_add n ((primorial d - n % primorial d) % primorial d) d).components.getD i 0 =
    (mk_omega_tail (n + (primorial d - n % primorial d) % primorial d) d).components.getD i 0 from
    congrArg (fun l => l.getD i 0) h_add]
  rw [mk_omega_tail_getD _ d i hi]
  rw [show (mk_omega_zero d) = mk_omega_tail 0 d from rfl]
  rw [mk_omega_tail_getD 0 d i hi]
  unfold reduce
  rw [show (0 : Nat) % primorial (i + 1) = 0 from Nat.zero_mod _]
  have hidvd : primorial (i + 1) ∣ primorial d := primorial_dvd (show i + 1 ≤ d by omega)
  rw [Nat.add_mod n _ (primorial (i + 1))]
  rw [mod_mod_of_dvd _ _ _ hidvd]
  rw [neg_mod_dvd n hidvd]
  exact add_neg_cancel_mod n (primorial (i + 1)) (primorial_pos (i + 1))

-- ============================================================
-- RING AXIOM COLLECTION
-- ============================================================

/-- Full boundary ring axioms: all eight ring properties, proved universally. -/
theorem bdry_ring_axioms :
    (∀ (n1 n2 d : TauIdx),
      (mk_omega_tail_add n1 n2 d).components = (mk_omega_tail_add n2 n1 d).components) ∧
    (∀ (n1 n2 n3 d : TauIdx),
      (mk_omega_tail_add (n1 + n2) n3 d).components =
      (mk_omega_tail_add n1 (n2 + n3) d).components) ∧
    (∀ (n d : TauIdx),
      (mk_omega_tail_add n 0 d).components = (mk_omega_tail n d).components) ∧
    (∀ (n d : TauIdx) (i : Nat), i < d →
      (mk_omega_tail_add n ((primorial d - n % primorial d) % primorial d) d).components.getD i 0 =
      (mk_omega_zero d).components.getD i 0) ∧
    (∀ (n1 n2 d : TauIdx),
      (mk_omega_tail_mul n1 n2 d).components = (mk_omega_tail_mul n2 n1 d).components) ∧
    (∀ (n1 n2 n3 d : TauIdx),
      (mk_omega_tail_mul (n1 * n2) n3 d).components =
      (mk_omega_tail_mul n1 (n2 * n3) d).components) ∧
    (∀ (n d : TauIdx),
      (mk_omega_tail_mul n 1 d).components = (mk_omega_tail n d).components) ∧
    (∀ (n1 n2 n3 d : TauIdx),
      (mk_omega_tail_mul n1 (n2 + n3) d).components =
      (mk_omega_tail_add (n1 * n2) (n1 * n3) d).components) :=
  ⟨omega_add_comm, omega_add_assoc, omega_add_zero, omega_add_neg_cancel,
   omega_mul_comm, omega_mul_assoc, omega_mul_one, omega_left_distrib⟩

-- ============================================================
-- BOOL-LEVEL CHECKS
-- ============================================================

def neg_compat_check (n d : TauIdx) : Bool :=
  compat_check (mk_omega_tail_neg n d)

def add_neg_check (n d : TauIdx) : Bool :=
  let neg_rep := (primorial d - n % primorial d) % primorial d
  (mk_omega_tail_add n neg_rep d).components == (mk_omega_zero d).components

def double_neg_check (n d : TauIdx) : Bool :=
  let neg_rep := (primorial d - n % primorial d) % primorial d
  let neg_neg_rep := (primorial d - neg_rep % primorial d) % primorial d
  (mk_omega_tail neg_neg_rep d).components == (mk_omega_tail n d).components

-- ============================================================
-- NATIVE_DECIDE VERIFICATIONS
-- ============================================================

example : neg_compat_check 7 5 = true := by native_decide
example : neg_compat_check 42 5 = true := by native_decide
example : neg_compat_check 100 5 = true := by native_decide
example : neg_compat_check 0 5 = true := by native_decide

example : add_neg_check 7 5 = true := by native_decide
example : add_neg_check 42 5 = true := by native_decide
example : add_neg_check 100 5 = true := by native_decide
example : add_neg_check 0 5 = true := by native_decide
example : add_neg_check 1 5 = true := by native_decide

example : double_neg_check 7 5 = true := by native_decide
example : double_neg_check 42 5 = true := by native_decide
example : double_neg_check 100 5 = true := by native_decide
example : double_neg_check 0 5 = true := by native_decide

-- ============================================================
-- SMOKE TESTS
-- ============================================================

#eval mk_omega_tail_neg 7 5
#eval mk_omega_tail_neg 42 5
#eval mk_omega_tail_neg 0 5
#eval add_neg_check 7 5
#eval add_neg_check 42 5
#eval add_neg_check 100 5
#eval double_neg_check 7 5
#eval double_neg_check 42 5
#eval neg_compat_check 7 5
#eval neg_compat_check 42 5

end Tau.Boundary
