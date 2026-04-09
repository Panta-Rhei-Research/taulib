import TauLib.BookI.Sets.Membership
import Mathlib.Tactic.Set
import Mathlib.Tactic.Ring

/-!
# TauLib.BookI.Sets.Operations

τ-Set operations: union (lcm), intersection (gcd), and their lattice laws.

## Registry Cross-References

- [I.D32] Set Operations — `tau_union`, `tau_inter`
- [I.P11] Distributive Lattice — `tau_inter_distrib_union`

## Ground Truth Sources
- chunk_0355_M003041: gcd/lcm as meet/join in the divisibility lattice

## Mathematical Content

Under the τ-membership encoding (a ∈_τ b iff a | b):
- Intersection = gcd: d ∈_τ gcd(a,b) iff d ∈_τ a and d ∈_τ b
- Union = lcm: d ∈_τ lcm(a,b) iff d ∈_τ a or d ∈_τ b (up to closure)

The divisibility poset (Nat, |) forms a DISTRIBUTIVE LATTICE with
gcd as meet and lcm as join. The distributivity identity
gcd(a, lcm(b,c)) = lcm(gcd(a,b), gcd(a,c)) is proved in full
via a coprime decomposition argument.
-/

namespace Tau.Sets

open Tau.Denotation Tau.Coordinates

-- ============================================================
-- SET OPERATIONS [I.D32]
-- ============================================================

/-- [I.D32] τ-union: lcm encodes set union under divisibility membership. -/
def tau_union (a b : TauIdx) : TauIdx := Nat.lcm a b

/-- [I.D32] τ-intersection: gcd encodes set intersection under divisibility membership. -/
def tau_inter (a b : TauIdx) : TauIdx := idx_gcd a b

-- ============================================================
-- COMMUTATIVITY
-- ============================================================

theorem tau_union_comm (a b : TauIdx) : tau_union a b = tau_union b a :=
  Nat.lcm_comm a b

theorem tau_inter_comm (a b : TauIdx) : tau_inter a b = tau_inter b a :=
  Nat.gcd_comm a b

-- ============================================================
-- ASSOCIATIVITY
-- ============================================================

theorem tau_union_assoc (a b c : TauIdx) :
    tau_union (tau_union a b) c = tau_union a (tau_union b c) :=
  Nat.lcm_assoc a b c

theorem tau_inter_assoc (a b c : TauIdx) :
    tau_inter (tau_inter a b) c = tau_inter a (tau_inter b c) :=
  Nat.gcd_assoc a b c

-- ============================================================
-- IDEMPOTENCY
-- ============================================================

theorem tau_union_self (a : TauIdx) : tau_union a a = a := by
  unfold tau_union
  simp [Nat.lcm, Nat.gcd_self]
  by_cases ha : a = 0
  · subst ha; simp
  · rw [Nat.mul_div_cancel _ (Nat.pos_of_ne_zero ha)]

theorem tau_inter_self (a : TauIdx) : tau_inter a a = a :=
  Nat.gcd_self a

-- ============================================================
-- IDENTITY AND ABSORBING ELEMENTS
-- ============================================================

theorem tau_union_one (a : TauIdx) : tau_union 1 a = a :=
  Nat.lcm_one_left a

-- Note: The following two identities are Nat-level lattice laws.
-- They hold at the type level but 0 is NOT a valid orbit index
-- (τ-Idx = ℕ⁺ semantically). These are kept for algebraic
-- completeness of the Nat lattice structure used in proofs.

theorem tau_inter_zero (a : TauIdx) : tau_inter 0 a = a :=
  Nat.gcd_zero_left a

theorem tau_union_zero (a : TauIdx) : tau_union 0 a = 0 :=
  Nat.lcm_zero_left a

theorem tau_inter_one (a : TauIdx) : tau_inter 1 a = 1 :=
  Nat.gcd_one_left a

-- ============================================================
-- MEMBERSHIP COMPATIBILITY
-- ============================================================

theorem tau_mem_union_left (a b : TauIdx) : tau_mem a (tau_union a b) :=
  (tau_mem_iff_dvd a _).mpr (Nat.dvd_lcm_left a b)

theorem tau_mem_union_right (a b : TauIdx) : tau_mem b (tau_union a b) :=
  (tau_mem_iff_dvd b _).mpr (Nat.dvd_lcm_right a b)

theorem tau_mem_inter_left (a b : TauIdx) : tau_mem (tau_inter a b) a :=
  (tau_mem_iff_dvd _ a).mpr (idx_gcd_dvd_left a b)

theorem tau_mem_inter_right (a b : TauIdx) : tau_mem (tau_inter a b) b :=
  (tau_mem_iff_dvd _ b).mpr (idx_gcd_dvd_right a b)

theorem tau_union_dvd {a b c : TauIdx}
    (ha : tau_mem a c) (hb : tau_mem b c) : tau_mem (tau_union a b) c :=
  (tau_mem_iff_dvd _ c).mpr
    (Nat.lcm_dvd ((tau_mem_iff_dvd a c).mp ha) ((tau_mem_iff_dvd b c).mp hb))

theorem tau_inter_dvd {a b c : TauIdx}
    (ha : tau_mem c a) (hb : tau_mem c b) : tau_mem c (tau_inter a b) :=
  (tau_mem_iff_dvd c _).mpr
    (Nat.dvd_gcd ((tau_mem_iff_dvd c a).mp ha) ((tau_mem_iff_dvd c b).mp hb))

-- ============================================================
-- ABSORPTION LAWS
-- ============================================================

theorem tau_union_inter_absorb (a b : TauIdx) :
    tau_union a (tau_inter a b) = a :=
  Nat.dvd_antisymm (Nat.lcm_dvd (Nat.dvd_refl a) (Nat.gcd_dvd_left a b))
    (Nat.dvd_lcm_left a _)

theorem tau_inter_union_absorb (a b : TauIdx) :
    tau_inter a (tau_union a b) = a :=
  Nat.dvd_antisymm (Nat.gcd_dvd_left a _)
    (Nat.dvd_gcd (Nat.dvd_refl a) (Nat.dvd_lcm_left a b))

-- ============================================================
-- DISTRIBUTIVITY INFRASTRUCTURE
-- ============================================================

/-- Nat multiplication left cancellation: a > 0 and a * b = a * c implies b = c. -/
private theorem nat_mul_cancel {a b c : Nat} (ha : a > 0) (h : a * b = a * c) : b = c := by
  rcases Nat.lt_or_ge b c with hbc | hbc
  · have h1 := Nat.mul_le_mul_left a hbc
    have h2 : a * Nat.succ b = a * b + a := Nat.mul_succ a b
    omega
  · rcases Nat.lt_or_ge c b with hcb | hcb
    · have h1 := Nat.mul_le_mul_left a hcb
      have h2 : a * Nat.succ c = a * c + a := Nat.mul_succ a c
      omega
    · omega

/-- Cancel a positive factor from divisibility: k > 0 and k*a | k*b implies a | b. -/
private theorem nat_mul_dvd_cancel {k a b : Nat} (hk : k > 0) (h : k * a ∣ k * b) : a ∣ b := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, nat_mul_cancel hk (by rw [hc, Nat.mul_assoc])⟩

/-- Helper: gcd(gcd(a,b), gcd(a,c)) = gcd(a, gcd(b,c)). -/
private theorem gcd_gcd_eq (a b c : Nat) :
    Nat.gcd (Nat.gcd a b) (Nat.gcd a c) = Nat.gcd a (Nat.gcd b c) := by
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd
    · exact Nat.dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left _ _)
    · exact Nat.dvd_gcd
        (Nat.dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _))
        (Nat.dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_right _ _))
  · apply Nat.dvd_gcd
    · exact Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
        (Nat.dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _))
    · exact Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
        (Nat.dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_right _ _))

/-- The coprime-case proof for distributivity. When a > 0 and gcd(a, gcd(b,c)) = 1,
    we show gcd(a, lcm(b,c)) = gcd(a,b) * gcd(a,c).

    Requires a > 0 to guarantee P = gcd(a,b)*gcd(a,c) > 0, avoiding
    degenerate cases. The a = 0 case is handled separately in nat_gcd_distrib_lcm. -/
private theorem distrib_coprime (a b c : Nat) (ha : a > 0)
    (h_coprime : Nat.Coprime a (Nat.gcd b c)) :
    Nat.gcd a (Nat.lcm b c) = Nat.gcd a b * Nat.gcd a c := by
  have hcop_parts : Nat.Coprime (Nat.gcd a b) (Nat.gcd a c) := by
    show Nat.gcd (Nat.gcd a b) (Nat.gcd a c) = 1; rw [gcd_gcd_eq]; exact h_coprime
  -- P = gcd(a,b) * gcd(a,c) > 0 since a > 0 implies gcd(a,b) ≥ 1 and gcd(a,c) ≥ 1
  set P := Nat.gcd a b * Nat.gcd a c with hP_def
  have hgab_pos : Nat.gcd a b > 0 := Nat.pos_of_ne_zero (fun h => by
    have := Nat.gcd_eq_zero_iff.mp h; omega)
  have hgac_pos : Nat.gcd a c > 0 := Nat.pos_of_ne_zero (fun h => by
    have := Nat.gcd_eq_zero_iff.mp h; omega)
  have hPpos : P > 0 := Nat.mul_pos hgab_pos hgac_pos
  have hPa : P ∣ a := hcop_parts.mul_dvd_of_dvd_of_dvd (Nat.gcd_dvd_left a b) (Nat.gcd_dvd_left a c)
  have hPl : P ∣ Nat.lcm b c := hcop_parts.mul_dvd_of_dvd_of_dvd
    (Nat.dvd_trans (Nat.gcd_dvd_right a b) (Nat.dvd_lcm_left b c))
    (Nat.dvd_trans (Nat.gcd_dvd_right a c) (Nat.dvd_lcm_right b c))
  obtain ⟨m, hm⟩ := hPa
  obtain ⟨n, hn⟩ := hPl
  have h_gcd : Nat.gcd a (Nat.lcm b c) = P * Nat.gcd m n := by rw [hm, hn, Nat.gcd_mul_left]
  rw [h_gcd]; suffices Nat.gcd m n = 1 by rw [this, Nat.mul_one]
  obtain ⟨b', hb'⟩ := Nat.gcd_dvd_right a b
  obtain ⟨c', hc'⟩ := Nat.gcd_dvd_right a c
  -- coprime(gcd(a,c)*m, b'): factor through gcd(a, b) = gcd(a,b) * gcd(gcd(a,c)*m, b')
  have h_cop1 : Nat.Coprime (Nat.gcd a c * m) b' := by
    have hm_expand : a = Nat.gcd a b * (Nat.gcd a c * m) := by
      rw [← Nat.mul_assoc]; exact hm
    have h_factor : Nat.gcd a b * Nat.gcd (Nat.gcd a c * m) b' = Nat.gcd a b := by
      rw [← Nat.gcd_mul_left, ← hm_expand, ← hb']
    have : Nat.gcd a b * 1 = Nat.gcd a b * Nat.gcd (Nat.gcd a c * m) b' := by
      rw [Nat.mul_one]; exact h_factor.symm
    exact (nat_mul_cancel hgab_pos this).symm
  -- coprime(gcd(a,b)*m, c'): symmetric argument
  have h_cop2 : Nat.Coprime (Nat.gcd a b * m) c' := by
    have hm_expand : a = Nat.gcd a c * (Nat.gcd a b * m) := by
      have : a = P * m := hm; rw [hP_def] at this
      calc a = Nat.gcd a b * Nat.gcd a c * m := this
        _ = Nat.gcd a c * Nat.gcd a b * m := by ring
        _ = Nat.gcd a c * (Nat.gcd a b * m) := by ring
    have h_factor : Nat.gcd a c * Nat.gcd (Nat.gcd a b * m) c' = Nat.gcd a c := by
      rw [← Nat.gcd_mul_left, ← hm_expand, ← hc']
    have : Nat.gcd a c * 1 = Nat.gcd a c * Nat.gcd (Nat.gcd a b * m) c' := by
      rw [Nat.mul_one]; exact h_factor.symm
    exact (nat_mul_cancel hgac_pos this).symm
  have h_m_b' : Nat.Coprime m b' := h_cop1.coprime_dvd_left (Nat.dvd_mul_left m _)
  have h_m_c' : Nat.Coprime m c' := h_cop2.coprime_dvd_left (Nat.dvd_mul_left m _)
  have h_m_prod : Nat.Coprime m (b' * c') := h_m_b'.mul_right h_m_c'
  have h_n_dvd : n ∣ b' * c' := by
    apply nat_mul_dvd_cancel hPpos
    show P * n ∣ P * (b' * c')
    have hn' : P * n = Nat.lcm b c := hn.symm
    rw [hn']
    calc Nat.lcm b c ∣ b * c := by
            rw [show b * c = Nat.gcd b c * Nat.lcm b c from (Nat.gcd_mul_lcm b c).symm]
            exact Nat.dvd_mul_left _ _
      _ = Nat.gcd a b * b' * (Nat.gcd a c * c') := by rw [← hb', ← hc']
      _ = P * (b' * c') := by rw [hP_def]; ring
  have : Nat.gcd m n ∣ Nat.gcd m (b' * c') :=
    Nat.dvd_gcd (Nat.gcd_dvd_left m n) (Nat.dvd_trans (Nat.gcd_dvd_right m n) h_n_dvd)
  rw [h_m_prod] at this
  exact Nat.eq_one_of_dvd_one this

/-- gcd distributes over lcm for Nat (the core identity).
    gcd(a, lcm(b,c)) = lcm(gcd(a,b), gcd(a,c)). -/
private theorem nat_gcd_distrib_lcm (a b c : Nat) :
    Nat.gcd a (Nat.lcm b c) = Nat.lcm (Nat.gcd a b) (Nat.gcd a c) := by
  -- Handle a = 0 case directly (everything collapses)
  by_cases ha : a = 0
  · subst ha; simp [Nat.gcd_zero_left]
  -- Factor out G = gcd(a, gcd(b,c))
  set G := Nat.gcd a (Nat.gcd b c) with hG_def
  have hG_pos : G > 0 := by
    apply Nat.pos_of_ne_zero; intro hG0
    rw [Nat.gcd_eq_zero_iff] at hG0; exact ha hG0.1
  have hGa : G ∣ a := Nat.gcd_dvd_left a _
  have hGb : G ∣ b := Nat.dvd_trans (Nat.gcd_dvd_right a _) (Nat.gcd_dvd_left b c)
  have hGc : G ∣ c := Nat.dvd_trans (Nat.gcd_dvd_right a _) (Nat.gcd_dvd_right b c)
  obtain ⟨a', ha'⟩ := hGa
  obtain ⟨b', hb'⟩ := hGb
  obtain ⟨c', hc'⟩ := hGc
  have h_lhs : Nat.gcd a (Nat.lcm b c) = G * Nat.gcd a' (Nat.lcm b' c') := by
    rw [ha', hb', hc', Nat.lcm_mul_left, Nat.gcd_mul_left]
  have h_rhs : Nat.lcm (Nat.gcd a b) (Nat.gcd a c) =
      G * Nat.lcm (Nat.gcd a' b') (Nat.gcd a' c') := by
    rw [ha', hb', hc', Nat.gcd_mul_left, Nat.gcd_mul_left, Nat.lcm_mul_left]
  rw [h_lhs, h_rhs]; congr 1
  -- Coprime case: gcd(a', gcd(b',c')) = 1
  have h_coprime : Nat.Coprime a' (Nat.gcd b' c') := by
    show Nat.gcd a' (Nat.gcd b' c') = 1
    have h_eq : G * Nat.gcd a' (Nat.gcd b' c') = G * 1 := by
      rw [Nat.mul_one, ← Nat.gcd_mul_left, ← Nat.gcd_mul_left, ← ha', ← hb', ← hc']
    exact nat_mul_cancel hG_pos h_eq
  have ha'_pos : a' > 0 := Nat.pos_of_ne_zero (fun h => by
    rw [h, Nat.mul_zero] at ha'; exact ha ha')
  have h_dist := distrib_coprime a' b' c' ha'_pos h_coprime
  have hcop_parts : Nat.Coprime (Nat.gcd a' b') (Nat.gcd a' c') := by
    show Nat.gcd (Nat.gcd a' b') (Nat.gcd a' c') = 1; rw [gcd_gcd_eq]; exact h_coprime
  have h_lcm_prod : Nat.lcm (Nat.gcd a' b') (Nat.gcd a' c') = Nat.gcd a' b' * Nat.gcd a' c' := by
    have := (Nat.gcd_mul_lcm (Nat.gcd a' b') (Nat.gcd a' c')).symm
    rw [hcop_parts, Nat.one_mul] at this; exact this.symm
  rw [h_lcm_prod, ← h_dist]

-- ============================================================
-- DISTRIBUTIVITY [I.P11]
-- ============================================================

/-- [I.P11] Distributive Lattice: gcd distributes over lcm.
    gcd(a, lcm(b,c)) = lcm(gcd(a,b), gcd(a,c)). -/
theorem tau_inter_distrib_union (a b c : TauIdx) :
    tau_inter a (tau_union b c) = tau_union (tau_inter a b) (tau_inter a c) := by
  unfold tau_inter tau_union idx_gcd
  exact nat_gcd_distrib_lcm a b c

-- ============================================================
-- BRIDGE: DUAL DISTRIBUTIVITY
-- ============================================================

/-- Dual distributivity: lcm distributes over gcd.
    lcm(a, gcd(b,c)) = gcd(lcm(a,b), lcm(a,c)). -/
theorem tau_union_distrib_inter (a b c : TauIdx) :
    tau_union a (tau_inter b c) = tau_inter (tau_union a b) (tau_union a c) := by
  unfold tau_union tau_inter idx_gcd
  show Nat.lcm a (Nat.gcd b c) = Nat.gcd (Nat.lcm a b) (Nat.lcm a c)
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd
    · exact Nat.lcm_dvd (Nat.dvd_lcm_left a b)
        (Nat.dvd_trans (Nat.gcd_dvd_left b c) (Nat.dvd_lcm_right a b))
    · exact Nat.lcm_dvd (Nat.dvd_lcm_left a c)
        (Nat.dvd_trans (Nat.gcd_dvd_right b c) (Nat.dvd_lcm_right a c))
  · have h_dist1 := nat_gcd_distrib_lcm (Nat.lcm a b) a c
    rw [h_dist1]
    have h_abs1 : Nat.gcd (Nat.lcm a b) a = a := by
      rw [Nat.gcd_comm]
      exact Nat.dvd_antisymm (Nat.gcd_dvd_left a _)
        (Nat.dvd_gcd (Nat.dvd_refl a) (Nat.dvd_lcm_left a b))
    rw [h_abs1]
    have h_dist2 : Nat.gcd (Nat.lcm a b) c = Nat.lcm (Nat.gcd c a) (Nat.gcd c b) := by
      rw [Nat.gcd_comm]; exact nat_gcd_distrib_lcm c a b
    rw [h_dist2, ← Nat.lcm_assoc]
    have h_abs2 : Nat.lcm a (Nat.gcd c a) = a := by
      rw [Nat.gcd_comm]
      exact Nat.dvd_antisymm
        (Nat.lcm_dvd (Nat.dvd_refl a) (Nat.gcd_dvd_left a c))
        (Nat.dvd_lcm_left a _)
    rw [h_abs2, Nat.gcd_comm c b]

-- ============================================================
-- SMOKE TESTS
-- ============================================================

#eval tau_union 4 6       -- expected: 12 (lcm)
#eval tau_inter 12 8      -- expected: 4  (gcd)
#eval tau_union 3 5       -- expected: 15
#eval tau_inter 15 10     -- expected: 5

end Tau.Sets
