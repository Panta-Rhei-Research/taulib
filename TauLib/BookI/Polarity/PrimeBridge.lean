import TauLib.BookI.Coordinates.Primes

/-!
# TauLib.BookI.Polarity.PrimeBridge

Reflection lemma: `is_prime_bool p = true ↔ idx_prime p`.

Bridges computable Boolean primality (`is_prime_bool`) to the propositional
definition (`idx_prime`). This is the foundational link needed for the CRT
formal proof chain.

## Main Results

- `no_factor_below_true_imp`: forward correctness of trial division
- `no_factor_below_of_spec`: backward correctness of trial division
- `is_prime_bool_iff`: the reflection lemma
-/

namespace Tau.Polarity

open Tau.Denotation Tau.Coordinates

-- ============================================================
-- NO_FACTOR_BELOW: FORWARD DIRECTION
-- ============================================================

private theorem no_factor_below_true_aux (n : TauIdx) (hn : n ≥ 2) :
    ∀ fuel : Nat, ∀ d : TauIdx, fuel = n - d → d ≥ 2 →
    no_factor_below n d = true →
    ∀ k : TauIdx, k ≥ d → k * k ≤ n → n % k ≠ 0 := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ fuel ih =>
  intro d hfuel hd h k hkd hkk
  unfold no_factor_below at h
  split at h
  · -- d ≥ n: k ≥ d ≥ n, so k*k ≥ n*n > n (since n ≥ 2)
    rename_i hdn
    have hkn : k ≥ n := Nat.le_trans hdn hkd
    have : n * n ≤ k * k := Nat.mul_le_mul hkn hkn
    -- n * n ≤ k * k ≤ n, but n * n > n for n ≥ 2
    have hnn : n * n ≤ n := Nat.le_trans this hkk
    have hnn1 : n * n ≤ n * 1 := by rwa [Nat.mul_one]
    have : n ≤ 1 := Nat.le_of_mul_le_mul_left hnn1 (by simp only [TauIdx] at *; omega)
    simp only [TauIdx] at *; omega
  · split at h
    · -- d * d > n: k ≥ d, so k*k ≥ d*d > n, contradiction
      rename_i hdn hdd
      have : d * d ≤ k * k := Nat.mul_le_mul hkd hkd
      simp only [TauIdx] at *; omega
    · split at h
      · -- n % d = 0: returns false, contradicts h
        exact absurd h Bool.false_ne_true
      · -- Recursive case: ¬(n % d = 0), h : no_factor_below n (d+1) = true
        rename_i hdn hdd hmod
        -- hmod : ¬(n % d = 0)
        rcases Nat.eq_or_lt_of_le hkd with rfl | hlt
        · -- k = d: n % d ≠ 0
          exact hmod
        · -- k > d, so k ≥ d + 1: recurse
          have hfuel_lt : n - (d + 1) < fuel := by
            rw [hfuel]; simp only [TauIdx] at *; omega
          exact ih (n - (d + 1)) hfuel_lt (d + 1) rfl
              (by simp only [TauIdx] at *; omega) h k hlt hkk

/-- If no_factor_below n d = true, then no k in [d, √n] divides n. -/
theorem no_factor_below_true_imp (n d : TauIdx) (hn : n ≥ 2) (hd : d ≥ 2)
    (h : no_factor_below n d = true) :
    ∀ k : TauIdx, k ≥ d → k * k ≤ n → n % k ≠ 0 :=
  no_factor_below_true_aux n hn (n - d) d rfl hd h

-- ============================================================
-- NO_FACTOR_BELOW: BACKWARD DIRECTION
-- ============================================================

private theorem no_factor_below_of_spec_aux (n : TauIdx) (hn : n ≥ 2) :
    ∀ fuel : Nat, ∀ d : TauIdx, fuel = n - d → d ≥ 2 →
    (∀ k : TauIdx, k ≥ d → k * k ≤ n → n % k ≠ 0) →
    no_factor_below n d = true := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ fuel ih =>
  intro d hfuel hd hspec
  unfold no_factor_below
  split
  · rfl  -- d ≥ n
  · rename_i hdn
    split
    · rfl  -- d * d > n
    · rename_i hdd
      have hle : d * d ≤ n := by simp only [TauIdx] at *; omega
      have hmod : n % d ≠ 0 := hspec d (Nat.le_refl d) hle
      split
      · -- n % d = 0: contradiction with hmod
        rename_i hmod0
        exact absurd hmod0 hmod
      · -- Recurse with d + 1
        have hfuel_lt : n - (d + 1) < fuel := by
          rw [hfuel]; simp only [TauIdx] at *; omega
        exact ih (n - (d + 1)) hfuel_lt (d + 1) rfl
            (by simp only [TauIdx] at *; omega)
            (fun k hk hkk => hspec k (by simp only [TauIdx] at *; omega) hkk)

/-- If no k in [d, √n] divides n, then no_factor_below n d = true. -/
theorem no_factor_below_of_spec (n d : TauIdx) (hn : n ≥ 2) (hd : d ≥ 2)
    (hspec : ∀ k : TauIdx, k ≥ d → k * k ≤ n → n % k ≠ 0) :
    no_factor_below n d = true :=
  no_factor_below_of_spec_aux n hn (n - d) d rfl hd hspec

-- ============================================================
-- IS_PRIME_BOOL REFLECTION: FORWARD
-- ============================================================

/-- Forward: is_prime_bool p = true → idx_prime p. -/
theorem is_prime_of_bool (p : TauIdx) (h : is_prime_bool p = true) : idx_prime p := by
  unfold is_prime_bool at h
  have hp2 : p ≥ 2 := by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1
  have hnfb : no_factor_below p 2 = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h.2
  constructor
  · exact hp2
  · intro d hd
    by_cases hd1 : d = 1
    · exact Or.inl hd1
    · by_cases hdp : d = p
      · exact Or.inr hdp
      · exfalso
        have hd0 : d ≠ 0 := by
          intro heq; subst heq; obtain ⟨k, hk⟩ := hd
          simp only [Nat.zero_mul] at hk; simp only [TauIdx] at hp2; omega
        have hd2 : d ≥ 2 := by
          rcases d with _ | _ | d
          · exact absurd rfl hd0
          · exact absurd rfl hd1
          · exact Nat.le_add_left 2 d
        have hddvd : d ∣ p := hd
        obtain ⟨q, hq⟩ := hd
        have hq2 : q ≥ 2 := by
          rcases q with _ | _ | q
          · simp only [TauIdx] at *; omega
          · simp only [TauIdx] at *; omega
          · exact Nat.le_add_left 2 q
        have hno := no_factor_below_true_imp p 2 hp2 (Nat.le_refl 2) hnfb
        by_cases hdq : d ≤ q
        · -- d*d ≤ d*q = p
          have hsq : d * d ≤ p := by rw [hq]; exact Nat.mul_le_mul_left d hdq
          have hmod : p % d = 0 := by
            obtain ⟨k, hk⟩ := hddvd; rw [hk, Nat.mul_mod_right]
          exact hno d hd2 hsq hmod
        · -- q < d, so q*q ≤ q*d ≤ d*q = p
          have hqd : q ≤ d := by simp only [TauIdx] at *; omega
          have hsq : q * q ≤ p := by
            calc q * q ≤ q * d := Nat.mul_le_mul_left q hqd
              _ = d * q := Nat.mul_comm q d
              _ = p := hq.symm
          have hmod : p % q = 0 := by
            rw [hq, Nat.mul_comm d q, Nat.mul_mod_right]
          exact hno q hq2 hsq hmod

-- ============================================================
-- IS_PRIME_BOOL REFLECTION: BACKWARD
-- ============================================================

/-- Backward: idx_prime p → is_prime_bool p = true. -/
theorem bool_of_is_prime (p : TauIdx) (h : idx_prime p) : is_prime_bool p = true := by
  unfold is_prime_bool
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨h.1, no_factor_below_of_spec p 2 h.1 (Nat.le_refl 2) fun k hk2 hkk hmod => ?_⟩
  have hkdvd : k ∣ p := Nat.dvd_of_mod_eq_zero hmod
  rcases h.2 k hkdvd with hk1 | hkp
  · -- k = 1 contradicts k ≥ 2
    simp only [TauIdx] at *; omega
  · -- k = p: k*k ≤ p with k = p contradicts p ≥ 2
    rw [hkp] at hkk
    have hp0 : p > 0 := by simp only [TauIdx] at *; omega
    have hkk' : p * p ≤ p * 1 := by rwa [Nat.mul_one]
    have := Nat.le_of_mul_le_mul_left hkk' hp0
    simp only [TauIdx] at *; omega

-- ============================================================
-- MAIN REFLECTION LEMMA
-- ============================================================

/-- Boolean primality reflects propositional primality. -/
theorem is_prime_bool_iff (p : TauIdx) : is_prime_bool p = true ↔ idx_prime p :=
  ⟨is_prime_of_bool p, bool_of_is_prime p⟩

-- ============================================================
-- SMOKE TESTS
-- ============================================================

example : idx_prime 2 := (is_prime_bool_iff 2).mp (by native_decide)
example : idx_prime 17 := (is_prime_bool_iff 17).mp (by native_decide)

end Tau.Polarity
