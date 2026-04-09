import TauLib.BookI.Polarity.PrimeBridge
import TauLib.BookI.Polarity.ModArith

/-!
# TauLib.BookI.Polarity.NthPrime

Formal properties of `nth_prime`: primality, primorial divisibility,
coprimality, and CRT hypothesis bundles.

## Main Results

- `nth_prime_go_is_prime`: Algorithmic invariant — nth_prime_go returns a prime
  when fuel contains enough primes (proved by induction on fuel)
- `nth_prime_prime_of_fuel`: Assembly — nth_prime k is prime when fuel suffices
- `nth_prime_dvd_primorial`: nth_prime(i+1) divides primorial(k) for i < k
- `nth_prime_coprime_primorial`: nth_prime(k+1) coprime to primorial(k)
- `nth_prime_pairwise_coprime`: Pairwise coprimality for CRT
- `CRTHyp`: Bundle of CRT hypotheses at depth k
-/

namespace Tau.Polarity

open Tau.Denotation Tau.Coordinates

-- ============================================================
-- SECTION 1: PRIME COUNTING HELPER
-- ============================================================

/-- Count primes in the half-open interval (lo, hi].
    Non-accumulator definition for clean inductive proofs. -/
def count_primes_in (lo hi : Nat) : Nat :=
  if lo ≥ hi then 0
  else (if is_prime_bool (lo + 1) then 1 else 0) + count_primes_in (lo + 1) hi
termination_by hi - lo

private theorem count_primes_in_unfold (lo hi : Nat) :
    count_primes_in lo hi =
    if lo ≥ hi then 0
    else (if is_prime_bool (lo + 1) then 1 else 0) + count_primes_in (lo + 1) hi :=
  count_primes_in.eq_1 lo hi

theorem count_primes_in_empty (lo : Nat) : count_primes_in lo lo = 0 := by
  rw [count_primes_in_unfold]; simp

theorem count_primes_in_step_prime (lo hi : Nat) (hlt : lo < hi)
    (hp : is_prime_bool (lo + 1) = true) :
    count_primes_in lo hi = 1 + count_primes_in (lo + 1) hi := by
  rw [count_primes_in_unfold]
  simp only [show ¬(lo ≥ hi) by omega, ↓reduceIte, hp]

theorem count_primes_in_step_not (lo hi : Nat) (hlt : lo < hi)
    (hnp : is_prime_bool (lo + 1) = false) :
    count_primes_in lo hi = count_primes_in (lo + 1) hi := by
  rw [count_primes_in_unfold]
  simp [show ¬(lo ≥ hi) by omega, hnp]

-- Smoke tests
#eval count_primes_in 1 20   -- 8  (primes 2,3,5,7,11,13,17,19)
#eval count_primes_in 1 100  -- 25

-- ============================================================
-- SECTION 2: nth_prime_go ALGORITHMIC INVARIANT
-- ============================================================

/-- If fuel contains enough primes, nth_prime_go returns a value that
    passes is_prime_bool.

    Invariant: count = target → is_prime_bool cur = true.
    This propagates cleanly:
    - When count < target and next is prime: count+1 = target → is_prime_bool next (trivially true)
    - When count < target and next is NOT prime: count = target → ... (vacuously true since count < target)
    - When count = target: function returns cur, and invariant gives primality. -/
theorem nth_prime_go_is_prime
    (target count cur fuel : Nat)
    (h_target : target ≥ 1)
    (h_le : count ≤ target)
    (h_inv : count = target → is_prime_bool cur = true)
    (h_fuel : count_primes_in cur (cur + fuel) ≥ target - count) :
    is_prime_bool (nth_prime_go target count cur fuel) = true := by
  induction fuel generalizing count cur with
  | zero =>
    -- fuel = 0: count_primes_in cur cur = 0 ≥ target - count forces count = target
    rw [Nat.add_zero] at h_fuel
    rw [count_primes_in_empty] at h_fuel
    have hcount_eq : count = target := by omega
    unfold nth_prime_go; simp
    exact h_inv hcount_eq
  | succ n ih =>
    unfold nth_prime_go
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    split
    · -- count == target: return cur
      rename_i hbeq
      exact h_inv (beq_iff_eq.mp hbeq)
    · -- count ≠ target
      rename_i hbeq
      have hne : count ≠ target := fun heq => hbeq (beq_iff_eq.mpr heq)
      have hlt : count < target := by omega
      have hcur_lt : cur < cur + (n + 1) := by omega
      have hshift : cur + (n + 1) = cur + 1 + n := by omega
      split
      · -- is_prime_bool (cur + 1) = true
        rename_i hp
        have hstep := count_primes_in_step_prime cur (cur + (n + 1)) hcur_lt hp
        rw [hshift] at hstep h_fuel
        -- ih : ∀ (count cur : Nat), count ≤ target → (count = target → ...) → fuel_hyp → ...
        exact ih (count + 1) (cur + 1) (by omega) (fun _ => hp) (by omega)
      · -- is_prime_bool (cur + 1) = false
        rename_i hp
        have hnp : is_prime_bool (cur + 1) = false := by
          revert hp; cases is_prime_bool (cur + 1) <;> simp
        have hstep := count_primes_in_step_not cur (cur + (n + 1)) hcur_lt hnp
        rw [hshift] at hstep h_fuel
        exact ih count (cur + 1) h_le (fun heq => absurd heq hne) (by omega)

-- ============================================================
-- SECTION 3: nth_prime_prime ASSEMBLY
-- ============================================================

/-- Boolean fuel-sufficiency check for nth_prime. -/
def nth_prime_fuel_ok (k : Nat) : Bool :=
  k == 0 || decide (count_primes_in 1 (1 + (k * k * 10 + 10)) ≥ k)

/-- When fuel suffices, nth_prime k is prime. -/
theorem nth_prime_prime_of_fuel {k : TauIdx} (hk : k ≥ 1)
    (hfuel : count_primes_in 1 (1 + (k * k * 10 + 10)) ≥ k) :
    idx_prime (nth_prime k) := by
  have hk0 : k ≠ 0 := by simp only [TauIdx] at *; omega
  unfold nth_prime; rw [if_neg hk0]
  have h := nth_prime_go_is_prime k 0 1 (k * k * 10 + 10)
    hk (Nat.zero_le k)
    (fun h => absurd h (by simp only [TauIdx] at *; omega))
    hfuel
  exact (is_prime_bool_iff _).mp h

-- Concrete primality instances
example : idx_prime (nth_prime 1) :=
  nth_prime_prime_of_fuel (by simp only [TauIdx]; omega) (by native_decide)
example : idx_prime (nth_prime 2) :=
  nth_prime_prime_of_fuel (by simp only [TauIdx]; omega) (by native_decide)
example : idx_prime (nth_prime 3) :=
  nth_prime_prime_of_fuel (by simp only [TauIdx]; omega) (by native_decide)
example : idx_prime (nth_prime 5) :=
  nth_prime_prime_of_fuel (by simp only [TauIdx]; omega) (by native_decide)
example : idx_prime (nth_prime 10) :=
  nth_prime_prime_of_fuel (by simp only [TauIdx]; omega) (by native_decide)

-- ============================================================
-- SECTION 4: nth_prime_dvd_primorial
-- ============================================================

/-- nth_prime(i+1) divides primorial(k) for i + 1 ≤ k. Structural induction. -/
theorem nth_prime_dvd_primorial {i k : TauIdx} (h : i + 1 ≤ k) :
    nth_prime (i + 1) ∣ primorial k := by
  induction k with
  | zero => exact absurd h (Nat.not_succ_le_zero i)
  | succ k' ih =>
    simp only [primorial]
    rcases Nat.eq_or_lt_of_le h with heq | hlt
    · -- i + 1 = k' + 1, so i = k'
      have hik : i = k' := by simp only [TauIdx] at *; omega
      rw [hik]
      exact ⟨primorial k', rfl⟩
    · -- i + 1 < k' + 1, so i + 1 ≤ k'
      have hle : i + 1 ≤ k' := by simp only [TauIdx] at *; omega
      obtain ⟨c, hc⟩ := ih hle
      exact ⟨nth_prime (k' + 1) * c, by
        rw [hc, ← Nat.mul_assoc,
          Nat.mul_comm (nth_prime (k' + 1)) (nth_prime (i + 1)),
          Nat.mul_assoc]⟩

-- ============================================================
-- SECTION 5: COPRIMALITY AND CRT BUNDLE
-- ============================================================

/-- ¬(a ∣ b) from b % a ≠ 0. -/
private theorem not_dvd_of_mod_ne_zero {a b : Nat} (h : b % a ≠ 0) : ¬(a ∣ b) := by
  intro ⟨k, hk⟩; rw [hk, Nat.mul_mod_right] at h; exact h rfl

/-- nth_prime(k+1) is coprime to primorial(k), given primality and freshness. -/
theorem nth_prime_coprime_primorial {k : TauIdx}
    (hprime : idx_prime (nth_prime (k + 1)))
    (hfresh : primorial k % nth_prime (k + 1) ≠ 0) :
    Nat.Coprime (nth_prime (k + 1)) (primorial k) :=
  prime_coprime_of_not_dvd hprime (not_dvd_of_mod_ne_zero hfresh)

/-- Pairwise coprimality from primality and distinctness. -/
theorem nth_prime_pairwise_coprime {k : TauIdx}
    (hprimes : ∀ i, i < k → idx_prime (nth_prime (i + 1)))
    (hdistinct : ∀ i j, i < k → j < k → i ≠ j → nth_prime (i + 1) ≠ nth_prime (j + 1)) :
    ∀ i j, i < k → j < k → i ≠ j →
    Nat.Coprime (nth_prime (i + 1)) (nth_prime (j + 1)) :=
  fun i j hi hj hij =>
    distinct_primes_coprime (hprimes i hi) (hprimes j hj) (hdistinct i j hi hj hij)

/-- CRT hypotheses at depth k: all primes are prime and pairwise coprime. -/
structure CRTHyp (k : TauIdx) where
  all_prime : ∀ i, i < k → idx_prime (nth_prime (i + 1))
  pairwise_coprime : ∀ i j, i < k → j < k → i ≠ j →
    Nat.Coprime (nth_prime (i + 1)) (nth_prime (j + 1))

-- Concrete CRT hypothesis bundles via omega case split + native_decide
private theorem all_primes_lt_5 : ∀ i, i < 5 → idx_prime (nth_prime (i + 1)) := by
  intro i hi
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by simp only [TauIdx] at *; omega
  rcases this with rfl | rfl | rfl | rfl | rfl <;>
    exact (is_prime_bool_iff _).mp (by native_decide)

theorem crt_hyp_5 : CRTHyp 5 where
  all_prime := all_primes_lt_5
  pairwise_coprime := by
    intro i j hi hj hij
    have hne : nth_prime (i + 1) ≠ nth_prime (j + 1) := by
      have hi5 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
        simp only [TauIdx] at *; omega
      have hj5 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by
        simp only [TauIdx] at *; omega
      rcases hi5 with rfl | rfl | rfl | rfl | rfl <;>
        rcases hj5 with rfl | rfl | rfl | rfl | rfl <;>
        first | exact absurd rfl hij | native_decide
    exact distinct_primes_coprime (all_primes_lt_5 i hi) (all_primes_lt_5 j hj) hne

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Fuel sufficiency verified at various depths
example : nth_prime_fuel_ok 1 = true := by native_decide
example : nth_prime_fuel_ok 5 = true := by native_decide
example : nth_prime_fuel_ok 10 = true := by native_decide

-- Freshness checks
example : primorial 1 % nth_prime 2 ≠ 0 := by native_decide
example : primorial 2 % nth_prime 3 ≠ 0 := by native_decide
example : primorial 3 % nth_prime 4 ≠ 0 := by native_decide
example : primorial 4 % nth_prime 5 ≠ 0 := by native_decide

-- Coprimality
example : Nat.Coprime (nth_prime 2) (primorial 1) :=
  nth_prime_coprime_primorial
    (nth_prime_prime_of_fuel (by simp only [TauIdx]; omega) (by native_decide))
    (by native_decide)

-- Primorial divisibility
example : nth_prime 1 ∣ primorial 3 := nth_prime_dvd_primorial (by simp only [TauIdx]; omega)
example : nth_prime 2 ∣ primorial 3 := nth_prime_dvd_primorial (by simp only [TauIdx]; omega)
example : nth_prime 3 ∣ primorial 3 := nth_prime_dvd_primorial (by simp only [TauIdx]; omega)

end Tau.Polarity
