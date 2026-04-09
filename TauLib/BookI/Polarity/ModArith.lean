import TauLib.BookI.Coordinates.Primes

/-!
# TauLib.BookI.Polarity.ModArith

Modular arithmetic infrastructure for the primorial ladder.

## Ground Truth Sources
- chunk_0120_M001406: Primorial ladder, local ring structure on ℤ_p^(τ)

## Mathematical Content

The k-th primorial M_k = p₁ · p₂ · ... · p_k is the product of the first k
internal primes. Reduction maps π_{ℓ→k} : Z/M_ℓZ → Z/M_kZ are given by
x ↦ x mod M_k. These form a compatible inverse system.

This module provides: nth_prime, primorial, reduction maps, and modular
arithmetic ring laws needed for omega-germ construction.
-/

namespace Tau.Polarity

open Tau.Denotation Tau.Coordinates

-- ============================================================
-- NTH PRIME (computable)
-- ============================================================

/-- Find the k-th prime by trial (1-indexed: nth_prime 1 = 2). -/
def nth_prime_go (target count cur : Nat) (fuel : Nat) : Nat :=
  if fuel = 0 then cur
  else if count == target then cur
  else
    let next := cur + 1
    if is_prime_bool next then
      nth_prime_go target (count + 1) next (fuel - 1)
    else
      nth_prime_go target count next (fuel - 1)
termination_by fuel

/-- The k-th prime (1-indexed). nth_prime 0 = 0 by convention. -/
def nth_prime (k : TauIdx) : TauIdx :=
  if k = 0 then 0
  else nth_prime_go k 0 1 (k * k * 10 + 10)

-- ============================================================
-- PRIMORIAL
-- ============================================================

/-- The k-th primorial: M_k = p₁ · p₂ · ... · p_k.
    primorial 0 = 1, primorial k = nth_prime(k) · primorial(k-1). -/
def primorial : TauIdx → TauIdx
  | 0 => 1
  | k + 1 => nth_prime (k + 1) * primorial k

-- ============================================================
-- REDUCTION MAPS
-- ============================================================

/-- Reduction map: x mod M_k. This is the canonical projection
    π_k : Z → Z/M_kZ. -/
def reduce (x k : TauIdx) : TauIdx := x % primorial k

/-- Primorial divisibility: M_k divides M_ℓ when k ≤ ℓ.
    Computable check. -/
def primorial_dvd_check (k l : TauIdx) : Bool :=
  k ≤ l && primorial l % primorial k == 0

/-- Reduction compatibility check: x % M_ℓ % M_k = x % M_k when k ≤ ℓ. -/
def reduction_compat_check (x k l : TauIdx) : Bool :=
  if k ≤ l then reduce (reduce x l) k == reduce x k
  else true

-- ============================================================
-- MODULAR ARITHMETIC RING LAWS
-- ============================================================

/-- Modular addition: (a + b) % m = ((a % m) + (b % m)) % m. -/
theorem mod_add_eq (a b m : Nat) : (a + b) % m = ((a % m) + (b % m)) % m :=
  Nat.add_mod a b m

/-- Modular multiplication: (a * b) % m = ((a % m) * (b % m)) % m. -/
theorem mod_mul_eq (a b m : Nat) : (a * b) % m = ((a % m) * (b % m)) % m :=
  Nat.mul_mod a b m

/-- a % m < m for m > 0. -/
theorem mod_lt_of_pos (a m : Nat) (hm : m > 0) : a % m < m :=
  Nat.mod_lt a hm

-- ============================================================
-- COPRIMALITY OF DISTINCT PRIMES
-- ============================================================

/-- If p and q are distinct primes, they are coprime. -/
theorem distinct_primes_coprime {p q : TauIdx}
    (hp : idx_prime p) (hq : idx_prime q) (hne : p ≠ q) :
    Nat.gcd p q = 1 := by
  have hgp := Nat.gcd_dvd_left p q
  have hgq := Nat.gcd_dvd_right p q
  rcases hp.2 (Nat.gcd p q) hgp with h | h
  · exact h
  · -- gcd = p, so p | q. Since q is prime, p = 1 or p = q.
    -- But p ≥ 2 and p ≠ q, contradiction.
    rw [h] at hgq
    rcases hq.2 p hgq with h' | h'
    · have := hp.1; simp only [TauIdx] at *; omega
    · exact absurd h' hne

-- ============================================================
-- PRIMORIAL POSITIVITY
-- ============================================================

/-- nth_prime_go always returns a value ≥ cur. -/
theorem nth_prime_go_ge (target count cur fuel : Nat) :
    nth_prime_go target count cur fuel ≥ cur := by
  induction fuel generalizing count cur with
  | zero => unfold nth_prime_go; simp
  | succ n ih =>
    unfold nth_prime_go
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    split
    · -- count == target: returns cur
      exact Nat.le_refl cur
    · -- count ≠ target: recurses with next = cur + 1
      split
      · -- is_prime_bool (cur + 1): recurse with (count+1, cur+1)
        show nth_prime_go target (count + 1) (cur + 1) n ≥ cur
        exact Nat.le_trans (Nat.le_succ cur) (ih (count + 1) (cur + 1))
      · -- not prime: recurse with (count, cur+1)
        show nth_prime_go target count (cur + 1) n ≥ cur
        exact Nat.le_trans (Nat.le_succ cur) (ih count (cur + 1))

/-- nth_prime k ≥ 1 for k ≥ 1. -/
theorem nth_prime_pos {k : TauIdx} (hk : k ≥ 1) : nth_prime k ≥ 1 := by
  simp only [nth_prime]
  have hk0 : k ≠ 0 := by simp only [TauIdx] at *; omega
  rw [if_neg hk0]
  exact nth_prime_go_ge k 0 1 (k * k * 10 + 10)

/-- Every primorial is positive: M_k > 0. -/
theorem primorial_pos (k : TauIdx) : primorial k > 0 := by
  induction k with
  | zero => simp [primorial]
  | succ k' ih =>
    simp only [primorial]
    have h_np : nth_prime (k' + 1) ≥ 1 :=
      nth_prime_pos (by simp only [TauIdx]; omega)
    exact Nat.mul_pos (by simp only [TauIdx] at *; omega) ih

-- ============================================================
-- PRIMORIAL DIVISIBILITY
-- ============================================================

/-- Primorial divisibility: M_k ∣ M_l when k ≤ l.
    This is the structural backbone of the inverse system. -/
theorem primorial_dvd {k l : TauIdx} (h : k ≤ l) : primorial k ∣ primorial l := by
  induction l with
  | zero =>
    have : k = 0 := Nat.le_antisymm h (Nat.zero_le k)
    subst this; exact ⟨1, (Nat.mul_one _).symm⟩
  | succ l' ih =>
    simp only [TauIdx] at *
    by_cases hk : k = l' + 1
    · subst hk; exact ⟨1, (Nat.mul_one _).symm⟩
    · have hk' : k ≤ l' := by simp only [TauIdx] at *; omega
      obtain ⟨m, hm⟩ := ih hk'
      simp only [primorial]
      exact ⟨nth_prime (l' + 1) * m, by rw [hm, ← Nat.mul_assoc,
        Nat.mul_comm (nth_prime (l' + 1)) (primorial k), Nat.mul_assoc]⟩

-- ============================================================
-- REDUCTION COMPATIBILITY (the core inverse system theorem)
-- ============================================================

/-- Helper: (a * k + r) % a = r % a. Proved by induction on k. -/
private theorem mul_add_mod (a k r : Nat) : (a * k + r) % a = r % a := by
  induction k with
  | zero => simp
  | succ k' ih =>
    have h_rearr : a * (k' + 1) + r = (a * k' + r) + a := by
      rw [Nat.mul_succ]; omega
    rw [h_rearr, Nat.add_mod_right, ih]

/-- If a ∣ b then (x % b) % a = x % a.
    Proved from first principles using Lean 4 core. -/
theorem mod_mod_of_dvd (x a b : Nat) (h : a ∣ b) : x % b % a = x % a := by
  obtain ⟨c, rfl⟩ := h
  -- Goal: x % (a * c) % a = x % a
  -- Key decomposition: x = a * (c * q) + r where q = x/(a*c), r = x%(a*c)
  have hd : a * (c * (x / (a * c))) + x % (a * c) = x := by
    rw [← Nat.mul_assoc]; exact Nat.div_add_mod x (a * c)
  -- From mul_add_mod: (a * (c*q) + r) % a = r % a
  have hmul := mul_add_mod a (c * (x / (a * c))) (x % (a * c))
  -- Rewrite the LHS of hmul using hd: big expression → x
  rw [hd] at hmul
  -- hmul : x % a = (x % (a * c)) % a
  exact hmul.symm

/-- Reduction maps compose: (x % M_l) % M_k = x % M_k for k ≤ l.
    This is the fundamental compatibility condition of the primorial inverse system. -/
theorem reduction_compat (x : TauIdx) {k l : TauIdx} (h : k ≤ l) :
    reduce (reduce x l) k = reduce x k := by
  simp only [reduce]
  exact mod_mod_of_dvd x (primorial k) (primorial l) (primorial_dvd h)

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- nth_prime
#eval nth_prime 1    -- 2
#eval nth_prime 2    -- 3
#eval nth_prime 3    -- 5
#eval nth_prime 4    -- 7
#eval nth_prime 5    -- 11
#eval nth_prime 10   -- 29

-- Primorials
#eval primorial 0    -- 1
#eval primorial 1    -- 2
#eval primorial 2    -- 6
#eval primorial 3    -- 30
#eval primorial 4    -- 210
#eval primorial 5    -- 2310

-- Reduction compatibility
#eval reduction_compat_check 100 2 4    -- true: 100%210%6 = 100%6
#eval reduction_compat_check 1000 3 5   -- true
#eval reduction_compat_check 42 1 3     -- true

-- Primorial divisibility
#eval primorial_dvd_check 2 4   -- true: M_2=6 divides M_4=210
#eval primorial_dvd_check 1 5   -- true: M_1=2 divides M_5=2310

end Tau.Polarity
