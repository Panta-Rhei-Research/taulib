import TauLib.BookI.Coordinates.Primes

/-!
# TauLib.BookI.Coordinates.TowerAtoms

Tower atoms T(a,b,c) = (a↑↑c)^b and computable peel-off tools.

## Registry Cross-References

- [I.D19c] Tower Atom — `tower_atom`
- [I.D19d] Greedy Peel Algorithm — `largest_prime_divisor`, `max_tet_height`, `max_exp_at`

## Ground Truth Sources
- chunk_0241_M002280: Tower atom definition T(A,B,C) = (A↑↑C)^B (Def 2.12), greedy peel algorithm

## Mathematical Content

A tower atom T(a,b,c) for prime a, b ≥ 1, c ≥ 1 is the canonical
multiplicative building block of τ-Idx. The nesting ((a↑↑c)^b) is the
unique binding from which all three parameters are recoverable.

Tower atoms are prime powers: T(a,b,c) = a^(b · a↑↑(c-1)), so the only
prime factor of T(a,b,c) is a.
-/

namespace Tau.Coordinates

open Tau.Denotation Tau.Orbit

-- ============================================================
-- TETRATION GROWTH LEMMAS
-- ============================================================

/-- a↑↑c ≥ 1 for a ≥ 1. -/
theorem tetration_pos (a : Nat) (ha : a ≥ 1) (c : Nat) : tetration a c ≥ 1 := by
  induction c with
  | zero => simp [tetration]
  | succ c ih => simp only [tetration]; exact Nat.one_le_pow (tetration a c) a ha

/-- a↑↑c ≥ a for a ≥ 2, c ≥ 1. -/
theorem tetration_ge_base (a : Nat) (ha : a ≥ 2) (c : Nat) (hc : c ≥ 1) :
    tetration a c ≥ a := by
  rcases c with _ | c
  · omega
  · simp only [tetration]
    have htet_pos := tetration_pos a (by omega : a ≥ 1) c
    have h1 := Nat.pow_le_pow_right (show a > 0 by omega) htet_pos
    rw [Nat.pow_one] at h1
    exact h1

/-- a↑↑(c+1) > a↑↑c for a ≥ 2 (strict monotonicity). -/
theorem tetration_strict_mono (a : Nat) (ha : a ≥ 2) (c : Nat) :
    tetration a (c + 1) > tetration a c := by
  induction c with
  | zero =>
    simp [tetration]
    have : a ^ 1 = a := Nat.pow_one a
    omega
  | succ c ih =>
    simp only [tetration]
    exact Nat.pow_lt_pow_right (by omega) ih

/-- Tetration is unbounded: for a ≥ 2 and any N, ∃ c, a↑↑c > N. -/
theorem tetration_unbounded (a : Nat) (ha : a ≥ 2) (N : Nat) :
    ∃ c, tetration a c > N := by
  induction N with
  | zero => exact ⟨0, by simp [tetration]⟩
  | succ N ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨c + 1, ?_⟩
    have hmono := tetration_strict_mono a ha c
    omega

-- ============================================================
-- TOWER ATOM [I.D19c]
-- ============================================================

/-- [I.D19c] Tower atom: T(a,b,c) = (a↑↑c)^b. -/
def tower_atom (a b c : TauIdx) : TauIdx := (tetration a c) ^ b

/-- Bridge: tower_atom a b c = (tetration a c) ^ b (definitional). -/
theorem tower_atom_eq_nat (a b c : TauIdx) :
    tower_atom a b c = (tetration a c) ^ b := rfl

/-- Tower atom factors through the earned fold chain:
    T(a,b,c) = idx_exp (idx_tetration a c) b.
    Ground truth: chunk_0241, chunk_0060 (UR-ITER). -/
theorem tower_atom_via_fold (a b c : TauIdx) :
    tower_atom a b c = idx_exp (idx_tetration a c) b := by
  unfold tower_atom
  rw [← idx_tetration_eq, ← idx_exp_eq_nat_pow]

/-- Tower atoms are at least 2 for prime base, b ≥ 1, c ≥ 1. -/
theorem tower_atom_ge_two (a b c : TauIdx) (ha : a ≥ 2) (hb : b ≥ 1) (hc : c ≥ 1) :
    tower_atom a b c ≥ 2 := by
  unfold tower_atom
  have htet : tetration a c ≥ 2 := Nat.le_trans ha (tetration_ge_base a ha c hc)
  have hpow : (tetration a c) ^ b ≥ (tetration a c) ^ 1 :=
    Nat.pow_le_pow_right (by omega : tetration a c > 0) hb
  rw [Nat.pow_one] at hpow
  exact Nat.le_trans htet hpow

/-- Tower atoms are positive for a ≥ 1. -/
theorem tower_atom_pos (a b c : TauIdx) (ha : a ≥ 1) : tower_atom a b c > 0 := by
  unfold tower_atom
  have := tetration_pos a ha c
  exact Nat.pos_of_ne_zero (Nat.ne_zero_of_lt (Nat.lt_of_lt_of_le
    (show 0 < 1 by omega) (Nat.one_le_pow b (tetration a c) (by omega))))

-- ============================================================
-- TOWER ATOM AS PRIME POWER
-- ============================================================

/-- The A-adic valuation of a↑↑c equals a↑↑(c-1) for a ≥ 2, c ≥ 1.
    That is, a↑↑c = a ^ (a↑↑(c-1)). -/
theorem tetration_as_pow (a : Nat) (c : Nat) (hc : c ≥ 1) :
    tetration a c = a ^ (tetration a (c - 1)) := by
  rcases c with _ | c
  · omega
  · simp [tetration]

/-- T(a,b,c) is a power of a: T(a,b,c) = a^(b * a↑↑(c-1)). -/
theorem tower_atom_as_prime_power (a b c : TauIdx) (hc : c ≥ 1) :
    tower_atom a b c = a ^ (b * tetration a (c - 1)) := by
  unfold tower_atom
  rw [tetration_as_pow a c hc, Nat.mul_comm b]
  exact (Nat.pow_mul a (tetration a (c - 1)) b).symm

/-- Any prime dividing a^e (for e ≥ 1) must divide a. -/
private theorem prime_dvd_of_dvd_pow {p a : TauIdx} (hp : idx_prime p) (e : Nat)
    (he : e ≥ 1) (h : p ∣ a ^ e) : p ∣ a := by
  induction e with
  | zero => omega
  | succ e ih =>
    rw [Nat.pow_succ] at h
    rcases euclid_lemma hp h with h1 | h2
    · -- h1 : p ∣ a ^ e
      rcases e with _ | e
      · -- e = 0: simp gives h1 : p = 1, contradicts p ≥ 2
        simp [Nat.pow_zero] at h1
        exact absurd h1 (by have := hp.1; simp only [TauIdx] at *; omega)
      · exact ih (by omega) h1
    · exact h2

/-- All prime factors of T(a,b,c) equal a (when a is prime, b ≥ 1, c ≥ 1). -/
theorem tower_atom_prime_factor (a b c p : TauIdx)
    (ha : idx_prime a) (hb : b ≥ 1) (hc : c ≥ 1)
    (hp : idx_prime p) (hpT : p ∣ tower_atom a b c) : p = a := by
  rw [tower_atom_as_prime_power a b c hc] at hpT
  have htet := tetration_pos a (show a ≥ 1 by have := ha.1; simp only [TauIdx] at *; omega) (c - 1)
  have hexp : b * tetration a (c - 1) ≥ 1 := by
    have h := Nat.mul_le_mul hb htet
    simp only [TauIdx] at *; omega
  have hpa : p ∣ a := prime_dvd_of_dvd_pow hp _ hexp hpT
  rcases ha.2 p hpa with h | h
  · have := hp.1; simp only [TauIdx] at *; omega
  · exact h

-- ============================================================
-- COMPUTABLE PEEL-OFF TOOLS [I.D19d partial]
-- ============================================================

/-- [I.D19d] Largest prime divisor of n (0 for n ≤ 1). -/
def largest_prime_divisor (n : TauIdx) : TauIdx :=
  if n ≤ 1 then 0
  else go n n
where
  go (n d : TauIdx) : TauIdx :=
    if d ≤ 1 then 1
    else if is_prime_bool d && (n % d == 0) then d
    else go n (d - 1)
  termination_by d
  decreasing_by simp_wf; simp only [TauIdx] at *; omega

/-- Max tetration height: largest c such that a↑↑(c+1) divides n. Returns 0-indexed. -/
def max_tet_height (a n : TauIdx) : TauIdx :=
  if a ≤ 1 then 0
  else go a n 0 n
where
  go (a n c fuel : TauIdx) : TauIdx :=
    if fuel = 0 then c
    else if n % (tetration a (c + 1)) ≠ 0 then c
    else go a n (c + 1) (fuel - 1)
  termination_by fuel
  decreasing_by simp_wf; simp only [TauIdx] at *; omega

/-- Max exponent: largest b such that base^(b+1) divides n. Returns 0-indexed. -/
def max_exp_at (base n : TauIdx) : TauIdx :=
  if base ≤ 1 then 0
  else go base n 0 n
where
  go (base n b fuel : TauIdx) : TauIdx :=
    if fuel = 0 then b
    else if n % (base ^ (b + 1)) ≠ 0 then b
    else go base n (b + 1) (fuel - 1)
  termination_by fuel
  decreasing_by simp_wf; simp only [TauIdx] at *; omega

/-- Max c such that a↑↑(c-1) divides v. Starts at c=1; increments while a↑↑c | v. -/
def max_tet_div (a v : TauIdx) : TauIdx :=
  if a ≤ 1 then 1
  else go a v 1 v
where
  go (a v c fuel : TauIdx) : TauIdx :=
    if fuel = 0 then c
    else if v % (tetration a c) ≠ 0 then c
    else go a v (c + 1) (fuel - 1)
  termination_by fuel
  decreasing_by simp_wf; simp only [TauIdx] at *; omega

/-- [I.D19d] One-step greedy peel: extract (A, B, C, D) from X ≥ 2.
    Uses A-adic valuation:
    1. A = largest prime divisor of X
    2. v = v_A(X)
    3. C = max c such that A↑↑(c-1) divides v
    4. B = v / A↑↑(C-1)
    5. T = tower_atom(A, B, C), D = X / T -/
def greedy_peel (x : TauIdx) : TauIdx × TauIdx × TauIdx × TauIdx :=
  if x ≤ 1 then (1, 0, 0, x)
  else
    let a := largest_prime_divisor x
    let v := p_adic_val a x
    let c := max_tet_div a v
    let b := v / (tetration a (c - 1))
    let t := tower_atom a b c
    let d := x / t
    (a, b, c, d)

-- ============================================================
-- SMOKE TESTS
-- ============================================================

#eval tower_atom 2 3 1       -- (2↑↑1)^3 = 2^3 = 8
#eval tower_atom 2 1 2       -- (2↑↑2)^1 = 4^1 = 4
#eval tower_atom 3 2 1       -- (3↑↑1)^2 = 3^2 = 9
#eval tower_atom 2 1 3       -- (2↑↑3)^1 = 16

#eval largest_prime_divisor 12   -- 3
#eval largest_prime_divisor 30   -- 5
#eval largest_prime_divisor 7    -- 7
#eval largest_prime_divisor 64   -- 2

#eval max_tet_height 2 16       -- 3 (2↑↑3 = 16 | 16)
#eval max_tet_height 2 4        -- 2 (2↑↑2 = 4 | 4)
#eval max_tet_height 3 27       -- 2 (3↑↑2 = 27 | 27)

#eval max_exp_at 4 64           -- 3 (4^3 = 64)
#eval max_exp_at 2 8            -- 3 (2^3 = 8)

#eval greedy_peel 12             -- (3, 1, 1, 4): T(3,1,1)=3, 12/3=4
#eval greedy_peel 64             -- (2, 3, 2, 1): T(2,3,2)=(2↑↑2)^3=4^3=64
#eval greedy_peel 7              -- (7, 1, 1, 1): T(7,1,1)=7
#eval greedy_peel 16             -- (2, 1, 3, 1): T(2,1,3)=(2↑↑3)^1=16
#eval greedy_peel 256            -- (2, 2, 3, 1): T(2,2,3)=(2↑↑3)^2=16^2=256
#eval greedy_peel 8              -- (2, 3, 1, 1): T(2,3,1)=2^3=8
#eval greedy_peel 360            -- (5, 1, 1, 72): T(5,1,1)=5, 360/5=72

end Tau.Coordinates
