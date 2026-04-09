import TauLib.BookI.Denotation.Arithmetic

/-!
# TauLib.BookI.Coordinates.Primes

Primes, divisibility, GCD, Euclid's Lemma, and FTA on τ-Idx.

## Registry Cross-References

- [I.D19a] Index Divisibility — `idx_divides`, `idx_divides_iff_nat_dvd`
- [I.D19b] Index Prime — `idx_prime`
- [I.T09]  Fundamental Theorem of Arithmetic — `prime_product_exists`, `prime_product_unique`

## Ground Truth Sources
- chunk_0310_M002679: Primes as finite witnesses, FTA as prerequisite for polarity partition
-/

namespace Tau.Coordinates

open Tau.Denotation

-- ============================================================
-- DIVISIBILITY HELPERS
-- ============================================================

private theorem nat_dvd_refl (a : Nat) : a ∣ a := ⟨1, (Nat.mul_one a).symm⟩

private theorem nat_dvd_trans {a b c : Nat} (hab : a ∣ b) (hbc : b ∣ c) : a ∣ c := by
  obtain ⟨k1, hk1⟩ := hab; obtain ⟨k2, hk2⟩ := hbc
  exact ⟨k1 * k2, by rw [hk2, hk1, Nat.mul_assoc]⟩

private theorem nat_dvd_mul_right (a b : Nat) : a ∣ a * b := ⟨b, rfl⟩

private theorem nat_dvd_mul_of_dvd {a b : Nat} (h : a ∣ b) (c : Nat) : a ∣ c * b := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨c * k, by rw [← Nat.mul_assoc, Nat.mul_comm c a, Nat.mul_assoc]⟩

-- ============================================================
-- INDEX DIVISIBILITY [I.D19a]
-- ============================================================

/-- [I.D19a] Index divisibility: a divides b in τ-Idx. -/
def idx_divides (a b : TauIdx) : Prop := ∃ k : TauIdx, b = idx_mul a k

/-- Bridge: idx_divides ↔ Nat.dvd. -/
theorem idx_divides_iff_nat_dvd (a b : TauIdx) : idx_divides a b ↔ a ∣ b := by
  constructor
  · rintro ⟨k, hk⟩; exact ⟨k, by rw [idx_mul_eq_nat_mul] at hk; exact hk⟩
  · rintro ⟨k, hk⟩; exact ⟨k, by rw [idx_mul_eq_nat_mul]; exact hk⟩

instance instDecidableIdxDivides (a b : TauIdx) : Decidable (idx_divides a b) :=
  decidable_of_iff (a ∣ b) (idx_divides_iff_nat_dvd a b).symm

-- ============================================================
-- DIVISIBILITY LAWS
-- ============================================================

theorem idx_divides_refl (a : TauIdx) : idx_divides a a :=
  (idx_divides_iff_nat_dvd a a).mpr (nat_dvd_refl a)

theorem idx_divides_trans {a b c : TauIdx}
    (hab : idx_divides a b) (hbc : idx_divides b c) : idx_divides a c :=
  (idx_divides_iff_nat_dvd a c).mpr
    (nat_dvd_trans ((idx_divides_iff_nat_dvd a b).mp hab)
                   ((idx_divides_iff_nat_dvd b c).mp hbc))

theorem idx_one_divides (a : TauIdx) : idx_divides 1 a :=
  (idx_divides_iff_nat_dvd 1 a).mpr ⟨a, (Nat.one_mul a).symm⟩

theorem idx_divides_zero (a : TauIdx) : idx_divides a 0 :=
  (idx_divides_iff_nat_dvd a 0).mpr ⟨0, (Nat.mul_zero a).symm⟩

theorem idx_divides_le {a b : TauIdx} (hab : idx_divides a b) (hb : b ≠ 0) : a ≤ b :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hb) ((idx_divides_iff_nat_dvd a b).mp hab)

theorem idx_divides_antisymm {a b : TauIdx}
    (hab : idx_divides a b) (hba : idx_divides b a) : a = b :=
  Nat.dvd_antisymm ((idx_divides_iff_nat_dvd a b).mp hab)
                    ((idx_divides_iff_nat_dvd b a).mp hba)

-- ============================================================
-- INDEX PRIME [I.D19b]
-- ============================================================

/-- [I.D19b] Index prime: p ≥ 2 and only divisors are 1 and p. -/
def idx_prime (p : TauIdx) : Prop :=
  p ≥ 2 ∧ ∀ d : TauIdx, d ∣ p → d = 1 ∨ d = p

/-- Boolean primality check via trial division. -/
def no_factor_below (n d : TauIdx) : Bool :=
  if d ≥ n then true
  else if d * d > n then true
  else if n % d = 0 then false
  else no_factor_below n (d + 1)
termination_by n - d
decreasing_by simp_wf; simp only [TauIdx] at *; omega

/-- Boolean primality test. -/
def is_prime_bool (p : TauIdx) : Bool := p ≥ 2 && no_factor_below p 2

-- ============================================================
-- PRIME DIVISOR EXISTENCE
-- ============================================================

/-- Every n ≥ 2 has a prime divisor. Proved by strong induction. -/
theorem exists_prime_divisor (n : TauIdx) (hn : n ≥ 2) :
    ∃ p, idx_prime p ∧ p ∣ n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rcases Classical.em (∀ d : TauIdx, d ∣ n → d = 1 ∨ d = n) with h | h
    · exact ⟨n, ⟨hn, h⟩, nat_dvd_refl n⟩
    · -- n is composite
      have ⟨d, hd_dvd, hd_ne⟩ : ∃ d, d ∣ n ∧ ¬(d = 1 ∨ d = n) :=
        Classical.byContradiction fun hall =>
          h fun d hd => Classical.byContradiction fun hbad => hall ⟨d, hd, hbad⟩
      have hd1 : d ≠ 1 := fun heq => hd_ne (Or.inl heq)
      have hdn : d ≠ n := fun heq => hd_ne (Or.inr heq)
      have hd0 : d ≠ 0 := by
        intro heq; subst heq
        obtain ⟨k, hk⟩ := hd_dvd
        simp only [Nat.zero_mul] at hk
        simp only [TauIdx] at hn; omega
      have hd_ge2 : d ≥ 2 := by
        rcases d with _ | _ | d
        · exact absurd rfl hd0
        · exact absurd rfl hd1
        · exact Nat.le_add_left 2 d
      have hd_lt : d < n := by
        have hpos : n > 0 := by simp only [TauIdx] at hn ⊢; omega
        have hle := Nat.le_of_dvd hpos hd_dvd
        rcases Nat.eq_or_lt_of_le hle with heq | hlt
        · exact absurd heq hdn
        · exact hlt
      obtain ⟨p, hp, hpd⟩ := ih d hd_lt hd_ge2
      exact ⟨p, hp, nat_dvd_trans hpd hd_dvd⟩

-- ============================================================
-- GCD
-- ============================================================

def idx_gcd (a b : TauIdx) : TauIdx := Nat.gcd a b

theorem idx_gcd_dvd_left (a b : TauIdx) : idx_gcd a b ∣ a := Nat.gcd_dvd_left a b
theorem idx_gcd_dvd_right (a b : TauIdx) : idx_gcd a b ∣ b := Nat.gcd_dvd_right a b

theorem idx_dvd_gcd {c a b : TauIdx} (hca : c ∣ a) (hcb : c ∣ b) : c ∣ idx_gcd a b :=
  Nat.dvd_gcd hca hcb

-- ============================================================
-- COPRIMALITY AND EUCLID'S LEMMA
-- ============================================================

def idx_coprime (a b : TauIdx) : Prop := idx_gcd a b = 1

theorem prime_coprime_of_not_dvd {p a : TauIdx} (hp : idx_prime p) (hna : ¬ p ∣ a) :
    idx_coprime p a := by
  unfold idx_coprime idx_gcd
  have hg := Nat.gcd_dvd_left p a
  rcases hp.2 (Nat.gcd p a) hg with h | h
  · exact h
  · exfalso; apply hna; rw [← h]; exact Nat.gcd_dvd_right p a

/-- Gauss's lemma via Nat.Coprime. -/
theorem coprime_dvd_of_dvd_mul {a b c : TauIdx}
    (hcop : idx_coprime a b) (h : a ∣ b * c) : a ∣ c := by
  unfold idx_coprime idx_gcd at hcop
  exact (show Nat.Coprime a b from hcop).dvd_of_dvd_mul_left h

/-- Euclid's Lemma: p prime, p ∣ a*b → p ∣ a ∨ p ∣ b. -/
theorem euclid_lemma {p a b : TauIdx} (hp : idx_prime p) (h : p ∣ a * b) :
    p ∣ a ∨ p ∣ b := by
  rcases Classical.em (p ∣ a) with hpa | hpa
  · exact Or.inl hpa
  · exact Or.inr (coprime_dvd_of_dvd_mul (prime_coprime_of_not_dvd hp hpa) h)

-- ============================================================
-- PRIMES ARE INFINITE
-- ============================================================

def idx_factorial : TauIdx → TauIdx
  | 0 => 1
  | n + 1 => (n + 1) * idx_factorial n

theorem idx_factorial_pos (n : TauIdx) : idx_factorial n > 0 := by
  induction n with
  | zero => simp [idx_factorial]
  | succ n ih => simp only [idx_factorial]; exact Nat.mul_pos (Nat.succ_pos n) ih

/-- Every prime p ≤ n divides n!. -/
theorem prime_dvd_factorial {p n : TauIdx} (hp : idx_prime p) (hpn : p ≤ n) :
    p ∣ idx_factorial n := by
  induction n with
  | zero =>
    have h2 : p ≥ 2 := hp.1
    have h0 : p ≤ 0 := hpn
    exact absurd (Nat.le_antisymm h0 (Nat.zero_le p))
      (by intro heq; subst heq; exact Nat.not_succ_le_zero 1 h2)
  | succ n ih =>
    simp only [idx_factorial]
    rcases Nat.eq_or_lt_of_le hpn with h | h
    · -- p = n + 1
      subst h; exact nat_dvd_mul_right (n + 1) (idx_factorial n)
    · -- p < n + 1, so p ≤ n
      exact nat_dvd_mul_of_dvd (ih (Nat.lt_succ_iff.mp h)) (n + 1)

/-- If g ≥ 2 divides both a and a+1, contradiction. -/
private theorem not_dvd_succ_of_ge_two {g a : Nat} (hg : g ≥ 2)
    (h1 : g ∣ a) (h2 : g ∣ a + 1) : False := by
  obtain ⟨j, rfl⟩ := h1      -- a = g * j
  obtain ⟨k, hk⟩ := h2        -- g * j + 1 = g * k
  -- k > j (else g*k ≤ g*j < g*j+1)
  suffices hgt : k > j by
    -- k ≤ j (else g*(j+1) ≤ g*k but g*(j+1) = g*j+g > g*j+1 = g*k)
    suffices hle : k ≤ j from absurd hgt (by omega)
    suffices ¬(j + 1 ≤ k) by omega
    intro hjk
    have h_mul : g * (j + 1) ≤ g * k := Nat.mul_le_mul_left g hjk
    have h_succ : g * (j + 1) = g * j + g := Nat.mul_succ g j
    omega
  suffices ¬(k ≤ j) by omega
  intro hkj
  have : g * k ≤ g * j := Nat.mul_le_mul_left g hkj
  omega

/-- For every n, there exists a prime p > n. -/
theorem primes_infinite (n : TauIdx) : ∃ p, idx_prime p ∧ p > n := by
  have hm2 : idx_factorial n + 1 ≥ 2 := Nat.succ_le_succ (idx_factorial_pos n)
  obtain ⟨p, hp, hpdvd⟩ := exists_prime_divisor (idx_factorial n + 1) hm2
  refine ⟨p, hp, ?_⟩
  suffices ¬(p ≤ n) by simp only [TauIdx] at *; omega
  intro hle
  exact not_dvd_succ_of_ge_two hp.1 (prime_dvd_factorial hp hle) hpdvd

-- ============================================================
-- PRIME FACTORIZATION [I.T09]
-- ============================================================

def list_prod : List TauIdx → TauIdx
  | [] => 1
  | x :: xs => x * list_prod xs

/-- Every n ≥ 2 is a product of primes. -/
theorem prime_product_exists (n : TauIdx) (hn : n ≥ 2) :
    ∃ ps : List TauIdx, (∀ p ∈ ps, idx_prime p) ∧ list_prod ps = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    obtain ⟨p, hp, hpn⟩ := exists_prime_divisor n hn
    obtain ⟨m, hm⟩ := hpn
    by_cases hm1 : m = 1
    · -- n = p * 1 = p
      refine ⟨[n], fun q hq => ?_, by simp [list_prod]⟩
      simp at hq; rw [hq, hm, hm1, Nat.mul_one]; exact hp
    · -- m ≥ 2
      have hm0 : m ≠ 0 := by
        intro heq; subst heq
        simp only [Nat.mul_zero] at hm
        simp only [TauIdx] at hn hm; omega
      have hm_ge2 : m ≥ 2 := by
        rcases m with _ | _ | m
        · exact absurd rfl hm0
        · exact absurd rfl hm1
        · exact Nat.le_add_left 2 m
      have hm_lt : m < n := by
        rw [hm]
        have hp2 := hp.1
        have : 2 * m ≤ p * m := Nat.mul_le_mul_right m hp2
        simp only [TauIdx] at *; omega
      obtain ⟨ps, hps, hprod⟩ := ih m hm_lt hm_ge2
      exact ⟨p :: ps, fun q hq => by
        simp at hq; rcases hq with rfl | hq
        · exact hp
        · exact hps q hq,
        by simp [list_prod, hprod, hm]⟩

-- ============================================================
-- FTA UNIQUENESS [I.T09]
-- ============================================================

/-- Product of a list of primes is ≥ 1. -/
private theorem list_prod_pos_of_primes (ps : List TauIdx)
    (hps : ∀ p ∈ ps, idx_prime p) : list_prod ps ≥ 1 := by
  induction ps with
  | nil => simp [list_prod]
  | cons p rest ih =>
    simp only [list_prod]
    have hp : p ≥ 2 := (hps p (by simp)).1
    have ihr := ih (fun q hq => hps q (List.mem_cons_of_mem p hq))
    have := Nat.mul_le_mul hp ihr
    simp only [TauIdx] at *; omega

/-- Product of primes = 1 implies empty list. -/
private theorem prod_one_implies_nil (ps : List TauIdx)
    (hps : ∀ p ∈ ps, idx_prime p) (h1 : list_prod ps = 1) : ps = [] := by
  rcases ps with _ | ⟨p, rest⟩
  · rfl
  · exfalso
    simp only [list_prod] at h1
    have hp : p ≥ 2 := (hps p (by simp)).1
    have hr : list_prod rest ≥ 1 :=
      list_prod_pos_of_primes rest (fun q hq => hps q (List.mem_cons_of_mem p hq))
    have := Nat.mul_le_mul hp hr
    simp only [TauIdx] at *; omega

/-- If p is prime and p divides a product of primes, then p is in the list. -/
theorem prime_mem_of_dvd_prod {p : TauIdx} (hp : idx_prime p)
    {ps : List TauIdx} (hps : ∀ q ∈ ps, idx_prime q) (hdvd : p ∣ list_prod ps) :
    p ∈ ps := by
  induction ps with
  | nil =>
    simp [list_prod] at hdvd
    obtain ⟨k, hk⟩ := hdvd; have := hp.1; simp only [TauIdx] at *; omega
  | cons q rest ih =>
    simp only [list_prod] at hdvd
    rcases euclid_lemma hp hdvd with h | h
    · -- p | q, both prime → p = q
      rcases (hps q (by simp)).2 p h with h' | h'
      · exfalso; have := hp.1; simp only [TauIdx] at *; omega
      · exact List.mem_cons.mpr (Or.inl h')
    · exact List.mem_cons.mpr (Or.inr
        (ih (fun q hq => hps q (List.mem_cons_of_mem _ hq)) h))

/-- Nat multiplication left cancellation. -/
private theorem nat_mul_cancel_left {a b c : Nat} (ha : a > 0)
    (h : a * b = a * c) : b = c := by
  rcases Nat.lt_or_ge b c with hbc | hbc
  · -- b < c: a*(b+1) ≤ a*c, but a*(b+1) = a*b + a > a*b = a*c
    have h1 := Nat.mul_le_mul_left a hbc
    have h2 : a * Nat.succ b = a * b + a := Nat.mul_succ a b
    omega
  · rcases Nat.lt_or_ge c b with hcb | hcb
    · have h1 := Nat.mul_le_mul_left a hcb
      have h2 : a * Nat.succ c = a * c + a := Nat.mul_succ a c
      omega
    · omega

-- Minimal sorted-list infrastructure

/-- All list elements ≥ bound. -/
private def all_ge (lo : TauIdx) : List TauIdx → Prop
  | [] => True
  | x :: rest => lo ≤ x ∧ all_ge lo rest

private theorem mem_ge_of_all_ge {lo : TauIdx} {ps : List TauIdx}
    (h : all_ge lo ps) {p : TauIdx} (hp : p ∈ ps) : lo ≤ p := by
  induction ps with
  | nil => simp at hp
  | cons q rest ih =>
    rcases List.mem_cons.mp hp with rfl | hr
    · exact h.1
    · exact ih h.2 hr

/-- Non-decreasing list (each element ≤ all successors). -/
def sorted_nd : List TauIdx → Prop
  | [] => True
  | x :: rest => all_ge x rest ∧ sorted_nd rest

/-- [I.T09] FTA uniqueness: two sorted non-decreasing prime lists
    with the same product are identical. -/
theorem prime_product_unique (ps qs : List TauIdx)
    (hps : ∀ p ∈ ps, idx_prime p) (hqs : ∀ q ∈ qs, idx_prime q)
    (hps_sorted : sorted_nd ps) (hqs_sorted : sorted_nd qs)
    (heq : list_prod ps = list_prod qs) : ps = qs := by
  induction ps generalizing qs with
  | nil =>
    exact (prod_one_implies_nil qs hqs (by simp [list_prod] at heq; exact heq.symm)).symm
  | cons p rest₁ ih =>
    rcases qs with _ | ⟨q, rest₂⟩
    · -- qs empty, ps nonempty: contradiction
      exfalso
      simp only [list_prod] at heq
      have hp : p ≥ 2 := (hps p (by simp)).1
      have hr : list_prod rest₁ ≥ 1 :=
        list_prod_pos_of_primes rest₁ (fun q hq => hps q (List.mem_cons_of_mem p hq))
      have := Nat.mul_le_mul hp hr
      simp only [TauIdx] at *; omega
    · -- Both nonempty: show p = q, then recurse
      have hp_prime : idx_prime p := hps p (by simp)
      have hq_prime : idx_prime q := hqs q (by simp)
      -- p ∈ qs (since p | product of qs)
      have hp_in_qs : p ∈ q :: rest₂ :=
        prime_mem_of_dvd_prod hp_prime hqs (heq ▸ ⟨list_prod rest₁, rfl⟩)
      -- q ∈ ps (since q | product of ps)
      have hq_in_ps : q ∈ p :: rest₁ :=
        prime_mem_of_dvd_prod hq_prime hps (heq ▸ ⟨list_prod rest₂, rfl⟩)
      -- p ≥ q (p ∈ sorted qs, q is head)
      have hp_ge_q : p ≥ q := by
        rcases List.mem_cons.mp hp_in_qs with rfl | hr
        · simp only [TauIdx] at *; omega
        · exact mem_ge_of_all_ge hqs_sorted.1 hr
      -- q ≥ p (q ∈ sorted ps, p is head)
      have hq_ge_p : q ≥ p := by
        rcases List.mem_cons.mp hq_in_ps with rfl | hr
        · simp only [TauIdx] at *; omega
        · exact mem_ge_of_all_ge hps_sorted.1 hr
      -- Therefore p = q
      have hpq : p = q := by simp only [TauIdx] at *; omega
      subst hpq
      -- Cancel p: list_prod rest₁ = list_prod rest₂
      simp only [list_prod] at heq
      have hp_pos : p > 0 := by have := hp_prime.1; simp only [TauIdx] at *; omega
      have h_rest : list_prod rest₁ = list_prod rest₂ := nat_mul_cancel_left hp_pos heq
      -- Inductive step
      have hps_rest : ∀ r ∈ rest₁, idx_prime r :=
        fun r hr => hps r (List.mem_cons_of_mem p hr)
      have hqs_rest : ∀ r ∈ rest₂, idx_prime r :=
        fun r hr => hqs r (List.mem_cons_of_mem p hr)
      exact congrArg (p :: ·) (ih rest₂ hps_rest hqs_rest hps_sorted.2 hqs_sorted.2 h_rest)

-- ============================================================
-- COMPUTABLE TOOLS
-- ============================================================

/-- p-adic valuation: how many times p divides n. -/
def p_adic_val (p n : TauIdx) : TauIdx :=
  if p ≤ 1 then 0
  else if n = 0 then 0
  else go p n n
where
  go (p n fuel : TauIdx) : TauIdx :=
    if fuel = 0 then 0
    else if n % p = 0 then 1 + go p (n / p) (fuel - 1)
    else 0
  termination_by fuel
  decreasing_by simp_wf; simp only [TauIdx] at *; omega

-- ============================================================
-- SMOKE TESTS
-- ============================================================

#eval is_prime_bool 2       -- expected: true
#eval is_prime_bool 4       -- expected: false
#eval is_prime_bool 17      -- expected: true
#eval is_prime_bool 1       -- expected: false
#eval p_adic_val 2 12       -- expected: 2
#eval p_adic_val 3 12       -- expected: 1

end Tau.Coordinates
