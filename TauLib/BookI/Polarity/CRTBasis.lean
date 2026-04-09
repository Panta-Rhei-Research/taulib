import TauLib.BookI.Polarity.ChineseRemainder
import TauLib.BookI.Polarity.NthPrime

/-!
# TauLib.BookI.Polarity.CRTBasis

Formal proofs of CRT basis orthogonality and the CRT round-trip theorem.
All results are universal (∀ depth, ∀ inputs), parameterized by `CRTHyp k`.

## Main Results

- `coprime_product`: coprimality preserved under multiplication
- `prime_coprime_primorial`: p_{k+1} coprime to M_k
- `cofactor_coprime`: M_k/p_{i+1} coprime to p_{i+1}
- `crt_basis_diagonal`: e_i ≡ 1 (mod p_{i+1})
- `crt_basis_off_diagonal`: e_i ≡ 0 (mod p_{j+1}) for j ≠ i
- `crt_unique_mod`: CRT uniqueness direction
- `crt_roundtrip_formal`: CRT round-trip theorem
-/

namespace Tau.Polarity

open Tau.Denotation Tau.Coordinates

-- ============================================================
-- SECTION 1: COPRIME PRODUCT LEMMA
-- ============================================================

/-- coprime(a,c) ∧ coprime(b,c) → coprime(a*b,c).
    Proof by prime factor contradiction using euclid_lemma. -/
theorem coprime_product {a b c : Nat}
    (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c) :
    Nat.Coprime (a * b) c := by
  by_contra hne
  -- gcd(a*b, c) ≥ 2
  have hne0 : Nat.gcd (a * b) c ≠ 0 := by
    intro h0
    apply hne
    -- gcd = 0 → c = 0
    have hc0 : c = 0 := by
      rcases Nat.gcd_dvd_right (a * b) c with ⟨k, hk⟩
      rw [h0, Nat.zero_mul] at hk; exact hk
    subst hc0
    -- hac : Coprime a 0, hbc : Coprime b 0 — unwrap to gcd form
    have ha : Nat.gcd a 0 = 1 := hac
    have hb : Nat.gcd b 0 = 1 := hbc
    rw [Nat.gcd_zero_right] at ha hb
    show Nat.gcd (a * b) 0 = 1
    rw [Nat.gcd_zero_right, ha, hb]
  have hge2 : Nat.gcd (a * b) c ≥ 2 := by omega
  obtain ⟨p, hp, hpdvd⟩ := exists_prime_divisor _ hge2
  have hpab : p ∣ a * b := dvd_trans hpdvd (Nat.gcd_dvd_left _ _)
  have hpc : p ∣ c := dvd_trans hpdvd (Nat.gcd_dvd_right _ _)
  rcases euclid_lemma hp hpab with hpa | hpb
  · -- p | a and p | c → p | gcd(a,c) = 1, but p ≥ 2
    have h1 := Nat.le_of_dvd (by omega) (Nat.dvd_gcd hpa hpc)
    rw [hac] at h1; have := hp.1; simp only [TauIdx] at *; omega
  · have h1 := Nat.le_of_dvd (by omega) (Nat.dvd_gcd hpb hpc)
    rw [hbc] at h1; have := hp.1; simp only [TauIdx] at *; omega

/-- Symmetric form: coprime(c,a) ∧ coprime(c,b) → coprime(c,a*b). -/
theorem coprime_product_right {a b c : Nat}
    (hca : Nat.Coprime c a) (hcb : Nat.Coprime c b) :
    Nat.Coprime c (a * b) :=
  (coprime_product hca.symm hcb.symm).symm

-- ============================================================
-- SECTION 2: PRIME COPRIME TO PRIMORIAL
-- ============================================================

/-- Any prime that is pairwise coprime to all primes in M_k is coprime to M_k. -/
private theorem coprime_primorial_of_coprime_primes {m : TauIdx} :
    ∀ {k : TauIdx}, (∀ j, j < k → Nat.Coprime (nth_prime m) (nth_prime (j + 1))) →
    Nat.Coprime (nth_prime m) (primorial k) := by
  intro k
  induction k with
  | zero =>
    intro _
    show Nat.gcd (nth_prime m) 1 = 1
    exact Nat.gcd_one_right _
  | succ n ih =>
    intro h
    simp only [primorial]
    apply coprime_product_right
    · exact h n (by simp only [TauIdx]; omega)
    · exact ih (fun j hj => h j (by simp only [TauIdx] at *; omega))

/-- The (k+1)-th prime is coprime to the k-th primorial. -/
theorem prime_coprime_primorial {k : TauIdx} (hyp : CRTHyp (k + 1)) :
    Nat.Coprime (nth_prime (k + 1)) (primorial k) :=
  coprime_primorial_of_coprime_primes fun j hj =>
    hyp.pairwise_coprime k j
      (by simp only [TauIdx] at *; omega)
      (by simp only [TauIdx] at *; omega)
      (by simp only [TauIdx] at *; omega)

-- ============================================================
-- SECTION 3: COFACTOR PROPERTIES
-- ============================================================

/-- Exact division: cofactor * p_{i+1} = M_k. -/
theorem cofactor_exact {k i : TauIdx} (hi : i + 1 ≤ k) :
    primorial k / nth_prime (i + 1) * nth_prime (i + 1) = primorial k :=
  Nat.div_mul_cancel (nth_prime_dvd_primorial hi)

/-- Key induction: the primorial cofactor M_k/p_{i+1} is coprime to p_{i+1}. -/
theorem cofactor_coprime : ∀ {k i : TauIdx}, i < k → CRTHyp k →
    Nat.Coprime (primorial k / nth_prime (i + 1)) (nth_prime (i + 1)) := by
  intro k
  induction k with
  | zero => intro i hi; exact absurd hi (Nat.not_succ_le_zero i)
  | succ n ih =>
    intro i hi hyp
    simp only [primorial]
    rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hi) with heq | hlt
    · -- i = n: cofactor = (p_{n+1} * M_n) / p_{n+1} = M_n
      rw [heq, Nat.mul_div_cancel_left _ (by
        have := nth_prime_pos (show n + 1 ≥ 1 by omega)
        simp only [TauIdx] at *; omega)]
      exact (prime_coprime_primorial hyp).symm
    · -- i < n: cofactor = p_{n+1} * (M_n / p_{i+1})
      have hi_n : i + 1 ≤ n := by simp only [TauIdx] at *; omega
      rw [Nat.mul_div_assoc _ (nth_prime_dvd_primorial hi_n)]
      apply coprime_product
      · -- Coprime p_{n+1} p_{i+1}
        exact hyp.pairwise_coprime n i
          (by simp only [TauIdx] at *; omega)
          (by simp only [TauIdx] at *; omega)
          (by simp only [TauIdx] at *; omega)
      · -- Coprime (M_n/p_{i+1}) p_{i+1}: IH
        exact ih (by simp only [TauIdx] at *; omega)
          ⟨fun j hj => hyp.all_prime j (by simp only [TauIdx] at *; omega),
           fun j l hj hl hjl => hyp.pairwise_coprime j l
             (by simp only [TauIdx] at *; omega) (by simp only [TauIdx] at *; omega) hjl⟩

-- ============================================================
-- SECTION 4: OTHER PRIME DIVIDES COFACTOR
-- ============================================================

/-- p_{j+1} divides the cofactor M_k/p_{i+1} when j ≠ i (both < k). -/
theorem other_prime_dvd_cofactor {k i j : TauIdx}
    (hi : i < k) (hj : j < k) (hne : i ≠ j) (hyp : CRTHyp k) :
    nth_prime (j + 1) ∣ primorial k / nth_prime (i + 1) := by
  have hjdvd := nth_prime_dvd_primorial (show j + 1 ≤ k by simp only [TauIdx] at *; omega)
  rw [← cofactor_exact (show i + 1 ≤ k by simp only [TauIdx] at *; omega)] at hjdvd
  have hp_j := hyp.all_prime j hj
  rcases euclid_lemma hp_j hjdvd with h | h
  · exact h
  · -- p_{j+1} | p_{i+1}: contradiction
    exfalso
    have hcop := hyp.pairwise_coprime j i hj hi (Ne.symm hne)
    -- p_{j+1} | p_{i+1} and gcd(p_{j+1}, p_{i+1}) = 1, but p_{j+1} ≥ 2
    have hle := Nat.le_of_dvd
      (by have := (hyp.all_prime i hi).1; simp only [TauIdx] at *; omega)
      (Nat.dvd_gcd ⟨1, (Nat.mul_one _).symm⟩ h)
    rw [hcop] at hle
    have := hp_j.1; simp only [TauIdx] at *; omega

-- ============================================================
-- SECTION 5: CRT BASIS ORTHOGONALITY
-- ============================================================

/-- Helper: if a ∣ b then (b * c) % a = 0. -/
private theorem mul_mod_eq_zero_of_dvd {a b c : Nat} (h : a ∣ b) :
    (b * c) % a = 0 := by
  obtain ⟨k, rfl⟩ := h
  rw [Nat.mul_assoc, Nat.mul_mod_right]

/-- e_i ≡ 1 (mod p_{i+1}): diagonal case of CRT basis orthogonality. -/
theorem crt_basis_diagonal {k i : TauIdx} (hi : i < k) (hyp : CRTHyp k) :
    crt_basis k i % nth_prime (i + 1) = 1 := by
  simp only [crt_basis]
  -- (cofactor * mod_inv cofactor pi) % M_k % pi
  -- Step 1: % M_k % pi = % pi (since pi | M_k)
  rw [mod_mod_of_dvd _ _ _
    (nth_prime_dvd_primorial (show i + 1 ≤ k by simp only [TauIdx] at *; omega))]
  -- Step 2: mod_inv_correct gives (cofactor * mod_inv cofactor pi) % pi = 1
  exact mod_inv_correct _ _
    (cofactor_coprime hi hyp)
    (by have := (hyp.all_prime i hi).1; simp only [TauIdx] at *; omega)

/-- e_i ≡ 0 (mod p_{j+1}) for j ≠ i: off-diagonal case. -/
theorem crt_basis_off_diagonal {k i j : TauIdx}
    (hi : i < k) (hj : j < k) (hne : i ≠ j) (hyp : CRTHyp k) :
    crt_basis k i % nth_prime (j + 1) = 0 := by
  simp only [crt_basis]
  -- Step 1: % M_k % pj = % pj
  rw [mod_mod_of_dvd _ _ _
    (nth_prime_dvd_primorial (show j + 1 ≤ k by simp only [TauIdx] at *; omega))]
  -- Step 2: pj | cofactor, so (cofactor * anything) % pj = 0
  exact mul_mod_eq_zero_of_dvd (other_prime_dvd_cofactor hi hj hne hyp)

-- ============================================================
-- SMOKE TESTS: Formal proofs at concrete depths
-- ============================================================

-- Diagonal: formal
example : crt_basis 5 0 % nth_prime 1 = 1 :=
  crt_basis_diagonal (by simp only [TauIdx]; omega) crt_hyp_5
example : crt_basis 5 2 % nth_prime 3 = 1 :=
  crt_basis_diagonal (by simp only [TauIdx]; omega) crt_hyp_5
example : crt_basis 5 4 % nth_prime 5 = 1 :=
  crt_basis_diagonal (by simp only [TauIdx]; omega) crt_hyp_5

-- Off-diagonal: formal
example : crt_basis 5 0 % nth_prime 2 = 0 :=
  crt_basis_off_diagonal (by simp only [TauIdx]; omega)
    (by simp only [TauIdx]; omega) (by simp only [TauIdx]; omega) crt_hyp_5
example : crt_basis 5 3 % nth_prime 1 = 0 :=
  crt_basis_off_diagonal (by simp only [TauIdx]; omega)
    (by simp only [TauIdx]; omega) (by simp only [TauIdx]; omega) crt_hyp_5

-- ============================================================
-- SECTION 6: CRT UNIQUENESS
-- ============================================================

/-- If a % m = 0 then m ∣ a. -/
private theorem dvd_of_mod_eq_zero {a m : Nat} (h : a % m = 0) : m ∣ a := by
  have := Nat.div_add_mod a m; rw [h, Nat.add_zero] at this
  exact ⟨a / m, this.symm⟩

/-- If m ∣ a then a % m = 0. -/
private theorem mod_eq_zero_of_dvd' {a m : Nat} (h : m ∣ a) : a % m = 0 := by
  obtain ⟨k, rfl⟩ := h; exact Nat.mul_mod_right m k

/-- Coprime divisibility product: gcd(p,q)=1, p∣n, q∣n → p*q∣n. -/
theorem coprime_mul_dvd {p q n : Nat} (hcop : Nat.Coprime p q)
    (hp : p ∣ n) (hq : q ∣ n) : p * q ∣ n := by
  obtain ⟨k, rfl⟩ := hp
  have : q ∣ k := hcop.symm.dvd_of_dvd_mul_left hq
  obtain ⟨j, rfl⟩ := this
  exact ⟨j, by rw [Nat.mul_assoc]⟩

/-- a ≥ b and a%m = b%m implies (a-b)%m = 0. -/
private theorem mod_sub_eq_zero {a b m : Nat} (hab : a ≥ b) (h : a % m = b % m) :
    (a - b) % m = 0 := by
  by_cases hm : m = 0
  · subst hm; simp at h; omega
  · have hm_pos : m > 0 := Nat.pos_of_ne_zero hm
    have key : (b + (a - b)) % m = b % m := by rw [Nat.add_sub_cancel' hab, h]
    rw [Nat.add_mod] at key
    have hr := Nat.mod_lt b hm_pos
    have hd := Nat.mod_lt (a - b) hm_pos
    -- key : (b%m + (a-b)%m) % m = b%m, with b%m < m and (a-b)%m < m
    rcases Nat.lt_or_ge (b % m + (a - b) % m) m with h1 | h1
    · rw [Nat.mod_eq_of_lt h1] at key; omega
    · have h2 : b % m + (a - b) % m < m + m := by omega
      rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)] at key; omega

/-- (a-b)%m = 0 and a ≥ b implies a%m = b%m. -/
private theorem mod_eq_of_sub_eq_zero {a b m : Nat} (hab : a ≥ b)
    (h : (a - b) % m = 0) : a % m = b % m := by
  by_cases hm : m = 0
  · subst hm; simp at h; omega
  · -- (a-b)%m = 0 → a-b = m*q → a = m*q + b → a%m = b%m
    have hk := Nat.div_add_mod (a - b) m
    rw [h, Nat.add_zero] at hk
    -- hk : m * ((a-b)/m) = a - b
    conv_lhs => rw [show a = m * ((a - b) / m) + b from by omega]
    rw [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add,
      mod_mod_of_dvd _ _ _ ⟨1, (Nat.mul_one _).symm⟩]

/-- Two-modulus CRT uniqueness step. -/
private theorem mod_eq_of_coprime_mod_eq {a b p q : Nat}
    (hcop : Nat.Coprime p q)
    (hp : a % p = b % p) (hq : a % q = b % q) :
    a % (p * q) = b % (p * q) := by
  rcases Nat.le_total a b with hab | hba
  · exact (mod_eq_of_sub_eq_zero hab
      (mod_eq_zero_of_dvd' (coprime_mul_dvd hcop
        (dvd_of_mod_eq_zero (mod_sub_eq_zero hab hp.symm))
        (dvd_of_mod_eq_zero (mod_sub_eq_zero hab hq.symm))))).symm
  · exact mod_eq_of_sub_eq_zero hba
      (mod_eq_zero_of_dvd' (coprime_mul_dvd hcop
        (dvd_of_mod_eq_zero (mod_sub_eq_zero hba hp))
        (dvd_of_mod_eq_zero (mod_sub_eq_zero hba hq))))

/-- CRT uniqueness: pointwise agreement at each prime implies agreement
    modulo the primorial. -/
theorem crt_unique_mod : ∀ {k : TauIdx}, CRTHyp k →
    ∀ {a b : TauIdx},
    (∀ l, l < k → a % nth_prime (l + 1) = b % nth_prime (l + 1)) →
    a % primorial k = b % primorial k := by
  intro k; induction k with
  | zero => intro _ _ _ _; simp only [primorial, Nat.mod_one]
  | succ n ih =>
    intro hyp a b h
    simp only [primorial]
    apply mod_eq_of_coprime_mod_eq (prime_coprime_primorial hyp)
    · exact h n (by simp only [TauIdx]; omega)
    · exact ih
        ⟨fun j hj => hyp.all_prime j (by simp only [TauIdx] at *; omega),
         fun j l hj hl hjl => hyp.pairwise_coprime j l
           (by simp only [TauIdx] at *; omega)
           (by simp only [TauIdx] at *; omega) hjl⟩
        (fun l hl => h l (by simp only [TauIdx] at *; omega))

-- Formal smoke test: CRT uniqueness at depth 5
example : ∀ a b, (∀ l, l < 5 → a % nth_prime (l + 1) = b % nth_prime (l + 1)) →
    a % primorial 5 = b % primorial 5 :=
  fun _ _ h => crt_unique_mod crt_hyp_5 h

-- ============================================================
-- SECTION 7: CRT ROUND-TRIP
-- ============================================================

/-- Helper: crt_decompose x k has l-th element = x % p_{l+1} when l < k. -/
private theorem crt_decompose_getD {x k l : TauIdx} (hl : l < k) :
    (crt_decompose x k).getD l 0 = x % nth_prime (l + 1) := by
  simp only [crt_decompose, List.getD, List.getElem?_map,
    List.getElem?_range hl, Option.map, Option.getD_some]

/-- crt_reconstruct_go result < primorial k when acc < primorial k. -/
private theorem crt_reconstruct_go_lt (residues : List TauIdx) (k : TauIdx)
    (hk : primorial k > 0) :
    ∀ (i fuel : Nat) (acc : TauIdx), acc < primorial k →
    crt_reconstruct_go residues k i fuel acc < primorial k := by
  intro i fuel
  induction fuel generalizing i with
  | zero => intro acc hacc; unfold crt_reconstruct_go; simp; exact hacc
  | succ n ih =>
    intro acc hacc
    unfold crt_reconstruct_go
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    split
    · exact hacc
    · exact ih (i + 1) _ (Nat.mod_lt _ hk)

/-- crt_reconstruct result < primorial k. -/
private theorem crt_reconstruct_lt {k : TauIdx} (residues : List TauIdx)
    (hk : primorial k > 0) :
    crt_reconstruct residues k < primorial k := by
  simp only [crt_reconstruct]
  exact crt_reconstruct_go_lt residues k hk 0 k 0 hk

/-- Off-diagonal: adding r * e_i doesn't change result mod p_{l+1}. -/
private theorem add_mul_basis_off_diag {acc r k i l : TauIdx}
    (hi : i < k) (hl : l < k) (hne : i ≠ l) (hyp : CRTHyp k) :
    (acc + r * crt_basis k i) % nth_prime (l + 1) = acc % nth_prime (l + 1) := by
  have h0 : crt_basis k i % nth_prime (l + 1) = 0 := crt_basis_off_diagonal hi hl hne hyp
  have h1 : (r * crt_basis k i) % nth_prime (l + 1) = 0 := by
    rw [Nat.mul_mod, h0, Nat.mul_zero, Nat.zero_mod]
  rw [Nat.add_mod, h1, Nat.add_zero,
    mod_mod_of_dvd _ _ _ ⟨1, (Nat.mul_one _).symm⟩]

/-- Diagonal: adding r * e_i changes result mod p_{i+1} by r. -/
private theorem add_mul_basis_diag {acc r k i : TauIdx}
    (hi : i < k) (hyp : CRTHyp k) :
    (acc + r * crt_basis k i) % nth_prime (i + 1) = (acc + r) % nth_prime (i + 1) := by
  have h1 : crt_basis k i % nth_prime (i + 1) = 1 := crt_basis_diagonal hi hyp
  rw [Nat.add_mod acc (r * _), Nat.mul_mod, h1, Nat.mul_one,
    mod_mod_of_dvd _ _ _ ⟨1, (Nat.mul_one _).symm⟩, ← Nat.add_mod]

/-- Reducing mod M_k is invisible mod p_{l+1}. -/
private theorem add_mod_primorial {a b k l : TauIdx}
    (hl : l < k) :
    (a % primorial k + b) % nth_prime (l + 1) = (a + b) % nth_prime (l + 1) := by
  rw [Nat.add_mod, mod_mod_of_dvd _ _ _
    (nth_prime_dvd_primorial (show l + 1 ≤ k by simp only [TauIdx] at *; omega)),
    ← Nat.add_mod]

/-- Accumulator invariant: crt_reconstruct_go modulo p_{l+1} picks up exactly
    the l-th residue (all other contributions vanish by basis orthogonality). -/
private theorem crt_reconstruct_go_mod_prime
    {k l : TauIdx} (residues : List TauIdx) (hl : l < k) (hyp : CRTHyp k) :
    ∀ (i fuel : Nat) (acc : TauIdx), i ≤ k → fuel ≥ k - i →
    crt_reconstruct_go residues k i fuel acc % nth_prime (l + 1) =
    (acc + if l ≥ i then residues.getD l 0 else 0) % nth_prime (l + 1) := by
  intro i fuel
  induction fuel generalizing i with
  | zero =>
    intro acc hi hfuel
    have hik : i = k := by omega
    unfold crt_reconstruct_go; simp
    rw [hik]
    have hlk : ¬(l ≥ k) := by simp only [TauIdx] at *; omega
    simp [hlk]
  | succ n ih =>
    intro acc hi hfuel
    unfold crt_reconstruct_go
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    split
    · -- i ≥ k: returns acc
      rename_i hige
      have hlti : ¬(l ≥ i) := by simp only [TauIdx] at *; omega
      simp [hlti]
    · -- i < k: take one step
      rename_i hige
      have hilt : i < k := by simp only [TauIdx] at *; omega
      -- Simplify fuel: n + 1 - 1 = n (clear afterward to not confuse omega)
      have hfuel_simp : n + 1 - 1 = n := by omega
      rw [hfuel_simp]; clear hfuel_simp
      -- Apply IH at i+1
      rw [ih (i + 1) _ (by omega) (by omega)]
      -- Clear hfuel (Nat subtraction confuses omega)
      clear hfuel
      -- Goal: (acc' + if l ≥ i+1 ...) % p = (acc + if l ≥ i ...) % p
      -- where acc' = (acc + r_i * e_i) % M_k
      by_cases hli : l = i
      · -- Diagonal: l = i (subst eliminates i, keeps l)
        subst hli
        rw [if_neg (show ¬(l ≥ l + 1) from by simp only [TauIdx] at *; omega), Nat.add_zero,
          if_pos (Nat.le_refl l)]
        -- Goal: ((acc + rl * el) % Mk) % p = (acc + rl) % p
        rw [mod_mod_of_dvd _ _ _
          (nth_prime_dvd_primorial (show l + 1 ≤ k by simp only [TauIdx] at *; omega))]
        exact add_mul_basis_diag hilt hyp
      · by_cases hlti : l < i
        · -- l < i: both ifs are false
          rw [if_neg (show ¬(l ≥ i + 1) from by simp only [TauIdx] at *; omega),
            if_neg (show ¬(l ≥ i) from by simp only [TauIdx] at *; omega),
            Nat.add_zero, Nat.add_zero]
          rw [mod_mod_of_dvd _ _ _
            (nth_prime_dvd_primorial (show l + 1 ≤ k by simp only [TauIdx] at *; omega))]
          exact add_mul_basis_off_diag hilt hl
            (by simp only [TauIdx] at *; omega) hyp
        · -- l > i: both ifs are true, same residue
          have hlgei1 : l ≥ i + 1 := by simp only [TauIdx] at *; omega
          have hlgei : l ≥ i := by simp only [TauIdx] at *; omega
          have hne_il : i ≠ l := by simp only [TauIdx] at *; omega
          rw [if_pos hlgei1, if_pos hlgei]
          -- Goal: ((acc + ri*ei) % Mk + rl) % p = (acc + rl) % p
          rw [add_mod_primorial hl]
          -- Rearrange: acc + ri*ei + rl = (acc + rl) + ri*ei
          rw [Nat.add_assoc,
            Nat.add_comm (residues.getD i 0 * crt_basis k i) (residues.getD l 0),
            ← Nat.add_assoc]
          exact add_mul_basis_off_diag hilt hl hne_il hyp

/-- CRT round-trip: reconstruct ∘ decompose = id (mod M_k). -/
theorem crt_roundtrip_formal {x k : TauIdx} (hyp : CRTHyp k) :
    crt_reconstruct (crt_decompose x k) k = x % primorial k := by
  -- Strategy: show both sides agree mod each prime, then apply CRT uniqueness.
  have h_agree : ∀ l, l < k →
      crt_reconstruct (crt_decompose x k) k % nth_prime (l + 1) =
      x % nth_prime (l + 1) := by
    intro l hl
    simp only [crt_reconstruct]
    rw [crt_reconstruct_go_mod_prime _ hl hyp 0 k 0 (Nat.zero_le k) (by omega)]
    simp only [Nat.zero_le, ↓reduceIte, Nat.zero_add]
    -- Goal: (crt_decompose x k).getD l 0 % p_{l+1} = x % p_{l+1}
    rw [crt_decompose_getD hl]
    -- Goal: x % p_{l+1} % p_{l+1} = x % p_{l+1}
    exact mod_mod_of_dvd x _ _ ⟨1, (Nat.mul_one _).symm⟩
  -- CRT uniqueness gives agreement mod M_k
  have h_mod := crt_unique_mod hyp h_agree
  -- h_mod : crt_reconstruct ... % M_k = x % M_k
  -- LHS is already < M_k, so % M_k is a no-op
  rw [Nat.mod_eq_of_lt (crt_reconstruct_lt _ (primorial_pos k))] at h_mod
  exact h_mod

-- Formal smoke tests
example : crt_reconstruct (crt_decompose 42 5) 5 = 42 % primorial 5 :=
  crt_roundtrip_formal crt_hyp_5
example : crt_reconstruct (crt_decompose 100 5) 5 = 100 % primorial 5 :=
  crt_roundtrip_formal crt_hyp_5
example : crt_reconstruct (crt_decompose 0 5) 5 = 0 % primorial 5 :=
  crt_roundtrip_formal crt_hyp_5

-- ============================================================
-- SECTION 8: CRT PROJECTION (public interface)
-- ============================================================

/-- CRT projection: crt_reconstruct residues k mod p_{l+1} = residues[l] mod p_{l+1}.
    This is the key interface theorem for downstream formal proofs
    (Teichmüller retraction, orthogonality, etc.). -/
theorem crt_reconstruct_mod_prime {k l : TauIdx} (residues : List TauIdx)
    (hl : l < k) (hyp : CRTHyp k) :
    crt_reconstruct residues k % nth_prime (l + 1) =
    residues.getD l 0 % nth_prime (l + 1) := by
  simp only [crt_reconstruct]
  rw [crt_reconstruct_go_mod_prime _ hl hyp 0 k 0 (Nat.zero_le k) (by omega)]
  simp only [Nat.zero_le, ↓reduceIte, Nat.zero_add]

end Tau.Polarity
