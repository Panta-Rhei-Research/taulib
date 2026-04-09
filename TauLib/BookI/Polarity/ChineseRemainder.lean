import TauLib.BookI.Polarity.ModArith
import TauLib.BookI.Polarity.ExtGCD

/-!
# TauLib.BookI.Polarity.ChineseRemainder

Chinese Remainder Theorem decomposition and reconstruction on the primorial ladder.

## Registry Cross-References

- [I.D29] CRT Decomposition — `crt_decompose`, `crt_reconstruct`, `crt_basis`
- [I.D28] Boundary Local Ring — CRT structure of Z/M_kZ

## Ground Truth Sources
- chunk_0243_M002286: CRT chapter, constructive decomposition via coprime idempotents
- chunk_0314_M002691: Finite-stage CRT, CRT coherence with primorial reduction

## Mathematical Content

The Chinese Remainder Theorem for the primorial M_k = p₁ · p₂ · ... · p_k gives:
  Z/M_kZ ≅ Z/p₁Z × Z/p₂Z × ... × Z/p_kZ

Forward map (decomposition): x ↦ (x mod p₁, ..., x mod p_k)
Inverse map (reconstruction): (r₁,...,r_k) ↦ Σ rᵢ · eᵢ mod M_k
where eᵢ = (M_k/pᵢ) · (M_k/pᵢ)⁻¹ mod M_k are coprime idempotents.

All constructions are computable. Correctness is verified by extensive native_decide.
-/

namespace Tau.Polarity

open Tau.Denotation

-- ============================================================
-- MODULAR INVERSE (brute-force search)
-- ============================================================

/-- Find modular inverse of a mod m by brute-force search.
    Returns x such that (a * x) % m = 1, or 0 if not found. -/
def mod_inv_go (a m x fuel : Nat) : Nat :=
  if fuel = 0 then 0
  else if (a * x) % m == 1 then x
  else mod_inv_go a m (x + 1) (fuel - 1)
termination_by fuel

/-- Modular inverse: a⁻¹ mod m. Correct for coprime a, m with m > 1. -/
def mod_inv (a m : Nat) : Nat := mod_inv_go a m 1 m

-- ============================================================
-- MODULAR INVERSE: FORMAL CORRECTNESS
-- ============================================================

/-- mod_inv_go finds a valid inverse when one exists in range. -/
theorem mod_inv_go_correct (a m x fuel : Nat)
    (h_exists : ∃ y, x ≤ y ∧ y < x + fuel ∧ (a * y) % m = 1) :
    (a * mod_inv_go a m x fuel) % m = 1 := by
  induction fuel generalizing x with
  | zero =>
    obtain ⟨y, _, hy_lt, _⟩ := h_exists; omega
  | succ n ih =>
    unfold mod_inv_go
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    split
    · rename_i heq; exact beq_iff_eq.mp heq
    · rename_i hne
      apply ih
      obtain ⟨y, hxy, hy_lt, hy_mod⟩ := h_exists
      refine ⟨y, ?_, by omega, hy_mod⟩
      rcases Nat.eq_or_lt_of_le hxy with rfl | hlt
      · exfalso; exact (beq_iff_eq.not.mp hne) hy_mod
      · omega

/-- mod_inv is correct for coprime inputs with m > 1. -/
theorem mod_inv_correct (a m : Nat) (hcop : Nat.Coprime a m) (hm : m > 1) :
    (a * mod_inv a m) % m = 1 := by
  unfold mod_inv
  apply mod_inv_go_correct
  obtain ⟨x, hx_lt, hx_mod⟩ := mod_inv_exists a m hcop hm
  have hx1 : x ≥ 1 := by
    rcases x with _ | x
    · -- x = 0: (a * 0) % m = 0 % m = 0 ≠ 1
      simp at hx_mod
    · exact Nat.succ_le_succ (Nat.zero_le x)
  exact ⟨x, hx1, by omega, hx_mod⟩

-- ============================================================
-- CRT FORWARD MAP (decomposition)
-- ============================================================

/-- CRT forward map: x ↦ (x mod p₁, ..., x mod p_k).
    Returns the list of residues modulo each prime. -/
def crt_decompose (x k : TauIdx) : List TauIdx :=
  (List.range k).map (fun i => x % nth_prime (i + 1))

-- ============================================================
-- CRT BASIS ELEMENTS (coprime idempotents)
-- ============================================================

/-- CRT basis element eᵢ: the unique element of Z/M_kZ with
    eᵢ ≡ 1 (mod pᵢ) and eᵢ ≡ 0 (mod pⱼ) for j ≠ i.
    i is 0-indexed: crt_basis k 0 corresponds to p₁. -/
def crt_basis (k i : TauIdx) : TauIdx :=
  let mk := primorial k
  let pi := nth_prime (i + 1)
  let cofactor := mk / pi
  (cofactor * mod_inv cofactor pi) % mk

-- ============================================================
-- CRT INVERSE MAP (reconstruction)
-- ============================================================

/-- CRT reconstruction accumulator: Σ rᵢ · eᵢ mod M_k. -/
def crt_reconstruct_go (residues : List TauIdx) (k : TauIdx) (i fuel : Nat)
    (acc : TauIdx) : TauIdx :=
  if fuel = 0 then acc
  else if i ≥ k then acc
  else
    let ri := residues.getD i 0
    let ei := crt_basis k i
    crt_reconstruct_go residues k (i + 1) (fuel - 1) ((acc + ri * ei) % primorial k)
termination_by fuel

/-- CRT inverse map: (r₁,...,r_k) ↦ Σ rᵢ · eᵢ mod M_k. -/
def crt_reconstruct (residues : List TauIdx) (k : TauIdx) : TauIdx :=
  crt_reconstruct_go residues k 0 k 0

-- ============================================================
-- VERIFICATION PREDICATES
-- ============================================================

/-- CRT basis orthogonality: eᵢ mod pⱼ = δᵢⱼ. -/
def crt_basis_check (k i j : TauIdx) : Bool :=
  crt_basis k i % nth_prime (j + 1) == (if i == j then 1 else 0)

/-- CRT round-trip: decompose ∘ reconstruct = id (mod M_k). -/
def crt_roundtrip_check (x k : TauIdx) : Bool :=
  crt_reconstruct (crt_decompose x k) k == x % primorial k

/-- CRT coherence: reducing CRT output from depth l to depth k
    gives the same as CRT at depth k with first k residues. -/
def crt_coherence_check (x k l : TauIdx) : Bool :=
  k ≤ l && (crt_reconstruct (crt_decompose x l) l % primorial k ==
            crt_reconstruct (crt_decompose x k) k)

/-- CRT full-range check: round-trip holds for all x in [0, M_k). -/
def crt_exhaustive_check_go (k x : TauIdx) (fuel : Nat) : Bool :=
  if fuel = 0 then true
  else if x ≥ primorial k then true
  else crt_roundtrip_check x k && crt_exhaustive_check_go k (x + 1) (fuel - 1)
termination_by fuel

def crt_exhaustive_check (k : TauIdx) : Bool :=
  crt_exhaustive_check_go k 0 (primorial k)

-- ============================================================
-- CRT IDEMPOTENT PROPERTIES
-- ============================================================

/-- eᵢ · eᵢ ≡ eᵢ (mod M_k): each basis element is idempotent. -/
def crt_idempotent_check (k i : TauIdx) : Bool :=
  let mk := primorial k
  let ei := crt_basis k i
  (ei * ei) % mk == ei

/-- eᵢ · eⱼ ≡ 0 (mod M_k) for i ≠ j: distinct basis elements are orthogonal. -/
def crt_orthogonal_check (k i j : TauIdx) : Bool :=
  i == j || (crt_basis k i * crt_basis k j) % primorial k == 0

/-- Σ eᵢ ≡ 1 (mod M_k): basis elements sum to unity. -/
def crt_partition_go (k : TauIdx) (i fuel : Nat) (acc : TauIdx) : TauIdx :=
  if fuel = 0 then acc
  else if i ≥ k then acc
  else crt_partition_go k (i + 1) (fuel - 1) ((acc + crt_basis k i) % primorial k)
termination_by fuel

def crt_partition_check (k : TauIdx) : Bool :=
  crt_partition_go k 0 k 0 == 1 % primorial k

-- ============================================================
-- NATIVE_DECIDE VERIFICATIONS: Basis Orthogonality
-- ============================================================

-- k=3: primes 2,3,5; M_3=30
-- e_0 (for p=2): e_0 mod 2 = 1, e_0 mod 3 = 0, e_0 mod 5 = 0
example : crt_basis_check 3 0 0 = true := by native_decide
example : crt_basis_check 3 0 1 = true := by native_decide
example : crt_basis_check 3 0 2 = true := by native_decide
-- e_1 (for p=3): e_1 mod 2 = 0, e_1 mod 3 = 1, e_1 mod 5 = 0
example : crt_basis_check 3 1 0 = true := by native_decide
example : crt_basis_check 3 1 1 = true := by native_decide
example : crt_basis_check 3 1 2 = true := by native_decide
-- e_2 (for p=5): e_2 mod 2 = 0, e_2 mod 3 = 0, e_2 mod 5 = 1
example : crt_basis_check 3 2 0 = true := by native_decide
example : crt_basis_check 3 2 1 = true := by native_decide
example : crt_basis_check 3 2 2 = true := by native_decide

-- k=4: primes 2,3,5,7; M_4=210
example : crt_basis_check 4 0 0 = true := by native_decide
example : crt_basis_check 4 0 1 = true := by native_decide
example : crt_basis_check 4 0 2 = true := by native_decide
example : crt_basis_check 4 0 3 = true := by native_decide
example : crt_basis_check 4 1 0 = true := by native_decide
example : crt_basis_check 4 1 1 = true := by native_decide
example : crt_basis_check 4 1 2 = true := by native_decide
example : crt_basis_check 4 1 3 = true := by native_decide
example : crt_basis_check 4 2 0 = true := by native_decide
example : crt_basis_check 4 2 1 = true := by native_decide
example : crt_basis_check 4 2 2 = true := by native_decide
example : crt_basis_check 4 2 3 = true := by native_decide
example : crt_basis_check 4 3 0 = true := by native_decide
example : crt_basis_check 4 3 1 = true := by native_decide
example : crt_basis_check 4 3 2 = true := by native_decide
example : crt_basis_check 4 3 3 = true := by native_decide

-- k=5: spot checks at depth 5 (M_5=2310)
example : crt_basis_check 5 0 0 = true := by native_decide
example : crt_basis_check 5 2 2 = true := by native_decide
example : crt_basis_check 5 4 4 = true := by native_decide
example : crt_basis_check 5 0 3 = true := by native_decide
example : crt_basis_check 5 3 0 = true := by native_decide

-- ============================================================
-- NATIVE_DECIDE VERIFICATIONS: Idempotent & Orthogonal
-- ============================================================

-- Idempotent: eᵢ² = eᵢ
example : crt_idempotent_check 3 0 = true := by native_decide
example : crt_idempotent_check 3 1 = true := by native_decide
example : crt_idempotent_check 3 2 = true := by native_decide
example : crt_idempotent_check 4 0 = true := by native_decide
example : crt_idempotent_check 4 1 = true := by native_decide
example : crt_idempotent_check 4 2 = true := by native_decide
example : crt_idempotent_check 4 3 = true := by native_decide
example : crt_idempotent_check 5 0 = true := by native_decide
example : crt_idempotent_check 5 4 = true := by native_decide

-- Orthogonal: eᵢ · eⱼ = 0 for i ≠ j
example : crt_orthogonal_check 3 0 1 = true := by native_decide
example : crt_orthogonal_check 3 0 2 = true := by native_decide
example : crt_orthogonal_check 3 1 2 = true := by native_decide
example : crt_orthogonal_check 4 0 1 = true := by native_decide
example : crt_orthogonal_check 4 0 3 = true := by native_decide
example : crt_orthogonal_check 4 2 3 = true := by native_decide

-- Partition of unity: Σ eᵢ = 1
example : crt_partition_check 1 = true := by native_decide
example : crt_partition_check 2 = true := by native_decide
example : crt_partition_check 3 = true := by native_decide
example : crt_partition_check 4 = true := by native_decide
example : crt_partition_check 5 = true := by native_decide

-- ============================================================
-- NATIVE_DECIDE VERIFICATIONS: Round-Trip
-- ============================================================

-- Spot checks at various depths
example : crt_roundtrip_check 0 3 = true := by native_decide
example : crt_roundtrip_check 1 3 = true := by native_decide
example : crt_roundtrip_check 7 3 = true := by native_decide
example : crt_roundtrip_check 29 3 = true := by native_decide
example : crt_roundtrip_check 42 3 = true := by native_decide
example : crt_roundtrip_check 100 3 = true := by native_decide

example : crt_roundtrip_check 0 4 = true := by native_decide
example : crt_roundtrip_check 7 4 = true := by native_decide
example : crt_roundtrip_check 42 4 = true := by native_decide
example : crt_roundtrip_check 100 4 = true := by native_decide
example : crt_roundtrip_check 209 4 = true := by native_decide

example : crt_roundtrip_check 0 5 = true := by native_decide
example : crt_roundtrip_check 7 5 = true := by native_decide
example : crt_roundtrip_check 42 5 = true := by native_decide
example : crt_roundtrip_check 100 5 = true := by native_decide
example : crt_roundtrip_check 1000 5 = true := by native_decide
example : crt_roundtrip_check 2309 5 = true := by native_decide

-- Exhaustive round-trip at small depths
example : crt_exhaustive_check 1 = true := by native_decide
example : crt_exhaustive_check 2 = true := by native_decide
example : crt_exhaustive_check 3 = true := by native_decide

-- ============================================================
-- NATIVE_DECIDE VERIFICATIONS: Coherence
-- ============================================================

-- Coherence: CRT at depth l reduced to depth k = CRT at depth k
example : crt_coherence_check 7 2 3 = true := by native_decide
example : crt_coherence_check 7 2 4 = true := by native_decide
example : crt_coherence_check 7 3 5 = true := by native_decide
example : crt_coherence_check 42 1 3 = true := by native_decide
example : crt_coherence_check 42 2 5 = true := by native_decide
example : crt_coherence_check 100 3 4 = true := by native_decide
example : crt_coherence_check 100 1 5 = true := by native_decide
example : crt_coherence_check 1000 2 4 = true := by native_decide
example : crt_coherence_check 1000 3 5 = true := by native_decide

-- ============================================================
-- CRT HOMOMORPHISM CHECKS
-- ============================================================

/-- CRT is a ring homomorphism: decompose(a+b) = decompose(a) + decompose(b) mod primes. -/
def crt_add_hom_check (a b k : TauIdx) : Bool :=
  let sum_decomp := crt_decompose (a + b) k
  let a_decomp := crt_decompose a k
  let b_decomp := crt_decompose b k
  (List.range k).all (fun i =>
    sum_decomp.getD i 0 == (a_decomp.getD i 0 + b_decomp.getD i 0) % nth_prime (i + 1))

/-- CRT is a ring homomorphism: decompose(a*b) = decompose(a) * decompose(b) mod primes. -/
def crt_mul_hom_check (a b k : TauIdx) : Bool :=
  let prod_decomp := crt_decompose (a * b) k
  let a_decomp := crt_decompose a k
  let b_decomp := crt_decompose b k
  (List.range k).all (fun i =>
    prod_decomp.getD i 0 == (a_decomp.getD i 0 * b_decomp.getD i 0) % nth_prime (i + 1))

-- CRT preserves addition
example : crt_add_hom_check 7 42 5 = true := by native_decide
example : crt_add_hom_check 100 200 5 = true := by native_decide
example : crt_add_hom_check 3 1000 4 = true := by native_decide

-- CRT preserves multiplication
example : crt_mul_hom_check 7 6 5 = true := by native_decide
example : crt_mul_hom_check 10 10 5 = true := by native_decide
example : crt_mul_hom_check 42 100 4 = true := by native_decide

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Modular inverses
#eval mod_inv 3 2     -- 1: 3*1 = 3 ≡ 1 (mod 2)
#eval mod_inv 5 3     -- 2: 5*2 = 10 ≡ 1 (mod 3)
#eval mod_inv 6 5     -- 1: 6*1 = 6 ≡ 1 (mod 5)
#eval mod_inv 15 7    -- 1: 15*1 = 15 ≡ 1 (mod 7)

-- CRT basis elements for k=3 (primes 2,3,5; M_3=30)
#eval crt_basis 3 0   -- e_0: ≡1 mod 2, ≡0 mod 3, ≡0 mod 5
#eval crt_basis 3 1   -- e_1: ≡0 mod 2, ≡1 mod 3, ≡0 mod 5
#eval crt_basis 3 2   -- e_2: ≡0 mod 2, ≡0 mod 3, ≡1 mod 5

-- CRT decompose
#eval crt_decompose 42 3   -- [0, 0, 2] (42 mod 2, 42 mod 3, 42 mod 5)
#eval crt_decompose 7 4    -- [1, 1, 2, 0] (7 mod 2, 7 mod 3, 7 mod 5, 7 mod 7)

-- CRT reconstruct
#eval crt_reconstruct (crt_decompose 42 3) 3   -- 12 (= 42 mod 30)
#eval crt_reconstruct (crt_decompose 7 4) 4    -- 7 (= 7 mod 210)
#eval crt_reconstruct (crt_decompose 100 5) 5  -- 100 (= 100 mod 2310)

-- Round-trip verification
#eval crt_roundtrip_check 42 3    -- true
#eval crt_roundtrip_check 7 4     -- true
#eval crt_roundtrip_check 100 5   -- true

-- Coherence
#eval crt_coherence_check 7 2 4   -- true
#eval crt_coherence_check 100 3 5 -- true

-- Exhaustive check at depth 3 (all 30 elements of Z/30Z)
#eval crt_exhaustive_check 3      -- true

-- Partition of unity
#eval crt_partition_check 3       -- true
#eval crt_partition_check 4       -- true
#eval crt_partition_check 5       -- true

end Tau.Polarity
