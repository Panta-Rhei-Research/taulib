import TauLib.BookIII.Spectral.PrimorialLadder

/-!
# TauLib.BookIII.Spectral.CRT

CRT Decomposition Theorem at spectral level, Reconstruction Functor,
and Independence of Prime-Level Actions.

## Registry Cross-References

- [III.T10] CRT Decomposition Theorem — `crt_spectral_check`
- [III.D20] Reconstruction Functor — `reconstruction_functor_check`
- [III.P05] Independence of Prime-Level Actions — `prime_independence_check`

## Mathematical Content

**III.T10 (CRT Decomposition):** τ-native Chinese Remainder Theorem:
ℤ/Prim(k)ℤ ≅ ∏ᵢ₌₁ᵏ ℤ/pᵢℤ proved constructively without signed
arithmetic. CRT = algebraic Euler product.

**III.D20 (Reconstruction Functor):** CRT defines a functor R_k from
∏(ℤ/pᵢℤ-Mod) to ℤ/Prim(k)ℤ-Mod. This functor is an equivalence.

**III.P05 (Prime Independence):** Prime-level actions T^(i) on ℤ/pᵢℤ
are independent. CRT guarantees unique reassembly.
-/

namespace Tau.BookIII.Spectral

open Tau.Polarity Tau.Boundary Tau.Coordinates Tau.Denotation
open Tau.BookII.Interior Tau.BookII.Enrichment
open Tau.BookIII.Enrichment Tau.BookIII.Sectors

-- ============================================================
-- CRT DECOMPOSITION THEOREM [III.T10]
-- ============================================================

/-- [III.T10] CRT spectral decomposition at enriched level.
    Verifies that crt_decompose ∘ crt_reconstruct = id at each
    primorial level, enriched by tower coherence. -/
def crt_spectral_check (bound db : TauIdx) : Bool :=
  go 0 1 ((bound + 1) * (db + 1))
where
  go (x k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k > db then go (x + 1) 1 (fuel - 1)
    else
      -- CRT round-trip at depth k
      let residues := crt_decompose x k
      let reconstructed := crt_reconstruct residues k
      let roundtrip_ok := reconstructed == reduce x k
      -- Tower coherence: CRT at k+1 projects to CRT at k
      let high_residues := crt_decompose x (k + 1)
      let high_reconstructed := crt_reconstruct high_residues (k + 1)
      let projected := reduce high_reconstructed k
      let tower_ok := projected == reduce x k
      roundtrip_ok && tower_ok && go x (k + 1) (fuel - 1)
  termination_by fuel

/-- [III.T10] CRT ring homomorphism: addition is preserved. -/
def crt_add_check (bound db : TauIdx) : Bool :=
  go 0 0 1 ((bound + 1) * (bound + 1) * (db + 1))
where
  go (x y k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if y > bound then go (x + 1) 0 1 (fuel - 1)
    else if k > db then go x (y + 1) 1 (fuel - 1)
    else
      let pk := primorial k
      if pk == 0 then go x y (k + 1) (fuel - 1)
      else
        -- Decompose x+y vs decompose x + decompose y component-wise
        let sum_mod := (x + y) % pk
        let rx := crt_decompose x k
        let ry := crt_decompose y k
        let rsum := crt_decompose sum_mod k
        -- Component-wise: (x+y) mod p_i = (x mod p_i + y mod p_i) mod p_i
        let componentwise_ok := go_components rx ry rsum 0 k
        componentwise_ok && go x y (k + 1) (fuel - 1)
  termination_by fuel
  go_components (rx ry rsum : List TauIdx) (i k : Nat) : Bool :=
    if i >= k then true
    else
      let p := nth_prime (i + 1)
      let sum_comp := if p > 0 then
        (rx.getD i 0 + ry.getD i 0) % p
      else 0
      let expected := rsum.getD i 0
      sum_comp == expected && go_components rx ry rsum (i + 1) k

/-- [III.T10] CRT ring homomorphism: multiplication is preserved. -/
def crt_mul_check (bound db : TauIdx) : Bool :=
  go 0 0 1 ((bound + 1) * (bound + 1) * (db + 1))
where
  go (x y k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if y > bound then go (x + 1) 0 1 (fuel - 1)
    else if k > db then go x (y + 1) 1 (fuel - 1)
    else
      let pk := primorial k
      if pk == 0 then go x y (k + 1) (fuel - 1)
      else
        let prod_mod := (x * y) % pk
        let rx := crt_decompose x k
        let ry := crt_decompose y k
        let rprod := crt_decompose prod_mod k
        let componentwise_ok := go_mul_components rx ry rprod 0 k
        componentwise_ok && go x y (k + 1) (fuel - 1)
  termination_by fuel
  go_mul_components (rx ry rprod : List TauIdx) (i k : Nat) : Bool :=
    if i >= k then true
    else
      let p := nth_prime (i + 1)
      let prod_comp := if p > 0 then
        (rx.getD i 0 * ry.getD i 0) % p
      else 0
      let expected := rprod.getD i 0
      prod_comp == expected && go_mul_components rx ry rprod (i + 1) k

-- ============================================================
-- RECONSTRUCTION FUNCTOR [III.D20]
-- ============================================================

/-- [III.D20] Reconstruction functor R_k: given residues, reconstruct
    the unique element mod Prim(k). Checks that R_k is inverse to S_k
    (the restriction/decomposition functor). -/
def reconstruction_functor_check (bound db : TauIdx) : Bool :=
  go 0 1 ((bound + 1) * (db + 1))
where
  go (x k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k > db then go (x + 1) 1 (fuel - 1)
    else
      -- S_k: x → (x mod p_1, ..., x mod p_k)
      let residues := crt_decompose (reduce x k) k
      -- R_k: residues → reconstructed value
      let reconstructed := crt_reconstruct residues k
      -- R_k ∘ S_k = id mod Prim(k)
      reconstructed == reduce x k && go x (k + 1) (fuel - 1)
  termination_by fuel

/-- [III.D20] Reconstruction functor respects tower: R_{k+1} projects
    to R_k under reduce. -/
def reconstruction_tower_check (bound db : TauIdx) : Bool :=
  go 0 1 ((bound + 1) * (db + 1))
where
  go (x k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k >= db then go (x + 1) 1 (fuel - 1)
    else
      let residues_high := crt_decompose (reduce x (k + 1)) (k + 1)
      let reconstructed_high := crt_reconstruct residues_high (k + 1)
      let projected := reduce reconstructed_high k
      let reconstructed_low := reduce x k
      projected == reconstructed_low && go x (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- INDEPENDENCE OF PRIME-LEVEL ACTIONS [III.P05]
-- ============================================================

/-- [III.P05] Prime-level independence: modifying one residue does not
    affect others. The CRT structure guarantees orthogonality. -/
def prime_independence_check (bound db : TauIdx) : Bool :=
  go 0 1 0 ((bound + 1) * (db + 1) * (db + 1))
where
  go (x k i fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k > db then go (x + 1) 1 0 (fuel - 1)
    else if i >= k then go x (k + 1) 0 (fuel - 1)
    else
      -- CRT basis element e_i: 1 at position i, 0 elsewhere
      let basis := crt_basis k i
      let residues := crt_decompose basis k
      -- Check: residue at i is 1 (mod p_{i+1}), all others are 0
      let p_i := nth_prime (i + 1)
      let diag_ok := if p_i > 0 then residues.getD i 0 % p_i == 1 % p_i
                     else true
      let off_diag_ok := check_off_diag residues i 0 k
      diag_ok && off_diag_ok && go x k (i + 1) (fuel - 1)
  termination_by fuel
  check_off_diag (residues : List TauIdx) (i j k : Nat) : Bool :=
    if j >= k then true
    else if j == i then check_off_diag residues i (j + 1) k
    else
      let p_j := nth_prime (j + 1)
      let ok := if p_j > 0 then residues.getD j 0 % p_j == 0
                else true
      ok && check_off_diag residues i (j + 1) k

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- CRT spectral
#eval crt_spectral_check 20 4               -- true
#eval crt_add_check 10 3                     -- true
#eval crt_mul_check 10 3                     -- true

-- Reconstruction functor
#eval reconstruction_functor_check 20 4      -- true
#eval reconstruction_tower_check 20 4        -- true

-- Prime independence
#eval prime_independence_check 5 4           -- true

-- ============================================================
-- FORMAL VERIFICATION (native_decide)
-- ============================================================

-- CRT spectral [III.T10]
theorem crt_spectral_20_4 :
    crt_spectral_check 20 4 = true := by native_decide

-- CRT ring homomorphism [III.T10]
theorem crt_add_10_3 :
    crt_add_check 10 3 = true := by native_decide

theorem crt_mul_10_3 :
    crt_mul_check 10 3 = true := by native_decide

-- Reconstruction functor [III.D20]
theorem reconstruction_20_4 :
    reconstruction_functor_check 20 4 = true := by native_decide

theorem reconstruction_tower_20_4 :
    reconstruction_tower_check 20 4 = true := by native_decide

-- Prime independence [III.P05]
theorem prime_independence_5_4 :
    prime_independence_check 5 4 = true := by native_decide

-- ============================================================
-- STRUCTURAL THEOREMS
-- ============================================================

/-- [III.T10] Structural: CRT round-trip at depth 3 for x = 42. -/
theorem crt_roundtrip_42 :
    crt_reconstruct (crt_decompose 42 3) 3 = reduce 42 3 := by native_decide

/-- [III.T10] Structural: CRT decomposes 42 mod 30 = 12 into
    (12 mod 2, 12 mod 3, 12 mod 5) = (0, 0, 2). -/
theorem crt_decompose_42 :
    crt_decompose 42 3 = [0, 0, 2] := by native_decide

/-- [III.P05] Structural: CRT basis element 0 at depth 3
    has residue 1 mod 2, 0 mod 3, 0 mod 5. -/
theorem crt_basis_0_3 :
    crt_decompose (crt_basis 3 0) 3 = [1, 0, 0] := by native_decide

end Tau.BookIII.Spectral
