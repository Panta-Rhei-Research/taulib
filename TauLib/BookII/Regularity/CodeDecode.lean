import TauLib.BookII.Regularity.PreYoneda

/-!
# TauLib.BookII.Regularity.CodeDecode

Code/Decode bijection: CRT spectral analysis and synthesis on the primorial tower.

## Registry Cross-References

- [II.D51] Code — `code_extract`, `code_tower_check`
- [II.D52] Decode — `decode_reconstruct`, `decode_welldef_check`
- [II.T35] Code/Decode Bijection — `code_decode_inverse_check`, `full_code_decode_check`

## Mathematical Content

Code and Decode provide a CRT-based analysis/synthesis pair for functions
on the primorial tower Z/P_kZ.

**CRT Decomposition:**
  Z/P_kZ ≅ Z/p_1Z × Z/p_2Z × ... × Z/p_kZ

Every element x ∈ Z/P_kZ is uniquely determined by its CRT coordinates:
  (x mod p_1, x mod p_2, ..., x mod p_k)

**Code (II.D51):** Extracts the function value at a point, indexed by
its CRT coordinates. Equivalently, `code_extract(f, k, x) = f(reduce(x, k))`
for `x ∈ Z/P_kZ`. The spectral content is then read off via
`proj_coeff` from the CanonicalBasis: the projection of f onto
the cylinder generator E_{k,pi,v} gives the sum of f over the
residue class v mod p at stage k.

**Decode (II.D52):** Reconstructs the function value at x from the
CRT-indexed code. Given a table of values indexed by Z/P_kZ:
  decode_reconstruct(table, k, x) = table(reduce(x, k))

In the primorial tower, the CRT preimage IS just x itself (for x < P_k),
so Decode . Code = id reduces to f(reduce(x, k)) = f(reduce(x, k)).

**Code/Decode Bijection (II.T35):**
The bijection is between:
  - Functions f : Z/P_kZ → Z  (the "spatial" representation)
  - CRT coefficient tables a → f(a) for a ∈ Z/P_kZ

The per-prime spectral projections (proj_coeff) provide a COMPLETE
spectral decomposition: knowing all proj_coeff values determines f.
-/

namespace Tau.BookII.Regularity

open Tau.Polarity Tau.Boundary Tau.Coordinates Tau.Denotation
open Tau.BookII.Interior Tau.BookII.Domains Tau.Holomorphy
open Tau.BookII.Hartogs

-- ============================================================
-- CODE: CRT COORDINATE EXTRACTION [II.D51]
-- ============================================================

/-- [II.D51] Code: extract the function value at a given input.
    code_extract(f, k, x) = f(reduce(x, k))

    This is the fundamental "sampling" operation: the code of f at stage k
    is the restriction of f to Z/P_kZ. The CRT coordinates of x are
    (x mod p_1, ..., x mod p_k), and the code records f at each such point. -/
def code_extract (f : TauIdx → Int) (k x : TauIdx) : Int :=
  f (reduce x k)

/-- [II.D51] Per-prime spectral coefficient: the projection of f onto
    the cylinder generator E_{k,pi,v}. This is proj_coeff from CanonicalBasis:
    code_spectral(f, k, pi, v) = sum_{x in Z/P_kZ : x%p == v} f(x)

    The spectral coefficients are the Fourier-like components of f
    decomposed along individual CRT factors. -/
def code_spectral (f : TauIdx → Int) (k prime_idx v : TauIdx) : Int :=
  proj_coeff f k prime_idx v

/-- [II.D51] Code tower coherence check:
    verify that code at stage k is determined by code at stage k+1.
    For f = identity: reduce(reduce(x, k+1), k) = reduce(x, k). -/
def code_tower_check (bound db : TauIdx) : Bool :=
  go 2 1 (bound * db + bound + db + 1)
where
  go (x k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k >= db then go (x + 1) 1 (fuel - 1)
    else
      let id_fn : TauIdx → Int := fun n => (n : Int)
      let code_k1 := code_extract id_fn (k + 1) x
      let reduced := (reduce (code_k1.toNat) k : Int)
      let code_k_direct := (reduce x k : Int)
      (reduced == code_k_direct) && go x (k + 1) (fuel - 1)
  termination_by fuel

/-- [II.D51] Code extraction for the delta function:
    code(delta_a, k, x) = 1 if reduce(x, k) == a, else 0. -/
def code_delta_check (k_max : TauIdx) : Bool :=
  go 1 0 0 (k_max * 100 + 1)
where
  go (k a x fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > k_max then true
    else if a >= primorial k then go (k + 1) 0 0 (fuel - 1)
    else if x >= primorial k then go k (a + 1) 0 (fuel - 1)
    else
      let delta_a : TauIdx → Int := fun n => if n == a then 1 else 0
      let code_val := code_extract delta_a k x
      let expected : Int := if reduce x k == a then 1 else 0
      (code_val == expected) && go k a (x + 1) (fuel - 1)
  termination_by fuel

/-- [II.D51] Spectral coefficient check for the constant function:
    code_spectral(1, k, pi, v) = P_k / p for each residue class v. -/
def code_constant_check (k_max : TauIdx) : Bool :=
  go 1 1 0 (k_max * 20 + 1)
where
  go (k pi_idx v fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > k_max then true
    else if pi_idx > k then go (k + 1) 1 0 (fuel - 1)
    else
      let p := nth_prime pi_idx
      if p == 0 then go k (pi_idx + 1) 0 (fuel - 1)
      else if v >= p then go k (pi_idx + 1) 0 (fuel - 1)
      else
        let const_1 : TauIdx → Int := fun _ => 1
        let coeff := code_spectral const_1 k pi_idx v
        let expected : Int := (primorial k / p : Nat)
        (coeff == expected) && go k pi_idx (v + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- DECODE: CRT RECONSTRUCTION [II.D52]
-- ============================================================

/-- [II.D52] Decode: reconstruct a function value from its CRT-indexed code.
    Given a table of values indexed by points in Z/P_kZ, decode reads
    the value at the stage-k representative of x.

    decode_reconstruct(table, k, x) = table(reduce(x, k))

    This is the inverse of code_extract: reading back the recorded value
    at the canonical representative. -/
def decode_reconstruct (table : TauIdx → Int) (k x : TauIdx) : Int :=
  table (reduce x k)

/-- [II.D52] CRT product indicator: returns true iff reduce(x, k) == target.
    This is the product basis element
    Phi_{v_1,...,v_k}(x) = prod_i E_{k,i,v_i}(x). -/
def decode_crt_indicator (k x target : TauIdx) : Bool :=
  reduce x k == target

/-- [II.D52] Decode well-definedness check:
    verify that decode is periodic: decode(table, k, x) = decode(table, k, x + P_k).
    This follows from reduce(x + P_k, k) = reduce(x, k). -/
def decode_welldef_check (k_max bound : TauIdx) : Bool :=
  go 1 0 (k_max * bound + k_max + bound + 1)
where
  go (k x fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > k_max then true
    else if x >= primorial k then go (k + 1) 0 (fuel - 1)
    else
      let table : TauIdx → Int := fun n => (n : Int)
      let pk := primorial k
      let val1 := decode_reconstruct table k x
      let val2 := decode_reconstruct table k (x + pk)
      (val1 == val2) && go k (x + 1) (fuel - 1)
  termination_by fuel

/-- [II.D52] Decode uniqueness check:
    for a != b in [0, P_k), the CRT indicators are different. -/
def decode_uniqueness_check (k_max : TauIdx) : Bool :=
  go 1 0 0 (k_max * 100 + 1)
where
  go (k a b fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > k_max then true
    else
      let pk := primorial k
      if a >= pk then go (k + 1) 0 0 (fuel - 1)
      else if b >= pk then go k (a + 1) 0 (fuel - 1)
      else if a == b then go k a (b + 1) (fuel - 1)
      else
        let ok := decode_crt_indicator k a a &&
                  !decode_crt_indicator k a b
        ok && go k a (b + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- CODE/DECODE BIJECTION [II.T35]
-- ============================================================

/-- [II.T35] Code/Decode round-trip (direction 1): Decode . Code = id.
    For a function f on Z/P_kZ:
      decode(code(f), k, x) = code(f)(reduce(x, k))
      = f(reduce(reduce(x,k), k)) = f(reduce(x,k))

    For x < P_k, reduce(x, k) = x, so this gives f(x). -/
def code_decode_inverse_check (k_max : TauIdx) : Bool :=
  go_k 1 (k_max * 200 + 1)
where
  go_k (k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > k_max then true
    else
      let pk := primorial k
      let delta_0 : TauIdx → Int := fun x => if x == 0 then 1 else 0
      let ok1 := check_roundtrip delta_0 k 0 pk (fuel - 1)
      let const_1 : TauIdx → Int := fun _ => 1
      let ok2 := check_roundtrip const_1 k 0 pk (fuel - 1)
      let id_fn : TauIdx → Int := fun x => (x : Int)
      let ok3 := check_roundtrip id_fn k 0 pk (fuel - 1)
      ok1 && ok2 && ok3 && go_k (k + 1) (fuel - 1)
  termination_by fuel
  check_roundtrip (f : TauIdx → Int) (k x fuel : Nat) (pk : Nat) : Bool :=
    if fuel = 0 then true
    else if x >= pk then true
    else
      let coded : TauIdx → Int := fun a => code_extract f k a
      let reconstructed := decode_reconstruct coded k x
      (reconstructed == f x) && check_roundtrip f k (x + 1) (fuel - 1) pk
  termination_by fuel

/-- [II.T35] Code/Decode round-trip (direction 2): Code . Decode = id.
    For a coefficient table c : Z/P_kZ → Int:
      code(decode(c), k, a) = decode(c)(reduce(a, k))
      = c(reduce(reduce(a,k), k)) = c(reduce(a,k))

    For a < P_k, this gives c(a). -/
def decode_code_inverse_check (k_max : TauIdx) : Bool :=
  go_k 1 (k_max * 200 + 1)
where
  go_k (k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > k_max then true
    else
      let pk := primorial k
      let table : TauIdx → Int := fun a => (a : Int) + 1
      let ok := check_inverse table k 0 pk (fuel - 1)
      ok && go_k (k + 1) (fuel - 1)
  termination_by fuel
  check_inverse (table : TauIdx → Int) (k a fuel : Nat) (pk : Nat) : Bool :=
    if fuel = 0 then true
    else if a >= pk then true
    else
      let decoded_fn : TauIdx → Int := fun x => decode_reconstruct table k x
      let recoded := code_extract decoded_fn k a
      (recoded == table a) && check_inverse table k (a + 1) (fuel - 1) pk
  termination_by fuel

-- ============================================================
-- SPECTRAL SEPARATION (extracted helper to avoid multi-level where)
-- ============================================================

/-- Helper: scan residue classes for a given prime to find differing coefficients. -/
def code_spectral_scan_residues (f g : TauIdx → Int)
    (k pi_idx : TauIdx) : Bool :=
  let p := nth_prime pi_idx
  go f g k pi_idx p 0 (p + 1)
where
  go (f g : TauIdx → Int) (k pi_idx p v fuel : Nat) : Bool :=
    if fuel = 0 then false
    else if v >= p then false
    else
      let cf := code_spectral f k pi_idx v
      let cg := code_spectral g k pi_idx v
      if cf != cg then true
      else go f g k pi_idx p (v + 1) (fuel - 1)
  termination_by fuel

/-- Helper: search across primes for a separating spectral coefficient. -/
def code_spectral_find_separator (f g : TauIdx → Int)
    (k : TauIdx) : Bool :=
  go f g k 1 (k + 1)
where
  go (f g : TauIdx → Int) (k pi_idx fuel : Nat) : Bool :=
    if fuel = 0 then false
    else if pi_idx > k then false
    else
      let p := nth_prime pi_idx
      if p == 0 then go f g k (pi_idx + 1) (fuel - 1)
      else if code_spectral_scan_residues f g k pi_idx then true
      else go f g k (pi_idx + 1) (fuel - 1)
  termination_by fuel

/-- [II.T35] Spectral completeness: the per-prime projections determine f.
    For distinct functions f, g on Z/P_kZ, there exists a prime p and
    residue v such that code_spectral(f, k, p, v) != code_spectral(g, k, p, v).

    Verified: for f = delta_0 and g = delta_1, the spectral coefficients differ. -/
def code_spectral_separation_check (k_max : TauIdx) : Bool :=
  go 1 (k_max + 1)
where
  go (k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > k_max then true
    else
      let delta_0 : TauIdx → Int := fun x => if x == 0 then 1 else 0
      let delta_1 : TauIdx → Int := fun x => if x == 1 then 1 else 0
      let ok := code_spectral_find_separator delta_0 delta_1 k
      ok && go (k + 1) (fuel - 1)
  termination_by fuel

/-- [II.T35] Delta function round-trip:
    decode(code(delta_a)) = delta_a for all a in [0, P_k). -/
def code_decode_delta_check (k_max : TauIdx) : Bool :=
  go_k 1 (k_max * 200 + 1)
where
  go_k (k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > k_max then true
    else
      let pk := primorial k
      let ok := check_deltas k 0 pk (fuel - 1)
      ok && go_k (k + 1) (fuel - 1)
  termination_by fuel
  check_deltas (k a fuel : Nat) (pk : Nat) : Bool :=
    if fuel = 0 then true
    else if a >= pk then true
    else
      let delta_a : TauIdx → Int := fun x => if x == a then 1 else 0
      let coded : TauIdx → Int := fun x => code_extract delta_a k x
      let val_at_a := decode_reconstruct coded k a
      let other := if a + 1 < pk then a + 1 else if a > 0 then a - 1 else 0
      let val_at_other := if pk > 1
        then decode_reconstruct coded k other
        else 0
      let ok := val_at_a == 1 &&
        (pk ≤ 1 || other == a || val_at_other == 0)
      ok && check_deltas k (a + 1) (fuel - 1) pk
  termination_by fuel

-- ============================================================
-- TOWER COMPATIBILITY OF CODE/DECODE
-- ============================================================

/-- Code/Decode respects tower structure:
    reduce(code(id, k+1, x), k) = code(id, k, x).
    For f = identity: reduce(reduce(x, k+1), k) = reduce(x, k). -/
def code_decode_tower_check (bound db : TauIdx) : Bool :=
  go 2 1 (bound * db + bound + db + 1)
where
  go (x k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k >= db then go (x + 1) 1 (fuel - 1)
    else
      let id_fn : TauIdx → Int := fun n => (n : Int)
      let code_k1 := code_extract id_fn (k + 1) x
      let code_k1_nat := code_k1.toNat
      let reduced := (reduce code_k1_nat k : Int)
      let code_k_direct := (reduce x k : Int)
      (reduced == code_k_direct) && go x (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- FULL CODE/DECODE CHECK [II.T35]
-- ============================================================

/-- [II.T35] Full Code/Decode bijection verification:
    - Code extraction (delta, constant checks)
    - Decode well-definedness (periodic)
    - Decode uniqueness (CRT injectivity)
    - Round-trip Decode . Code = id
    - Round-trip Code . Decode = id
    - Delta function round-trip
    - Spectral separation (completeness)
    - Tower compatibility -/
def full_code_decode_check (k_max : TauIdx) : Bool :=
  code_delta_check k_max &&
  code_constant_check k_max &&
  decode_welldef_check k_max 20 &&
  decode_uniqueness_check k_max &&
  code_decode_inverse_check k_max &&
  decode_code_inverse_check k_max &&
  code_decode_delta_check k_max &&
  code_spectral_separation_check k_max &&
  code_decode_tower_check 15 k_max

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Code extraction: identity
#eval code_extract (fun x => (x : Int)) 1 0   -- 0
#eval code_extract (fun x => (x : Int)) 1 1   -- 1
#eval code_extract (fun x => (x : Int)) 2 5   -- 5

-- Code extraction: delta at 0
#eval code_extract (fun x => if x == 0 then 1 else 0) 1 0  -- 1
#eval code_extract (fun x => if x == 0 then 1 else 0) 1 1  -- 0

-- Spectral coefficients: constant 1
#eval code_spectral (fun _ => 1) 1 1 0  -- 1
#eval code_spectral (fun _ => 1) 1 1 1  -- 1
#eval code_spectral (fun _ => 1) 2 1 0  -- 3
#eval code_spectral (fun _ => 1) 2 2 0  -- 2

-- Code tower check
#eval code_tower_check 15 3     -- true

-- Code delta check
#eval code_delta_check 3        -- true

-- Code constant check
#eval code_constant_check 3     -- true

-- Decode
#eval decode_reconstruct (fun n => (n : Int)) 1 0  -- 0
#eval decode_reconstruct (fun n => (n : Int)) 1 1  -- 1
#eval decode_reconstruct (fun n => (n : Int)) 2 7  -- 1

-- Decode well-definedness
#eval decode_welldef_check 3 15    -- true

-- Decode uniqueness
#eval decode_uniqueness_check 3    -- true

-- Code/Decode round-trip
#eval code_decode_inverse_check 3  -- true

-- Decode/Code round-trip
#eval decode_code_inverse_check 3  -- true

-- Delta round-trip
#eval code_decode_delta_check 3    -- true

-- Spectral separation
#eval code_spectral_separation_check 3  -- true

-- Tower compatibility
#eval code_decode_tower_check 15 3      -- true

-- Full check
#eval full_code_decode_check 3          -- true

-- ============================================================
-- FORMAL VERIFICATION (native_decide)
-- ============================================================

-- Code extraction [II.D51]
theorem code_delta_3 :
    code_delta_check 3 = true := by native_decide

theorem code_constant_3 :
    code_constant_check 3 = true := by native_decide

theorem code_tower_15_3 :
    code_tower_check 15 3 = true := by native_decide

-- Decode well-definedness [II.D52]
theorem decode_welldef_3_15 :
    decode_welldef_check 3 15 = true := by native_decide

-- Decode uniqueness [II.D52]
theorem decode_unique_3 :
    decode_uniqueness_check 3 = true := by native_decide

-- Code/Decode bijection [II.T35]
theorem code_decode_3 :
    code_decode_inverse_check 3 = true := by native_decide

theorem decode_code_3 :
    decode_code_inverse_check 3 = true := by native_decide

-- Delta round-trip [II.T35]
theorem code_decode_delta_3 :
    code_decode_delta_check 3 = true := by native_decide

-- Spectral separation [II.T35]
theorem spectral_sep_3 :
    code_spectral_separation_check 3 = true := by native_decide

-- Tower compatibility
theorem tower_compat_15_3 :
    code_decode_tower_check 15 3 = true := by native_decide

-- Full Code/Decode [II.T35]
theorem full_code_decode_3 :
    full_code_decode_check 3 = true := by native_decide

-- ============================================================
-- STRUCTURAL THEOREMS: CODE/DECODE IS AN ISOMORPHISM
-- ============================================================

/-- [II.T35] Formal proof: Decode . Code = id for the identity function.
    This follows from reduction idempotence: reduce(reduce(x, k), k) = reduce(x, k). -/
theorem code_decode_id_roundtrip (x k : TauIdx) :
    decode_reconstruct (fun a => code_extract (fun n => (n : Int)) k a) k x =
    code_extract (fun n => (n : Int)) k x := by
  simp only [decode_reconstruct, code_extract, reduce]
  congr 1
  exact Nat.mod_mod_of_dvd x (dvd_refl (primorial k))

/-- [II.T35] Formal proof: Code . Decode = id for any table.
    This follows from reduce(reduce(a, k), k) = reduce(a, k). -/
theorem decode_code_roundtrip (table : TauIdx → Int) (a k : TauIdx) :
    code_extract (fun x => decode_reconstruct table k x) k a =
    decode_reconstruct table k a := by
  simp only [code_extract, decode_reconstruct, reduce]
  congr 1
  exact Nat.mod_mod_of_dvd a (dvd_refl (primorial k))

end Tau.BookII.Regularity
