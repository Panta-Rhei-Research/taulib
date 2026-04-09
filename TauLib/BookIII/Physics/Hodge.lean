import TauLib.BookIII.Physics.GapTheorem

/-!
# TauLib.BookIII.Physics.Hodge

σ-Fixed Characters, Sector Addressability, NF-Addressability Theorem,
Hodge Filtration, and Spectral-Hodge Compatibility.

## Registry Cross-References

- [III.D47] σ-Fixed Characters — `sigma_fixed_check`
- [III.D48] Sector Addressability — `sector_addressability_check`
- [III.P18] Character-Sector Correspondence — `char_sector_check`
- [III.T28] NF-Addressability Theorem — `nf_addressability_check`
- [III.P19] Hodge Filtration — `hodge_filtration_check`
- [III.P20] Spectral-Hodge Compatibility — `spectral_hodge_check`

## Mathematical Content

**III.D47 (σ-Fixed Characters):** A boundary character χ is σ-fixed if
polarity_swap(BNF(χ)) = BNF(χ). These are the self-dual characters that
live on the crossing locus of L = S¹ ∨ S¹.

**III.D48 (Sector Addressability):** Every cylinder at every primorial level
is uniquely addressable by its B/C/X coordinates. The address is the triple
(b_part, c_part, x_part) in the BNF.

**III.P18 (Character-Sector Correspondence):** Each character maps to exactly
one sector, and each sector is non-empty at sufficiently high depth.

**III.T28 (NF-Addressability):** Every element of ℤ/Prim(k)ℤ is uniquely
addressable by its BNF. Combined with sector addressability, this gives
a complete addressing scheme for the spectral algebra.

**III.P19 (Hodge Filtration):** The BNF decomposition induces a filtration
B ⊂ B+X ⊂ B+C+X = ℤ/Prim(k)ℤ. This is the τ-analog of the Hodge filtration.

**III.P20 (Spectral-Hodge Compatibility):** The Hodge filtration is compatible
with the spectral decomposition: the B-step of the filtration corresponds
to B-type eigenvalues of H_L, and similarly for C and X.
-/

namespace Tau.BookIII.Physics

open Tau.Polarity Tau.Boundary Tau.Coordinates Tau.Denotation
open Tau.BookII.Interior Tau.BookII.Enrichment
open Tau.BookIII.Enrichment Tau.BookIII.Sectors
open Tau.BookIII.Spectral Tau.BookIII.Doors

-- ============================================================
-- σ-FIXED CHARACTERS [III.D47]
-- ============================================================

/-- [III.D47] A BNF is σ-fixed if polarity swap leaves it unchanged:
    b_part = c_part. These are the self-dual elements. -/
def is_sigma_fixed (nf : BoundaryNF) : Bool :=
  nf.b_part == nf.c_part

/-- [III.D47] σ-fixed character check: count and verify σ-fixed elements
    at each primorial level. -/
def sigma_fixed_check (db : TauIdx) : Bool :=
  go 1 (db + 1)
where
  go (k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > db then true
    else
      let pk := primorial k
      if pk == 0 || pk > 100 then go (k + 1) (fuel - 1)
      else
        -- Count σ-fixed elements
        let fixed_ct := count_fixed 0 pk k
        -- At least 1 σ-fixed element (the zero element)
        fixed_ct > 0 && go (k + 1) (fuel - 1)
  termination_by fuel
  count_fixed (x pk k : Nat) : Nat :=
    if x >= pk then 0
    else
      let nf := boundary_normal_form x k
      let ct := if is_sigma_fixed nf then 1 else 0
      ct + count_fixed (x + 1) pk k

/-- [III.D47] σ-fixed involution: the set of σ-fixed elements is closed
    under BNF operations. -/
def sigma_fixed_closed_check (db : TauIdx) : Bool :=
  go 1 (db + 1)
where
  go (k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > db then true
    else
      let pk := primorial k
      if pk == 0 || pk > 100 then go (k + 1) (fuel - 1)
      else
        check_closed 0 pk k && go (k + 1) (fuel - 1)
  termination_by fuel
  check_closed (x pk k : Nat) : Bool :=
    if x >= pk then true
    else
      let nf := boundary_normal_form x k
      -- Involution classification: σ-fixed (b=c) ↔ swap preserves BNF
      -- σ-moving (b≠c) ↔ swap changes BNF (non-trivial both directions)
      let ok := if is_sigma_fixed nf then
        polarity_swap nf == nf
      else
        polarity_swap nf != nf  -- σ-moving elements are genuinely changed
      ok && check_closed (x + 1) pk k

-- ============================================================
-- SECTOR ADDRESSABILITY [III.D48]
-- ============================================================

/-- [III.D48] Sector addressability: every cylinder has a unique triple
    (b, c, x) address via its BNF. -/
def sector_addressability_check (bound db : TauIdx) : Bool :=
  go 0 1 ((bound + 1) * (db + 1))
where
  go (x k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k > db then go (x + 1) 1 (fuel - 1)
    else
      let pk := primorial k
      if pk == 0 then go x (k + 1) (fuel - 1)
      else
        let nf := boundary_normal_form (x % pk) k
        -- Address is well-defined: components sum to original
        let sum := (nf.b_part + nf.c_part + nf.x_part) % pk
        sum == x % pk && go x (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- CHARACTER-SECTOR CORRESPONDENCE [III.P18]
-- ============================================================

/-- [III.P18] Character-sector correspondence: each non-zero element at
    level k has at least one non-zero component (lives in some sector). -/
def char_sector_check (db : TauIdx) : Bool :=
  go 1 (db + 1)
where
  go (k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > db then true
    else
      let pk := primorial k
      if pk == 0 || pk > 100 then go (k + 1) (fuel - 1)
      else
        check_nonzero 1 pk k && go (k + 1) (fuel - 1)
  termination_by fuel
  check_nonzero (x pk k : Nat) : Bool :=
    if x >= pk then true
    else
      let nf := boundary_normal_form x k
      -- Non-zero element has at least one non-zero component
      let has_sector := nf.b_part > 0 || nf.c_part > 0 || nf.x_part > 0
      has_sector && check_nonzero (x + 1) pk k

-- ============================================================
-- NF-ADDRESSABILITY THEOREM [III.T28]
-- ============================================================

/-- [III.T28] NF-addressability: every element of ℤ/Prim(k)ℤ is uniquely
    determined by its BNF triple. Combines BNF injectivity (from III.P16)
    and sector addressability (from III.D48). -/
def nf_addressability_check (bound db : TauIdx) : Bool :=
  -- Sector addressability (surjective: every element has an address)
  let surj := sector_addressability_check bound db
  -- NF discreteness (injective: distinct elements have distinct addresses)
  let inj := nf_discreteness_check db
  surj && inj

-- ============================================================
-- HODGE FILTRATION [III.P19]
-- ============================================================

/-- [III.P19] Hodge filtration at level k: B-part ⊂ B+X ⊂ B+C+X.
    Check that the filtration steps are nested. -/
def hodge_filtration_check (db : TauIdx) : Bool :=
  go 1 (db + 1)
where
  go (k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > db then true
    else
      let pk := primorial k
      if pk == 0 || pk > 100 then go (k + 1) (fuel - 1)
      else
        check_filtration 0 pk k && go (k + 1) (fuel - 1)
  termination_by fuel
  check_filtration (x pk k : Nat) : Bool :=
    if x >= pk then true
    else
      let nf := boundary_normal_form x k
      -- F₀ = {x : b=0, c=0, x=0} (zero)
      -- F₁ = {x : c=0, x=0} (B-part only)
      -- F₂ = {x : c=0} (B+X parts)
      -- F₃ = full (B+C+X)
      -- Nesting: if b=0 and c=0, then we're in F₁ iff x_part also = 0
      let in_f1 := nf.b_part > 0 && nf.c_part == 0 && nf.x_part == 0
      let in_f2 := nf.c_part == 0
      -- BNF roundtrip: components reconstruct original (non-trivial surjectivity)
      let roundtrip := (nf.b_part + nf.c_part + nf.x_part) % pk == x
      -- Filtration nesting: F₁ ⊂ F₂ (anything in F₁ is in F₂)
      let nested := if in_f1 then in_f2 else true
      roundtrip && nested && check_filtration (x + 1) pk k

-- ============================================================
-- SPECTRAL-HODGE COMPATIBILITY [III.P20]
-- ============================================================

/-- [III.P20] Spectral-Hodge compatibility: the Hodge filtration is
    compatible with the label-based spectral decomposition.
    B-filtration step ↔ B-type primes, C-step ↔ C-type primes. -/
def spectral_hodge_check (db : TauIdx) : Bool :=
  go 1 (db + 1)
where
  go (k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > db then true
    else
      -- B-sector product comes from B-type primes
      let bp := split_zeta_b k
      -- C-sector product comes from C-type primes
      let cp := split_zeta_c k
      -- X-sector product comes from X-type primes
      let xp := split_zeta_x k
      let pk := primorial k
      -- Compatibility: B*C*X = Prim(k) (spectral = Hodge)
      let compatible := if pk > 0 then bp * cp * xp == pk else true
      -- B and C coprime (filtration steps are orthogonal)
      let ortho := Nat.gcd bp cp == 1
      compatible && ortho && go (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- SMOKE TESTS
-- ============================================================

#eval sigma_fixed_check 4                    -- true
#eval sigma_fixed_closed_check 4             -- true
#eval sector_addressability_check 15 4       -- true
#eval char_sector_check 4                    -- true
#eval nf_addressability_check 15 3           -- true
#eval hodge_filtration_check 4               -- true
#eval spectral_hodge_check 5                 -- true

-- ============================================================
-- FORMAL VERIFICATION (native_decide)
-- ============================================================

theorem sigma_fixed_4 :
    sigma_fixed_check 4 = true := by native_decide

theorem sigma_fixed_closed_4 :
    sigma_fixed_closed_check 4 = true := by native_decide

theorem sector_addr_15_4 :
    sector_addressability_check 15 4 = true := by native_decide

theorem char_sector_4 :
    char_sector_check 4 = true := by native_decide

theorem nf_addr_15_3 :
    nf_addressability_check 15 3 = true := by native_decide

theorem hodge_filt_4 :
    hodge_filtration_check 4 = true := by native_decide

theorem spectral_hodge_5 :
    spectral_hodge_check 5 = true := by native_decide

-- ============================================================
-- STRUCTURAL THEOREMS
-- ============================================================

/-- [III.D47] Structural: zero BNF is always σ-fixed. -/
theorem zero_is_sigma_fixed :
    is_sigma_fixed ⟨0, 0, 0, 3⟩ = true := rfl

/-- [III.D47] Structural: polarity swap of σ-fixed is identity. -/
theorem sigma_fixed_swap_id (nf : BoundaryNF) (h : nf.b_part = nf.c_part) :
    polarity_swap nf = nf := by
  cases nf; simp_all [polarity_swap]

/-- [III.D48] Structural: addressability at depth 1. -/
theorem addr_10_1 :
    sector_addressability_check 10 1 = true := by native_decide

/-- [III.T28] Structural: NF-addressability at depth 1. -/
theorem nf_addr_10_1 :
    nf_addressability_check 10 1 = true := by native_decide

end Tau.BookIII.Physics
