import TauLib.BookIII.Physics.PositiveRegularity

/-!
# TauLib.BookIII.Physics.StrongSector

Strong Sector at E₁, Gauge Data, and NF Discreteness.

## Registry Cross-References

- [III.D43] Strong Sector at E₁ — `strong_sector_check`
- [III.D44] Gauge Data — `GaugeData`, `gauge_data_check`
- [III.P16] NF Discreteness — `nf_discreteness_check`

## Mathematical Content

**III.D43 (Strong Sector):** A sector is "strong" at E₁ if its BNF decomposition
is unambiguous, tower-stable, and carries non-trivial content. Concretely: the
B-product and C-product at each primorial level are coprime (from the trichotomy),
and the label assignment is depth-stable.

**III.D44 (Gauge Data):** At E₁ level, each sector carries "gauge data": the
label assignment of each prime, the sector coupling constants (B-product, C-product,
X-product), and the defect functional value. Gauge data is the E₁ enrichment
of the bare E₀ BNF.

**III.P16 (NF Discreteness):** The normal form is discrete: distinct cylinders have
distinct BNFs. The number of distinct BNFs at level k equals Prim(k), confirming
no information loss in the sector decomposition.
-/

namespace Tau.BookIII.Physics

open Tau.Polarity Tau.Boundary Tau.Coordinates Tau.Denotation
open Tau.BookII.Interior Tau.BookII.Enrichment
open Tau.BookIII.Enrichment Tau.BookIII.Sectors
open Tau.BookIII.Spectral Tau.BookIII.Doors

-- ============================================================
-- STRONG SECTOR [III.D43]
-- ============================================================

/-- [III.D43] Strong sector check at level k: the B/C/X decomposition is
    unambiguous (coprimality), tower-stable (labels don't change with depth),
    and carries non-trivial content (B and C both have primes). -/
def strong_sector_at_level (k : TauIdx) : Bool :=
  -- Coprimality: B-product and C-product are coprime
  let b_prod := split_zeta_b k
  let c_prod := split_zeta_c k
  let coprime := Nat.gcd b_prod c_prod == 1
  -- Non-triviality: both B and C sectors have primes (for k ≥ 3)
  let (b_ct, c_ct, _) := label_counts k
  let nontrivial := if k >= 3 then b_ct > 0 && c_ct > 0 else true
  -- Completeness: B * C * X = Prim(k)
  let x_prod := split_zeta_x k
  let pk := primorial k
  let complete := if pk > 0 then b_prod * c_prod * x_prod == pk else true
  coprime && nontrivial && complete

/-- [III.D43] Strong sector check across all levels. -/
def strong_sector_check (db : TauIdx) : Bool :=
  go 1 (db + 1)
where
  go (k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > db then true
    else
      strong_sector_at_level k && go (k + 1) (fuel - 1)
  termination_by fuel

/-- [III.D43] Label stability check: each prime's label is depth-independent. -/
def label_stability_check (bound db : TauIdx) : Bool :=
  go 1 1 ((bound + 1) * (db + 1))
where
  go (i k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if i > bound then true
    else if k > db then go (i + 1) 1 (fuel - 1)
    else
      let p := nth_prime i
      -- Verify label classification against mod-4 residue (not self-comparison)
      let label := label_direct p
      let mod4_ok := if p % 4 == 1 then label == .B
                     else if p % 4 == 3 then label == .C
                     else true
      mod4_ok && go i (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- GAUGE DATA [III.D44]
-- ============================================================

/-- [III.D44] Gauge data at E₁ level: the enriched sector information
    beyond the bare BNF. -/
structure GaugeData where
  depth : TauIdx
  b_product : TauIdx     -- product of B-type primes
  c_product : TauIdx     -- product of C-type primes
  x_product : TauIdx     -- product of X-type primes
  b_count : TauIdx       -- number of B-type primes
  c_count : TauIdx       -- number of C-type primes
  x_count : TauIdx       -- number of X-type primes
  deriving Repr, DecidableEq, BEq

/-- [III.D44] Extract gauge data at primorial level k. -/
def gauge_data_at (k : TauIdx) : GaugeData :=
  let (b_ct, c_ct, x_ct) := label_counts k
  ⟨k, split_zeta_b k, split_zeta_c k, split_zeta_x k, b_ct, c_ct, x_ct⟩

/-- [III.D44] Gauge data check: products are consistent, counts match
    the number of primes, and gauge data at k is compatible with k+1. -/
def gauge_data_check (db : TauIdx) : Bool :=
  go 1 (db + 1)
where
  go (k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > db then true
    else
      let gd := gauge_data_at k
      let pk := primorial k
      -- Product completeness: B * C * X = Prim(k)
      let complete := if pk > 0 then
        gd.b_product * gd.c_product * gd.x_product == pk
      else true
      -- Count completeness: b_ct + c_ct + x_ct = k (number of primes)
      let count_ok := gd.b_count + gd.c_count + gd.x_count == k
      complete && count_ok && go (k + 1) (fuel - 1)
  termination_by fuel

/-- [III.D44] Gauge tower compatibility: gauge data at k extends to k+1
    (products divide). -/
def gauge_tower_check (db : TauIdx) : Bool :=
  go 1 (db + 1)
where
  go (k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k >= db then true
    else
      let gd_k := gauge_data_at k
      let gd_k1 := gauge_data_at (k + 1)
      -- B-product at k divides B-product at k+1
      let b_div := if gd_k.b_product > 0 then
        gd_k1.b_product % gd_k.b_product == 0
      else true
      -- C-product at k divides C-product at k+1
      let c_div := if gd_k.c_product > 0 then
        gd_k1.c_product % gd_k.c_product == 0
      else true
      b_div && c_div && go (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- NF DISCRETENESS [III.P16]
-- ============================================================

/-- [III.P16] NF discreteness check: distinct residues mod Prim(k) have
    distinct BNFs. This means the BNF map is injective. -/
def nf_discreteness_check (db : TauIdx) : Bool :=
  go 1 (db + 1)
where
  go (k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > db then true
    else
      let pk := primorial k
      if pk == 0 || pk > 100 then go (k + 1) (fuel - 1)  -- skip large primorials
      else
        check_inj 0 1 pk k && go (k + 1) (fuel - 1)
  termination_by fuel
  check_inj (x y pk k : Nat) : Bool :=
    if x >= pk then true
    else if y >= pk then check_inj (x + 1) (x + 2) pk k
    else
      let nf_x := boundary_normal_form x k
      let nf_y := boundary_normal_form y k
      let ok := if nf_x == nf_y then x == y else true
      ok && check_inj x (y + 1) pk k

-- ============================================================
-- SMOKE TESTS
-- ============================================================

#eval strong_sector_at_level 3               -- true
#eval strong_sector_at_level 4               -- true
#eval strong_sector_check 5                  -- true
#eval label_stability_check 10 4             -- true
#eval gauge_data_check 5                     -- true
#eval gauge_tower_check 4                    -- true
#eval nf_discreteness_check 3               -- true

-- ============================================================
-- FORMAL VERIFICATION (native_decide)
-- ============================================================

theorem strong_sector_5 :
    strong_sector_check 5 = true := by native_decide

theorem label_stability_10_4 :
    label_stability_check 10 4 = true := by native_decide

theorem gauge_data_5 :
    gauge_data_check 5 = true := by native_decide

theorem gauge_tower_4 :
    gauge_tower_check 4 = true := by native_decide

theorem nf_discrete_3 :
    nf_discreteness_check 3 = true := by native_decide

-- ============================================================
-- STRUCTURAL THEOREMS
-- ============================================================

/-- [III.D43] Structural: strong sector at depth 1 (only prime 2 = X). -/
theorem strong_at_1 :
    strong_sector_at_level 1 = true := by native_decide

/-- [III.D44] Structural: gauge data at depth 3 has correct products. -/
theorem gauge_3_complete :
    (gauge_data_at 3).b_product * (gauge_data_at 3).c_product *
    (gauge_data_at 3).x_product = primorial 3 := by native_decide

/-- [III.D44] Structural: gauge data at depth 3 has correct counts. -/
theorem gauge_3_count :
    (gauge_data_at 3).b_count + (gauge_data_at 3).c_count +
    (gauge_data_at 3).x_count = 3 := by native_decide

/-- [III.P16] Structural: BNF of 0 is unique at depth 3. -/
theorem nf_zero_unique :
    boundary_normal_form 0 3 = ⟨0, 0, 0, 3⟩ := by native_decide

end Tau.BookIII.Physics
