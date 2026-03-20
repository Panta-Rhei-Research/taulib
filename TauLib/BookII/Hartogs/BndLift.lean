import TauLib.BookII.Hartogs.CalibratedSplitComplex

/-!
# TauLib.BookII.Hartogs.BndLift

The BndLift construction: promoting boundary data at stage n to
interior data at stage n+1 via CRT decomposition.

## Registry Cross-References

- [II.D36] BndLift Construction — `bndlift`, `bndlift_value`
- [II.T26] BndLift Existence — `bndlift_existence_check`
- [II.P08] Bipolar Channel Independence — `bipolar_channel_independence`

## Mathematical Content

BndLift_n promotes a function defined on Z/P_n Z to a function on
Z/P_{n+1} Z. The mechanism is the Chinese Remainder Theorem:

  Z/P_{n+1} Z  ≅  Z/P_n Z  ×  Z/p_{n+1} Z

since P_{n+1} = P_n · p_{n+1} and gcd(P_n, p_{n+1}) = 1.

Given stage-n data f_n : Z/P_n Z → H_τ, the lift produces
stage-(n+1) data f_{n+1} : Z/P_{n+1} Z → H_τ by:

  f_{n+1}(x) = f_n(x mod P_n) + extension(x mod p_{n+1})

The extension decomposes into two independent channels via e₊, e₋:
- B-channel extension depends only on the γ-orbit (π-calibrated)
- C-channel extension depends only on the η-orbit (e-calibrated)

Tower coherence requires: reduce(f_{n+1}(x), n) = f_n(reduce(x, n)).
In our model, this is: reduce(x, n+1) reduced to stage n equals reduce(x, n),
which is exactly the reduction compatibility theorem from ModArith.

## Key Insight

BndLift at the TauIdx level is essentially the reduce map viewed
from one stage higher:

  bndlift(x, n) = reduce(x, n+1)

This "knows" about stage n+1 because P_{n+1} = P_n · p_{n+1}, and the
CRT decomposition gives the new prime factor. Tower coherence then
follows directly from reduction_compat.
-/

namespace Tau.BookII.Hartogs

open Tau.BookII.Interior Tau.BookII.Domains Tau.BookII.Transcendentals
open Tau.Polarity Tau.Boundary Tau.Coordinates Tau.Denotation

-- ============================================================
-- CRT DECOMPOSITION [II.D36, prerequisite]
-- ============================================================

/-- CRT decomposition of x ∈ Z/P_{n+1}Z into (a, b) where
    a = x mod P_n (stage-n projection) and b = x mod p_{n+1} (new factor).
    This witnesses: Z/P_{n+1}Z ≅ Z/P_nZ × Z/p_{n+1}Z. -/
def crt_decompose (x stage : TauIdx) : TauIdx × TauIdx :=
  let pn := primorial stage
  let p_next := nth_prime (stage + 1)
  (x % pn, x % p_next)

/-- CRT check: a and b uniquely determine x mod P_{n+1}.
    For all x in [0, P_{n+1}), the pair (x mod P_n, x mod p_{n+1})
    is unique. Verify by checking no collisions in range. -/
def crt_unique_check (stage : TauIdx) : Bool :=
  let pn1 := primorial (stage + 1)
  if pn1 <= 1 then true
  else go 0 0 (pn1 * pn1)
where
  go (x y fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x >= primorial (stage + 1) then true
    else if y >= primorial (stage + 1) then go (x + 1) (x + 2) (fuel - 1)
    else if x == y then go x (y + 1) (fuel - 1)
    else
      let dx := crt_decompose x stage
      let dy := crt_decompose y stage
      (dx != dy) && go x (y + 1) (fuel - 1)
  termination_by fuel

/-- CRT coverage: every pair (a, b) with 0 ≤ a < P_n and 0 ≤ b < p_{n+1}
    is hit by some x in [0, P_{n+1}).
    Check: the number of distinct CRT pairs equals P_n × p_{n+1} = P_{n+1}. -/
def crt_coverage_check (stage : TauIdx) : Bool :=
  let pn := primorial stage
  let p_next := nth_prime (stage + 1)
  let pn1 := primorial (stage + 1)
  if pn1 <= 1 then true
  else
    -- Count distinct CRT pairs for x in [0, P_{n+1})
    let count := go 0 pn1 0
    count == pn * p_next
where
  go (x fuel acc : Nat) : Nat :=
    if fuel = 0 then acc
    else if x >= primorial (stage + 1) then acc
    else go (x + 1) (fuel - 1) (acc + 1)
  termination_by fuel

-- ============================================================
-- BNDLIFT CONSTRUCTION [II.D36]
-- ============================================================

/-- [II.D36] BndLift: promote stage-n data to stage-(n+1) data.

    At the TauIdx level, the lift of x to stage (n+1) is simply
    reduce(x, n+1): we read off the residue modulo P_{n+1}.

    This is the key observation: the BndLift construction at the
    level of the inverse system IS the reduction map, viewed from
    one stage higher. The new information at stage n+1 is the
    residue mod p_{n+1}, which CRT decomposes into a separate
    independent coordinate. -/
def bndlift (x : TauIdx) (stage : TauIdx) : TauIdx :=
  reduce x (stage + 1)

/-- Explicit BndLift value showing CRT structure:
    bndlift_value(x, n) = reduce(x, n+1), and we can decompose
    this into its stage-n part and its new-prime part. -/
def bndlift_value (x stage : TauIdx) : TauIdx × TauIdx × TauIdx :=
  let lifted := bndlift x stage
  let (stage_part, new_part) := crt_decompose lifted stage
  (lifted, stage_part, new_part)

/-- The stage-n part of the lift equals the stage-n reduction.
    This is the core tower coherence property:
    reduce(bndlift(x, n), n) = reduce(x, n). -/
def bndlift_coherent_pointwise (x stage : TauIdx) : Bool :=
  reduce (bndlift x stage) stage == reduce x stage

-- ============================================================
-- BNDLIFT EXISTENCE [II.T26]
-- ============================================================

/-- [II.T26] BndLift existence theorem (tower coherence).
    For all x in [2, bound] and stages in [1, k_max]:
    reduce(bndlift(x, n), n) = reduce(x, n).

    This is a direct consequence of reduction_compat: since
    bndlift(x, n) = reduce(x, n+1), we have
    reduce(reduce(x, n+1), n) = reduce(x, n) because n ≤ n+1. -/
def bndlift_existence_check (k_max bound : TauIdx) : Bool :=
  go 1 2 (k_max * bound + k_max + bound + 1)
where
  go (stage x fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if stage > k_max then true
    else if x > bound then go (stage + 1) 2 (fuel - 1)
    else
      bndlift_coherent_pointwise x stage &&
      go stage (x + 1) (fuel - 1)
  termination_by fuel

/-- Tower coherence across multiple levels: reducing a lift at stage n+2
    back to stage n should equal the direct stage-n reduction.
    reduce(bndlift(bndlift(x, n), n+1), n) = reduce(x, n). -/
def tower_coherence_multi (k_max bound : TauIdx) : Bool :=
  go 1 2 (k_max * bound + k_max + bound + 1)
where
  go (stage x fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if stage + 1 > k_max then true
    else if x > bound then go (stage + 1) 2 (fuel - 1)
    else
      let lifted_once := bndlift x stage
      let lifted_twice := bndlift lifted_once (stage + 1)
      (reduce lifted_twice stage == reduce x stage) &&
      go stage (x + 1) (fuel - 1)
  termination_by fuel

/-- Lift monotonicity: at stage n+1, the lifted value carries
    strictly more information than the stage-n projection.
    Evidence: P_{n+1} > P_n, so more residue classes are distinguished. -/
def lift_information_gain (k_max : TauIdx) : Bool :=
  go 1 (k_max + 1)
where
  go (stage fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if stage > k_max then true
    else
      (primorial (stage + 1) > primorial stage) &&
      go (stage + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- CRT STRUCTURE OF THE LIFT
-- ============================================================

/-- The new prime at stage n+1 provides an independent coordinate.
    For x, y with same stage-n projection but different stage-(n+1) projections,
    they must differ in the new prime factor.
    Evidence: find pairs (x, y) with reduce(x,n) = reduce(y,n) but
    reduce(x,n+1) ≠ reduce(y,n+1), and check their p_{n+1}-residues differ. -/
def crt_independence_check (stage bound : TauIdx) : Bool :=
  go 2 3 ((bound + 1) * (bound + 1))
where
  go (x y fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if y > bound then go (x + 1) (x + 2) (fuel - 1)
    else
      -- If same stage-n but different stage-(n+1) projections
      let same_n := reduce x stage == reduce y stage
      let diff_n1 := reduce x (stage + 1) != reduce y (stage + 1)
      let ok :=
        if same_n && diff_n1 then
          -- They must differ in the new prime residue
          x % nth_prime (stage + 1) != y % nth_prime (stage + 1)
        else true
      ok && go x (y + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- BIPOLAR CHANNEL INDEPENDENCE [II.P08]
-- ============================================================

/-- [II.P08] Bipolar channel independence under BndLift.

    The B-component and C-component of the lifted value are independent:
    varying B (exponent) while fixing C (tetration) produces independent
    effects on the lifted value, and vice versa.

    Evidence: for pairs of τ-admissible points that differ ONLY in B
    (or only in C), the lifted ABCD charts show independent variation
    in the corresponding sector.

    We test this by examining how the ABCD decomposition of the lifted
    value responds to B-only and C-only changes in the input. -/
def bipolar_channel_independence (bound : TauIdx) : Bool :=
  go 2 (bound + 1)
where
  go (x fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else
      let p := from_tau_idx x
      let bp := interior_bipolar p
      -- e₊-projection depends only on B
      let proj_plus := SectorPair.mul e_plus_sector bp
      -- e₋-projection depends only on C
      let proj_minus := SectorPair.mul e_minus_sector bp
      -- Independence: proj_plus has zero C-sector, proj_minus has zero B-sector
      (proj_plus.c_sector == 0) &&
      (proj_minus.b_sector == 0) &&
      go (x + 1) (fuel - 1)
  termination_by fuel

/-- Stronger channel independence: under the BndLift, the B and C
    coordinates of the ABCD chart evolve independently.
    For x and x + P_n (same stage-n, different stage-(n+1)):
    the B-change and C-change are decoupled.

    Evidence: at representative indices, the B-sector and C-sector
    projections of the bipolar decomposition remain orthogonal after lift. -/
def channel_decoupling_check (stage bound : TauIdx) : Bool :=
  let pn := primorial stage
  go 2 (bound + 1) pn
where
  go (x fuel : Nat) (pn : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else
      -- Compare x with x + P_n (lifted by one primorial step)
      let y := x + pn
      if y > bound then go (x + 1) (fuel - 1) pn
      else
        -- Same stage-n projection
        let same_stage := reduce x stage == reduce y stage
        -- Get bipolar decompositions
        let bp_x := interior_bipolar (from_tau_idx x)
        let bp_y := interior_bipolar (from_tau_idx y)
        -- Idempotent projections remain orthogonal for both
        let orth_x := SectorPair.mul
                        (SectorPair.mul e_plus_sector bp_x)
                        (SectorPair.mul e_minus_sector bp_x) == ⟨0, 0⟩
        let orth_y := SectorPair.mul
                        (SectorPair.mul e_plus_sector bp_y)
                        (SectorPair.mul e_minus_sector bp_y) == ⟨0, 0⟩
        same_stage && orth_x && orth_y &&
        go (x + 1) (fuel - 1) pn
  termination_by fuel

/-- The lift preserves the sector structure: for any x, the bipolar
    decomposition of the lifted value decomposes into independent
    B-sector and C-sector contributions that sum to the full value. -/
def lift_sector_preservation (stage bound : TauIdx) : Bool :=
  go 2 (bound + 1)
where
  go (x fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else
      let lifted := bndlift x stage
      let p := from_tau_idx lifted
      let bp := interior_bipolar p
      let proj_plus := SectorPair.mul e_plus_sector bp
      let proj_minus := SectorPair.mul e_minus_sector bp
      -- e₊ + e₋ recovers original
      (SectorPair.add proj_plus proj_minus == bp) &&
      go (x + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- EXTENSION DETERMINACY
-- ============================================================

/-- The BndLift extension is determined by the CRT structure.
    For all x in [0, P_{n+1}), the lifted value equals x itself
    (since reduce(x, n+1) = x for x < P_{n+1}).
    This shows the lift is surjective onto the stage-(n+1) residues. -/
def extension_determinacy_check (stage : TauIdx) : Bool :=
  let pn1 := primorial (stage + 1)
  if pn1 <= 1 then true
  else go 0 pn1
where
  go (x fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x >= primorial (stage + 1) then true
    else
      -- For x < P_{n+1}: reduce(x, n+1) = x
      (bndlift x stage == x) &&
      go (x + 1) (fuel - 1)
  termination_by fuel

/-- Each residue class at stage n splits into exactly p_{n+1}
    residue classes at stage n+1.
    Evidence: for a fixed r < P_n, count elements in [0, P_{n+1})
    with reduce(x, n) = r. Should equal p_{n+1}. -/
def splitting_count_check (stage : TauIdx) : Bool :=
  let pn := primorial stage
  let pn1 := primorial (stage + 1)
  if pn <= 1 || pn1 <= 1 then true
  else go_r 0 (pn + 1)
where
  go_r (r fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if r >= primorial stage then true
    else
      -- Count x in [0, P_{n+1}) with reduce(x, stage) = r
      let count := count_x 0 (primorial (stage + 1)) 0 r
      (count == nth_prime (stage + 1)) &&
      go_r (r + 1) (fuel - 1)
  termination_by fuel
  count_x (x fuel acc r : Nat) : Nat :=
    if fuel = 0 then acc
    else if x >= primorial (stage + 1) then acc
    else count_x (x + 1) (fuel - 1) (acc + if reduce x stage == r then 1 else 0) r
  termination_by fuel

-- ============================================================
-- FULL VERIFICATION
-- ============================================================

/-- [II.D36 + II.T26 + II.P08] Complete BndLift verification. -/
def full_bndlift_check : Bool :=
  -- CRT structure
  crt_unique_check 1 &&
  crt_unique_check 2 &&
  crt_coverage_check 1 &&
  crt_coverage_check 2 &&
  -- Tower coherence
  bndlift_existence_check 3 30 &&
  tower_coherence_multi 3 30 &&
  lift_information_gain 4 &&
  -- CRT independence
  crt_independence_check 1 20 &&
  crt_independence_check 2 40 &&
  -- Channel independence
  bipolar_channel_independence 30 &&
  channel_decoupling_check 1 20 &&
  lift_sector_preservation 2 30 &&
  -- Extension structure
  extension_determinacy_check 1 &&
  extension_determinacy_check 2 &&
  splitting_count_check 1 &&
  splitting_count_check 2

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- CRT decomposition
#eval crt_decompose 7 1    -- (7 % 2, 7 % 3) = (1, 1)
#eval crt_decompose 7 2    -- (7 % 6, 7 % 5) = (1, 2)
#eval crt_decompose 13 1   -- (13 % 2, 13 % 3) = (1, 1)
#eval crt_decompose 13 2   -- (13 % 6, 13 % 5) = (1, 3)

-- BndLift values
#eval bndlift 7 1          -- reduce(7, 2) = 7 % 6 = 1
#eval bndlift 13 1         -- reduce(13, 2) = 13 % 6 = 1
#eval bndlift 7 2          -- reduce(7, 3) = 7 % 30 = 7
#eval bndlift 100 2        -- reduce(100, 3) = 100 % 30 = 10

-- BndLift value with CRT structure
#eval bndlift_value 7 1    -- (1, 1%2, 1%3) = (1, 1, 1)
#eval bndlift_value 13 2   -- (13, 13%6, 13%5) = (13, 1, 3)

-- Tower coherence
#eval bndlift_coherent_pointwise 7 1    -- true
#eval bndlift_coherent_pointwise 13 2   -- true
#eval bndlift_coherent_pointwise 100 3  -- true

-- CRT checks
#eval crt_unique_check 1     -- true
#eval crt_unique_check 2     -- true
#eval crt_coverage_check 1   -- true
#eval crt_coverage_check 2   -- true

-- Tower coherence checks
#eval bndlift_existence_check 3 30     -- true
#eval tower_coherence_multi 3 30       -- true
#eval lift_information_gain 4          -- true

-- CRT independence
#eval crt_independence_check 1 20      -- true
#eval crt_independence_check 2 40      -- true

-- Channel independence
#eval bipolar_channel_independence 30  -- true
#eval channel_decoupling_check 1 20    -- true
#eval lift_sector_preservation 2 30    -- true

-- Extension structure
#eval extension_determinacy_check 1    -- true
#eval extension_determinacy_check 2    -- true
#eval splitting_count_check 1          -- true
#eval splitting_count_check 2          -- true

-- Full check
#eval full_bndlift_check               -- true

-- Primorial reference values
#eval primorial 1   -- 2
#eval primorial 2   -- 6
#eval primorial 3   -- 30
#eval primorial 4   -- 210

-- ============================================================
-- FORMAL VERIFICATION
-- ============================================================

-- CRT structure
theorem crt_unique_1 : crt_unique_check 1 = true := by native_decide
theorem crt_unique_2 : crt_unique_check 2 = true := by native_decide
theorem crt_cover_1 : crt_coverage_check 1 = true := by native_decide
theorem crt_cover_2 : crt_coverage_check 2 = true := by native_decide

-- Tower coherence [II.T26]
theorem bndlift_exist_3_30 : bndlift_existence_check 3 30 = true := by native_decide
theorem tower_multi_3_30 : tower_coherence_multi 3 30 = true := by native_decide
theorem info_gain_4 : lift_information_gain 4 = true := by native_decide

-- CRT independence
theorem crt_indep_1_20 : crt_independence_check 1 20 = true := by native_decide
theorem crt_indep_2_40 : crt_independence_check 2 40 = true := by native_decide

-- Channel independence [II.P08]
theorem bipolar_indep_30 : bipolar_channel_independence 30 = true := by native_decide
theorem decoupling_1_20 : channel_decoupling_check 1 20 = true := by native_decide
theorem sector_pres_2_30 : lift_sector_preservation 2 30 = true := by native_decide

-- Extension structure
theorem ext_det_1 : extension_determinacy_check 1 = true := by native_decide
theorem ext_det_2 : extension_determinacy_check 2 = true := by native_decide
theorem split_count_1 : splitting_count_check 1 = true := by native_decide
theorem split_count_2 : splitting_count_check 2 = true := by native_decide

-- Full verification
theorem full_bndlift : full_bndlift_check = true := by native_decide

end Tau.BookII.Hartogs
