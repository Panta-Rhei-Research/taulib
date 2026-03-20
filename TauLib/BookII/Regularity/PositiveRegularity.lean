import TauLib.BookII.Regularity.ThreeLemmaChain

/-!
# TauLib.BookII.Regularity.PositiveRegularity

tau-Regularity: stabilization of the evolution operator at finite depth,
and the regularity criterion via channel decomposition.

## Registry Cross-References

- [II.D49] tau-Regularity — `regularity_depth`, `is_regular`
- [II.T34] Regularity Criterion — `regularity_criterion_check`

## Mathematical Content

**D49 (tau-Regularity):** A point p is tau-regular for a function f if the
evolution operator stabilizes at some finite stage N. Concretely: there
exists N such that for all m >= N, the ABCD chart of reduce(x, m)
produces the same B and C coordinates as reduce(x, N).

The regularity depth rd_f(x) is the smallest such N. Since the primorial
tower is a profinite completion, stabilization at a finite stage means
the point's data is determined by finitely many prime factors.

**T34 (Regularity Criterion):** A point x is regular if and only if both
its B-channel and C-channel components stabilize independently:

  is_regular(x) <=> is_b_stable(x) AND is_c_stable(x)

Moreover, the regularity depth is the maximum of the two channel depths:

  rd_f(x) = max(rd_b(x), rd_c(x))

This follows from the idempotent decomposition (II.L07): since the
channels are orthogonal and complete, stabilization of the whole function
is equivalent to stabilization of each channel separately.
-/

namespace Tau.BookII.Regularity

open Tau.Polarity Tau.Boundary Tau.Coordinates Tau.Denotation
open Tau.BookII.Interior Tau.BookII.Domains Tau.BookII.Hartogs Tau.Holomorphy

-- ============================================================
-- REGULARITY DEPTH [II.D49]
-- ============================================================

/-- [II.D49] B-channel stabilization depth: the smallest stage k
    (starting from 1) at which the B-coordinate of from_tau_idx(reduce(x, k))
    equals the B-coordinate at all subsequent stages up to db.

    Returns the stabilization stage, or db+1 if no stabilization. -/
def b_stabilization_depth (x db : TauIdx) : Nat :=
  go x 1 (db + 1)
where
  go (x k fuel : Nat) : Nat :=
    if fuel = 0 then db + 1
    else if k > db then db + 1
    else
      let bk := (from_tau_idx (reduce x k)).b
      -- Check if B-coordinate stays the same for all stages k+1 .. db
      let stable := check_stable x bk (k + 1) (db - k)
      if stable then k
      else go x (k + 1) (fuel - 1)
  termination_by fuel
  check_stable (x : Nat) (target : Nat) (j fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if j > db then true
    else
      let bj := (from_tau_idx (reduce x j)).b
      (bj == target) && check_stable x target (j + 1) (fuel - 1)
  termination_by fuel

/-- [II.D49] C-channel stabilization depth: the smallest stage k
    at which the C-coordinate stabilizes through all subsequent stages. -/
def c_stabilization_depth (x db : TauIdx) : Nat :=
  go x 1 (db + 1)
where
  go (x k fuel : Nat) : Nat :=
    if fuel = 0 then db + 1
    else if k > db then db + 1
    else
      let ck := (from_tau_idx (reduce x k)).c
      let stable := check_stable x ck (k + 1) (db - k)
      if stable then k
      else go x (k + 1) (fuel - 1)
  termination_by fuel
  check_stable (x : Nat) (target : Nat) (j fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if j > db then true
    else
      let cj := (from_tau_idx (reduce x j)).c
      (cj == target) && check_stable x target (j + 1) (fuel - 1)
  termination_by fuel

/-- [II.D49] Full regularity depth: the smallest stage k at which
    BOTH the B-coordinate and C-coordinate stabilize.

    By the regularity criterion (II.T34), this equals
    max(b_depth, c_depth). We compute it directly for verification. -/
def regularity_depth (x db : TauIdx) : Nat :=
  go x 1 (db + 1)
where
  go (x k fuel : Nat) : Nat :=
    if fuel = 0 then db + 1
    else if k > db then db + 1
    else
      let pk := from_tau_idx (reduce x k)
      let bk := pk.b
      let ck := pk.c
      -- Check if both B and C stay stable from k+1 to db
      let stable := check_both_stable x bk ck (k + 1) (db - k)
      if stable then k
      else go x (k + 1) (fuel - 1)
  termination_by fuel
  check_both_stable (x : Nat) (b_target c_target : Nat) (j fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if j > db then true
    else
      let pj := from_tau_idx (reduce x j)
      (pj.b == b_target && pj.c == c_target) &&
        check_both_stable x b_target c_target (j + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- REGULARITY PREDICATE [II.D49]
-- ============================================================

/-- [II.D49] A point x is tau-regular (within depth bound db) if the
    evolution operator stabilizes before reaching the depth bound.
    Returns true iff regularity_depth(x, db) <= db. -/
def is_regular (x db : TauIdx) : Bool :=
  regularity_depth x db ≤ db

/-- B-channel regularity: the B-coordinate stabilizes. -/
def is_b_regular (x db : TauIdx) : Bool :=
  b_stabilization_depth x db ≤ db

/-- C-channel regularity: the C-coordinate stabilizes. -/
def is_c_regular (x db : TauIdx) : Bool :=
  c_stabilization_depth x db ≤ db

-- ============================================================
-- REGULARITY DEPTH = MAX OF CHANNEL DEPTHS [II.T34]
-- ============================================================

/-- [II.T34] Regularity depth equals max of channel depths.
    rd_f(x) = max(rd_b(x), rd_c(x)).

    This follows from the orthogonality of the idempotent decomposition:
    the full stabilization happens precisely when both channels have
    independently stabilized. -/
def regularity_depth_max_check (bound db : TauIdx) : Bool :=
  go 2 (bound + 1)
where
  go (x fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else
      let rd := regularity_depth x db
      let rd_b := b_stabilization_depth x db
      let rd_c := c_stabilization_depth x db
      let expected := max rd_b rd_c
      (rd == expected) && go (x + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- REGULARITY CRITERION [II.T34]
-- ============================================================

/-- [II.T34] Regularity criterion: x is regular iff both B-channel
    and C-channel are individually regular.

    is_regular(x, db) <=> is_b_regular(x, db) AND is_c_regular(x, db)

    This is the channel decomposition of regularity: the idempotent
    decomposition (II.L07) guarantees that stabilization decomposes
    into independent channel conditions. -/
def regularity_criterion_check (bound db : TauIdx) : Bool :=
  go 2 (bound + 1)
where
  go (x fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else
      let reg := is_regular x db
      let b_reg := is_b_regular x db
      let c_reg := is_c_regular x db
      -- is_regular iff (is_b_regular AND is_c_regular)
      let ok := reg == (b_reg && c_reg)
      ok && go (x + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- REGULARITY FOR SMALL POINTS [II.D49]
-- ============================================================

/-- Small points (x < P_k for some k) are always regular at depth k,
    because reduce(x, k) = x for x < P_k, so the ABCD chart is
    constant from stage k onward. -/
def small_point_regularity_check (db : TauIdx) : Bool :=
  go 2 (primorial db + 1)
where
  go (x fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x >= primorial db then true
    else
      -- x < P_db, so x is regular at some stage <= db
      let ok := is_regular x db
      ok && go (x + 1) (fuel - 1)
  termination_by fuel

/-- Evolution stabilization: for regular points, the evolution operator
    output at the regularity depth equals the output at all deeper stages. -/
def evolution_stabilization_check (bound db : TauIdx) : Bool :=
  go 2 (bound + 1)
where
  go (x fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else
      let rd := regularity_depth x db
      if rd > db then go (x + 1) (fuel - 1)  -- not regular, skip
      else
        -- At the regularity depth, the evolved point stabilizes
        let bp_rd := interior_bipolar (from_tau_idx (reduce x rd))
        -- Check all deeper stages agree
        let ok := check_deep x bp_rd rd db (db - rd + 1)
        ok && go (x + 1) (fuel - 1)
  termination_by fuel
  check_deep (x : Nat) (bp_rd : SectorPair) (rd k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > db then true
    else
      let bp_k := interior_bipolar (from_tau_idx (reduce x k))
      -- B and C sectors should match the regularity-depth values
      (bp_k.b_sector == bp_rd.b_sector && bp_k.c_sector == bp_rd.c_sector) &&
      check_deep x bp_rd rd (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- REGULARITY AND IDEMPOTENT DECOMPOSITION
-- ============================================================

/-- Channel-wise evolution stabilization: the B-component stabilizes
    independently of the C-component, and vice versa.
    This connects regularity back to the idempotent decomposition. -/
def channel_stabilization_check (bound db : TauIdx) : Bool :=
  go 2 (bound + 1)
where
  go (x fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else
      let rd_b := b_stabilization_depth x db
      let rd_c := c_stabilization_depth x db
      -- B-channel stabilizes independently
      let b_ok := if rd_b ≤ db then
        let b_val := (from_tau_idx (reduce x rd_b)).b
        check_b_stable x b_val rd_b db (db - rd_b + 1)
      else true
      -- C-channel stabilizes independently
      let c_ok := if rd_c ≤ db then
        let c_val := (from_tau_idx (reduce x rd_c)).c
        check_c_stable x c_val rd_c db (db - rd_c + 1)
      else true
      b_ok && c_ok && go (x + 1) (fuel - 1)
  termination_by fuel
  check_b_stable (x : Nat) (target : Nat) (from_k to_k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if from_k > to_k then true
    else
      let bk := (from_tau_idx (reduce x from_k)).b
      (bk == target) && check_b_stable x target (from_k + 1) to_k (fuel - 1)
  termination_by fuel
  check_c_stable (x : Nat) (target : Nat) (from_k to_k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if from_k > to_k then true
    else
      let ck := (from_tau_idx (reduce x from_k)).c
      (ck == target) && check_c_stable x target (from_k + 1) to_k (fuel - 1)
  termination_by fuel

-- ============================================================
-- FULL REGULARITY CHECK
-- ============================================================

/-- [II.D49 + II.T34] Complete regularity verification:
    - Regularity depth = max of channel depths
    - Regularity criterion (channel decomposition)
    - Small point regularity
    - Evolution stabilization
    - Channel stabilization -/
def full_regularity_check (bound db : TauIdx) : Bool :=
  regularity_depth_max_check bound db &&
  regularity_criterion_check bound db &&
  small_point_regularity_check db &&
  evolution_stabilization_check bound db &&
  channel_stabilization_check bound db

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Stabilization depths
#eval b_stabilization_depth 7 4     -- B-depth for x=7
#eval c_stabilization_depth 7 4     -- C-depth for x=7
#eval regularity_depth 7 4          -- full depth for x=7

-- Regularity
#eval is_regular 7 4                -- true (small point)
#eval is_regular 2 4                -- true
#eval is_regular 30 4               -- true
#eval is_b_regular 7 4              -- true
#eval is_c_regular 7 4              -- true

-- Regularity depth = max of channel depths
#eval regularity_depth_max_check 20 4   -- true

-- Regularity criterion
#eval regularity_criterion_check 20 4   -- true

-- Small point regularity
#eval small_point_regularity_check 3    -- true (all x < P_3 = 30)

-- Evolution stabilization
#eval evolution_stabilization_check 20 4  -- true

-- Channel stabilization
#eval channel_stabilization_check 20 4    -- true

-- Full regularity check
#eval full_regularity_check 15 4          -- true

-- ============================================================
-- FORMAL VERIFICATION (native_decide)
-- ============================================================

-- Regularity depth = max [II.T34]
theorem depth_max_20_4 :
    regularity_depth_max_check 20 4 = true := by native_decide

-- Regularity criterion [II.T34]
theorem criterion_20_4 :
    regularity_criterion_check 20 4 = true := by native_decide

-- Small point regularity [II.D49]
theorem small_point_3 :
    small_point_regularity_check 3 = true := by native_decide

-- Evolution stabilization [II.D49]
theorem evolution_stab_20_4 :
    evolution_stabilization_check 20 4 = true := by native_decide

-- Channel stabilization
theorem channel_stab_20_4 :
    channel_stabilization_check 20 4 = true := by native_decide

-- Full regularity
theorem full_regularity_15_4 :
    full_regularity_check 15 4 = true := by native_decide

end Tau.BookII.Regularity
