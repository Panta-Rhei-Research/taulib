import TauLib.BookII.CentralTheorem.Categoricity

/-!
# TauLib.BookII.Closure.BSDbridge

Proto-rationality: the finite-stage-determined points of the primorial tower.

## Registry Cross-References

- [II.D65] Proto-Rationality — `is_proto_rational`, `proto_rational_check`,
  `proto_rational_examples_check`

## Mathematical Content

**II.D65 (Proto-Rationality):** A point x is proto-rational if:
1. x > 1 (nontrivial), and
2. There exists a stage k such that reduce(x, k) = x (the point is
   determined at a finite stage -- it lives entirely within Z/P_kZ).

The proto-rational points are the "algebraic" points of the primorial
tower: they are determined by finitely many prime residues. Points that
are NOT proto-rational would require the full inverse limit (infinitely
many prime residues) to specify -- these are the "transcendental" points
in the tower's number-theoretic sense.

Proto-rationality connects to BSD because:
- Rational points on an elliptic curve are finitely determined
- Proto-rational points in the primorial tower are finitely determined
- The rank of the Mordell-Weil group measures how many independent
  rational points exist -- analogously, the count of proto-rational
  points at each stage measures the arithmetic complexity

**Examples:**
- x = 2 is proto-rational: reduce(2, 2) = 2 (since P_2 = 6 > 2)
- x = 5 is proto-rational: reduce(5, 3) = 5 (since P_3 = 30 > 5)
- x = 0 is NOT proto-rational: x > 1 required
- x = 1 is NOT proto-rational: x > 1 required
-/

namespace Tau.BookII.Closure

open Tau.Polarity Tau.Boundary Tau.Coordinates Tau.Denotation
open Tau.BookII.Interior Tau.BookII.Domains Tau.Holomorphy
open Tau.BookII.Hartogs Tau.BookII.Regularity
open Tau.BookII.CentralTheorem

-- ============================================================
-- PROTO-RATIONALITY [II.D65]
-- ============================================================

/-- [II.D65] Check if a point x is proto-rational: x > 1 and there exists
    a stage k (searched up to max_k) such that reduce(x, k) = x. -/
def is_proto_rational (x max_k : TauIdx) : Bool :=
  if x ≤ 1 then false
  else find_stage x 1 (max_k + 1)
where
  find_stage (x k fuel : Nat) : Bool :=
    if fuel = 0 then false
    else if k > max_k then false
    else if reduce x k == x then true
    else find_stage x (k + 1) (fuel - 1)
  termination_by fuel

/-- [II.D65] Find the smallest stage k at which x is determined.
    Returns 0 if x is not proto-rational within max_k stages. -/
def proto_rational_stage (x max_k : TauIdx) : TauIdx :=
  if x ≤ 1 then 0
  else find_min_stage x 1 (max_k + 1)
where
  find_min_stage (x k fuel : Nat) : Nat :=
    if fuel = 0 then 0
    else if k > max_k then 0
    else if reduce x k == x then k
    else find_min_stage x (k + 1) (fuel - 1)
  termination_by fuel

/-- [II.D65] ABCD structure of a proto-rational point.
    For proto-rational x, from_tau_idx(x) gives the ABCD coordinates,
    and the A-coordinate indicates the prime direction. -/
def proto_rational_abcd (x : TauIdx) : TauAdmissiblePoint :=
  from_tau_idx x

/-- [II.D65] Proto-rationality verification for a range [2, bound].
    Check that every x in the range is proto-rational (which is true
    for all finite x, since reduce(x, k) = x whenever P_k > x). -/
def proto_rational_check (bound max_k : TauIdx) : Bool :=
  go 2 (bound + 1)
where
  go (x fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else
      is_proto_rational x max_k && go (x + 1) (fuel - 1)
  termination_by fuel

/-- [II.D65] Proto-rational examples check: verify specific examples.
    - x = 2 is proto-rational at stage 2 (P_2 = 6 > 2)
    - x = 5 is proto-rational at stage 2 (P_2 = 6 > 5)
    - x = 7 is proto-rational at stage 3 (P_3 = 30 > 7)
    - x = 12 is proto-rational at stage 3 (P_3 = 30 > 12) -/
def proto_rational_examples_check : Bool :=
  is_proto_rational 2 5 &&
  is_proto_rational 5 5 &&
  is_proto_rational 7 5 &&
  is_proto_rational 12 5 &&
  -- Stage checks
  proto_rational_stage 2 5 == 2 &&
  proto_rational_stage 5 5 == 2 &&
  proto_rational_stage 7 5 == 3 &&
  proto_rational_stage 12 5 == 3

/-- [II.D65] Proto-rational count at stage k: the number of proto-rational
    points determined at exactly stage k (i.e., reduce(x, k) = x but
    reduce(x, k-1) != x, for x > 1). -/
def proto_rational_count_at_stage (k : TauIdx) : TauIdx :=
  if k = 0 then 0
  else
    let pk := primorial k
    let pk_prev := if k >= 1 then primorial (k - 1) else 1
    go pk pk_prev 2 0 (pk + 1)
where
  go (pk pk_prev x count fuel : Nat) : Nat :=
    if fuel = 0 then count
    else if x >= pk then count
    else
      -- x is determined at stage k: reduce(x, k) = x (always true if x < pk)
      -- x is NOT determined at stage k-1: reduce(x, k-1) != x
      let at_prev := reduce x (k - 1)
      let new_stage := x ≥ 2 && at_prev != x
      let new_count := if new_stage then count + 1 else count
      go pk pk_prev (x + 1) new_count (fuel - 1)
  termination_by fuel

/-- Proto-rational count check: at stage 1 (P_1 = 2), no points are
    newly determined (x=0 and x=1 are excluded by x > 1 condition,
    but reduce(0, 0) = 0 and reduce(1, 0) = 0, so stage 0 already
    captures them). Actually at stage 1, x = 0 has reduce(0, 0) = 0 = x
    but x <= 1, so not counted. x = 1 is also <= 1.
    At stage 2 (P_2 = 6): points 2, 3, 4, 5 are new (reduce(x, 1) != x
    for x >= 2 since P_1 = 2). -/
def proto_rational_count_check : Bool :=
  proto_rational_count_at_stage 2 == 4 &&    -- x = 2, 3, 4, 5
  proto_rational_count_at_stage 3 >= 10       -- many new at stage 3

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Proto-rationality checks
#eval is_proto_rational 2 5     -- true
#eval is_proto_rational 5 5     -- true
#eval is_proto_rational 7 5     -- true
#eval is_proto_rational 12 5    -- true
#eval is_proto_rational 0 5     -- false (x <= 1)
#eval is_proto_rational 1 5     -- false (x <= 1)

-- Stage determination
#eval proto_rational_stage 2 5   -- 2 (P_2 = 6 > 2)
#eval proto_rational_stage 5 5   -- 2 (P_2 = 6 > 5)
#eval proto_rational_stage 7 5   -- 3 (P_3 = 30 > 7)
#eval proto_rational_stage 12 5  -- 3 (P_3 = 30 > 12)

-- ABCD coordinates
#eval proto_rational_abcd 2      -- (2, 1, 1, 1)
#eval proto_rational_abcd 12     -- (3, 1, 1, 4)

-- Range check
#eval proto_rational_check 30 5  -- true

-- Examples
#eval proto_rational_examples_check  -- true

-- Count at stages
#eval proto_rational_count_at_stage 2  -- 4
#eval proto_rational_count_at_stage 3  -- should be >= 10

-- Count check
#eval proto_rational_count_check       -- true

-- ============================================================
-- FORMAL VERIFICATION (native_decide)
-- ============================================================

-- Proto-rational specific examples [II.D65]
theorem proto_2 :
    is_proto_rational 2 5 = true := by native_decide

theorem proto_5 :
    is_proto_rational 5 5 = true := by native_decide

theorem proto_7 :
    is_proto_rational 7 5 = true := by native_decide

theorem proto_12 :
    is_proto_rational 12 5 = true := by native_decide

-- Non-proto-rational [II.D65]
theorem not_proto_0 :
    is_proto_rational 0 5 = false := by native_decide

theorem not_proto_1 :
    is_proto_rational 1 5 = false := by native_decide

-- Stage determination [II.D65]
theorem stage_2 :
    proto_rational_stage 2 5 = 2 := by native_decide

theorem stage_5 :
    proto_rational_stage 5 5 = 2 := by native_decide

theorem stage_7 :
    proto_rational_stage 7 5 = 3 := by native_decide

-- Proto-rational examples [II.D65]
theorem proto_examples :
    proto_rational_examples_check = true := by native_decide

-- Range check [II.D65]
theorem proto_range_30 :
    proto_rational_check 30 5 = true := by native_decide

-- Count checks [II.D65]
theorem proto_count_check :
    proto_rational_count_check = true := by native_decide

-- ============================================================
-- STRUCTURAL THEOREMS
-- ============================================================

/-- [II.D65] Every finite x > 1 is proto-rational at a sufficiently large stage.
    If P_k > x, then reduce(x, k) = x % P_k = x. Verified for x = 2. -/
theorem finite_is_proto_rational_2 :
    is_proto_rational 2 5 = true := by native_decide

/-- [II.D65] Proto-rationality is stable: if x < P_k, then reduce(x, k) = x.
    This follows from x % P_k = x when x < P_k. -/
theorem proto_at_stage (x k : TauIdx) (h : x < primorial k) :
    reduce x k = x := by
  simp only [reduce]
  exact Nat.mod_eq_of_lt h

/-- [II.D65] The ABCD chart of a proto-rational point round-trips.
    to_tau_idx(proto_rational_abcd(x)) = x. -/
theorem proto_abcd_roundtrip_2 :
    to_tau_idx (proto_rational_abcd 2) = 2 := by native_decide

theorem proto_abcd_roundtrip_12 :
    to_tau_idx (proto_rational_abcd 12) = 12 := by native_decide

end Tau.BookII.Closure
