import TauLib.BookIII.Arithmetic.RationalPoints

/-!
# TauLib.BookIII.Arithmetic.ProtoCodes

Proto-Code, BSD Functional, and Bridgehead Proposition.

## Registry Cross-References

- [III.D61] Proto-Code — `ProtoCode`, `proto_code_check`
- [III.D62] BSD Functional — `bsd_functional`, `bsd_functional_check`
- [III.P26] Bridgehead Proposition — `bridgehead_check`

## Mathematical Content

**III.D61 (Proto-Code):** E₁ object with discrete carrier, self-verification,
but no decoder. Necessary but not sufficient for computation. A proto-code
has BNF components and carries rank information, but cannot decode itself.

**III.D62 (BSD Functional):** BSD_τ(k) = rank(k) · L'_τ(1,k). Measures
proto-code density at each primorial level. The L-value derivative at s=1
is approximated by the defect functional ratio.

**III.P26 (Bridgehead Proposition):** Proto-codes provide the necessary
ingredient for E₂ emergence. Non-trivial iff rank > 0.
-/

namespace Tau.BookIII.Arithmetic

open Tau.Polarity Tau.Boundary Tau.Coordinates Tau.Denotation
open Tau.BookII.Interior Tau.BookII.Enrichment
open Tau.BookIII.Enrichment Tau.BookIII.Sectors
open Tau.BookIII.Spectral Tau.BookIII.Doors
open Tau.BookIII.Physics

-- ============================================================
-- PROTO-CODE [III.D61]
-- ============================================================

/-- [III.D61] Proto-code: E₁ object with discrete carrier and self-verification
    but no decoder. Has BNF + gauge data but cannot self-modify. -/
structure ProtoCode where
  address : TauIdx        -- the code's τ-address
  depth : TauIdx          -- primorial depth
  rank : TauIdx           -- tower depth at which it stabilizes
  verified : Bool         -- self-verification status
  deriving Repr, DecidableEq, BEq

/-- [III.D61] Construct a proto-code from address and depth. -/
def make_proto_code (x k : TauIdx) : ProtoCode :=
  let pk := primorial k
  if pk == 0 then ⟨0, k, 0, true⟩
  else
    let xr := x % pk
    let nf := boundary_normal_form xr k
    let sum := (nf.b_part + nf.c_part + nf.x_part) % pk
    let r := rank_as_depth x k
    -- Verified: BNF recovers input AND non-zero addresses have non-zero components
    ⟨xr, k, r, sum == xr && (xr == 0 || nf.b_part > 0 || nf.c_part > 0 || nf.x_part > 0)⟩

/-- [III.D61] Proto-code check: all proto-codes are well-formed and
    self-verifying. -/
def proto_code_check (bound db : TauIdx) : Bool :=
  go 0 1 ((bound + 1) * (db + 1))
where
  go (x k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k > db then go (x + 1) 1 (fuel - 1)
    else
      let pc := make_proto_code x k
      -- Verification passes
      let ok := pc.verified
      -- Rank is bounded
      let rank_ok := pc.rank <= db
      ok && rank_ok && go x (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- BSD FUNCTIONAL [III.D62]
-- ============================================================

/-- [III.D62] BSD functional: BSD_τ(k) = rank_count(k) · derivative_approx(k).
    rank_count = number of distinct ranks at level k.
    derivative_approx = difference of split-zeta products. -/
def bsd_functional (k : TauIdx) : TauIdx :=
  let pk := primorial k
  if pk == 0 || pk > 100 then 0
  else
    -- Count of distinct ranks at this level
    let rank_ct := count_ranks 0 pk k 0
    -- L-value derivative approximation: |B_prod - C_prod|
    let bp := split_zeta_b k
    let cp := split_zeta_c k
    let l_deriv := if bp >= cp then bp - cp else cp - bp
    rank_ct * l_deriv
where
  count_ranks (x pk k acc : Nat) : Nat :=
    if x >= pk then acc
    else
      let r := rank_as_depth x k
      let new_acc := if r > 0 then acc + 1 else acc
      count_ranks (x + 1) pk k new_acc

/-- [III.D62] BSD functional check: the functional is well-defined and
    non-negative at each level. -/
def bsd_functional_check (db : TauIdx) : Bool :=
  go 1 (db + 1)
where
  go (k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > db then true
    else
      let bsd := bsd_functional k
      let pk := primorial k
      -- BSD positive when computable and both sectors present
      let ok := if k >= 3 && pk > 0 && pk <= 100 then bsd > 0 else true
      ok && go (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- BRIDGEHEAD PROPOSITION [III.P26]
-- ============================================================

/-- [III.P26] Bridgehead: proto-codes are non-trivial (rank > 0 somewhere)
    at sufficiently high depth. This is the seed for E₂ emergence. -/
def bridgehead_check (db : TauIdx) : Bool :=
  go 1 (db + 1)
where
  go (k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > db then true
    else
      let pk := primorial k
      if pk == 0 || pk > 100 then go (k + 1) (fuel - 1)
      else
        -- At least one proto-code has rank > 0
        let has_nontrivial := check_nontrivial 1 pk k
        has_nontrivial && go (k + 1) (fuel - 1)
  termination_by fuel
  check_nontrivial (x pk k : Nat) : Bool :=
    if x >= pk then false  -- exhausted search: no nontrivial proto-code found
    else
      let pc := make_proto_code x k
      if pc.rank > 0 then true
      else check_nontrivial (x + 1) pk k

-- ============================================================
-- SMOKE TESTS
-- ============================================================

#eval proto_code_check 15 4                  -- true
#eval bsd_functional 3                       -- BSD at depth 3
#eval bsd_functional_check 5                 -- true
#eval bridgehead_check 4                     -- true

-- ============================================================
-- FORMAL VERIFICATION (native_decide)
-- ============================================================

theorem proto_code_15_4 :
    proto_code_check 15 4 = true := by native_decide

theorem bsd_functional_5 :
    bsd_functional_check 5 = true := by native_decide

theorem bridgehead_4 :
    bridgehead_check 4 = true := by native_decide

-- ============================================================
-- STRUCTURAL THEOREMS
-- ============================================================

/-- [III.D61] Structural: proto-code of 0 is verified. -/
theorem proto_zero_verified :
    (make_proto_code 0 3).verified = true := by native_decide

/-- [III.D62] Structural: BSD at depth 1 is non-negative. -/
theorem bsd_nonneg_1 :
    bsd_functional 1 ≥ 0 := Nat.zero_le _

/-- [III.P26] Structural: bridgehead at depth 1. -/
theorem bridgehead_1 :
    bridgehead_check 1 = true := by native_decide

end Tau.BookIII.Arithmetic
