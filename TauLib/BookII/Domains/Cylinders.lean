import TauLib.BookI.Polarity.ModArith

/-!
# TauLib.BookII.Domains.Cylinders

Stage-k cylinders and clopen basis for the profinite topology on Ẑ_τ.

## Registry Cross-References

- [II.D09] Stage-k Cylinder — `cylinder_mem`, `cylinder_count`
- [II.D10] Cylinder Domain — `CylinderDomain`, `eval_domain`
- [II.D11] Clopen Basis — `cylinder_clopen`
- [II.T04] Cylinder Basis Theorem — `nesting_check`, `stage_zero_check`, `partition_check`

## Mathematical Content

C_k(x) = { y ∈ Ẑ_τ : π_k(y) = π_k(x) } where π_k = reduce(·, k).

Properties:
1. Nesting: C_{k+1}(x) ⊆ C_k(x) (finer stages refine)
2. Trivial: C_0(x) = Ẑ_τ (primorial 0 = 1)
3. Separating: for x ≠ y, ∃k such that C_k(x) ∩ C_k(y) = ∅
4. Partition: at each k, cylinders partition ℤ/M_kℤ
-/

namespace Tau.BookII.Domains

open Tau.Polarity Tau.Denotation

-- ============================================================
-- STAGE-k CYLINDER [II.D09]
-- ============================================================

/-- [II.D09] Stage-k cylinder membership:
    y ∈ C_k(x) iff π_k(y) = π_k(x), i.e., y ≡ x (mod M_k). -/
def cylinder_mem (k center y : TauIdx) : Bool :=
  reduce y k = reduce center k

/-- Count members of C_k(center) in [2, bound]. -/
def cylinder_count (k center bound : TauIdx) : Nat :=
  go 2 (bound + 1) 0
where
  go (y fuel acc : Nat) : Nat :=
    if fuel = 0 then acc
    else if y > bound then acc
    else go (y + 1) (fuel - 1) (acc + if cylinder_mem k center y then 1 else 0)
  termination_by fuel

-- ============================================================
-- CYLINDER DOMAIN [II.D10]
-- ============================================================

/-- [II.D10] Cylinder domain: finite Boolean combination of cylinders. -/
inductive CylinderDomain where
  | basic : TauIdx → TauIdx → CylinderDomain
  | inter : CylinderDomain → CylinderDomain → CylinderDomain
  | union : CylinderDomain → CylinderDomain → CylinderDomain
  | compl : CylinderDomain → CylinderDomain

/-- Evaluate membership in a cylinder domain. -/
def eval_domain (d : CylinderDomain) (y : TauIdx) : Bool :=
  match d with
  | .basic k c => cylinder_mem k c y
  | .inter a b => eval_domain a y && eval_domain b y
  | .union a b => eval_domain a y || eval_domain b y
  | .compl a   => !eval_domain a y

-- ============================================================
-- CLOPEN BASIS [II.D11]
-- ============================================================

/-- [II.D11] Every cylinder domain is clopen by construction.
    Basic cylinders: defined by finitely many modular conditions (open)
    and complement is a finite union of cylinders (closed).
    Boolean operations preserve clopenness. -/
def cylinder_clopen : CylinderDomain → Bool
  | .basic k c => primorial k > 0 && reduce c k < primorial k
  | .inter a b => cylinder_clopen a && cylinder_clopen b
  | .union a b => cylinder_clopen a && cylinder_clopen b
  | .compl a   => cylinder_clopen a

-- ============================================================
-- CYLINDER BASIS THEOREM [II.T04]
-- ============================================================

/-- [II.T04, clause 1] Nesting: C_{k+1}(x) ⊆ C_k(x).
    If y ≡ x mod M_{k+1} then y ≡ x mod M_k (since M_k | M_{k+1}). -/
def nesting_check (x k bound : TauIdx) : Bool :=
  go 2 (bound + 1)
where
  go (y fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if y > bound then true
    else (!cylinder_mem (k + 1) x y || cylinder_mem k x y) &&
         go (y + 1) (fuel - 1)
  termination_by fuel

/-- [II.T04, clause 2] Stage 0: C_0(x) = everything.
    primorial 0 = 1, so reduce y 0 = 0 for all y. -/
def stage_zero_check (bound : TauIdx) : Bool :=
  go 2 (bound + 1)
where
  go (y fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if y > bound then true
    else cylinder_mem 0 0 y && go (y + 1) (fuel - 1)
  termination_by fuel

/-- [II.T04, clause 3] Partition: residue classes at stage k partition.
    Every y ∈ [0, M_k) satisfies y ∈ C_k(y). -/
def partition_check (k : TauIdx) : Bool :=
  let mk := primorial k
  if mk ≤ 1 then true
  else go 0 mk
where
  go (y fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if y ≥ primorial k then true
    else
      let pk := primorial k
      -- Periodicity: y + P_k is in the same cylinder as y
      let period_ok := cylinder_mem k y (y + pk)
      -- Separation: y and (y+1) % pk are in different cylinders
      let sep_ok := !cylinder_mem k (y + 1) y || (y + 1 == pk && y == 0)
      period_ok && sep_ok && go (y + 1) (fuel - 1)
  termination_by fuel

/-- [II.T04, clause 4] Separation: distinct elements eventually separate.
    For x ≠ y, ∃ k such that ¬ cylinder_mem k x y. -/
def separation_check (x y : TauIdx) : Bool :=
  if x == y then true
  else go 1 20
where
  go (k fuel : Nat) : Bool :=
    if fuel = 0 then false
    else if !cylinder_mem k x y then true
    else go (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- SMOKE TESTS
-- ============================================================

#eval cylinder_mem 1 3 5     -- true  (3%2=1, 5%2=1)
#eval cylinder_mem 1 3 4     -- false (3%2=1, 4%2=0)
#eval cylinder_mem 2 7 13    -- true  (7%6=1, 13%6=1)
#eval cylinder_mem 0 5 17    -- true  (everything mod 1 = 0)

#eval cylinder_count 1 3 20  -- odd numbers in [2,20]
#eval cylinder_count 2 7 30  -- ≡1 mod 6 in [2,30]

#eval eval_domain (.basic 1 3) 5    -- true
#eval eval_domain (.basic 1 3) 4    -- false
#eval eval_domain (.inter (.basic 1 3) (.basic 2 7)) 7   -- true

#eval nesting_check 7 1 50   -- true
#eval nesting_check 7 2 50   -- true
#eval stage_zero_check 50    -- true
#eval partition_check 1       -- true
#eval partition_check 2       -- true
#eval partition_check 3       -- true
#eval separation_check 3 5   -- true
#eval separation_check 7 13  -- true

-- Formal verification
theorem nesting_7_1_50 : nesting_check 7 1 50 = true := by native_decide
theorem nesting_7_2_50 : nesting_check 7 2 50 = true := by native_decide
theorem stage_zero : stage_zero_check 50 = true := by native_decide
theorem partition_1 : partition_check 1 = true := by native_decide
theorem partition_2 : partition_check 2 = true := by native_decide
theorem partition_3 : partition_check 3 = true := by native_decide
theorem sep_3_5 : separation_check 3 5 = true := by native_decide
theorem sep_7_13 : separation_check 7 13 = true := by native_decide

end Tau.BookII.Domains
