import TauLib.BookII.Domains.Ultrametric
import TauLib.BookI.Holomorphy.TauHolomorphic

/-!
# TauLib.BookII.Domains.HolImpliesCont

The key inversion of Book II: holomorphic ⟹ continuous.

## Registry Cross-References

- [II.L01] Cylinder Compatibility Lemma — `cyl_compat_check`
- [II.T06] Hol ⟹ Cont — `hol_cont_check`

## Mathematical Content

II.L01 (Cylinder Compatibility):
  If f is a stage-local StageFun (f_k depends only on π_k),
  then f maps cylinders to cylinders:
    π_k(x) = π_k(y)  ⟹  f_k(x) = f_k(y)

II.T06 (Hol ⟹ Cont):
  Every τ-holomorphic function is 1-Lipschitz:
    δ(f(x), f(y)) ≥ δ(x, y)
  i.e., holomorphic functions are uniformly continuous.

This INVERTS the classical order: in standard complex analysis,
holomorphy is defined via topology (continuity + Cauchy–Riemann).
Here, holomorphy = algebraic tower coherence, and continuity follows.
-/

namespace Tau.BookII.Domains

open Tau.Polarity Tau.Denotation Tau.Holomorphy

-- ============================================================
-- STAGE LOCALITY
-- ============================================================

/-- A StageFun is stage-local if f_k(n) depends only on π_k(n).
    Check: f_k(n) = f_k(reduce(n, k)) for all n in [2, bound]. -/
def stage_local_check (sf : StageFun) (k bound : TauIdx) : Bool :=
  go 2 (bound + 1)
where
  go (n fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if n > bound then true
    else
      (sf.b_fun n k == sf.b_fun (reduce n k) k) &&
      (sf.c_fun n k == sf.c_fun (reduce n k) k) &&
      go (n + 1) (fuel - 1)
  termination_by fuel

/-- Batch stage locality across stages 1..k_max. -/
def stage_local_batch (sf : StageFun) (k_max bound : TauIdx) : Bool :=
  go 1 (k_max + 1)
where
  go (k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > k_max then true
    else stage_local_check sf k bound && go (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- CYLINDER COMPATIBILITY LEMMA [II.L01]
-- ============================================================

/-- [II.L01] Cylinder compatibility: stage-local functions map
    cylinders to cylinders.
    Check: cylinder_mem k x y → f_k(x) = f_k(y).
    Flat double loop with single fuel counter. -/
def cyl_compat_check (sf : StageFun) (k bound : TauIdx) : Bool :=
  go 2 2 ((bound + 1) * (bound + 1))
where
  go (x y fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if y > bound then go (x + 1) 2 (fuel - 1)
    else
      let ok := !cylinder_mem k x y ||
        (sf.b_fun x k == sf.b_fun y k && sf.c_fun x k == sf.c_fun y k)
      ok && go x (y + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- HOL ⟹ CONT [II.T06]
-- ============================================================

/-- Check output agreement at all stages up to a given depth. -/
def check_depth (sf : StageFun) (x y depth k_max : TauIdx) : Bool :=
  let lim := min depth k_max
  go 1 (lim + 1)
where
  go (k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > min depth k_max then true
    else
      (sf.b_fun x k == sf.b_fun y k && sf.c_fun x k == sf.c_fun y k) &&
      go (k + 1) (fuel - 1)
  termination_by fuel

/-- [II.T06] Hol ⟹ Cont: stage-local functions preserve
    agreement depth (1-Lipschitz in the ultrametric).
    If x,y agree at stage k, then f(x),f(y) agree at stage k.
    Flat double loop with single fuel counter. -/
def hol_cont_check (sf : StageFun) (k_max bound : TauIdx) : Bool :=
  go 2 2 ((bound + 1) * (bound + 1))
where
  go (x y fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if y > bound then go (x + 1) 2 (fuel - 1)
    else
      let input_depth := disagree_depth x y k_max
      check_depth sf x y input_depth k_max &&
      go x (y + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- VERIFICATION FOR CANONICAL EXAMPLES
-- ============================================================

-- Stage locality
#eval stage_local_batch chi_plus_stage 4 30    -- true
#eval stage_local_batch chi_minus_stage 4 30   -- true
#eval stage_local_batch id_stage 4 30          -- true

-- Cylinder compatibility (II.L01)
#eval cyl_compat_check chi_plus_stage 1 20     -- true
#eval cyl_compat_check chi_plus_stage 2 20     -- true
#eval cyl_compat_check chi_minus_stage 1 20    -- true
#eval cyl_compat_check id_stage 1 20           -- true

-- Hol ⟹ Cont (II.T06)
#eval hol_cont_check chi_plus_stage 4 20       -- true
#eval hol_cont_check chi_minus_stage 4 20      -- true
#eval hol_cont_check id_stage 4 20             -- true

-- Formal verification
theorem chi_plus_local : stage_local_batch chi_plus_stage 4 20 = true := by native_decide
theorem chi_minus_local : stage_local_batch chi_minus_stage 4 20 = true := by native_decide
theorem id_local : stage_local_batch id_stage 4 20 = true := by native_decide

theorem chi_plus_compat_k1 : cyl_compat_check chi_plus_stage 1 20 = true := by native_decide
theorem chi_plus_compat_k2 : cyl_compat_check chi_plus_stage 2 20 = true := by native_decide
theorem chi_minus_compat_k1 : cyl_compat_check chi_minus_stage 1 20 = true := by native_decide
theorem id_compat_k1 : cyl_compat_check id_stage 1 20 = true := by native_decide

theorem chi_plus_cont : hol_cont_check chi_plus_stage 4 15 = true := by native_decide
theorem chi_minus_cont : hol_cont_check chi_minus_stage 4 15 = true := by native_decide
theorem id_cont : hol_cont_check id_stage 4 15 = true := by native_decide

end Tau.BookII.Domains
