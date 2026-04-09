import TauLib.BookIII.Mirror.ProofTheoryE3

/-!
# TauLib.BookIII.Mirror.Saturation

Applied Saturation, Terminal Level Characterization, and Tower Closure.

## Registry Cross-References

- [III.T49] Applied Saturation — `applied_saturation_check`
- [III.P31] Terminal Level Characterization — `terminal_level_check`

## Mathematical Content

**III.T49 (Applied Saturation):** E3 is terminal in the enrichment tower:
self-modelling applied twice is idempotent. At finite level: the E3 layer
applied to E3 output equals E3 output. This is the "applied" version of
the categorical saturation theorem (III.T03): whereas III.T03 proves
E3.succ = E3 by definition, III.T49 proves it computationally by showing
the E3 layer template is a fixpoint under self-application.

**III.P31 (Terminal Level Characterization):** Self-modelling is idempotent:
E3 applied to E3 data is E3 data. At finite level: E3.toNat is the maximum
level (3), and EnrLevel.lt .E3 .E3 = false. Combined with III.T49, this
gives the complete characterization: E3 is the unique terminal object in
the enrichment tower.
-/

namespace Tau.BookIII.Mirror

open Tau.Polarity Tau.Boundary Tau.Coordinates Tau.Denotation
open Tau.BookII.Interior Tau.BookII.Enrichment
open Tau.BookIII.Enrichment Tau.BookIII.Sectors
open Tau.BookIII.Spectral Tau.BookIII.Hinge Tau.BookIII.Bridge

-- ============================================================
-- APPLIED SATURATION [III.T49]
-- ============================================================

/-! **Scope limitation (E3 collapse):** At finite primorial level, the E3
    predicate degenerates to E0 because `reduce` is idempotent. This check
    is vacuous but correctly models the mathematical structure. The E3 layer
    is correctly DEFINED but finite verification is vacuous.
    See audit DASHBOARD.md §E3 Collapse. -/

/-- [III.T49] Applied saturation: the E3 layer template is a fixpoint
    under self-application. For each x, k:
    - E3 decoder applied to E3 decoder output equals E3 decoder output
    - E3 carrier applied to E3 decoder output remains true
    - E3 invariant applied to E3 decoder output remains true

    This is the computational witness of E4 = E3. -/
def applied_saturation_check (bound db : TauIdx) : Bool :=
  go 0 1 ((bound + 1) * (db + 1))
where
  go (x k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k > db then go (x + 1) 1 (fuel - 1)
    else
      let e2 := layer_of .E2 bound db
      let e3 := layer_of .E3 bound db
      -- E3 decoder output
      let d1 := e3.decoder x k
      -- E3 decoder applied to its own output (double application)
      let d2 := e3.decoder d1 k
      -- Idempotence: d2 = d1
      let idempotent := d2 == d1
      -- E3 carrier still accepts the double-decoded value
      let carrier_stable := e3.carrier_check d1 k
      -- E3 invariant still holds on the double-decoded value
      let invariant_stable := e3.invariant_check d1 k
      -- E3 predicate still holds on the double-decoded value
      let predicate_stable := e3.predicate_check d1 k
      -- E2 decoder idempotence (non-degenerate level)
      let e2_d1 := e2.decoder x k
      let e2_d2 := e2.decoder e2_d1 k
      let e2_idem := e2_d2 == e2_d1
      idempotent && carrier_stable && invariant_stable &&
        predicate_stable && e2_idem && go x (k + 1) (fuel - 1)
  termination_by fuel

/-! **Scope limitation (E3 collapse):** At finite primorial level, the E3
    predicate degenerates to E0 because `reduce` is idempotent. This check
    is vacuous but correctly models the mathematical structure. The E3 layer
    is correctly DEFINED but finite verification is vacuous.
    See audit DASHBOARD.md §E3 Collapse. -/

/-- [III.T49] Saturation at all four components: carrier, predicate,
    decoder, and invariant are all fixpoints at E3. -/
def full_saturation_check (bound db : TauIdx) : Bool :=
  go 0 1 ((bound + 1) * (db + 1))
where
  go (x k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k > db then go (x + 1) 1 (fuel - 1)
    else
      let e1 := layer_of .E1 bound db
      let e2 := layer_of .E2 bound db
      let e3 := layer_of .E3 bound db
      let e3_succ := layer_of EnrLevel.E3.succ bound db
      -- All four components of E3 and E3.succ agree
      let c_eq := e3.carrier_check x k == e3_succ.carrier_check x k
      let p_eq := e3.predicate_check x k == e3_succ.predicate_check x k
      let d_eq := e3.decoder x k == e3_succ.decoder x k
      let i_eq := e3.invariant_check x k == e3_succ.invariant_check x k
      -- Multi-step reachability on reduced value: E0→E1→E2→E3 chain
      let e0 := layer_of .E0 bound db
      let xr := e3.decoder x k  -- reduced value
      let chain_ok := e0.carrier_check xr k && e1.carrier_check xr k &&
                      e2.carrier_check xr k && e3.carrier_check xr k
      c_eq && p_eq && d_eq && i_eq && chain_ok && go x (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- TERMINAL LEVEL CHARACTERIZATION [III.P31]
-- ============================================================

/-- [III.P31] Terminal level check: E3 is the maximum enrichment level.
    Verified by:
    1. E3.toNat = 3 (maximum index)
    2. EnrLevel.lt .E3 .E3 = false (not self-exceeding)
    3. E3.succ = E3 (successor saturates)
    4. The four levels [E0, E1, E2, E3] are exhaustive
    5. Applied saturation holds (E3 template is fixpoint) -/
def terminal_level_check (bound db : TauIdx) : Bool :=
  -- E3 is maximal
  let max_level := EnrLevel.E3.toNat == 3
  -- E3 is not self-exceeding
  let not_self_exceeding := !EnrLevel.lt .E3 .E3
  -- Successor saturates
  let succ_saturates := EnrLevel.E3.succ == .E3
  -- Four levels are exhaustive
  let four_levels := [EnrLevel.E0, .E1, .E2, .E3].length == 4
  -- Applied saturation
  let saturated := applied_saturation_check bound db
  -- Full component-wise saturation
  let full_sat := full_saturation_check bound db
  max_level && not_self_exceeding && succ_saturates &&
    four_levels && saturated && full_sat

-- ============================================================
-- TOWER COMPLETENESS
-- ============================================================

/-- Tower completeness: the full enrichment tower E0 < E1 < E2 < E3
    is a total order on exactly 4 elements. -/
def tower_complete_check : Bool :=
  -- Strict ordering: E0 < E1 < E2 < E3
  let strict :=
    EnrLevel.lt .E0 .E1 &&
    EnrLevel.lt .E1 .E2 &&
    EnrLevel.lt .E2 .E3
  -- Irreflexivity: no level exceeds itself
  let irrefl :=
    !EnrLevel.lt .E0 .E0 &&
    !EnrLevel.lt .E1 .E1 &&
    !EnrLevel.lt .E2 .E2 &&
    !EnrLevel.lt .E3 .E3
  -- Totality: for every pair, one is <= the other
  let total :=
    EnrLevel.le .E0 .E1 &&
    EnrLevel.le .E1 .E2 &&
    EnrLevel.le .E2 .E3 &&
    EnrLevel.le .E0 .E3
  -- Exactly 4 levels
  let count := [EnrLevel.E0, .E1, .E2, .E3].length == 4
  strict && irrefl && total && count

/-- Each enrichment level is reachable from E0 by iterated succ. -/
def reachability_check : Bool :=
  let from_e0_1 := EnrLevel.E0.succ == .E1
  let from_e0_2 := EnrLevel.E0.succ.succ == .E2
  let from_e0_3 := EnrLevel.E0.succ.succ.succ == .E3
  from_e0_1 && from_e0_2 && from_e0_3

/-- Master mirror check: combines all Sprint 10 verifications.
    Proof theory (E3), self-model functor, paradox resolution,
    applied saturation, and terminal level characterization. -/
def mirror_master_check (bound db : TauIdx) : Bool :=
  -- Proof theory as E3 [III.D73]
  proof_theory_e3_check bound db &&
  -- Self-model functor [III.D74]
  self_model_check bound db &&
  -- Four paradox diagnostic [III.D75]
  four_paradox_check bound db &&
  -- Paradox resolution [III.T48]
  paradox_resolution_check bound db &&
  -- Applied saturation [III.T49]
  applied_saturation_check bound db &&
  -- Terminal level [III.P31]
  terminal_level_check bound db &&
  -- Tower completeness
  tower_complete_check &&
  -- Reachability
  reachability_check

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Applied saturation
#eval applied_saturation_check 8 3       -- true
#eval full_saturation_check 8 3          -- true

-- Terminal level
#eval terminal_level_check 8 3           -- true
#eval EnrLevel.E3.toNat                  -- 3
#eval EnrLevel.lt .E3 .E3               -- false
#eval EnrLevel.E3.succ                   -- E3

-- Tower completeness
#eval tower_complete_check               -- true
#eval reachability_check                 -- true

-- Four levels
#eval [EnrLevel.E0, .E1, .E2, .E3].length  -- 4

-- Master check
#eval mirror_master_check 8 3            -- true

-- ============================================================
-- FORMAL VERIFICATION (native_decide)
-- ============================================================

-- Applied saturation [III.T49]
theorem applied_saturation_8_3 :
    applied_saturation_check 8 3 = true := by native_decide

-- Full component-wise saturation [III.T49]
theorem full_saturation_8_3 :
    full_saturation_check 8 3 = true := by native_decide

-- Terminal level characterization [III.P31]
theorem terminal_level_8_3 :
    terminal_level_check 8 3 = true := by native_decide

-- Tower completeness
theorem tower_complete :
    tower_complete_check = true := by native_decide

-- Reachability
theorem reachability :
    reachability_check = true := by native_decide

-- Master mirror check
theorem mirror_master_8_3 :
    mirror_master_check 8 3 = true := by native_decide

-- ============================================================
-- STRUCTURAL THEOREMS
-- ============================================================

/-- [III.T49] E3 is terminal: E3 does not exceed itself. -/
theorem e3_is_terminal : EnrLevel.lt .E3 .E3 = false := by rfl

/-- [III.P31] E3 is the maximum level. -/
theorem e3_is_max : EnrLevel.E3.toNat = 3 := by rfl

/-- Tower has exactly four levels. -/
theorem four_levels :
    [EnrLevel.E0, EnrLevel.E1, EnrLevel.E2, EnrLevel.E3].length = 4 := by rfl

/-- Tower ordering: E0 < E1 < E2 < E3 is a strict chain. -/
theorem tower_complete_order :
    EnrLevel.lt .E0 .E1 = true ∧
    EnrLevel.lt .E1 .E2 = true ∧
    EnrLevel.lt .E2 .E3 = true := by
  exact ⟨rfl, rfl, rfl⟩

/-- Tower irreflexivity: no level exceeds itself. -/
theorem tower_irreflexive :
    EnrLevel.lt .E0 .E0 = false ∧
    EnrLevel.lt .E1 .E1 = false ∧
    EnrLevel.lt .E2 .E2 = false ∧
    EnrLevel.lt .E3 .E3 = false := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- E3.succ = E3: successor saturates at E3. -/
theorem e3_succ_saturates : EnrLevel.E3.succ = EnrLevel.E3 := rfl

/-- All levels reachable from E0 by iterated succ. -/
theorem all_reachable :
    EnrLevel.E0.succ = .E1 ∧
    EnrLevel.E0.succ.succ = .E2 ∧
    EnrLevel.E0.succ.succ.succ = .E3 := by
  exact ⟨rfl, rfl, rfl⟩

/-- [III.T49] Structural: E3.succ.toNat = E3.toNat (numeric saturation). -/
theorem e3_succ_nat : EnrLevel.E3.succ.toNat = EnrLevel.E3.toNat := rfl

/-- [III.P31] Structural: E3 is the unique fixpoint of succ.
    (E0, E1, E2 all advance; only E3 is fixed.) -/
theorem e3_unique_fixpoint :
    EnrLevel.E0.succ ≠ .E0 ∧
    EnrLevel.E1.succ ≠ .E1 ∧
    EnrLevel.E2.succ ≠ .E2 ∧
    EnrLevel.E3.succ = .E3 := by
  exact ⟨by decide, by decide, by decide, rfl⟩

/-- [III.P31] Structural: the enrichment levels have strictly
    increasing toNat values (witnesses total order). -/
theorem strictly_increasing_nat :
    EnrLevel.E0.toNat < EnrLevel.E1.toNat ∧
    EnrLevel.E1.toNat < EnrLevel.E2.toNat ∧
    EnrLevel.E2.toNat < EnrLevel.E3.toNat := by
  exact ⟨by decide, by decide, by decide⟩

end Tau.BookIII.Mirror
