import TauLib.BookIII.Spectral.Trichotomy

/-!
# TauLib.BookIII.Computation.E2Agent

E₂ Computational Agent and Operational Closure.

## Registry Cross-References

- [III.D49] E₂ Computational Agent — `E2Agent`, `e2_agent_check`
- [III.D50] Operational Closure — `operational_closure_check`

## Mathematical Content

**III.D49 (E₂ Computational Agent):** A self-referential code+decoder structure
at E₂ level. An E₂ agent is a pair (C, D) where C is a τ-address (the code)
and D is a τ-address (the decoder). The agent cycle: C → D(C) → C' → D(C') → ...

**III.D50 (Operational Closure):** Programs operate on programs with no meta-level
escape required. D applied to C produces another valid code. The E₂ level is
"operationally closed" if every decoder applied to every code yields a valid output.
-/

namespace Tau.BookIII.Computation

open Tau.Polarity Tau.Boundary Tau.Coordinates Tau.Denotation
open Tau.BookII.Interior Tau.BookII.Enrichment
open Tau.BookIII.Enrichment Tau.BookIII.Sectors
open Tau.BookIII.Spectral

-- ============================================================
-- E₂ COMPUTATIONAL AGENT [III.D49]
-- ============================================================

/-- [III.D49] E₂ agent: code + decoder pair. Both are τ-addresses at
    some primorial depth. The decoder transforms codes into new codes. -/
structure E2Agent where
  code : TauIdx         -- the program-as-τ-address
  decoder : TauIdx      -- the decoder-as-τ-address
  depth : TauIdx        -- primorial depth of operation
  deriving Repr, DecidableEq, BEq

/-- [III.D49] Apply the decoder to the code: D(C) at primorial level k.
    The decoder operates by modular arithmetic on the code. -/
def agent_step (a : E2Agent) : TauIdx :=
  let pk := primorial a.depth
  if pk == 0 then 0
  else (a.code + a.decoder) % pk

/-- [III.D49] Agent iteration: apply the decoder n times. -/
def agent_iterate (a : E2Agent) (n : TauIdx) : TauIdx :=
  go a.code a.decoder a.depth n
where
  go (code decoder depth fuel : Nat) : TauIdx :=
    if fuel = 0 then code
    else
      let pk := primorial depth
      if pk == 0 then 0
      else go ((code + decoder) % pk) decoder depth (fuel - 1)
  termination_by fuel

/-- [III.D49] Agent well-formedness: code and decoder are valid addresses
    (within primorial range). -/
def e2_agent_check (bound db : TauIdx) : Bool :=
  go 0 0 1 ((bound + 1) * (bound + 1) * (db + 1))
where
  go (c d k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if c > bound then true
    else if d > bound then go (c + 1) 0 1 (fuel - 1)
    else if k > db then go c (d + 1) 1 (fuel - 1)
    else
      let pk := primorial k
      if pk == 0 then go c d (k + 1) (fuel - 1)
      else
        let agent := E2Agent.mk (c % pk) (d % pk) k
        -- Step output is valid (within range)
        let result := agent_step agent
        let valid := result < pk
        -- Orbit test: step(step(x)) is also valid (2-step closure)
        let agent2 := E2Agent.mk result (d % pk) k
        let result2 := agent_step agent2
        let orbit_ok := result2 < pk
        valid && orbit_ok && go c d (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- OPERATIONAL CLOSURE [III.D50]
-- ============================================================

/-- [III.D50] Operational closure: decoder applied to any code produces
    another valid code at the same depth. -/
def operational_closure_check (bound db : TauIdx) : Bool :=
  go 0 0 1 ((bound + 1) * (bound + 1) * (db + 1))
where
  go (c d k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if c > bound then true
    else if d > bound then go (c + 1) 0 1 (fuel - 1)
    else if k > db then go c (d + 1) 1 (fuel - 1)
    else
      let pk := primorial k
      if pk == 0 then go c d (k + 1) (fuel - 1)
      else
        let agent := E2Agent.mk (c % pk) (d % pk) k
        let result := agent_step agent
        -- Result is a valid code at same depth
        let closed := result < pk
        -- Applying decoder to result also yields valid code (2-step closure)
        let agent2 := E2Agent.mk result (d % pk) k
        let result2 := agent_step agent2
        let closed2 := result2 < pk
        -- BNF coherence on output: result's BNF sums to itself
        let nf_out := boundary_normal_form result k
        let bnf_ok := (nf_out.b_part + nf_out.c_part + nf_out.x_part) % pk == result
        closed && closed2 && bnf_ok && go c d (k + 1) (fuel - 1)
  termination_by fuel

/-- [III.D50] Cycle detection: agent iteration eventually returns to start
    (finite state space). -/
def cycle_detection_check (bound db : TauIdx) : Bool :=
  go 0 0 1 ((bound + 1) * (bound + 1) * (db + 1))
where
  go (c d k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if c > bound then true
    else if d > bound then go (c + 1) 0 1 (fuel - 1)
    else if k > db then go c (d + 1) 1 (fuel - 1)
    else
      let pk := primorial k
      if pk == 0 then go c d (k + 1) (fuel - 1)
      else
        -- After at most pk steps, must return to start (pigeonhole)
        let start := c % pk
        let final := agent_iterate (E2Agent.mk start (d % pk) k) pk
        let cycled := final == start
        cycled && go c d (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- SMOKE TESTS
-- ============================================================

#eval e2_agent_check 5 3                     -- true
#eval operational_closure_check 5 3          -- true
#eval cycle_detection_check 5 3              -- true
#eval agent_step ⟨7, 3, 3⟩                  -- (7+3) % 30 = 10
#eval agent_iterate ⟨7, 3, 3⟩ 5             -- 5 steps

-- ============================================================
-- FORMAL VERIFICATION (native_decide)
-- ============================================================

theorem e2_agent_5_3 :
    e2_agent_check 5 3 = true := by native_decide

theorem operational_closure_5_3 :
    operational_closure_check 5 3 = true := by native_decide

theorem cycle_detection_5_3 :
    cycle_detection_check 5 3 = true := by native_decide

-- ============================================================
-- STRUCTURAL THEOREMS
-- ============================================================

/-- [III.D49] Structural: agent step at depth 0 is 0. -/
theorem agent_step_depth_0 :
    agent_step ⟨42, 7, 0⟩ = 0 := by native_decide

/-- [III.D49] Structural: agent step is modular. -/
theorem agent_step_mod :
    agent_step ⟨7, 3, 3⟩ = 10 := by native_decide

/-- [III.D50] Structural: identity decoder (d=0) is a fixpoint. -/
theorem identity_decoder :
    agent_step ⟨7, 0, 3⟩ = 7 := by native_decide

end Tau.BookIII.Computation
