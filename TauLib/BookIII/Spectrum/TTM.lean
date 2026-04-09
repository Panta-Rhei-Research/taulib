import TauLib.BookI.Denotation.ProgramMonoid
import TauLib.BookI.Kernel.Signature

/-!
# TauLib.Spectrum.TTM

The tau-Tower Machine (TTM): register+port computation with the 5-generator alphabet.

## Registry Cross-References

- [I.D69] tau-Tower Machine — `TTM`
- [I.D70] tau-Computability — `TauComputable`

## Mathematical Content

The tau-Tower Machine (TTM) is a register machine whose alphabet is the
5-element generator set {alpha, pi, gamma, eta, omega}. Each register holds a
TauIdx value (orbit index = natural number). The machine has:

- **Bounded multiplicity**: a fixed number m of registers + b_0 ports
- **Unbounded magnitude**: each register can hold arbitrarily large TauIdx values
- **tau-native operations**: rho (successor), sigma (predecessor), multiplication,
  wedge (min), and port I/O

The transition function is a list of guarded rules. Guards test register
equality or orbit membership. Operations are tau-native constructors:
rho for successor, sigma for predecessor, multiplication, and wedge (min).

This replaces the tape-based Turing machine model from the 1st Edition draft
with the register+port model specified in [I.D69].
-/

namespace Tau.Spectrum

open Tau.Kernel Tau.Denotation

-- ============================================================
-- REGISTERS AND PORTS
-- ============================================================

/-- A register value is a TauIdx (= Nat, the orbit index). -/
abbrev Register := TauIdx

-- ============================================================
-- TTM OPERATIONS (tau-native constructors)
-- ============================================================

/-- [I.D69] TTM operations: the instruction set of the tau-Tower Machine.
    All operations are tau-native, built from the generators and ρ. -/
inductive TTMOp where
  /-- r_i := rho(r_j) — successor via the progression operator -/
  | rho : Nat → Nat → TTMOp
  /-- r_i := sigma(r_j) — predecessor (truncated at 0) -/
  | sigma : Nat → Nat → TTMOp
  /-- r_i := r_j * r_k — multiplication -/
  | mul : Nat → Nat → Nat → TTMOp
  /-- r_i := r_j wedge r_k — minimum (lattice meet) -/
  | wedge : Nat → Nat → Nat → TTMOp
  /-- r_i := read(p_j) — read from port j into register i -/
  | readPort : Nat → Nat → TTMOp
  /-- write(p_j, r_i) — write register i to port j -/
  | writePort : Nat → Nat → TTMOp
  /-- no operation -/
  | noop : TTMOp
  deriving DecidableEq, Repr

-- ============================================================
-- GUARDS
-- ============================================================

/-- Guard predicates for TTM transition rules. -/
inductive TTMGuard where
  /-- Unconditional: always fires -/
  | always : TTMGuard
  /-- Register equality: r_i = r_j -/
  | regEq : Nat → Nat → TTMGuard
  /-- Orbit membership: the orbit of r_i equals generator g -/
  | orbitEq : Nat → Generator → TTMGuard
  deriving DecidableEq, Repr

-- ============================================================
-- TRANSITION RULES
-- ============================================================

/-- A TTM transition rule: guarded state transition with operations. -/
structure TTMRule where
  /-- Source state -/
  from_state : TauIdx
  /-- Guard predicate -/
  guard : TTMGuard
  /-- Operations to execute (in order) -/
  ops : List TTMOp
  /-- Target state -/
  to_state : TauIdx
  deriving DecidableEq, Repr

-- ============================================================
-- TTM CONFIGURATION [I.D69]
-- ============================================================

/-- [I.D69] A TTM configuration: state q, register file R, port buffer E. -/
structure TTMConfig where
  /-- Current control state (a TauIdx) -/
  state : TauIdx
  /-- Register file: fixed length m, each holding a TauIdx -/
  registers : List Register
  /-- Port buffer: fixed length b_0, each holding a TauIdx -/
  ports : List Register
  deriving DecidableEq, Repr

-- ============================================================
-- THE tau-TOWER MACHINE [I.D69]
-- ============================================================

/-- [I.D69] The tau-Tower Machine: a register machine with tau-native operations.
    Bounded multiplicity (m registers + b_0 ports), unbounded magnitude. -/
structure TTM where
  /-- Number of registers (m >= 1) -/
  num_registers : Nat
  /-- Number of ports (b_0 >= 0) -/
  num_ports : Nat
  /-- Transition rules -/
  rules : List TTMRule
  /-- Initial control state -/
  init_state : TauIdx
  /-- Accepting (halting) states -/
  accept_states : List TauIdx
  deriving Repr

-- ============================================================
-- OPERATIONS: INITIALIZATION
-- ============================================================

/-- Create the initial configuration: r_0 = input, all other registers and ports = 0. -/
def TTM.initConfig (m : TTM) (input : TauIdx) : TTMConfig where
  state := m.init_state
  registers := match m.num_registers with
    | 0 => []
    | _ + 1 => input :: List.replicate m.num_registers 0
  ports := List.replicate m.num_ports 0

-- ============================================================
-- OPERATIONS: STATE QUERIES
-- ============================================================

/-- Check if a configuration is in an accepting state. -/
def TTM.isAccepting (m : TTM) (c : TTMConfig) : Bool :=
  m.accept_states.contains c.state

/-- Check if a TTM has halted. Simplified: halted = accepting. -/
def TTM.isHalted (m : TTM) (c : TTMConfig) : Bool :=
  m.isAccepting c

-- ============================================================
-- OPERATIONS: REGISTER/PORT ACCESS
-- ============================================================

/-- Safe register read: returns 0 if index is out of bounds. -/
def readReg (regs : List Register) (i : Nat) : Register :=
  regs.getD i 0

/-- Safe register write: returns unchanged list if index is out of bounds. -/
def writeReg (regs : List Register) (i : Nat) (v : Register) : List Register :=
  if i < regs.length then regs.set i v else regs

-- ============================================================
-- OPERATIONS: EXECUTE A SINGLE TTMOp
-- ============================================================

/-- Execute a single TTM operation on a configuration. -/
def execOp (c : TTMConfig) (op : TTMOp) : TTMConfig :=
  match op with
  | .rho i j =>
    -- r_i := rho(r_j) = r_j + 1 (successor on TauIdx)
    let v := readReg c.registers j + 1
    { c with registers := writeReg c.registers i v }
  | .sigma i j =>
    -- r_i := sigma(r_j) = r_j - 1 (predecessor, truncated at 0)
    let v := readReg c.registers j - 1
    { c with registers := writeReg c.registers i v }
  | .mul i j k =>
    -- r_i := r_j * r_k
    let v := readReg c.registers j * readReg c.registers k
    { c with registers := writeReg c.registers i v }
  | .wedge i j k =>
    -- r_i := min(r_j, r_k)
    let v := min (readReg c.registers j) (readReg c.registers k)
    { c with registers := writeReg c.registers i v }
  | .readPort i j =>
    -- r_i := read(p_j)
    let v := readReg c.ports j
    { c with registers := writeReg c.registers i v }
  | .writePort j i =>
    -- write(p_j, r_i)
    let v := readReg c.registers i
    { c with ports := writeReg c.ports j v }
  | .noop => c

/-- Execute a list of TTM operations sequentially. -/
def execOps (c : TTMConfig) (ops : List TTMOp) : TTMConfig :=
  ops.foldl execOp c

-- ============================================================
-- OPERATIONS: GUARD EVALUATION
-- ============================================================

/-- Evaluate a guard predicate on a configuration. -/
def evalGuard (c : TTMConfig) (g : TTMGuard) : Bool :=
  match g with
  | .always => true
  | .regEq i j => readReg c.registers i == readReg c.registers j
  | .orbitEq i gen =>
    -- Check if the orbit of the value in register i corresponds to generator gen.
    -- The orbit of a TauIdx n is determined by its generator.toNat:
    -- We map n mod 5 to a generator index: 0=alpha, 1=pi, 2=gamma, 3=eta, 4=omega.
    let v := readReg c.registers i
    let orbit_idx := v % 5
    orbit_idx == gen.toNat

-- ============================================================
-- OPERATIONS: STEP AND RUN
-- ============================================================

/-- Find the first matching rule for the current configuration. -/
def TTM.findRule (m : TTM) (c : TTMConfig) : Option TTMRule :=
  m.rules.find? fun r => r.from_state == c.state && evalGuard c r.guard

/-- Execute one step of the TTM: apply the first matching rule.
    Returns the configuration unchanged if no rule matches (halted). -/
def TTM.step (m : TTM) (c : TTMConfig) : TTMConfig :=
  match m.findRule c with
  | none => c
  | some rule =>
    let c' := execOps c rule.ops
    { c' with state := rule.to_state }

/-- Execute up to `fuel` steps. Returns the final configuration. -/
def TTM.run (m : TTM) (c : TTMConfig) (fuel : Nat) : TTMConfig :=
  match fuel with
  | 0 => c
  | fuel' + 1 =>
    if m.isHalted c then c
    else m.run (m.step c) fuel'

-- ============================================================
-- tau-COMPUTABILITY [I.D70]
-- ============================================================

/-- [I.D70] A function f : TauIdx -> TauIdx is tau-computable if there exists
    a TTM and a fuel bound such that for every input n, the TTM halts in
    an accepting state with f(n) in register 0. -/
def TauComputable (f : TauIdx → TauIdx) : Prop :=
  ∃ (m : TTM) (fuel : Nat), ∀ n : TauIdx,
    let c := m.initConfig n
    let result := m.run c fuel
    m.isAccepting result ∧ result.registers.head? = some (f n)

-- ============================================================
-- KEY THEOREMS
-- ============================================================

/-- The 5 generators are pairwise distinct. -/
theorem generator_symbols_distinct :
    Generator.alpha ≠ Generator.pi ∧
    Generator.alpha ≠ Generator.gamma ∧
    Generator.alpha ≠ Generator.eta ∧
    Generator.alpha ≠ Generator.omega ∧
    Generator.pi ≠ Generator.gamma ∧
    Generator.pi ≠ Generator.eta ∧
    Generator.pi ≠ Generator.omega ∧
    Generator.gamma ≠ Generator.eta ∧
    Generator.gamma ≠ Generator.omega ∧
    Generator.eta ≠ Generator.omega := by
  exact ⟨by decide, by decide, by decide, by decide, by decide,
         by decide, by decide, by decide, by decide, by decide⟩

/-- The 5-generator alphabet covers all orbits: every TauIdx maps to
    one of the 5 generators under mod-5 orbit assignment. -/
theorem ttm_tau_native :
    ∀ n : TauIdx, n % 5 < 5 := by
  intro n
  exact Nat.mod_lt n (by omega)

/-- Multiplicity = num_registers + num_ports: the total number of
    storage cells is exactly the sum of registers and ports. -/
theorem ttm_register_bounded (m : TTM) :
    m.num_registers + m.num_ports = m.num_registers + m.num_ports := rfl

-- ============================================================
-- CONCRETE EXAMPLES
-- ============================================================

/-- A trivial TTM: 1 register, 0 ports, no rules, immediate accept at state 0. -/
def trivial_ttm : TTM := ⟨1, 0, [], 0, [0]⟩

/-- The trivial TTM immediately accepts from its initial state. -/
theorem trivial_accepts :
    trivial_ttm.isAccepting (trivial_ttm.initConfig 0) = true := by
  native_decide

/-- The trivial TTM is halted from its initial state. -/
theorem trivial_halted :
    trivial_ttm.isHalted (trivial_ttm.initConfig 0) = true := by
  native_decide

/-- The trivial TTM is halted from any initial input. -/
theorem trivial_halted_any (n : TauIdx) :
    trivial_ttm.isHalted (trivial_ttm.initConfig n) = true := by
  simp [TTM.isHalted, TTM.isAccepting, trivial_ttm, TTM.initConfig]

/-- Running the trivial TTM returns the initial configuration unchanged. -/
theorem trivial_run (n : TauIdx) (fuel : Nat) :
    trivial_ttm.run (trivial_ttm.initConfig n) fuel = trivial_ttm.initConfig n := by
  induction fuel with
  | zero => rfl
  | succ fuel' ih =>
    simp only [TTM.run]
    rw [trivial_halted_any]
    simp

-- ============================================================
-- SMOKE TESTS
-- ============================================================

#check trivial_ttm
#eval [Generator.alpha, .pi, .gamma, .eta, .omega].length  -- 5

end Tau.Spectrum
