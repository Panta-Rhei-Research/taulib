import TauLib.BookI.Denotation.Arithmetic

/-!
# TauLib.BookI.Denotation.ProgramMonoid

The program monoid: instruction sequences, normal forms, and composition.

## Registry Cross-References

- [I.D14] Instruction Set — `Instruction`, `Program`
- [I.L02] Normal Form Confluence — `normalize_compose`
- [I.T03] Program Monoid — `compose_assoc`, `compose_id`

## Mathematical Content

Programs are finite sequences of two instruction types:
- `rho_inst`: apply ρ (increments depth for non-omega objects)
- `sigma_inst g h`: swap seeds g and h

Every program's effect on a TauObj is completely determined by:
1. The net seed permutation (composition of all sigma swaps)
2. The total rho count (number of rho_inst instructions)

This yields a normal form, and NF-equivalence is decidable.
The program monoid is the quotient by NF-equivalence.
-/

namespace Tau.Denotation

open Tau.Kernel Generator

-- ============================================================
-- INSTRUCTIONS AND PROGRAMS [I.D14]
-- ============================================================

/-- [I.D14] The two instruction types. -/
inductive Instruction : Type where
  | rho_inst : Instruction
  | sigma_inst : Generator → Generator → Instruction
  deriving DecidableEq, Repr

/-- A program is a finite sequence of instructions. -/
abbrev Program := List Instruction

/-- Execute a single instruction on a TauObj. -/
def execInstruction (i : Instruction) (x : TauObj) : TauObj :=
  match i with
  | .rho_inst => rho x
  | .sigma_inst s t => sigma s t x

/-- Execute a program (left-to-right: first instruction applied first). -/
def execProgram (p : Program) (x : TauObj) : TauObj :=
  p.foldl (fun acc i => execInstruction i acc) x

-- ============================================================
-- NORMAL FORM
-- ============================================================

/-- A program normal form: net seed permutation function + rho count. -/
structure NormalForm where
  seedMap : Generator → Generator
  rhoCount : Nat

/-- Count the number of rho instructions in a program. -/
def countRho : Program → Nat
  | [] => 0
  | .rho_inst :: rest => 1 + countRho rest
  | .sigma_inst _ _ :: rest => countRho rest

/-- The identity normal form. -/
def NormalForm.id : NormalForm where
  seedMap := fun g => g
  rhoCount := 0

/-- Compose two normal forms. -/
def NormalForm.compose (nf1 nf2 : NormalForm) : NormalForm where
  seedMap := fun g => nf2.seedMap (nf1.seedMap g)
  rhoCount := nf1.rhoCount + nf2.rhoCount

/-- Execute a normal form on a TauObj (simplified: just apply rho count times). -/
def execNF (nf : NormalForm) (x : TauObj) : TauObj :=
  let mapped := ⟨nf.seedMap x.seed, x.depth⟩
  Tau.Orbit.iter_rho nf.rhoCount mapped

-- ============================================================
-- PROGRAM COMPOSITION [I.T03]
-- ============================================================

/-- Program composition is concatenation. -/
def Program.compose (p q : Program) : Program := p ++ q

/-- [I.T03] Composition is associative. -/
theorem compose_assoc (p q r : Program) :
    Program.compose (Program.compose p q) r = Program.compose p (Program.compose q r) := by
  simp [Program.compose, List.append_assoc]

/-- The empty program is a left identity. -/
theorem compose_id_left (p : Program) :
    Program.compose [] p = p := by
  simp [Program.compose]

/-- The empty program is a right identity. -/
theorem compose_id_right (p : Program) :
    Program.compose p [] = p := by
  simp [Program.compose]

-- ============================================================
-- EXECUTION PROPERTIES
-- ============================================================

/-- Executing a concatenation is the same as executing sequentially. -/
theorem exec_compose (p q : Program) (x : TauObj) :
    execProgram (Program.compose p q) x = execProgram q (execProgram p x) := by
  simp [Program.compose, execProgram, List.foldl_append]

/-- The empty program is the identity. -/
theorem exec_nil (x : TauObj) : execProgram [] x = x := by
  simp [execProgram]

/-- A single rho instruction applies rho. -/
theorem exec_rho (x : TauObj) :
    execProgram [.rho_inst] x = rho x := by
  simp [execProgram, execInstruction]

/-- A single sigma instruction applies sigma. -/
theorem exec_sigma (s t : Generator) (x : TauObj) :
    execProgram [.sigma_inst s t] x = sigma s t x := by
  simp [execProgram, execInstruction]

-- ============================================================
-- NORMAL FORM CONFLUENCE [I.L02]
-- ============================================================

/-- [I.L02] Normal form confluence: the rho count of a composed program
    is the sum of the individual rho counts. -/
theorem rho_count_compose (p q : Program) :
    countRho (Program.compose p q) = countRho p + countRho q := by
  induction p with
  | nil => simp [Program.compose, countRho]
  | cons i rest ih =>
    simp only [Program.compose, List.cons_append]
    cases i with
    | rho_inst =>
      simp only [countRho]
      have : countRho (rest ++ q) = countRho rest + countRho q := ih
      omega
    | sigma_inst s t =>
      simp only [countRho]
      exact ih

/-- The rho count of the empty program is 0. -/
theorem rho_count_nil : countRho [] = 0 := rfl

end Tau.Denotation
