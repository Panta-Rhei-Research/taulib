import TauLib.BookIV.Sectors.SectorParameters
import TauLib.BookI.Boundary.Iota

/-!
# TauLib.BookIV.Arena.CoherenceKernel

The coherence kernel K: the categorical core that generates all physics.
At E₁ it manifests as the 5-generator system {α,π,γ,η,ω} with canonical
sector assignment.

## Registry Cross-References

- [IV.D246] Coherence Kernel — Physics Presentation — `CoherenceKernel`
- [IV.D247] Generator–Sector Assignment — `GenSectorAssignment`
- [IV.P146] Uniqueness of Assignment — `assignment_unique`
- [IV.D248] Ontic Minimality — `ontic_minimality`

## Mathematical Content

The coherence kernel wraps the 5 generators with their canonical sector
assignment Φ: {α,π,γ,η,ω} → {D,A,B,C,Ω}. The assignment is unique (any
polarity-preserving, depth-respecting map must agree with Φ) and ontically
minimal (no proper subset of generators spans all 5 sectors).

## Ground Truth Sources
- Chapter 2 of Book IV (2nd Edition)
-/

namespace Tau.BookIV.Arena

open Tau.Kernel Tau.Boundary Tau.BookIV.Sectors Tau.BookIII.Sectors

-- ============================================================
-- GENERATOR–SECTOR ASSIGNMENT [IV.D247]
-- ============================================================

/-- [IV.D247] The bijective map Φ: {α,π,γ,η,ω} → {D,A,B,C,Ω}
    assigning each generator to its unique sector. -/
def GenSectorAssignment (g : Generator) : Sector :=
  match g with
  | .alpha => .D
  | .pi    => .A
  | .gamma => .B
  | .eta   => .C
  | .omega => .Omega

/-- Φ maps each generator to a distinct sector (injective). -/
theorem assignment_injective :
    GenSectorAssignment .alpha ≠ GenSectorAssignment .pi ∧
    GenSectorAssignment .alpha ≠ GenSectorAssignment .gamma ∧
    GenSectorAssignment .alpha ≠ GenSectorAssignment .eta ∧
    GenSectorAssignment .alpha ≠ GenSectorAssignment .omega ∧
    GenSectorAssignment .pi ≠ GenSectorAssignment .gamma ∧
    GenSectorAssignment .pi ≠ GenSectorAssignment .eta ∧
    GenSectorAssignment .pi ≠ GenSectorAssignment .omega ∧
    GenSectorAssignment .gamma ≠ GenSectorAssignment .eta ∧
    GenSectorAssignment .gamma ≠ GenSectorAssignment .omega ∧
    GenSectorAssignment .eta ≠ GenSectorAssignment .omega := by
  simp [GenSectorAssignment]

/-- Φ hits all 5 sectors (surjective). -/
theorem assignment_surjective (s : Sector) :
    ∃ g : Generator, GenSectorAssignment g = s := by
  cases s with
  | D => exact ⟨.alpha, rfl⟩
  | A => exact ⟨.pi, rfl⟩
  | B => exact ⟨.gamma, rfl⟩
  | C => exact ⟨.eta, rfl⟩
  | Omega => exact ⟨.omega, rfl⟩

-- ============================================================
-- COHERENCE KERNEL [IV.D246]
-- ============================================================

/-- [IV.D246] The coherence kernel K: the categorical core generating
    all physics. At E₁, K = {α,π,γ,η,ω} with canonical sector assignment
    and polarity signatures. Minimal generating set for the coupling ledger. -/
structure CoherenceKernel where
  /-- Number of generators. -/
  gen_count : Nat
  gen_count_eq : gen_count = 5
  /-- Number of sectors covered (= gen_count for bijective assignment). -/
  sector_count : Nat
  sector_count_eq : sector_count = 5
  /-- Bijective (gen_count = sector_count). -/
  bijective : gen_count = sector_count
  deriving Repr

/-- The canonical coherence kernel at E₁. -/
def canonical_kernel : CoherenceKernel where
  gen_count := 5
  gen_count_eq := rfl
  sector_count := 5
  sector_count_eq := rfl
  bijective := rfl

-- ============================================================
-- UNIQUENESS OF ASSIGNMENT [IV.P146]
-- ============================================================

/-- Polarity of a generator in the canonical assignment. -/
def gen_polarity (g : Generator) : PolaritySign :=
  (sector_physics (GenSectorAssignment g)).polarity

/-- Depth of a generator in the canonical assignment. -/
def gen_depth (g : Generator) : Nat :=
  (sector_physics (GenSectorAssignment g)).depth

/-- Helper: extract polarity from sector_physics without exposing coupling Nats. -/
private theorem sp_polarity :
    ∀ s : Sector,
    (sector_physics s).polarity = match s with
      | .D => PolaritySign.ChiPlus | .A => .Balanced
      | .B => .ChiPlus | .C => .ChiMinus | .Omega => .Crossing := by
  intro s; cases s <;> rfl

/-- Helper: extract depth from sector_physics without exposing coupling Nats. -/
private theorem sp_depth :
    ∀ s : Sector,
    (sector_physics s).depth = match s with
      | .D => 1 | .A => 1 | .B => 2 | .C => 3 | .Omega => 3 := by
  intro s; cases s <;> rfl

/-- [IV.P146] Uniqueness of generator–sector assignment:
    any assignment Ψ agreeing on polarity and depth must equal Φ.
    Proved by exhaustive case analysis on generator × sector. -/
theorem assignment_unique (Psi : Generator → Sector)
    (h_pol : ∀ g, (sector_physics (Psi g)).polarity = gen_polarity g)
    (h_dep : ∀ g, (sector_physics (Psi g)).depth = gen_depth g) :
    ∀ g, Psi g = GenSectorAssignment g := by
  intro g
  have hp := h_pol g; have hd := h_dep g
  -- Rewrite polarity/depth to simple match expressions
  rw [sp_polarity] at hp; rw [sp_depth] at hd
  simp only [gen_polarity, gen_depth, GenSectorAssignment, sp_polarity, sp_depth] at hp hd ⊢
  cases g <;> cases hPsi : (Psi _) <;> simp_all

-- ============================================================
-- ONTIC MINIMALITY [IV.D248]
-- ============================================================

/-- All 5 generators as a list. -/
def all_generators : List Generator := [.alpha, .pi, .gamma, .eta, .omega]

/-- Sectors covered by a list of generators. -/
def covered_sectors (gens : List Generator) : List Sector :=
  gens.map GenSectorAssignment

/-- [IV.D248] Ontic minimality: each generator is the unique preimage
    of its sector under Φ, so removing any one loses a sector. -/
theorem ontic_minimality :
    GenSectorAssignment .alpha = .D ∧ GenSectorAssignment .pi ≠ .D ∧
    GenSectorAssignment .gamma ≠ .D ∧ GenSectorAssignment .eta ≠ .D ∧
    GenSectorAssignment .omega ≠ .D ∧
    GenSectorAssignment .pi = .A ∧ GenSectorAssignment .alpha ≠ .A ∧
    GenSectorAssignment .gamma ≠ .A ∧ GenSectorAssignment .eta ≠ .A ∧
    GenSectorAssignment .omega ≠ .A ∧
    GenSectorAssignment .gamma = .B ∧ GenSectorAssignment .alpha ≠ .B ∧
    GenSectorAssignment .pi ≠ .B ∧ GenSectorAssignment .eta ≠ .B ∧
    GenSectorAssignment .omega ≠ .B ∧
    GenSectorAssignment .eta = .C ∧ GenSectorAssignment .alpha ≠ .C ∧
    GenSectorAssignment .pi ≠ .C ∧ GenSectorAssignment .gamma ≠ .C ∧
    GenSectorAssignment .omega ≠ .C ∧
    GenSectorAssignment .omega = .Omega ∧ GenSectorAssignment .alpha ≠ .Omega ∧
    GenSectorAssignment .pi ≠ .Omega ∧ GenSectorAssignment .gamma ≠ .Omega ∧
    GenSectorAssignment .eta ≠ .Omega := by
  simp [GenSectorAssignment]

theorem kernel_generator_count : all_generators.length = 5 := by rfl

-- ============================================================
-- CONSISTENCY WITH SECTOR PARAMETERS
-- ============================================================

/-- Assignment agrees with sector parameter generator fields. -/
theorem assignment_agrees_with_params :
    gravity_sector.generator = .alpha ∧
    weak_sector.generator = .pi ∧
    em_sector.generator = .gamma ∧
    strong_sector.generator = .eta ∧
    higgs_sector.generator = .omega := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

-- ============================================================
-- SMOKE TESTS
-- ============================================================

#eval GenSectorAssignment .alpha   -- D
#eval GenSectorAssignment .pi     -- A
#eval GenSectorAssignment .gamma  -- B
#eval GenSectorAssignment .eta    -- C
#eval GenSectorAssignment .omega  -- Omega
#eval all_generators.length        -- 5
#eval gen_polarity .alpha          -- ChiPlus
#eval gen_polarity .pi             -- Balanced
#eval gen_depth .alpha             -- 1
#eval gen_depth .gamma             -- 2

end Tau.BookIV.Arena
