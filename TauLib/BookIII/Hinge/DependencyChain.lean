import TauLib.BookIII.Arithmetic.TowerAssembly

/-!
# TauLib.BookIII.Hinge.DependencyChain

Complete Dependency Chain from K0 through E3+: the 14-link backbone.

## Registry Cross-References

- [III.D66] Complete Dependency Chain — `dependency_chain_check`
- [III.P29] Chain Linearity — `chain_linearity_check`
- [III.P30] Terminal Completeness — `terminal_completeness_check`

## Mathematical Content

**III.D66 (Complete Dependency Chain):** The 14-link dependency chain
K0 -> K1 -> ... -> K6 -> E0 -> E1 -> E1+ -> E2 -> E2+ -> E3 -> E3+
is the backbone of the entire Panta Rhei series. Each link builds on the
previous: the seven axioms (K0-K6) construct tau^3, the four enrichment
levels (E0-E3) stratify the content, and the three plus-levels (E1+, E2+,
E3+) mark the interfaces where enrichment genuinely expands.

**III.P29 (Chain Linearity):** The chain has no cycles. Each link's index
is strictly greater than the previous. This ensures the dependency is a
total order, not a lattice.

**III.P30 (Terminal Completeness):** The chain covers all enrichment levels.
E0 through E3 each appear as a link, and E3+ is the terminal node.
After E3+, the chain saturates (E4 = E3).
-/

namespace Tau.BookIII.Hinge

open Tau.Polarity Tau.Boundary Tau.Coordinates Tau.Denotation
open Tau.BookII.Interior Tau.BookII.Enrichment
open Tau.BookIII.Enrichment Tau.BookIII.Sectors
open Tau.BookIII.Spectral Tau.BookIII.Doors
open Tau.BookIII.Physics Tau.BookIII.Arithmetic

-- ============================================================
-- DEPENDENCY CHAIN LINK ENCODING
-- ============================================================

/-- A link in the 14-step dependency chain.
    K0-K6 = the seven axioms (Book I construction).
    E0-E3 = the four enrichment levels (Books I-VII).
    E1p, E2p, E3p = the plus-interfaces (enrichment transitions). -/
inductive ChainLink where
  | K0 : ChainLink   -- void axiom
  | K1 : ChainLink   -- unit axiom
  | K2 : ChainLink   -- polarity axiom
  | K3 : ChainLink   -- boundary axiom
  | K4 : ChainLink   -- denotation axiom
  | K5 : ChainLink   -- composition axiom
  | K6 : ChainLink   -- omega axiom
  | E0 : ChainLink   -- mathematics (Books I-III)
  | E1 : ChainLink   -- physics (Books IV-V)
  | E1p : ChainLink  -- E1+ interface (NS/YM/Hodge acquired)
  | E2 : ChainLink   -- computation (Book VI)
  | E2p : ChainLink  -- E2+ interface (BSD/Langlands acquired)
  | E3 : ChainLink   -- metaphysics (Book VII)
  | E3p : ChainLink  -- E3+ terminal (saturation)
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Numeric position of each link in the chain (0-indexed). -/
def ChainLink.toNat : ChainLink -> Nat
  | .K0  => 0
  | .K1  => 1
  | .K2  => 2
  | .K3  => 3
  | .K4  => 4
  | .K5  => 5
  | .K6  => 6
  | .E0  => 7
  | .E1  => 8
  | .E1p => 9
  | .E2  => 10
  | .E2p => 11
  | .E3  => 12
  | .E3p => 13

/-- The full 14-link chain as a list. -/
def chain_links : List ChainLink :=
  [.K0, .K1, .K2, .K3, .K4, .K5, .K6,
   .E0, .E1, .E1p, .E2, .E2p, .E3, .E3p]

/-- Map a chain link to its enrichment level (K-links map to E0). -/
def ChainLink.toEnrLevel : ChainLink -> EnrLevel
  | .K0 | .K1 | .K2 | .K3 | .K4 | .K5 | .K6 | .E0 => .E0
  | .E1 | .E1p => .E1
  | .E2 | .E2p => .E2
  | .E3 | .E3p => .E3

/-- Successor link in the chain (saturates at E3p). -/
def ChainLink.succ : ChainLink -> ChainLink
  | .K0  => .K1
  | .K1  => .K2
  | .K2  => .K3
  | .K3  => .K4
  | .K4  => .K5
  | .K5  => .K6
  | .K6  => .E0
  | .E0  => .E1
  | .E1  => .E1p
  | .E1p => .E2
  | .E2  => .E2p
  | .E2p => .E3
  | .E3  => .E3p
  | .E3p => .E3p

-- ============================================================
-- COMPLETE DEPENDENCY CHAIN [III.D66]
-- ============================================================

/-- [III.D66] Verify that the chain is strictly ordered: each link's
    index is strictly less than the next link's index. -/
def chain_strict_order_check : Bool :=
  go chain_links
where
  go : List ChainLink -> Bool
    | [] => true
    | [_] => true
    | a :: b :: rest =>
      -- Strict ordering + successor consistency
      a.toNat < b.toNat && a.succ.toNat <= b.toNat && go (b :: rest)

/-- [III.D66] Verify that each enrichment level's layer template is valid
    at the corresponding chain link. For K-links, verify that the axiom
    level infrastructure (primorial, reduce, etc.) is operational. -/
def chain_layer_check (bound db : TauIdx) : Bool :=
  go chain_links bound db (chain_links.length + 1)
where
  go (links : List ChainLink) (bound db fuel : Nat) : Bool :=
    if fuel = 0 then true
    else match links with
    | [] => true
    | link :: rest =>
      let lev := link.toEnrLevel
      let layer_ok := layer_valid_at lev bound db
      layer_ok && go rest bound db (fuel - 1)
  termination_by fuel

/-- [III.D66] Verify tower coherence at each enrichment transition.
    At each E-link, the tower assembly check passes. -/
def chain_tower_check (bound db : TauIdx) : Bool :=
  -- Tower strictness: E0 < E1 < E2 < E3
  tower_strict_check &&
  -- Tower assembly: CRT + BNF + sector products coherent
  tower_assembly_check bound db

/-- [III.D66] Complete dependency chain check: strict order, layer validity,
    and tower coherence all hold simultaneously. -/
def dependency_chain_check (bound db : TauIdx) : Bool :=
  chain_strict_order_check &&
  chain_layer_check bound db &&
  chain_tower_check bound db

-- ============================================================
-- CHAIN LINEARITY [III.P29]
-- ============================================================

/-- [III.P29] Chain linearity: the chain has no cycles.
    Verification: for every pair (i, j) with i < j in the chain,
    link_i.toNat < link_j.toNat (no backward edges). -/
def chain_linearity_check : Bool :=
  go chain_links 0 (chain_links.length + 1)
where
  go (links : List ChainLink) (prev_idx fuel : Nat) : Bool :=
    if fuel = 0 then true
    else match links with
    | [] => true
    | link :: rest =>
      let curr := link.toNat
      let ok := if prev_idx == 0 && curr == 0 then true
                else curr > prev_idx || (curr == 0 && prev_idx == 0)
      ok && go rest curr (fuel - 1)
  termination_by fuel

/-- [III.P29] Acyclicity witness: no link appears twice in the chain. -/
def chain_no_duplicates_check : Bool :=
  go chain_links [] (chain_links.length + 1)
where
  go (links : List ChainLink) (seen : List Nat) (fuel : Nat) : Bool :=
    if fuel = 0 then true
    else match links with
    | [] => true
    | link :: rest =>
      let idx := link.toNat
      let fresh := !(seen.contains idx)
      fresh && go rest (idx :: seen) (fuel - 1)
  termination_by fuel

/-- [III.P29] Full chain linearity: strict order + no duplicates. -/
def chain_linearity_full_check : Bool :=
  chain_linearity_check && chain_no_duplicates_check

-- ============================================================
-- TERMINAL COMPLETENESS [III.P30]
-- ============================================================

/-- [III.P30] Terminal completeness: the chain covers all four enrichment
    levels. Accumulate which levels appear; verify all 4 are present. -/
def terminal_completeness_check : Bool :=
  go chain_links false false false false (chain_links.length + 1)
where
  go (links : List ChainLink) (e0 e1 e2 e3 : Bool) (fuel : Nat) : Bool :=
    if fuel = 0 then e0 && e1 && e2 && e3
    else match links with
    | [] => e0 && e1 && e2 && e3
    | link :: rest =>
      let lev := link.toEnrLevel
      let e0' := e0 || lev == .E0
      let e1' := e1 || lev == .E1
      let e2' := e2 || lev == .E2
      let e3' := e3 || lev == .E3
      go rest e0' e1' e2' e3' (fuel - 1)
  termination_by fuel

/-- [III.P30] The chain has exactly 14 links. -/
def chain_length_check : Bool :=
  chain_links.length == 14

/-- [III.P30] The terminal link is E3+ (saturation). -/
def chain_terminal_check : Bool :=
  match chain_links.getLast? with
  | some link => link == .E3p
  | none => false

/-- [III.P30] E3+ is terminal: its successor is itself. -/
def chain_saturation_check : Bool :=
  ChainLink.E3p.succ == .E3p

/-- [III.P30] Full terminal completeness: coverage + length + terminal
    + saturation. -/
def terminal_completeness_full_check : Bool :=
  terminal_completeness_check &&
  chain_length_check &&
  chain_terminal_check &&
  chain_saturation_check

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Chain structure
#eval chain_links.length                         -- 14
#eval ChainLink.K0.toNat                         -- 0
#eval ChainLink.E3p.toNat                        -- 13
#eval ChainLink.E3p.succ                         -- E3p (saturates)

-- Strict order
#eval chain_strict_order_check                   -- true

-- Layer check
#eval chain_layer_check 8 3                      -- true

-- Tower check
#eval chain_tower_check 10 3                     -- true

-- Complete dependency chain
#eval dependency_chain_check 8 3                 -- true

-- Chain linearity
#eval chain_linearity_check                      -- true
#eval chain_no_duplicates_check                  -- true
#eval chain_linearity_full_check                 -- true

-- Terminal completeness
#eval terminal_completeness_check                -- true
#eval chain_length_check                         -- true
#eval chain_terminal_check                       -- true
#eval chain_saturation_check                     -- true
#eval terminal_completeness_full_check           -- true

-- ============================================================
-- FORMAL VERIFICATION (native_decide)
-- ============================================================

-- [III.D66] Dependency chain
theorem dependency_chain_8_3 :
    dependency_chain_check 8 3 = true := by native_decide

theorem chain_strict_order :
    chain_strict_order_check = true := by native_decide

theorem chain_layer_8_3 :
    chain_layer_check 8 3 = true := by native_decide

theorem chain_tower_10_3 :
    chain_tower_check 10 3 = true := by native_decide

-- [III.P29] Chain linearity
theorem chain_linearity :
    chain_linearity_check = true := by native_decide

theorem chain_no_duplicates :
    chain_no_duplicates_check = true := by native_decide

theorem chain_linearity_full :
    chain_linearity_full_check = true := by native_decide

-- [III.P30] Terminal completeness
theorem terminal_completeness :
    terminal_completeness_check = true := by native_decide

theorem chain_length :
    chain_length_check = true := by native_decide

theorem chain_terminal :
    chain_terminal_check = true := by native_decide

theorem chain_saturation :
    chain_saturation_check = true := by native_decide

theorem terminal_completeness_full :
    terminal_completeness_full_check = true := by native_decide

-- ============================================================
-- STRUCTURAL THEOREMS
-- ============================================================

/-- [III.D66] Structural: the chain has exactly 14 links. -/
theorem chain_has_14_links :
    chain_links.length = 14 := rfl

/-- [III.D66] Structural: K0 is the first link (index 0). -/
theorem k0_is_first : ChainLink.K0.toNat = 0 := rfl

/-- [III.D66] Structural: E3p is the last link (index 13). -/
theorem e3p_is_last : ChainLink.E3p.toNat = 13 := rfl

/-- [III.D66] Structural: K6 -> E0 is the axiom-to-enrichment transition. -/
theorem axiom_to_enrichment :
    ChainLink.K6.succ = .E0 := rfl

/-- [III.P29] Structural: successor always increases index (except at E3p). -/
theorem succ_monotone (link : ChainLink) :
    link.toNat <= link.succ.toNat := by
  cases link <;> simp [ChainLink.toNat, ChainLink.succ]

/-- [III.P30] Structural: E3p.succ = E3p (terminal saturation). -/
theorem e3p_saturates : ChainLink.E3p.succ = .E3p := rfl

/-- [III.P30] Structural: every link maps to a valid enrichment level. -/
theorem all_links_have_level (link : ChainLink) :
    link.toEnrLevel = .E0 \/
    link.toEnrLevel = .E1 \/
    link.toEnrLevel = .E2 \/
    link.toEnrLevel = .E3 := by
  cases link <;> simp [ChainLink.toEnrLevel]

/-- [III.D66] Structural: the chain covers 7 axiom links + 7 enrichment links. -/
theorem seven_plus_seven :
    (chain_links.filter (fun l => l.toNat < 7)).length = 7 := by native_decide

end Tau.BookIII.Hinge
