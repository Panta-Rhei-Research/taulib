import TauLib.BookI.Polarity.OmegaGerms
import TauLib.BookI.Polarity.Polarity

/-!
# TauLib.BookI.Polarity.PolarizedGerms

Polarized omega-germs: B-polarized, C-polarized, and the crossing-point germ.

## Registry Cross-References

- [I.D26] Polarized Omega-Germ — `BPolarized`, `CPolarized`, `CrossingGerm`

## Ground Truth Sources
- chunk_0123_M001424: Branch predicates ∂τ₃^B, ∂τ₃^C (lines 369-386)
- chunk_0155_M001710: Crossing-point germ, σ-fixed germ class

## Mathematical Content

Given the spectral signature σ_N(p) = (B_max, C_max), the polarity at each
primorial stage provides a sequence of B/C channel values. An omega-germ is:

- B-polarized if the C-channel eventually freezes AND the B-channel keeps refining
- C-polarized if the B-channel eventually freezes AND the C-channel keeps refining
- A crossing-point germ if neither channel freezes

The crossing-point germ corresponds to the unique element ω where both
channels continue to refine at every stage. It exists as a structural
consequence of the bipolar partition.
-/

namespace Tau.Polarity

open Tau.Denotation Tau.Orbit Tau.Coordinates

-- ============================================================
-- CHANNEL SEQUENCES
-- ============================================================

/-- B-channel sequence at primorial stages: B_max for prime p at bound M_k. -/
def b_channel_seq (p k : TauIdx) : TauIdx := b_max p (primorial k)

/-- C-channel sequence at primorial stages: C_max for prime p at bound M_k. -/
def c_channel_seq (p k : TauIdx) : TauIdx := c_max p (primorial k)

-- ============================================================
-- EVENTUAL CONSTANCY
-- ============================================================

/-- A sequence (represented as function Nat → Nat) is eventually constant
    at depth d if f(k) = f(d) for all k ≥ d. -/
def eventually_constant_at (f : Nat → Nat) (d : Nat) : Prop :=
  ∀ k, k ≥ d → f k = f d

/-- A sequence is eventually constant if there exists such a depth. -/
def eventually_constant (f : Nat → Nat) : Prop :=
  ∃ d, eventually_constant_at f d

/-- Computable check: is the sequence constant from depth d₀ to d₁? -/
def const_check_go (f : Nat → Nat) (d0 d1 : Nat) (fuel : Nat) : Bool :=
  if fuel = 0 then true
  else if d0 > d1 then true
  else
    (f d0 == f (d0 + 1)) && const_check_go f (d0 + 1) d1 (fuel - 1)
termination_by fuel

def const_check (f : Nat → Nat) (from_depth to_depth : Nat) : Bool :=
  const_check_go f from_depth to_depth (to_depth - from_depth + 1)

-- ============================================================
-- COFINALITY (channel keeps refining)
-- ============================================================

/-- A sequence is cofinal if it takes nonzero values at arbitrarily large indices.
    Ground truth (chunk_0123): ∀M ∃n≥M, Bₙ ≠ α₁. -/
def cofinal (f : Nat → Nat) : Prop :=
  ∀ M, ∃ k, k ≥ M ∧ f k ≠ 0

/-- Computable check: does the sequence have a nonzero value between from_depth and to_depth? -/
def cofinal_check_go (f : Nat → Nat) (i to_depth : Nat) (fuel : Nat) : Bool :=
  if fuel = 0 then false
  else if i > to_depth then false
  else if f i ≠ 0 then true
  else cofinal_check_go f (i + 1) to_depth (fuel - 1)
termination_by fuel

def cofinal_check (f : Nat → Nat) (from_depth to_depth : Nat) : Bool :=
  cofinal_check_go f from_depth to_depth (to_depth - from_depth + 1)

-- ============================================================
-- POLARIZED GERMS [I.D26]
-- ============================================================

/-- [I.D26] B-polarized at a prime p: C-channel eventually freezes AND B-channel
    keeps refining (cofinal). Ground truth (chunk_0123, lines 369-386):
    ∂τ₃^B := { [x•] | ∃N ∀n≥N, Cₙ=α₁  ∧  ∀M ∃n≥M, Bₙ≠α₁ }. -/
def BPolarized (p : TauIdx) : Prop :=
  eventually_constant (c_channel_seq p) ∧ cofinal (b_channel_seq p)

/-- C-polarized at a prime p: B-channel eventually freezes AND C-channel
    keeps refining (cofinal). Symmetric to BPolarized. -/
def CPolarized (p : TauIdx) : Prop :=
  eventually_constant (b_channel_seq p) ∧ cofinal (c_channel_seq p)

/-- Crossing germ at a prime p: neither channel eventually freezes.
    Corresponds to the unique wedge point of the lemniscate ∂τ₃ ≅ S¹∨S¹. -/
def CrossingGerm (p : TauIdx) : Prop :=
  ¬eventually_constant (c_channel_seq p) ∧ ¬eventually_constant (b_channel_seq p)

-- ============================================================
-- COMPUTABLE POLARIZATION CHECKS
-- ============================================================

/-- Check if prime p appears B-polarized up to primorial depth d:
    C-channel constant from some point AND B-channel has nonzero values. -/
def b_polarized_check (p d : TauIdx) : Bool :=
  if d ≤ 2 then false
  else const_check (c_channel_seq p) 2 d && cofinal_check (b_channel_seq p) 1 d

/-- Check if prime p appears C-polarized up to primorial depth d:
    B-channel constant from some point AND C-channel has nonzero values. -/
def c_polarized_check (p d : TauIdx) : Bool :=
  if d ≤ 2 then false
  else const_check (b_channel_seq p) 2 d && cofinal_check (c_channel_seq p) 1 d

/-- Polarity status string for a prime at a given primorial depth. -/
def germ_status (p d : TauIdx) : String :=
  if b_polarized_check p d then "B-polarized (C frozen)"
  else if c_polarized_check p d then "C-polarized (B frozen)"
  else "undetermined"

-- ============================================================
-- CHANNEL VALUE DISPLAY
-- ============================================================

/-- Display the B and C channel sequences for a prime at primorial stages 1..d. -/
def channel_display_go (p k d : Nat) (fuel : Nat) (acc : List (Nat × Nat)) :
    List (Nat × Nat) :=
  if fuel = 0 then acc.reverse
  else if k > d then acc.reverse
  else
    let bv := b_channel_seq p k
    let cv := c_channel_seq p k
    channel_display_go p (k + 1) d (fuel - 1) (acc ++ [(bv, cv)])
termination_by fuel

def channel_display (p d : TauIdx) : List (TauIdx × TauIdx) :=
  channel_display_go p 1 d d []

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Channel sequences at primorial stages
-- M_1=2, M_2=6, M_3=30, M_4=210, M_5=2310
#eval channel_display 2 5    -- B,C values for prime 2 at stages 1..5
#eval channel_display 3 5    -- for prime 3
#eval channel_display 5 4    -- for prime 5

-- Polarization checks
#eval b_polarized_check 2 5   -- is prime 2 B-polarized up to depth 5?
#eval b_polarized_check 3 5   -- prime 3?
#eval c_polarized_check 2 5   -- is prime 2 C-polarized?
#eval c_polarized_check 3 5

-- Germ status
#eval germ_status 2 5
#eval germ_status 3 5
#eval germ_status 5 4
#eval germ_status 7 4

end Tau.Polarity
