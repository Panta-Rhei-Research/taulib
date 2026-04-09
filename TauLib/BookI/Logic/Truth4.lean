import TauLib.BookI.Polarity.BipolarAlgebra

/-!
# TauLib.BookI.Logic.Truth4

The four-valued logic earned from bipolar prime polarity.

## Registry Cross-References
- [I.D21] Truth4 Logic — `Truth4`, `Truth4.meet`, `Truth4.join`, `Truth4.neg`

## Ground Truth Sources
- chunk_0228_M002194: Split-complex algebra, bipolar balance
- chunk_0310_M002679: Bipolar partition lifts to split-complex via Chi character

## Mathematical Content

The two spectral sectors (B and C) can independently confirm or deny a predicate,
yielding four truth values: T (both confirm), F (both deny), B (overdetermined),
N (underdetermined). These form a diamond lattice T > B, N > F.

Truth4 is isomorphic to Bool x Bool via the sector encoding:
  T = (true, true),  F = (false, false),  B = (true, false),  N = (false, true).

As a lattice, Truth4 is the product 2 x 2, hence a Boolean algebra.
The non-classical behavior arises not from the lattice structure but from the
material implication (impl a b := join (neg a) b), which does not validate
all classical tautologies when evaluated at B or N.
-/

namespace Tau.Logic

-- ============================================================
-- TRUTH4 TYPE [I.D21]
-- ============================================================

/-- [I.D21] The four truth values from bipolar evaluation.
    - T: both sectors confirm (overdetermined-true)
    - F: both sectors deny (underdetermined-false)
    - B: B-sector confirms, C-sector denies (overdetermined / "both")
    - N: neither sector confirms (underdetermined / "neither") -/
inductive Truth4 where
  | T : Truth4
  | F : Truth4
  | B : Truth4
  | N : Truth4
  deriving DecidableEq, Repr, Inhabited

open Truth4

-- ============================================================
-- PARTIAL ORDER (diamond lattice: F < B, F < N, B < T, N < T)
-- ============================================================

/-- Lattice ordering on Truth4.
    Diamond: F is bottom, T is top, B and N are incomparable middle elements. -/
def Truth4.le : Truth4 -> Truth4 -> Bool
  | F, _ => true
  | _, T => true
  | B, B => true
  | N, N => true
  | _, _ => false

-- ============================================================
-- MEET (conjunction / infimum)
-- ============================================================

/-- Meet (conjunction): greatest lower bound in the diamond lattice. -/
def Truth4.meet : Truth4 -> Truth4 -> Truth4
  | T, b => b
  | a, T => a
  | F, _ => F
  | _, F => F
  | B, B => B
  | N, N => N
  | B, N => F
  | N, B => F

-- ============================================================
-- JOIN (disjunction / supremum)
-- ============================================================

/-- Join (disjunction): least upper bound in the diamond lattice. -/
def Truth4.join : Truth4 -> Truth4 -> Truth4
  | F, b => b
  | a, F => a
  | T, _ => T
  | _, T => T
  | B, B => B
  | N, N => N
  | B, N => T
  | N, B => T

-- ============================================================
-- NEGATION (bipolar swap: T <-> F, B <-> N)
-- ============================================================

/-- Negation: bipolar polarity swap. T <-> F, B <-> N.
    Corresponds to the polarity involution sigma on the split-complex algebra. -/
def Truth4.neg : Truth4 -> Truth4
  | T => F
  | F => T
  | B => N
  | N => B

-- ============================================================
-- MATERIAL IMPLICATION
-- ============================================================

/-- Material implication: a -> b := join(neg a, b).
    Note: this does NOT validate all classical tautologies at B and N. -/
def Truth4.impl (a b : Truth4) : Truth4 := Truth4.join (Truth4.neg a) b

-- ============================================================
-- BOOL x BOOL ISOMORPHISM
-- ============================================================

/-- Encode Truth4 as a pair of Booleans (B-sector, C-sector). -/
def Truth4.toBoolPair : Truth4 -> Bool × Bool
  | T => (true, true)
  | F => (false, false)
  | B => (true, false)
  | N => (false, true)

/-- Decode a Boolean pair back to Truth4. -/
def Truth4.fromBoolPair : Bool × Bool -> Truth4
  | (true, true) => T
  | (false, false) => F
  | (true, false) => B
  | (false, true) => N

-- ============================================================
-- LATTICE AXIOMS
-- ============================================================

/-- Meet is commutative. -/
theorem Truth4.meet_comm (a b : Truth4) : Truth4.meet a b = Truth4.meet b a := by
  cases a <;> cases b <;> rfl

/-- Join is commutative. -/
theorem Truth4.join_comm (a b : Truth4) : Truth4.join a b = Truth4.join b a := by
  cases a <;> cases b <;> rfl

/-- Meet is associative. -/
theorem Truth4.meet_assoc (a b c : Truth4) :
    Truth4.meet (Truth4.meet a b) c = Truth4.meet a (Truth4.meet b c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- Join is associative. -/
theorem Truth4.join_assoc (a b c : Truth4) :
    Truth4.join (Truth4.join a b) c = Truth4.join a (Truth4.join b c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- Meet is idempotent. -/
theorem Truth4.meet_idem (a : Truth4) : Truth4.meet a a = a := by
  cases a <;> rfl

/-- Join is idempotent. -/
theorem Truth4.join_idem (a : Truth4) : Truth4.join a a = a := by
  cases a <;> rfl

/-- Absorption law: meet a (join a b) = a. -/
theorem Truth4.absorption_meet_join (a b : Truth4) :
    Truth4.meet a (Truth4.join a b) = a := by
  cases a <;> cases b <;> rfl

/-- Absorption law: join a (meet a b) = a. -/
theorem Truth4.absorption_join_meet (a b : Truth4) :
    Truth4.join a (Truth4.meet a b) = a := by
  cases a <;> cases b <;> rfl

/-- Meet distributes over join. -/
theorem Truth4.meet_distrib_join (a b c : Truth4) :
    Truth4.meet a (Truth4.join b c) = Truth4.join (Truth4.meet a b) (Truth4.meet a c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- Join distributes over meet. -/
theorem Truth4.join_distrib_meet (a b c : Truth4) :
    Truth4.join a (Truth4.meet b c) = Truth4.meet (Truth4.join a b) (Truth4.join a c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- F is the bottom element for meet. -/
theorem Truth4.meet_F (a : Truth4) : Truth4.meet F a = F := by
  cases a <;> rfl

/-- T is the top element for join. -/
theorem Truth4.join_T (a : Truth4) : Truth4.join T a = T := by
  cases a <;> rfl

/-- T is the identity for meet. -/
theorem Truth4.meet_T (a : Truth4) : Truth4.meet T a = a := by
  cases a <;> rfl

/-- F is the identity for join. -/
theorem Truth4.join_F (a : Truth4) : Truth4.join F a = a := by
  cases a <;> rfl

-- ============================================================
-- NEGATION PROPERTIES
-- ============================================================

/-- Negation is involutive: neg (neg v) = v. -/
theorem Truth4.neg_involutive (v : Truth4) : Truth4.neg (Truth4.neg v) = v := by
  cases v <;> rfl

/-- neg T = F. -/
theorem Truth4.neg_T : Truth4.neg T = F := rfl

/-- neg F = T. -/
theorem Truth4.neg_F : Truth4.neg F = T := rfl

/-- neg B = N. -/
theorem Truth4.neg_B : Truth4.neg B = N := rfl

/-- neg N = B. -/
theorem Truth4.neg_N : Truth4.neg N = B := rfl

-- ============================================================
-- COMPLEMENTATION (Boolean algebra property)
-- ============================================================

/-- Complement law: meet a (neg a) = F for all a. -/
theorem Truth4.complement_meet (a : Truth4) : Truth4.meet a (Truth4.neg a) = F := by
  cases a <;> rfl

/-- Complement law: join a (neg a) = T for all a. -/
theorem Truth4.complement_join (a : Truth4) : Truth4.join a (Truth4.neg a) = T := by
  cases a <;> rfl

-- ============================================================
-- DE MORGAN LAWS
-- ============================================================

/-- De Morgan: neg (meet a b) = join (neg a) (neg b). -/
theorem Truth4.de_morgan_meet (a b : Truth4) :
    Truth4.neg (Truth4.meet a b) = Truth4.join (Truth4.neg a) (Truth4.neg b) := by
  cases a <;> cases b <;> rfl

/-- De Morgan: neg (join a b) = meet (neg a) (neg b). -/
theorem Truth4.de_morgan_join (a b : Truth4) :
    Truth4.neg (Truth4.join a b) = Truth4.meet (Truth4.neg a) (Truth4.neg b) := by
  cases a <;> cases b <;> rfl

-- ============================================================
-- BOOL x BOOL ISOMORPHISM PROPERTIES
-- ============================================================

/-- toBoolPair is injective: distinct truth values map to distinct pairs. -/
theorem Truth4.toBoolPair_injective (a b : Truth4)
    (h : Truth4.toBoolPair a = Truth4.toBoolPair b) : a = b := by
  cases a <;> cases b <;> simp [Truth4.toBoolPair] at h <;> rfl

/-- Round-trip: fromBoolPair (toBoolPair v) = v. -/
theorem Truth4.fromBoolPair_roundtrip (v : Truth4) :
    Truth4.fromBoolPair (Truth4.toBoolPair v) = v := by
  cases v <;> rfl

/-- Round-trip: toBoolPair (fromBoolPair p) = p for valid pairs. -/
theorem Truth4.toBoolPair_roundtrip (p : Bool × Bool) :
    Truth4.toBoolPair (Truth4.fromBoolPair p) = p := by
  rcases p with ⟨b1, b2⟩
  cases b1 <;> cases b2 <;> rfl

-- ============================================================
-- BRIDGE: TRUTH4 <-> SECTOR PAIRS
-- ============================================================

/-- Map Truth4 to sector pairs: T = (1,1), F = (0,0), B = (1,0), N = (0,1).
    Links Truth4 to the split-complex idempotent structure from BipolarAlgebra. -/
def Truth4.toSectorPair : Truth4 -> Tau.Polarity.SectorPair
  | T => { b_sector := 1, c_sector := 1 }
  | F => { b_sector := 0, c_sector := 0 }
  | B => Tau.Polarity.e_plus_sector
  | N => Tau.Polarity.e_minus_sector

/-- B maps to the B-sector idempotent e+. -/
theorem Truth4.B_is_e_plus :
    Truth4.toSectorPair B = Tau.Polarity.e_plus_sector := rfl

/-- N maps to the C-sector idempotent e-. -/
theorem Truth4.N_is_e_minus :
    Truth4.toSectorPair N = Tau.Polarity.e_minus_sector := rfl

/-- Spectral bridge: meet of B and N gives F, mirroring e+ * e- = 0. -/
theorem Truth4.B_meet_N_spectral :
    Truth4.meet B N = F := rfl

-- ============================================================
-- LE PROPERTIES
-- ============================================================

/-- le is reflexive. -/
theorem Truth4.le_refl (a : Truth4) : Truth4.le a a = true := by
  cases a <;> rfl

/-- F is the bottom element. -/
theorem Truth4.le_F (a : Truth4) : Truth4.le F a = true := by
  cases a <;> rfl

/-- T is the top element. -/
theorem Truth4.le_T (a : Truth4) : Truth4.le a T = true := by
  cases a <;> rfl

/-- B and N are incomparable (B not le N). -/
theorem Truth4.B_not_le_N : Truth4.le B N = false := rfl

/-- B and N are incomparable (N not le B). -/
theorem Truth4.N_not_le_B : Truth4.le N B = false := rfl

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Meet table spot checks
#eval Truth4.meet T B      -- B
#eval Truth4.meet B N      -- F
#eval Truth4.meet N N      -- N
#eval Truth4.meet F T      -- F

-- Join table spot checks
#eval Truth4.join F B      -- B
#eval Truth4.join B N      -- T
#eval Truth4.join N N      -- N
#eval Truth4.join T F      -- T

-- Negation
#eval Truth4.neg T         -- F
#eval Truth4.neg B         -- N
#eval Truth4.neg N         -- B
#eval Truth4.neg F         -- T

-- Material implication
#eval Truth4.impl T F      -- F
#eval Truth4.impl F T      -- T
#eval Truth4.impl B F      -- N (explosion barrier!)
#eval Truth4.impl B B      -- T

-- Bool pair round-trips
#eval Truth4.toBoolPair T                        -- (true, true)
#eval Truth4.toBoolPair B                        -- (true, false)
#eval Truth4.fromBoolPair (true, false)           -- B
#eval Truth4.fromBoolPair (Truth4.toBoolPair N)   -- N

-- De Morgan spot checks
#eval Truth4.neg (Truth4.meet B N)                           -- T
#eval Truth4.join (Truth4.neg B) (Truth4.neg N)              -- T (matches)
#eval Truth4.neg (Truth4.join B N)                           -- F
#eval Truth4.meet (Truth4.neg B) (Truth4.neg N)              -- F (matches)

-- Complement laws
#eval Truth4.meet B (Truth4.neg B)   -- F
#eval Truth4.join B (Truth4.neg B)   -- T
#eval Truth4.meet N (Truth4.neg N)   -- F
#eval Truth4.join N (Truth4.neg N)   -- T

-- Sector pair bridge
#eval Truth4.toSectorPair T   -- { b_sector := 1, c_sector := 1 }
#eval Truth4.toSectorPair B   -- { b_sector := 1, c_sector := 0 } = e+
#eval Truth4.toSectorPair N   -- { b_sector := 0, c_sector := 1 } = e-
#eval Truth4.toSectorPair F   -- { b_sector := 0, c_sector := 0 }

end Tau.Logic
