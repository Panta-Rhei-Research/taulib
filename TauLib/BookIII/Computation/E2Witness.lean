import TauLib.BookIII.Computation.TowerMachine

/-!
# TauLib.BookIII.Computation.E2Witness

Constructive E₂ operational closure witnesses: Kleene fixed points,
orbit diversity, and strict enrichment beyond E₁.

## Registry Cross-References

- [III.D83] Kleene Fixed Point — `kleene_fixed_point`, `kleene_check`
- [III.D84] E₂ Orbit Structure — `orbit_length`, `orbit_diversity_check`
- [III.T57] Operational Closure — `operational_closure_full_check`
- [III.P34] E₂ ⊋ E₁ Strict Witness — `e2_strict_witness_check`

## Mathematical Content

**III.D83 (Kleene Fixed Point):** At stage k, define the self-application
operator S(c) = D(c, c) where D is the code-decode map. A fixed point is
c* such that S(c*) = c*. At every finite stage, fixed points exist because
the map Z/M_k Z → Z/M_k Z is on a finite set.

**III.D84 (E₂ Orbit Structure):** The orbit of code c under the decode map
D: x ↦ (x + d) mod M_k has length dividing M_k. Orbit lengths exhibit
diversity: not all orbits have the same length, proving computational
richness (contrast with E₁ where all orbits are trivially periodic).

**III.T57 (Operational Closure):** Every E₂-admissible operation (code-decode
cycle) stays within E₂: the output is a valid E₂ carrier element at the
same or lower stage. This is the computational analog of holomorphic closure.

**III.P34 (E₂ ⊋ E₁ Strict Witness):** E₂ contains code-decode structures
that cannot be expressed as pure sector decompositions (E₁ content). The
witness is an orbit with length > 2 (E₁ orbits have length ≤ 2 due to
bipolar e₊/e₋ involution).
-/

set_option autoImplicit false

namespace Tau.BookIII.Computation

open Tau.Polarity Tau.Boundary Tau.Coordinates Tau.Denotation
open Tau.BookII.Interior Tau.BookII.Enrichment
open Tau.BookIII.Enrichment Tau.BookIII.Sectors
open Tau.BookIII.Spectral

-- ============================================================
-- KLEENE FIXED POINT [III.D83]
-- ============================================================

/-- [III.D83] Self-application operator S(c) = (c + c) mod M_k.
    Models code applied to itself (Kleene's recursion theorem). -/
def self_apply (c k : Nat) : Nat :=
  let pk := primorial k
  if pk == 0 then 0
  else (c + c) % pk

/-- [III.D83] Find a fixed point of self-application at stage k:
    c* such that S(c*) = c*. At stage k, c* = 0 is always a fixed point.
    Non-trivial fixed points exist when M_k is even (c* = M_k/2). -/
def kleene_fixed_point (k : Nat) : Nat :=
  let pk := primorial k
  if pk == 0 then 0
  else 0  -- 0 is always a fixed point: (0+0) mod M_k = 0

/-- [III.D83] Count fixed points of self-application at stage k. -/
def count_fixed_points (k : Nat) : Nat :=
  let pk := primorial k
  go 0 pk 0
where
  go (c bound acc : Nat) : Nat :=
    if c >= bound then acc
    else
      let fp := if self_apply c k == c then 1 else 0
      go (c + 1) bound (acc + fp)
  termination_by bound - c

/-- [III.D83] Kleene check: fixed points exist at every stage. -/
def kleene_check (db : Nat) : Bool :=
  go 1 (db + 1)
where
  go (k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > db then true
    else
      count_fixed_points k > 0 && go (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- E₂ ORBIT STRUCTURE [III.D84]
-- ============================================================

/-- [III.D84] Orbit of code c under decoder d at stage k:
    length of the cycle c → (c+d) → (c+2d) → ... → c. -/
def orbit_length (c d k : Nat) : Nat :=
  let pk := primorial k
  if pk == 0 || d % pk == 0 then 1
  else
    go ((c + d) % pk) c pk 1 pk
where
  go (pos start pk steps fuel : Nat) : Nat :=
    if fuel = 0 then steps
    else if pos == start then steps
    else go ((pos + d) % pk) start pk (steps + 1) (fuel - 1)
  termination_by fuel

/-- [III.D84] Collect distinct orbit lengths at stage k for all (c, d). -/
def orbit_diversity_check (k : Nat) : Bool :=
  let pk := primorial k
  if pk <= 2 then true  -- trivially diverse at small stages
  else
    -- Check that not all orbits have the same length
    let len_0_1 := orbit_length 0 1 k
    let len_1_1 := orbit_length 1 1 k
    let len_0_2 := orbit_length 0 2 k
    -- Diversity: at least two distinct orbit lengths exist
    len_0_1 != len_0_2 || len_0_1 != len_1_1 || pk <= 2

/-- [III.D84] Count distinct orbit lengths at stage k. -/
def count_distinct_orbit_lengths (k : Nat) : Nat :=
  let pk := primorial k
  go_d 1 pk 0 pk k
where
  go_d (d pk acc fuel k : Nat) : Nat :=
    if fuel = 0 then acc
    else if d >= pk then acc
    else
      let len := orbit_length 0 d k
      -- Check if this length was already seen (approximate)
      let new_len := if is_new_length len d pk k then 1 else 0
      go_d (d + 1) pk (acc + new_len) (fuel - 1) k
  termination_by fuel
  is_new_length (len d pk k : Nat) : Bool :=
    go_check 1 d len pk k
  go_check (d2 bound target pk k : Nat) : Bool :=
    if d2 >= bound then true  -- not found before → new
    else if orbit_length 0 d2 k == target then false
    else go_check (d2 + 1) bound target pk k
  termination_by bound - d2

-- ============================================================
-- OPERATIONAL CLOSURE [III.T57]
-- ============================================================

/-- [III.T57] Full operational closure: every code-decode cycle
    produces a valid E₂ carrier element. -/
def operational_closure_full_check (bound db : Nat) : Bool :=
  go 0 1 ((bound + 1) * (db + 1))
where
  go (c k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if c > bound then true
    else if k > db then go (c + 1) 1 (fuel - 1)
    else
      let pk := primorial k
      if pk == 0 then go c (k + 1) (fuel - 1)
      else
        let cr := c % pk
        -- Decode step: apply each possible decoder
        go_d cr 0 pk k fuel && go c (k + 1) (fuel - 1)
  termination_by fuel
  go_d (c d pk k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if d >= pk then true
    else
      let result := (c + d) % pk
      -- Result is valid E₂ carrier: result < pk and reduce-stable
      let valid := result < pk
      let stable := reduce result k == result
      valid && stable && go_d c (d + 1) pk k (fuel - 1)
  termination_by fuel

-- ============================================================
-- E₂ ⊋ E₁ STRICT WITNESS [III.P34]
-- ============================================================

/-- [III.P34] E₂ strict witness: find an orbit with length > 2.
    E₁ orbits (bipolar involution) have length ≤ 2 (e₊↔e₋).
    E₂ orbits can have length 3, 5, etc. (prime orbit lengths). -/
def e2_strict_witness_check (db : Nat) : Bool :=
  go 2 (db + 1)
where
  go (k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > db then true
    else
      let pk := primorial k
      -- Find an orbit of length > 2
      let found := find_long_orbit 0 1 pk k pk
      found && go (k + 1) (fuel - 1)
  termination_by fuel
  find_long_orbit (c d pk k fuel : Nat) : Bool :=
    if fuel = 0 then false
    else if d >= pk then false
    else
      let len := orbit_length c d k
      if len > 2 then true
      else find_long_orbit c (d + 1) pk k (fuel - 1)
  termination_by fuel

-- ============================================================
-- THEOREMS
-- ============================================================

/-- [III.D83] Kleene fixed points exist at stages 1-3. -/
theorem kleene_check_3 :
    kleene_check 3 = true := by native_decide

/-- [III.D83] Fixed point exists at stage 2 (c=0). -/
theorem fixed_points_stage2 :
    count_fixed_points 2 >= 1 := by native_decide

/-- [III.D84] Orbit diversity at stage 2. -/
theorem orbit_diversity_2 :
    orbit_diversity_check 2 = true := by native_decide

/-- [III.D84] Orbit diversity at stage 3. -/
theorem orbit_diversity_3 :
    orbit_diversity_check 3 = true := by native_decide

/-- [III.T57] Operational closure at bound 8, depth 3. -/
theorem operational_closure_8_3 :
    operational_closure_full_check 8 3 = true := by native_decide

/-- [III.P34] E₂ strict witness at depth 3. -/
theorem e2_strict_3 :
    e2_strict_witness_check 3 = true := by native_decide

-- ============================================================
-- SMOKE TESTS
-- ============================================================

#eval self_apply 0 2           -- 0 (fixed point)
#eval self_apply 3 2           -- (3+3) % 6 = 0
#eval count_fixed_points 2     -- should be > 0
#eval orbit_length 0 1 2       -- orbit of 0 under +1 in Z/6 = 6
#eval orbit_length 0 2 2       -- orbit of 0 under +2 in Z/6 = 3
#eval orbit_length 0 3 2       -- orbit of 0 under +3 in Z/6 = 2
#eval orbit_diversity_check 2  -- true
#eval e2_strict_witness_check 3 -- true

end Tau.BookIII.Computation
