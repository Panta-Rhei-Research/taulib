import TauLib.BookI.Polarity.ChineseRemainder
import TauLib.BookI.Polarity.OmegaRing
import TauLib.BookI.Polarity.CRTBasis

/-!
# TauLib.BookI.Polarity.TeichmuellerLift

Teichmüller-style canonical lifts from single-prime residues to omega-tails via CRT.

## Registry Cross-References

- [I.D30] Teichmüller Lift — `teich_lift`, `teich_component`
- [I.D29] CRT Decomposition — used for reconstruction at each stage

## Ground Truth Sources
- chunk_0177_M001919: Teichmüller chapter (Lift_ω, refinement coherence, multiplicativity)
- chunk_0314_M002691: Teichmüller lifts as CRT idempotent projections

## Mathematical Content

A Teichmüller lift embeds a single-prime residue r ∈ Z/p_iZ into the full
primorial tower as an omega-tail. The lift is constructed via CRT at each stage:
at depth k ≥ i, place residue r at position i and 0 at all other positions,
then reconstruct via crt_reconstruct.

Properties:
- Retraction: Lift_i(r) mod p_i = r mod p_i
- Orthogonality: Lift_i(r) mod p_j = 0 for j ≠ i
- Compatibility: Lift_i(r) is a compatible tower
- Decomposition: every omega-tail = Σ Lift_i(r_i)
- Multiplicativity: Lift_i(r) · Lift_i(s) = Lift_i(r·s)
-/

namespace Tau.Polarity

open Tau.Denotation

-- ============================================================
-- TEICHMÜLLER RESIDUES
-- ============================================================

/-- Teichmüller residue vector: r at position i (0-indexed), 0 elsewhere.
    This is the input to CRT reconstruction for a single-prime lift. -/
def teich_residues (r i k : TauIdx) : List TauIdx :=
  (List.range k).map (fun j => if j == i then r % nth_prime (i + 1) else 0)

-- ============================================================
-- TEICHMÜLLER COMPONENT
-- ============================================================

/-- Teichmüller component at depth k: CRT reconstruction with single active residue.
    Returns 0 for k < i+1 (prime p_{i+1} not yet in the primorial). -/
def teich_component (r i k : TauIdx) : TauIdx :=
  if k ≤ i then 0 else crt_reconstruct (teich_residues r i k) k

-- ============================================================
-- TEICHMÜLLER LIFT (omega-tail construction)
-- ============================================================

/-- Recursive list construction (tail_list pattern for clean induction). -/
private def teich_list (r i : TauIdx) : Nat → List TauIdx
  | 0 => []
  | d + 1 => teich_list r i d ++ [teich_component r i (d + 1)]

private theorem teich_list_length (r i d : Nat) : (teich_list r i d).length = d := by
  induction d with
  | zero => rfl
  | succ d' ih => simp [teich_list, ih]

/-- The Teichmüller omega-tail: canonical lift of residue r at prime p_{i+1}.
    i is 0-indexed (i=0 → prime p_1=2). -/
def teich_lift (r i d : TauIdx) : OmegaTail :=
  ⟨d, teich_list r i d, teich_list_length r i d⟩

-- ============================================================
-- VERIFICATION PREDICATES
-- ============================================================

/-- Retraction check: Lift_i(r) at depth d, mod p_{i+1} = r mod p_{i+1}. -/
def teich_retract_check (r i d : TauIdx) : Bool :=
  i < d && (teich_component r i d % nth_prime (i + 1) == r % nth_prime (i + 1))

/-- Orthogonality check: Lift_i(r) mod p_{j+1} = 0 for j ≠ i. -/
def teich_orthog_check (r i j d : TauIdx) : Bool :=
  i == j || (i < d && j < d && teich_component r i d % nth_prime (j + 1) == 0)

/-- Compatibility check: the Teichmüller lift is a compatible tower. -/
def teich_compat_check (r i d : TauIdx) : Bool :=
  compat_check (teich_lift r i d)

/-- Multiplicativity check: Lift_i(r) * Lift_i(s) = Lift_i(r*s) (componentwise). -/
def teich_mult_check (r s i d : TauIdx) : Bool :=
  let lift_r := teich_lift r i d
  let lift_s := teich_lift s i d
  let lift_rs := teich_lift (r * s) i d
  let prod := lift_r.mul lift_s rfl
  prod.components == lift_rs.components

/-- Decomposition check: nat_to_tail(n) = Σ teich_lift(n mod p_i, i, d). -/
def teich_decomp_check_go (n d : TauIdx) (i fuel : Nat) (acc : List TauIdx) : List TauIdx :=
  if fuel = 0 then acc
  else if i ≥ d then acc
  else
    let lift_i := (teich_lift (n % nth_prime (i + 1)) i d).components
    let new_acc := (List.range d).map (fun j =>
      (acc.getD j 0 + lift_i.getD j 0) % primorial (j + 1))
    teich_decomp_check_go n d (i + 1) (fuel - 1) new_acc
termination_by fuel

def teich_decomp_check (n d : TauIdx) : Bool :=
  let zero_list := (List.range d).map (fun _ => 0)
  let sum := teich_decomp_check_go n d 0 d zero_list
  let target := (mk_omega_tail n d).components
  sum == target

-- ============================================================
-- NATIVE_DECIDE VERIFICATIONS: Retraction
-- ============================================================

-- Lift_0(r) mod p_1 = r mod 2
example : teich_retract_check 1 0 3 = true := by native_decide
example : teich_retract_check 0 0 3 = true := by native_decide
example : teich_retract_check 7 0 5 = true := by native_decide
-- Lift_1(r) mod p_2 = r mod 3
example : teich_retract_check 1 1 3 = true := by native_decide
example : teich_retract_check 2 1 3 = true := by native_decide
example : teich_retract_check 7 1 5 = true := by native_decide
-- Lift_2(r) mod p_3 = r mod 5
example : teich_retract_check 3 2 3 = true := by native_decide
example : teich_retract_check 4 2 5 = true := by native_decide
-- Lift at depth 5
example : teich_retract_check 5 3 5 = true := by native_decide
example : teich_retract_check 10 4 5 = true := by native_decide

-- ============================================================
-- NATIVE_DECIDE VERIFICATIONS: Orthogonality
-- ============================================================

-- Lift_0(r) mod p_2 = 0, Lift_0(r) mod p_3 = 0
example : teich_orthog_check 1 0 1 3 = true := by native_decide
example : teich_orthog_check 1 0 2 3 = true := by native_decide
-- Lift_1(r) mod p_1 = 0, Lift_1(r) mod p_3 = 0
example : teich_orthog_check 2 1 0 3 = true := by native_decide
example : teich_orthog_check 2 1 2 3 = true := by native_decide
-- Lift_2(r) mod p_1 = 0, Lift_2(r) mod p_2 = 0
example : teich_orthog_check 3 2 0 3 = true := by native_decide
example : teich_orthog_check 3 2 1 3 = true := by native_decide
-- At depth 5
example : teich_orthog_check 7 0 3 5 = true := by native_decide
example : teich_orthog_check 7 3 0 5 = true := by native_decide
example : teich_orthog_check 7 2 4 5 = true := by native_decide

-- ============================================================
-- NATIVE_DECIDE VERIFICATIONS: Compatibility
-- ============================================================

-- Teichmüller lifts produce compatible towers
example : teich_compat_check 1 0 5 = true := by native_decide
example : teich_compat_check 2 1 5 = true := by native_decide
example : teich_compat_check 3 2 5 = true := by native_decide
example : teich_compat_check 5 3 5 = true := by native_decide
example : teich_compat_check 7 4 5 = true := by native_decide
example : teich_compat_check 0 0 5 = true := by native_decide
example : teich_compat_check 42 0 5 = true := by native_decide
example : teich_compat_check 42 2 5 = true := by native_decide

-- ============================================================
-- NATIVE_DECIDE VERIFICATIONS: Multiplicativity
-- ============================================================

-- Lift_i(r) · Lift_i(s) = Lift_i(r·s)
example : teich_mult_check 1 1 0 5 = true := by native_decide
example : teich_mult_check 1 0 1 5 = true := by native_decide
example : teich_mult_check 2 2 2 5 = true := by native_decide
example : teich_mult_check 3 4 2 5 = true := by native_decide
example : teich_mult_check 5 3 3 5 = true := by native_decide

-- ============================================================
-- NATIVE_DECIDE VERIFICATIONS: Decomposition
-- ============================================================

-- nat_to_tail(n) = Σ teich_lift(n mod p_i, i, d)
example : teich_decomp_check 7 3 = true := by native_decide
example : teich_decomp_check 42 3 = true := by native_decide
example : teich_decomp_check 100 3 = true := by native_decide
example : teich_decomp_check 7 4 = true := by native_decide
example : teich_decomp_check 42 4 = true := by native_decide
example : teich_decomp_check 7 5 = true := by native_decide
example : teich_decomp_check 42 5 = true := by native_decide
example : teich_decomp_check 100 5 = true := by native_decide

-- ============================================================
-- FORMAL PROOFS: TEICHMÜLLER PROPERTIES
-- ============================================================

/-- Helper: teich_residues diagonal — getD at position i = r % p_{i+1}. -/
private theorem teich_residues_getD_diag {r i k : TauIdx} (hi : i < k) :
    (teich_residues r i k).getD i 0 = r % nth_prime (i + 1) := by
  simp only [teich_residues, List.getD, List.getElem?_map,
    List.getElem?_range hi, Option.map, Option.getD_some, beq_self_eq_true, ↓reduceIte]

/-- Helper: teich_residues off-diagonal — getD at position j ≠ i = 0. -/
private theorem teich_residues_getD_off {r i j k : TauIdx}
    (hj : j < k) (hne : j ≠ i) :
    (teich_residues r i k).getD j 0 = 0 := by
  simp only [teich_residues, List.getD, List.getElem?_map,
    List.getElem?_range hj, Option.map, Option.getD_some]
  have : ¬(j == i) = true := by simp [beq_iff_eq, hne]
  simp [show (j == i) = false from by rwa [Bool.not_eq_true] at this]

/-- Teichmüller retraction (formal):
    teich_component r i d ≡ r (mod p_{i+1}) for i < d. -/
theorem teich_retraction_formal {r i d : TauIdx} (hi : i < d)
    (hyp : CRTHyp d) :
    teich_component r i d % nth_prime (i + 1) = r % nth_prime (i + 1) := by
  simp only [teich_component, show ¬(d ≤ i) from by simp only [TauIdx] at *; omega,
    ↓reduceIte]
  rw [crt_reconstruct_mod_prime _ hi hyp, teich_residues_getD_diag hi]
  exact mod_mod_of_dvd r _ _ ⟨1, (Nat.mul_one _).symm⟩

/-- Teichmüller orthogonality (formal):
    teich_component r i d ≡ 0 (mod p_{j+1}) for j ≠ i, both < d. -/
theorem teich_orthogonality_formal {r i j d : TauIdx}
    (hi : i < d) (hj : j < d) (hne : i ≠ j)
    (hyp : CRTHyp d) :
    teich_component r i d % nth_prime (j + 1) = 0 := by
  simp only [teich_component, show ¬(d ≤ i) from by simp only [TauIdx] at *; omega,
    ↓reduceIte]
  rw [crt_reconstruct_mod_prime _ hj hyp, teich_residues_getD_off hj (Ne.symm hne)]
  simp

-- Formal smoke tests: retraction
example : teich_component 7 0 5 % nth_prime 1 = 7 % nth_prime 1 :=
  teich_retraction_formal (by simp only [TauIdx]; omega) crt_hyp_5
example : teich_component 42 2 5 % nth_prime 3 = 42 % nth_prime 3 :=
  teich_retraction_formal (by simp only [TauIdx]; omega) crt_hyp_5

-- Formal smoke tests: orthogonality
example : teich_component 7 0 5 % nth_prime 3 = 0 :=
  teich_orthogonality_formal (by simp only [TauIdx]; omega)
    (by simp only [TauIdx]; omega) (by simp only [TauIdx]; omega) crt_hyp_5
example : teich_component 42 2 5 % nth_prime 1 = 0 :=
  teich_orthogonality_formal (by simp only [TauIdx]; omega)
    (by simp only [TauIdx]; omega) (by simp only [TauIdx]; omega) crt_hyp_5

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Teichmüller components
#eval teich_component 1 0 3   -- CRT lift of 1 at p=2, depth 3
#eval teich_component 2 1 3   -- CRT lift of 2 at p=3, depth 3
#eval teich_component 3 2 3   -- CRT lift of 3 at p=5, depth 3

-- Teichmüller lifts (full towers)
#eval teich_lift 1 0 5        -- Lift of 1 at p=2, depth 5
#eval teich_lift 1 1 5        -- Lift of 1 at p=3, depth 5
#eval teich_lift 1 2 5        -- Lift of 1 at p=5, depth 5

-- Compatibility
#eval teich_compat_check 1 0 5    -- true
#eval teich_compat_check 2 1 5    -- true

-- Decomposition
#eval teich_decomp_check 42 5     -- true
#eval teich_decomp_check 100 5    -- true

-- Verify: lift(1,i) are the CRT idempotents
#eval (teich_lift 1 0 3).components  -- e_0 tower
#eval (teich_lift 1 1 3).components  -- e_1 tower
#eval (teich_lift 1 2 3).components  -- e_2 tower

end Tau.Polarity
