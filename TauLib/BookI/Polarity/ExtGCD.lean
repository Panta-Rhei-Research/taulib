import TauLib.BookI.Polarity.ModArith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# TauLib.BookI.Polarity.ExtGCD

Extended GCD algorithm, Bézout identity, and modular inverse existence.

## Main Results

- `ext_gcd`: Extended GCD returning (gcd, s, t) with Int Bézout coefficients
- `ext_gcd_bezout`: Bézout identity: ↑a * s + ↑b * t = ↑(gcd a b)
- `mod_inv_exists`: For coprime a, m with m > 1, a modular inverse exists
-/

namespace Tau.Polarity

open Tau.Denotation Tau.Coordinates

-- ============================================================
-- EXTENDED GCD
-- ============================================================

/-- Extended GCD: returns (gcd, s, t) with gcd = Nat.gcd a b
    and ↑a * s + ↑b * t = ↑gcd (Int coefficients). -/
def ext_gcd (a b : Nat) : Nat × Int × Int :=
  if b = 0 then (a, 1, 0)
  else
    let r := ext_gcd b (a % b)
    (r.1, r.2.2, r.2.1 - ↑(a / b) * r.2.2)
termination_by b
decreasing_by exact Nat.mod_lt a (by omega)

-- ============================================================
-- BÉZOUT IDENTITY
-- ============================================================

/-- ext_gcd computes the GCD. -/
theorem ext_gcd_fst (a b : Nat) : (ext_gcd a b).1 = Nat.gcd a b := by
  induction b using Nat.strongRecOn generalizing a with
  | _ b ih =>
  unfold ext_gcd
  split
  · -- b = 0
    rename_i hb; rw [hb, Nat.gcd_zero_right]
  · -- b > 0
    rename_i hb
    simp only []
    have hlt : a % b < b := Nat.mod_lt a (by omega)
    rw [ih (a % b) hlt b]
    -- Goal: Nat.gcd b (a % b) = Nat.gcd a b
    rw [Nat.gcd_comm a b, Nat.gcd_rec b a, Nat.gcd_comm]

/-- Bézout identity: ↑a * s + ↑b * t = ↑(ext_gcd a b).1. -/
theorem ext_gcd_bezout (a b : Nat) :
    (↑a : Int) * (ext_gcd a b).2.1 + (↑b : Int) * (ext_gcd a b).2.2 =
    ↑(ext_gcd a b).1 := by
  induction b using Nat.strongRecOn generalizing a with
  | _ b ih =>
  unfold ext_gcd
  split
  · -- b = 0: (a, 1, 0). ↑a * 1 + ↑0 * 0 = ↑a ✓
    simp
  · -- b > 0
    rename_i hb
    simp only []
    have hlt : a % b < b := Nat.mod_lt a (by omega)
    have ih' := ih (a % b) hlt b
    -- ih': ↑b * (ext_gcd b (a%b)).2.1 + ↑(a%b) * (ext_gcd b (a%b)).2.2 = ↑(ext_gcd b (a%b)).1
    -- Goal: ↑a * (ext_gcd b (a%b)).2.2 + ↑b * ((ext_gcd b (a%b)).2.1 - ↑(a/b) * (ext_gcd b (a%b)).2.2) = ↑(ext_gcd b (a%b)).1
    set g := (ext_gcd b (a % b)).1
    set x := (ext_gcd b (a % b)).2.1
    set y := (ext_gcd b (a % b)).2.2
    -- Key: a = b * (a/b) + a%b (lifted to Int)
    have hdiv : (↑a : Int) = ↑b * ↑(a / b) + ↑(a % b) := by
      have := Nat.div_add_mod a b; omega
    linear_combination ih' + y * hdiv

/-- Combined: ext_gcd gives Bézout coefficients for gcd. -/
theorem ext_gcd_spec (a b : Nat) :
    (↑a : Int) * (ext_gcd a b).2.1 + (↑b : Int) * (ext_gcd a b).2.2 =
    ↑(Nat.gcd a b) := by
  rw [← ext_gcd_fst a b]; exact ext_gcd_bezout a b

-- ============================================================
-- MODULAR INVERSE EXISTENCE (from Bézout)
-- ============================================================

/-- If gcd(a, m) = 1 and m > 1, there exists x < m with (a*x) % m = 1. -/
theorem mod_inv_exists (a m : Nat) (hcop : Nat.Coprime a m) (hm : m > 1) :
    ∃ x : Nat, x < m ∧ (a * x) % m = 1 := by
  -- Get Bézout: ↑a * s + ↑m * t = ↑(gcd a m) = 1
  have hbez := ext_gcd_spec a m
  rw [hcop] at hbez
  -- hbez : ↑a * s + ↑m * t = 1
  set s := (ext_gcd a m).2.1
  set t := (ext_gcd a m).2.2
  -- (↑a * s) mod ↑m = 1
  have hm0 : (↑m : Int) ≠ 0 := by omega
  have hm_pos : (↑m : Int) > 0 := by omega
  have has_mod : ((↑a : Int) * s) % (↑m : Int) = 1 := by
    -- (↑a * s + ↑m * t) % ↑m = (↑a * s) % ↑m
    have h1 := Int.add_mul_emod_self_left ((↑a : Int) * s) (↑m : Int) t
    -- h1 : (↑a * s + ↑m * t) % ↑m = (↑a * s) % ↑m
    rw [hbez] at h1
    -- h1 : (1 : Int) % ↑m = (↑a * s) % ↑m
    rw [Int.emod_eq_of_lt (by omega) (by omega)] at h1
    -- h1 : 1 = (↑a * s) % ↑m
    exact h1.symm
  -- Positive representative: x = ((s % m) + m) % m
  let x_int := (s % (↑m : Int) + ↑m) % (↑m : Int)
  have hx_nonneg : x_int ≥ 0 := Int.emod_nonneg _ hm0
  have hx_lt : x_int < (↑m : Int) := Int.emod_lt_of_pos _ hm_pos
  -- x_int = s % ↑m (and hence x_int ≡ s mod m)
  have hx_eq : x_int = s % (↑m : Int) := by
    show (s % (↑m : Int) + ↑m) % (↑m : Int) = s % (↑m : Int)
    have h1 := Int.add_mul_emod_self_left (s % (↑m : Int)) (↑m : Int) 1
    simp only [Int.mul_one] at h1
    rw [h1]; exact Int.emod_emod_of_dvd s ⟨1, by ring⟩
  have hx_mod : ((↑a : Int) * x_int) % (↑m : Int) = 1 := by
    rw [hx_eq, Int.mul_emod (↑a : Int) (s % (↑m : Int)) (↑m : Int),
        Int.emod_emod_of_dvd s ⟨1, by ring⟩, ← Int.mul_emod, has_mod]
  -- Convert to Nat
  use x_int.toNat
  refine ⟨?_, ?_⟩
  · exact (Int.toNat_lt hx_nonneg).mpr hx_lt
  · have : (↑(a * x_int.toNat) : Int) % (↑m : Int) = 1 := by
      rw [Nat.cast_mul, Int.toNat_of_nonneg hx_nonneg]; exact hx_mod
    exact_mod_cast this

-- ============================================================
-- SMOKE TESTS
-- ============================================================

#eval ext_gcd 35 15    -- (5, 1, -2): 35*1 + 15*(-2) = 5
#eval ext_gcd 12 8     -- (4, 1, -1): 12*1 + 8*(-1) = 4
#eval ext_gcd 3 5      -- (1, 2, -1): 3*2 + 5*(-1) = 1

end Tau.Polarity
