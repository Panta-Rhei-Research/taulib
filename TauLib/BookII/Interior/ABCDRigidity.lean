import TauLib.BookII.Interior.BipolarDecomposition

/-!
# TauLib.BookII.Interior.ABCDRigidity

ABCD four-ray rigidity: the four rays (A, B, C, D) provide complete
and rigid coordinate structure for holomorphic analysis on τ³.

## Registry Cross-References

- [II.R04] ABCD vs Quaternions — comparison (remarks only)
- [II.P03] Four-Ray Rigidity — `four_ray_complete`, `four_ray_bipolar`

## Mathematical Content

The ABCD chart replaces quaternionic structure:

| Feature | Quaternionic (ℍ) | ABCD |
|---------|-------------------|------|
| Scalars | ℍ, dim 4, noncommutative | H_τ = Ẑ_τ[j], commutative |
| Imaginary | i²=j²=k²=-1 | j²=+1 (split-complex) |
| Zero divisors | None (division algebra) | e₊·e₋ = 0 (bipolar) |
| Coordinates | ℝ⁴ (two-sided axes) | ℕ⁴ (one-sided rays) |
| Bipolarity | Not native | Native (e₊, e₋ sectors) |
| Status in τ | Not earned (imported) | Earned (from K0-K6) |

Four-ray rigidity (II.P03):
1. Completeness: every Obj(τ) gets a unique ABCD quadruple (I.T04)
2. Bipolar compatibility: (B,C) carry sector assignment
3. Coherence: fibered product interlocks four rays
4. No imports: earned from kernel axioms
-/

namespace Tau.BookII.Interior

open Tau.Coordinates Tau.Denotation Tau.Polarity

-- ============================================================
-- FOUR-RAY RIGIDITY [II.P03]
-- ============================================================

/-- [II.P03, clause 1] Completeness:
    The ABCD chart assigns a unique quadruple to every X ≥ 2.
    Verified by injectivity (no collisions) for X = 2..bound. -/
def four_ray_complete (bound : TauIdx) : Bool :=
  faithful_check bound

/-- [II.P03, clause 2] Bipolar compatibility:
    Fiber coordinates (B,C) carry sector assignment compatible with
    the idempotent decomposition of H_τ.

    For all X in range: interior_bipolar produces orthogonal projections. -/
def four_ray_bipolar_check (bound : TauIdx) : Bool :=
  go 2 (bound + 1)
where
  go (x fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else
      let p := from_tau_idx x
      let sp := interior_bipolar p
      -- Bipolar completeness: e₊·sp + e₋·sp = sp (orthogonal projections)
      let fp := SectorPair.mul e_plus_sector sp
      let fm := SectorPair.mul e_minus_sector sp
      SectorPair.add fp fm == sp &&
      go (x + 1) (fuel - 1)
  termination_by fuel

/-- [II.P03, clause 3] Coherence:
    The fibered product structure interlocks all four rays.
    Verified: base validity (C1, C3) holds for all ABCD decompositions. -/
def four_ray_coherent (bound : TauIdx) : Bool :=
  go 2 (bound + 1)
where
  go (x fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else
      let p := from_tau_idx x
      let t3 := to_tau3 p
      t3.base.valid && go (x + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- ABCD VS QUATERNIONS [II.R04]
-- ============================================================

/-- [II.R04] Key structural difference: ABCD uses one-sided rays (ℕ),
    not two-sided axes (ℝ). Rays have a starting prime but no origin.

    The four starting primes are distinct:
    α₁ = 2, π₁ = 3, γ₁ = 5, η₁ = 7. -/
def four_starting_primes : List TauIdx := [2, 3, 5, 7]

/-- The four starting primes are all distinct. -/
def starting_primes_distinct : Bool :=
  let ps := four_starting_primes
  ps.length == 4 && ps.eraseDups.length == 4

/-- The four starting primes are all prime. -/
def starting_primes_all_prime : Bool :=
  four_starting_primes.all is_prime_bool

/-- [II.R04] Split-complex has zero divisors; quaternions don't.
    This is the key algebraic difference: H_τ admits bipolar sectors
    via e₊ · e₋ = 0, while ℍ is a division algebra. -/
theorem abcd_has_zero_divisors :
    ∃ z w : SplitComplex,
    z ≠ ⟨0, 0⟩ ∧ w ≠ ⟨0, 0⟩ ∧
    SplitComplex.mul z w = ⟨0, 0⟩ := by
  refine ⟨⟨1, 1⟩, ⟨1, -1⟩, ?_, ?_, ?_⟩
  · intro h; have := congrArg SplitComplex.re h; simp at this
  · intro h; have := congrArg SplitComplex.re h; simp at this
  · unfold SplitComplex.mul; ext <;> simp

-- ============================================================
-- PARA-COMPLEX STRUCTURE [II.R04]
-- ============================================================

/-- The ABCD chart induces a para-complex structure (j² = +id),
    not a complex structure (J² = -id).

    Para-complex: decomposes into two REAL eigenspaces (e₊ ⊕ e₋).
    Complex: rotates between two components (no real eigenspaces).

    Verification: j² = +1 in split-complex arithmetic. -/
theorem para_complex_structure :
    SplitComplex.mul ⟨0, 1⟩ ⟨0, 1⟩ = ⟨1, 0⟩ := by
  unfold SplitComplex.mul; ext <;> simp

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Rigidity checks
#eval four_ray_complete 100       -- true
#eval four_ray_bipolar_check 100  -- true
#eval four_ray_coherent 100       -- true

-- Starting primes
#eval starting_primes_distinct     -- true
#eval starting_primes_all_prime    -- true

-- Formal verification
theorem rigidity_2_to_30 : four_ray_complete 30 = true := by native_decide
theorem bipolar_2_to_30 : four_ray_bipolar_check 30 = true := by native_decide
theorem coherent_2_to_30 : four_ray_coherent 30 = true := by native_decide
theorem primes_distinct : starting_primes_distinct = true := by native_decide
theorem primes_all_prime : starting_primes_all_prime = true := by native_decide

end Tau.BookII.Interior
