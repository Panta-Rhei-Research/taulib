import TauLib.BookI.Denotation.RankTransfer
import TauLib.BookI.Orbit.Ladder

/-!
# TauLib.BookI.Denotation.Arithmetic

Earned arithmetic: addition, multiplication, exponentiation, and tetration
derived from the iterator ρ.

## Registry Cross-References

- [I.D10] Index Addition — `idx_add`, `idx_add_eq_nat_add`
- [I.D11] Index Multiplication — `idx_mul`, `idx_mul_eq_nat_mul`
- [I.D12] Index Exponentiation — `idx_exp`, `idx_exp_eq_nat_pow`
- [I.D13] Index Tetration — `idx_tetration`
- [I.P05] Arithmetic Injectivity — `idx_add_injective`, `idx_mul_injective`, `idx_exp_injective`
- [I.P06] Arithmetic Laws — `idx_add_comm`, `idx_add_assoc`, `idx_mul_comm`, etc.

## Ground Truth Sources
- chunk_0057_M000678: Multiplication as stride iteration of ρ
- chunk_0060_M000698: UR-ITER requirement, arithmetic from ρ without algebraic substrate
- chunk_0052_M000622: Binary operators derived, not primitive

## Mathematical Content

The key insight: arithmetic is NOT imported but *earned* from ρ iteration.

- Addition: n + m = depth of ρᵐ(⟨α, n⟩)
- Multiplication: n × m = iterated addition
- Exponentiation: n ^ m = iterated multiplication
- Tetration: ⁿm = iterated exponentiation

The "bridge lemmas" prove each coincides with the Nat operation.
-/

namespace Tau.Denotation

open Tau.Kernel Tau.Orbit Generator

-- ============================================================
-- INDEX ADDITION [I.D10]
-- ============================================================

/-- [I.D10] Index addition: the depth after m applications of ρ to ⟨α, n⟩.
    This *earns* addition from the iterator. -/
def idx_add (n m : TauIdx) : TauIdx :=
  (iter_rho m (toAlphaOrbit n)).depth

/-- Bridge lemma: idx_add coincides with Nat.add. -/
theorem idx_add_eq_nat_add (n m : TauIdx) : idx_add n m = n + m := by
  simp [idx_add, toAlphaOrbit, iter_rho_depth alpha (by decide : alpha ≠ omega) n m]

-- ============================================================
-- INDEX MULTIPLICATION [I.D11]
-- ============================================================

/-- [I.D11] Index multiplication: iterated addition. -/
def idx_mul (n m : TauIdx) : TauIdx :=
  match m with
  | 0 => 0
  | m + 1 => idx_add (idx_mul n m) n

/-- Bridge lemma: idx_mul coincides with Nat.mul. -/
theorem idx_mul_eq_nat_mul (n m : TauIdx) : idx_mul n m = n * m := by
  induction m with
  | zero => simp [idx_mul]
  | succ m ih =>
    simp only [idx_mul, idx_add_eq_nat_add, ih]
    exact (Nat.mul_succ n m).symm

-- ============================================================
-- INDEX EXPONENTIATION [I.D12]
-- ============================================================

/-- [I.D12] Index exponentiation: iterated multiplication. -/
def idx_exp (n m : TauIdx) : TauIdx :=
  match m with
  | 0 => 1
  | m + 1 => idx_mul (idx_exp n m) n

/-- Bridge lemma: idx_exp coincides with Nat.pow. -/
theorem idx_exp_eq_nat_pow (n m : TauIdx) : idx_exp n m = n ^ m := by
  induction m with
  | zero => simp [idx_exp]
  | succ m ih =>
    simp only [idx_exp, idx_mul_eq_nat_mul, ih]
    exact (Nat.pow_succ n m).symm

-- ============================================================
-- INDEX TETRATION [I.D13]
-- ============================================================

/-- [I.D13] Index tetration: iterated exponentiation (right-associative tower).
    ⁿm means n^(n^(n^...)) with m copies of n. -/
def idx_tetration (n m : TauIdx) : TauIdx :=
  match m with
  | 0 => 1
  | m + 1 => idx_exp n (idx_tetration n m)

/-- Bridge lemma: idx_tetration matches the Nat tetration from Ladder. -/
theorem idx_tetration_eq (n m : TauIdx) :
    idx_tetration n m = tetration n m := by
  induction m with
  | zero => simp [idx_tetration, tetration]
  | succ m ih =>
    simp only [idx_tetration, tetration, idx_exp_eq_nat_pow, ih]

-- ============================================================
-- LADDER-OP BRIDGE
-- ============================================================

/-- ladderOp at add_level coincides with earned idx_add. -/
theorem ladderOp_add_eq_idx (n m : TauIdx) :
    ladderOp .add_level n m = idx_add n m := by
  simp [ladderOp, idx_add_eq_nat_add]

/-- ladderOp at mul_level coincides with earned idx_mul. -/
theorem ladderOp_mul_eq_idx (n m : TauIdx) :
    ladderOp .mul_level n m = idx_mul n m := by
  simp [ladderOp, idx_mul_eq_nat_mul]

/-- ladderOp at exp_level coincides with earned idx_exp. -/
theorem ladderOp_exp_eq_idx (n m : TauIdx) :
    ladderOp .exp_level n m = idx_exp n m := by
  simp [ladderOp, idx_exp_eq_nat_pow]

/-- ladderOp at tet_level coincides with earned idx_tetration. -/
theorem ladderOp_tet_eq_idx (n m : TauIdx) :
    ladderOp .tet_level n m = idx_tetration n m := by
  simp [ladderOp, idx_tetration_eq]

/-- The Fold Chain Principle: each arithmetic level is obtained by
    structural recursion on the previous level.
    Ground truth: chunk_0060 (UR-ITER), chunk_0057 (counting = time). -/
theorem fold_chain :
    (∀ n m, idx_add n m = (iter_rho m (toAlphaOrbit n)).depth) ∧
    (∀ n m, idx_mul n (m + 1) = idx_add (idx_mul n m) n) ∧
    (∀ n m, idx_exp n (m + 1) = idx_mul (idx_exp n m) n) ∧
    (∀ n m, idx_tetration n (m + 1) = idx_exp n (idx_tetration n m)) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

-- ============================================================
-- ARITHMETIC LAWS [I.P06]
-- ============================================================

/-- Addition is commutative. -/
theorem idx_add_comm (n m : TauIdx) : idx_add n m = idx_add m n := by
  rw [idx_add_eq_nat_add, idx_add_eq_nat_add]
  exact Nat.add_comm n m

/-- Addition is associative. -/
theorem idx_add_assoc (a b c : TauIdx) :
    idx_add (idx_add a b) c = idx_add a (idx_add b c) := by
  rw [idx_add_eq_nat_add, idx_add_eq_nat_add, idx_add_eq_nat_add, idx_add_eq_nat_add]
  exact Nat.add_assoc a b c

/-- Addition has identity 0. -/
theorem idx_add_zero (n : TauIdx) : idx_add n 0 = n := by
  simp [idx_add_eq_nat_add]

/-- Zero is a left identity for addition. -/
theorem idx_zero_add (n : TauIdx) : idx_add 0 n = n := by
  simp [idx_add_eq_nat_add]

/-- Multiplication is commutative. -/
theorem idx_mul_comm (n m : TauIdx) : idx_mul n m = idx_mul m n := by
  simp only [idx_mul_eq_nat_mul]; exact Nat.mul_comm n m

/-- Multiplication is associative. -/
theorem idx_mul_assoc (a b c : TauIdx) :
    idx_mul (idx_mul a b) c = idx_mul a (idx_mul b c) := by
  simp only [idx_mul_eq_nat_mul]; exact Nat.mul_assoc a b c

/-- Multiplication has identity 1. -/
theorem idx_mul_one (n : TauIdx) : idx_mul n 1 = n := by
  simp [idx_mul_eq_nat_mul]

/-- One is a left identity for multiplication. -/
theorem idx_one_mul (n : TauIdx) : idx_mul 1 n = n := by
  simp [idx_mul_eq_nat_mul]

/-- Multiplication has absorbing element 0. -/
theorem idx_mul_zero (n : TauIdx) : idx_mul n 0 = 0 := by
  simp [idx_mul_eq_nat_mul]

/-- Distributivity: a × (b + c) = a × b + a × c. -/
theorem idx_distrib (a b c : TauIdx) :
    idx_mul a (idx_add b c) = idx_add (idx_mul a b) (idx_mul a c) := by
  simp only [idx_mul_eq_nat_mul, idx_add_eq_nat_add]
  exact Nat.left_distrib a b c

-- ============================================================
-- ARITHMETIC INJECTIVITY [I.P05]
-- ============================================================

/-- [I.P05] Addition is injective in the second argument. -/
theorem idx_add_injective (n : TauIdx) : Function.Injective (idx_add n) := by
  intro a b h
  have h3 : n + a = n + b := by
    rw [← idx_add_eq_nat_add, ← idx_add_eq_nat_add]; exact h
  exact Tau.Orbit.add_injective n h3

/-- Multiplication by n > 0 is injective in the second argument. -/
theorem idx_mul_injective (n : TauIdx) (hn : n > 0) :
    Function.Injective (idx_mul n) := by
  intro a b h
  simp only [idx_mul_eq_nat_mul] at h
  exact Tau.Orbit.mul_injective n hn h

/-- Exponentiation with base ≥ 2 is injective in the exponent. -/
theorem idx_exp_injective (n : TauIdx) (hn : n ≥ 2) :
    Function.Injective (idx_exp n) := by
  intro a b h
  simp only [idx_exp_eq_nat_pow] at h
  exact Tau.Orbit.exp_injective n hn h

/-- Exponentiation is not commutative (counterexample: 2^3 ≠ 3^2). -/
theorem idx_exp_non_comm : ¬(∀ n m, idx_exp n m = idx_exp m n) := by
  intro h
  have h23 := h 2 3
  simp only [idx_exp_eq_nat_pow] at h23
  -- h23 : 2 ^ 3 = 3 ^ 2, i.e. 8 = 9
  exact absurd h23 (by decide)

end Tau.Denotation
