import TauLib.BookI.Logic.Truth4
import TauLib.BookI.Polarity.BipolarAlgebra

/-!
# TauLib.BookI.Logic.Explosion

The explosion barrier: paraconsistent behavior of Truth4 material implication.

## Registry Cross-References
- [I.T13] Explosion Barrier — `explosion_barrier`, `explosion_exists_counterexample`

## Ground Truth Sources
- chunk_0228_M002194: Split-complex algebra, bipolar balance
- chunk_0310_M002679: Bipolar partition and sector orthogonality

## Mathematical Content

In classical logic, from a contradiction P and not-P one can derive any
proposition Q (ex falso quodlibet / principle of explosion). In Truth4,
this fails for the overdetermined value B.

The explosion barrier theorem: impl B F = N, not T. That is, from an
overdetermined truth value, one cannot derive arbitrary falsehood via
material implication.

Key insight: Truth4 IS a Boolean algebra (it is isomorphic to Bool x Bool),
so the "non-classical" behavior is not about the lattice structure. Rather,
the explosion barrier concerns MATERIAL IMPLICATION (impl a b := join(neg a, b)):
evaluating impl at B does not yield T for all targets.

The spectral interpretation: the explosion barrier mirrors the orthogonality
of the sector idempotents e+ * e- = 0. The B value (= e+) and its negation
N (= e-) live in orthogonal sectors; their interaction annihilates rather
than propagating.
-/

namespace Tau.Logic

open Truth4

-- ============================================================
-- EXPLOSION BARRIER [I.T13]
-- ============================================================

/-- [I.T13] The explosion barrier: B does not imply everything.
    Specifically, impl B F = N, not T.
    This is the central paraconsistent feature of Truth4.

    Calculation: impl B F = join (neg B) F = join N F = N.
    Since N <> T, the implication B -> F is not "true". -/
theorem explosion_barrier : Truth4.impl B F ≠ T := by
  simp [Truth4.impl, Truth4.neg, Truth4.join]

/-- Existential form: there exists a target Q such that impl B Q <> T. -/
theorem explosion_exists_counterexample :
    ∃ Q : Truth4, Truth4.impl B Q ≠ T :=
  ⟨F, explosion_barrier⟩

/-- Full tabulation: impl B is not constantly T.
    impl B T = T, impl B F = N, impl B B = T, impl B N = T. -/
theorem impl_B_not_constant :
    ¬(∀ Q : Truth4, Truth4.impl B Q = T) := by
  intro h
  have := h F
  simp [Truth4.impl, Truth4.neg, Truth4.join] at this

-- ============================================================
-- CLASSICAL EXPLOSION PRESERVED
-- ============================================================

/-- Classical explosion is preserved: from F (genuinely false), everything follows.
    impl F Q = join (neg F) Q = join T Q = T. -/
theorem classical_explosion (Q : Truth4) : Truth4.impl F Q = T := by
  cases Q <;> rfl

/-- The classical path: meet a (neg a) = F, and impl F Q = T.
    So the two-step chain "from a and neg a deduce F, then from F deduce Q"
    still works. The explosion barrier blocks the ONE-STEP path at B. -/
theorem classical_chain (a Q : Truth4) :
    Truth4.impl (Truth4.meet a (Truth4.neg a)) Q = T := by
  cases a <;> cases Q <;> rfl

-- ============================================================
-- B-PROPAGATION PROPERTIES
-- ============================================================

/-- B is idempotent under meet. -/
theorem B_meet_B : Truth4.meet B B = B := rfl

/-- B is idempotent under join. -/
theorem B_join_B : Truth4.join B B = B := rfl

/-- neg B = N. -/
theorem neg_B_eq_N : Truth4.neg B = N := rfl

/-- neg N = B. -/
theorem neg_N_eq_B : Truth4.neg N = B := rfl

/-- B implies itself: impl B B = T. -/
theorem B_impl_B : Truth4.impl B B = T := by
  simp [Truth4.impl, Truth4.neg, Truth4.join]

/-- B infects conjunction with T: meet B T = B. -/
theorem B_meet_T : Truth4.meet B T = B := rfl

/-- B absorbed by disjunction with T: join B T = T. -/
theorem B_join_T : Truth4.join B T = T := rfl

/-- Symmetrically, N propagation: impl N F = B, not T. -/
theorem N_explosion_barrier : Truth4.impl N F ≠ T := by
  simp [Truth4.impl, Truth4.neg, Truth4.join]

-- ============================================================
-- IMPL TRUTH TABLE
-- ============================================================

/-- impl T a = a (modus ponens compatible). -/
theorem impl_T (a : Truth4) : Truth4.impl T a = a := by
  cases a <;> rfl

/-- impl a T = T (T is always implied). -/
theorem impl_T_right (a : Truth4) : Truth4.impl a T = T := by
  cases a <;> rfl

/-- impl a a = join(neg a, a) = T for all a (reflexivity of implication). -/
theorem impl_refl (a : Truth4) : Truth4.impl a a = T := by
  cases a <;> rfl

/-- The full impl table as a computable function, verified against the definition. -/
theorem impl_table_T_row : Truth4.impl T T = T ∧ Truth4.impl T F = F ∧
    Truth4.impl T B = B ∧ Truth4.impl T N = N := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

theorem impl_table_F_row : Truth4.impl F T = T ∧ Truth4.impl F F = T ∧
    Truth4.impl F B = T ∧ Truth4.impl F N = T := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

theorem impl_table_B_row : Truth4.impl B T = T ∧ Truth4.impl B F = N ∧
    Truth4.impl B B = T ∧ Truth4.impl B N = N := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

theorem impl_table_N_row : Truth4.impl N T = T ∧ Truth4.impl N F = B ∧
    Truth4.impl N B = B ∧ Truth4.impl N N = T := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

-- ============================================================
-- SPECTRAL BRIDGE: EXPLOSION <-> ORTHOGONALITY
-- ============================================================

/-- The spectral bridge: the explosion barrier corresponds to
    sector orthogonality e+ * e- = 0.

    Truth4.B maps to e_plus_sector = (1,0).
    Truth4.N maps to e_minus_sector = (0,1).
    Their product e+ * e- = (0,0), the zero sector pair.

    The explosion barrier (impl B F = N, not T) mirrors the fact that
    B and its negation N live in orthogonal spectral sectors that cannot
    "communicate" to produce the top element T = (1,1). -/
theorem spectral_bridge_orthogonality :
    Tau.Polarity.SectorPair.mul
      (Truth4.toSectorPair B) (Truth4.toSectorPair N) =
    ⟨0, 0⟩ := by
  simp [Truth4.toSectorPair, Tau.Polarity.e_plus_sector,
        Tau.Polarity.e_minus_sector, Tau.Polarity.SectorPair.mul]

/-- The sector product of B with itself is B (idempotent), matching e+^2 = e+. -/
theorem spectral_bridge_B_idem :
    Tau.Polarity.SectorPair.mul
      (Truth4.toSectorPair B) (Truth4.toSectorPair B) =
    Truth4.toSectorPair B := by
  simp [Truth4.toSectorPair, Tau.Polarity.e_plus_sector,
        Tau.Polarity.SectorPair.mul]

/-- The sector product of N with itself is N (idempotent), matching e-^2 = e-. -/
theorem spectral_bridge_N_idem :
    Tau.Polarity.SectorPair.mul
      (Truth4.toSectorPair N) (Truth4.toSectorPair N) =
    Truth4.toSectorPair N := by
  simp [Truth4.toSectorPair, Tau.Polarity.e_minus_sector,
        Tau.Polarity.SectorPair.mul]

/-- Sector partition of unity: e+ + e- = (1,1) = T. -/
theorem spectral_bridge_partition :
    Tau.Polarity.SectorPair.add
      (Truth4.toSectorPair B) (Truth4.toSectorPair N) =
    Truth4.toSectorPair T := by
  simp [Truth4.toSectorPair, Tau.Polarity.e_plus_sector,
        Tau.Polarity.e_minus_sector, Tau.Polarity.SectorPair.add]

-- ============================================================
-- CONTRAPOSITION
-- ============================================================

/-- Contraposition holds: impl a b = impl (neg b) (neg a). -/
theorem contraposition (a b : Truth4) :
    Truth4.impl a b = Truth4.impl (Truth4.neg b) (Truth4.neg a) := by
  cases a <;> cases b <;> rfl

/-- Modus ponens: if impl a b = T and a = T, then b = T. -/
theorem modus_ponens (a b : Truth4) (h_impl : Truth4.impl a b = T)
    (h_a : a = T) : b = T := by
  subst h_a
  simp [Truth4.impl, Truth4.neg, Truth4.join] at h_impl
  exact h_impl

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Explosion barrier
#eval Truth4.impl B F            -- N (not T!)
#eval Truth4.impl B F == T       -- false: explosion blocked
#eval Truth4.impl F T            -- T: classical explosion works
#eval Truth4.impl F B            -- T: classical explosion works

-- B-propagation
#eval Truth4.meet B B            -- B
#eval Truth4.join B B            -- B
#eval Truth4.impl B B            -- T
#eval Truth4.meet B T            -- B

-- N-propagation
#eval Truth4.impl N F            -- B (not T: N also blocks explosion)
#eval Truth4.impl N N            -- T

-- Classical chain: meet a (neg a) always gives F, and impl F Q = T
#eval Truth4.meet B (Truth4.neg B)   -- F
#eval Truth4.meet N (Truth4.neg N)   -- F
#eval Truth4.impl (Truth4.meet B (Truth4.neg B)) T   -- T

-- Spectral bridge: sector products
#eval Tau.Polarity.SectorPair.mul
        (Truth4.toSectorPair B) (Truth4.toSectorPair N)   -- (0, 0)
#eval Tau.Polarity.SectorPair.mul
        (Truth4.toSectorPair B) (Truth4.toSectorPair B)   -- (1, 0) = e+
#eval Tau.Polarity.SectorPair.add
        (Truth4.toSectorPair B) (Truth4.toSectorPair N)   -- (1, 1) = T

-- Contraposition
#eval Truth4.impl T F                          -- F
#eval Truth4.impl (Truth4.neg F) (Truth4.neg T)  -- F (matches)
#eval Truth4.impl B N                          -- T
#eval Truth4.impl (Truth4.neg N) (Truth4.neg B)  -- T (matches)

-- Impl reflexivity
#eval Truth4.impl T T   -- T
#eval Truth4.impl F F   -- T
#eval Truth4.impl B B   -- T
#eval Truth4.impl N N   -- T

end Tau.Logic
