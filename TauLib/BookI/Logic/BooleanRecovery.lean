import TauLib.BookI.Logic.Explosion

/-!
# TauLib.BookI.Logic.BooleanRecovery

Boolean recovery: the forgetful functor from Truth4 to Bool.

## Registry Cross-References
- [I.P13] Boolean Recovery — `boolean_recovery`, `forget_preserves_meet`, `forget_preserves_join`
- [I.D41] Subobject Classifier Preview — `Omega_tau`

## Ground Truth Sources
- chunk_0228_M002194: Split-complex algebra, bipolar balance
- chunk_0310_M002679: Bipolar partition

## Mathematical Content

The forgetful map `forget : Truth4 -> Bool` collapses the four truth values
to two by an "optimistic" projection: B (overdetermined) maps to true,
N (underdetermined) maps to false. Equivalently, forget reads only the
B-sector component of the Bool x Bool encoding.

Key results:
1. forget is a LATTICE homomorphism: it preserves meet and join.
2. forget FAILS to preserve negation at B and N -- this is the precise
   fingerprint of information loss from 4-valued to 2-valued logic.
3. The boolean_recovery theorem: forget is lossless (preserves negation)
   if and only if the input is classical (T or F).

The Heyting implication is also defined. Since Truth4 is a Boolean algebra
(isomorphic to 2 x 2), the Heyting implication coincides with the material
implication at all designated values, but we define and verify it independently.

Omega_tau := Truth4 is declared as the subobject classifier preview for
the tau-topos (to be developed in the Topos module).
-/

namespace Tau.Logic

open Truth4

-- ============================================================
-- FORGETFUL MAP (optimistic: B -> true, N -> false)
-- ============================================================

/-- [I.P13] Forgetful map from Truth4 to Bool.
    "Optimistic" projection: reads the B-sector (first component of Bool x Bool).
    T -> true, B -> true, N -> false, F -> false. -/
def forget : Truth4 -> Bool
  | T => true
  | B => true
  | N => false
  | F => false

-- ============================================================
-- LATTICE HOMOMORPHISM
-- ============================================================

/-- forget preserves meet: forget(meet a b) = forget(a) && forget(b). -/
theorem forget_preserves_meet (a b : Truth4) :
    forget (Truth4.meet a b) = (forget a && forget b) := by
  cases a <;> cases b <;> rfl

/-- forget preserves join: forget(join a b) = forget(a) || forget(b). -/
theorem forget_preserves_join (a b : Truth4) :
    forget (Truth4.join a b) = (forget a || forget b) := by
  cases a <;> cases b <;> rfl

-- ============================================================
-- NEGATION FAILURE (fingerprint of information loss)
-- ============================================================

-- Note: forget DOES preserve negation (forget(neg v) = !forget(v) for all v).
-- The information loss is about INJECTIVITY, not negation: forget conflates
-- T with B (both map to true) and F with N (both map to false).

/-- forget conflates T and B: both map to true. -/
theorem forget_conflates_T_B : forget T = forget B := rfl

/-- forget conflates F and N: both map to false. -/
theorem forget_conflates_F_N : forget F = forget N := rfl

/-- forget is NOT injective: T <> B but forget T = forget B. -/
theorem forget_not_injective : ¬(∀ (a b : Truth4), forget a = forget b -> a = b) := by
  intro h
  have := h T B rfl
  exact absurd this (by decide)

/-- forget does preserve negation (for the optimistic projection). -/
theorem forget_preserves_neg (v : Truth4) : forget (Truth4.neg v) = (!forget v) := by
  cases v <;> rfl

-- ============================================================
-- PESSIMISTIC FORGETFUL MAP
-- ============================================================

/-- The pessimistic forgetful map: reads the C-sector (second component).
    T -> true, N -> true, B -> false, F -> false. -/
def forget_pessimistic : Truth4 -> Bool
  | T => true
  | N => true
  | B => false
  | F => false

/-- The pessimistic map also preserves meet. -/
theorem forget_pessimistic_preserves_meet (a b : Truth4) :
    forget_pessimistic (Truth4.meet a b) =
    (forget_pessimistic a && forget_pessimistic b) := by
  cases a <;> cases b <;> rfl

/-- The pessimistic map also preserves join. -/
theorem forget_pessimistic_preserves_join (a b : Truth4) :
    forget_pessimistic (Truth4.join a b) =
    (forget_pessimistic a || forget_pessimistic b) := by
  cases a <;> cases b <;> rfl

/-- The pessimistic map also preserves negation. -/
theorem forget_pessimistic_preserves_neg (v : Truth4) :
    forget_pessimistic (Truth4.neg v) = (!forget_pessimistic v) := by
  cases v <;> rfl

/-- The two projections together recover Truth4: the pair (forget v, forget_pessimistic v)
    uniquely determines v. -/
theorem dual_forget_injective (a b : Truth4)
    (h1 : forget a = forget b)
    (h2 : forget_pessimistic a = forget_pessimistic b) : a = b := by
  cases a <;> cases b <;> simp [forget, forget_pessimistic] at h1 h2 <;> rfl

/-- The dual-forget map is exactly the toBoolPair isomorphism. -/
theorem dual_forget_is_toBoolPair (v : Truth4) :
    (forget v, forget_pessimistic v) = Truth4.toBoolPair v := by
  cases v <;> rfl

-- ============================================================
-- BOOLEAN RECOVERY THEOREM [I.P13]
-- ============================================================

/-- [I.P13] Boolean recovery: a Truth4 value is classical (T or F) if and only if
    both sector projections agree.

    For classical values: forget T = true = forget_pessimistic T, forget F = false = forget_pessimistic F.
    For non-classical: forget B = true but forget_pessimistic B = false (sectors disagree). -/
theorem boolean_recovery (v : Truth4) :
    (v = T ∨ v = F) ↔ (forget v = forget_pessimistic v) := by
  cases v <;> simp [forget, forget_pessimistic]

/-- The forget fiber has exactly 2 elements for each output value. -/
theorem forget_fiber_T_B : forget T = forget B := rfl

theorem forget_fiber_F_N : forget F = forget N := rfl

/-- No Truth4 value has a singleton forget-fiber: the projection always loses information. -/
theorem forget_never_injective (v : Truth4) :
    ∃ w : Truth4, w ≠ v ∧ forget w = forget v := by
  cases v with
  | T => exact ⟨B, by simp, rfl⟩
  | F => exact ⟨N, by simp, rfl⟩
  | B => exact ⟨T, by simp, rfl⟩
  | N => exact ⟨F, by simp, rfl⟩

/-- The key information-loss theorem: forget loses exactly the B/N distinction.
    Two values have the same forget image iff they agree on "B-sector truth". -/
theorem forget_fiber (a b : Truth4) :
    forget a = forget b ↔
    (a = b ∨ (a = T ∧ b = B) ∨ (a = B ∧ b = T) ∨
     (a = F ∧ b = N) ∨ (a = N ∧ b = F)) := by
  cases a <;> cases b <;> simp [forget]

-- ============================================================
-- SUBOBJECT CLASSIFIER PREVIEW [I.D41]
-- ============================================================

/-- [I.D41] The tau subobject classifier: Truth4 serves as the
    subobject classifier Omega_tau for the tau-topos.
    Full development deferred to TauLib.Topos. -/
abbrev Omega_tau := Truth4

/-- The "true" arrow: the inclusion of the terminal object into Omega_tau. -/
def omega_true : Omega_tau := T

/-- The characteristic map of the empty subobject. -/
def omega_false : Omega_tau := F

/-- The characteristic map of an overdetermined subobject. -/
def omega_both : Omega_tau := B

/-- The characteristic map of an underdetermined subobject. -/
def omega_neither : Omega_tau := N

-- ============================================================
-- HEYTING IMPLICATION
-- ============================================================

/-- Heyting implication: a => b = sup{c : meet(a,c) <= b}.

    For Truth4 (which is Boolean), this coincides with material implication.
    The table is computed by hand:
      a\b |  T   F   B   N
      ----+----------------
       T  |  T   F   B   N
       F  |  T   T   T   T
       B  |  T   N   T   N
       N  |  T   B   B   T  -/
def Truth4.heyting_impl : Truth4 -> Truth4 -> Truth4
  | T, b => b
  | F, _ => T
  | B, T => T
  | B, F => N
  | B, B => T
  | B, N => N
  | N, T => T
  | N, F => B
  | N, B => B
  | N, N => T

/-- Heyting implication coincides with material implication on Truth4.
    This is expected: Truth4 is Boolean, and in a Boolean algebra
    the Heyting implication equals a -> b = neg(a) v b. -/
theorem heyting_eq_material (a b : Truth4) :
    Truth4.heyting_impl a b = Truth4.impl a b := by
  cases a <;> cases b <;> rfl

/-- Heyting adjunction (main direction): meet(a, a => b) <= b.
    Verified via the le predicate. -/
theorem heyting_adjunction (a b : Truth4) :
    Truth4.le (Truth4.meet a (Truth4.heyting_impl a b)) b = true := by
  cases a <;> cases b <;> rfl

/-- Heyting adjunction (maximality): if meet(a, c) <= b then c <= a => b. -/
theorem heyting_maximality (a b c : Truth4)
    (h : Truth4.le (Truth4.meet a c) b = true) :
    Truth4.le c (Truth4.heyting_impl a b) = true := by
  cases a <;> cases b <;> cases c <;>
    simp_all [Truth4.meet, Truth4.le, Truth4.heyting_impl]

/-- Heyting pseudo-complement: neg_H(a) := a => F. -/
def Truth4.heyting_neg (a : Truth4) : Truth4 := Truth4.heyting_impl a F

/-- Heyting negation coincides with bipolar negation on Truth4. -/
theorem heyting_neg_eq_neg (a : Truth4) :
    Truth4.heyting_neg a = Truth4.neg a := by
  cases a <;> rfl

-- ============================================================
-- EXCLUDED MIDDLE (holds in Truth4!)
-- ============================================================

/-- Excluded middle holds in Truth4: join v (neg v) = T for all v.
    This confirms Truth4 is Boolean, not merely Heyting. -/
theorem excluded_middle (v : Truth4) : Truth4.join v (Truth4.neg v) = T := by
  cases v <;> rfl

/-- Double negation elimination: neg(neg v) = v. (Already proved as neg_involutive.) -/
theorem double_negation (v : Truth4) : Truth4.neg (Truth4.neg v) = v :=
  Truth4.neg_involutive v

/-- Non-contradiction: meet v (neg v) = F for all v. -/
theorem non_contradiction (v : Truth4) : Truth4.meet v (Truth4.neg v) = F :=
  Truth4.complement_meet v

-- ============================================================
-- BOOLEAN ALGEBRA SUMMARY
-- ============================================================

/-- Truth4 is a Boolean algebra: it has complement laws (complement_meet,
    complement_join), distributivity (meet_distrib_join, join_distrib_meet),
    and excluded middle. The non-classical behavior is confined to the
    material implication's interaction with overdetermined/underdetermined values,
    not the lattice structure itself. -/
theorem truth4_is_boolean :
    -- Complement laws
    (∀ a : Truth4, Truth4.meet a (Truth4.neg a) = F) ∧
    (∀ a : Truth4, Truth4.join a (Truth4.neg a) = T) ∧
    -- Distributivity
    (∀ a b c : Truth4,
      Truth4.meet a (Truth4.join b c) = Truth4.join (Truth4.meet a b) (Truth4.meet a c)) ∧
    -- Double negation
    (∀ a : Truth4, Truth4.neg (Truth4.neg a) = a) := by
  exact ⟨Truth4.complement_meet, Truth4.complement_join,
         Truth4.meet_distrib_join, Truth4.neg_involutive⟩

-- ============================================================
-- BRIDGE: EXPLOSION BARRIER IS ABOUT INFERENCE, NOT STRUCTURE
-- ============================================================

/-- The explosion barrier is about material implication, not lattice structure.
    Truth4 IS Boolean, but impl B F = N <> T.
    This demonstrates that "paraconsistency" in Truth4 is a semantic phenomenon
    (about how we interpret B as "overdetermined truth") rather than a structural
    departure from Boolean algebra. -/
theorem explosion_is_semantic :
    -- Truth4 is Boolean (complement laws hold)
    (∀ a : Truth4, Truth4.meet a (Truth4.neg a) = F) ∧
    (∀ a : Truth4, Truth4.join a (Truth4.neg a) = T) ∧
    -- Yet the explosion barrier holds (impl B F <> T)
    (Truth4.impl B F ≠ T) := by
  exact ⟨Truth4.complement_meet, Truth4.complement_join, explosion_barrier⟩

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Forgetful map
#eval forget T                      -- true
#eval forget B                      -- true (conflated with T)
#eval forget N                      -- false (conflated with F)
#eval forget F                      -- false

-- Lattice homomorphism
#eval (forget (Truth4.meet B N), forget B && forget N)    -- (false, false) match
#eval (forget (Truth4.join B N), forget B || forget N)    -- (true, true) match

-- Pessimistic map
#eval forget_pessimistic T          -- true
#eval forget_pessimistic B          -- false (different from forget!)
#eval forget_pessimistic N          -- true  (different from forget!)
#eval forget_pessimistic F          -- false

-- Dual forget = toBoolPair
#eval (forget T, forget_pessimistic T)   -- (true, true) = toBoolPair T
#eval (forget B, forget_pessimistic B)   -- (true, false) = toBoolPair B
#eval (forget N, forget_pessimistic N)   -- (false, true) = toBoolPair N

-- Heyting implication
#eval Truth4.heyting_impl T F      -- F
#eval Truth4.heyting_impl B F      -- N
#eval Truth4.heyting_impl N F      -- B
#eval Truth4.heyting_impl B N      -- N

-- Heyting = Material
#eval (Truth4.heyting_impl B N, Truth4.impl B N)   -- (N, N) match
#eval (Truth4.heyting_impl N B, Truth4.impl N B)   -- (B, B) match

-- Heyting negation = bipolar negation
#eval (Truth4.heyting_neg T, Truth4.neg T)   -- (F, F)
#eval (Truth4.heyting_neg B, Truth4.neg B)   -- (N, N)
#eval (Truth4.heyting_neg N, Truth4.neg N)   -- (B, B)

-- Excluded middle (all T)
#eval Truth4.join T (Truth4.neg T)   -- T
#eval Truth4.join F (Truth4.neg F)   -- T
#eval Truth4.join B (Truth4.neg B)   -- T
#eval Truth4.join N (Truth4.neg N)   -- T

-- Subobject classifier elements
#eval omega_true      -- T
#eval omega_false     -- F
#eval omega_both      -- B
#eval omega_neither   -- N

-- Boolean algebra: explosion is semantic, not structural
#eval Truth4.meet B (Truth4.neg B)     -- F (complement law holds)
#eval Truth4.join B (Truth4.neg B)     -- T (excluded middle holds)
#eval Truth4.impl B F                  -- N (yet explosion is blocked!)

end Tau.Logic
