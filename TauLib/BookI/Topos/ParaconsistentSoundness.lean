import TauLib.BookI.Topos.CircularityResolution

/-!
# TauLib.BookI.Topos.ParaconsistentSoundness

**Hinge 6 §6 — Paraconsistent soundness of `Cat_τ`'s internal logic.**

Lean structural rendering of paper §6 (`papers/tau-topos/
section-06-paraconsistent-soundness.tex`).  Verifies that the
four-valued subobject classifier `Ω_τ = B_σ = Truth4` with the
paraconsistent Belnap–Dunn connectives `∧, ∨, σ, →` is **sound**
with respect to first-degree-entailment (FDE) designated-value
preservation; that the classical explosion rule
`p ∧ ¬p ⊨ q` **fails**; and that the classical Boolean logic
sits inside `Cat_τ`'s four-valued logic as a canonical
truth-order subquotient.

## Registry Cross-References

- [I.D21] Truth4 (Logic.Truth4)
- [I.T13] Explosion barrier (Logic.Explosion)
- [I.D123] cauchyIter, sigmaSwap (Topos.CircularityResolution)
- [I.T60] liar_stabilises_at_Both (Topos.CircularityResolution)
- [I.T-H6-IsDesignated] `IsDesignated` (this module)
- [I.T-H6-FDEEntails] `Entails` FDE designated-preservation
- [I.T-H6-NonExplosion] `non_explosion` (paper Thm 6.2)
- [I.T-H6-ClassicalSubquotient] `classicalTruncation` functoriality
- [I.T-H6-LiarECQ] `liar_ECQ_failure_from_Wave9` (integrates Wave 9)

## Mathematical Content

**Paper §6 structure**:
- §6.2 Internal language of `Cat_τ` (typed first-order with 4-valued semantics)
- §6.3 Semantic interpretation `⟦ − ⟧` into `Ω_τ = B_σ`
- §6.4 Designated-preservation entailment `φ ⊨ ψ`
- §6.5 **Soundness** (paper Thm 6.1): Belnap–Dunn axioms → all valid
- §6.6 **Non-explosion** (paper Thm 6.2): `L ∧ ¬L ⊭ q` for `q` unstabilised
- §6.7 **Classical subquotient** (paper Thm 6.3): truth-order truncation
- §6.8 Propositional completeness (partial converse, Book II-deferred)

**The designated sector**: `D = {T, B} = {e_+, 1} ⊂ B_σ` — paper's
"Belnap–Dunn truths and near-truths."  A valuation is *designated*
if it lands in `D`.  A formula is *valid* if it is designated at
every valuation; entailment `φ ⊨ ψ` is designated-preservation.

**The paraconsistent σ-implication**: paper §6.3 Clause (5) gives
`⟦ φ → ψ ⟧ = σ(⟦ φ ⟧) ∨ ⟦ ψ ⟧`.  This is the σ-implication
`sigmaImpl p q := (σ p) ∨ q`, distinct from `Truth4.impl` which
uses the diamond-lattice complement `Truth4.neg`.  Both co-exist
in the paper bundle; H6.3 uses the σ-implication.

**The central non-explosion witness**: taking `p = B = Both` (the
Liar's ω-germ stabilised value from Wave 9's
`liar_stabilises_at_Both`) and `q = N = Neither`, we have
`p ∧ σp = B ∧ σB = B ∧ B = B ∈ D` but `q = N ∉ D` — so
designated-preservation fails.  This is the FDE non-explosion
witness realised via the Liar from Wave 9.

**Scope**: \scopetau, modulo Hinge 7 NF confluence for the full
§6.1 first-order soundness (propositional-level soundness is
\scopeest via Belnap–Dunn axioms on B_σ's De Morgan bilattice
structure).  The non-explosion theorem is *unconditional* at the
structural-witness level (just a `decide` check on the 4-element
`Truth4`).

## Public API

- `IsDesignated : Truth4 → Prop` — membership in `D = {T, B}`.
- `sigmaImpl p q` — σ-implication `σ(p) ∨ q` (paper §6.3 Clause 5).
- `Entails a b` — FDE designated-preservation `IsDesignated a →
  IsDesignated b` (paper Def 6.4.ii).
- `isDesignated_meet_iff` — `IsDesignated (a ∧ b) ↔
  IsDesignated a ∧ IsDesignated b` (conjunction designation
  preservation, the core soundness lemma).
- `isDesignated_join_of_left/right` — `∨`-introduction is
  designation-preserving.
- `sigmaSwap_meet_de_morgan` / `sigmaSwap_join_de_morgan` — the
  De Morgan laws for the σ-involution.
- `non_explosion` — **the main theorem** (paper Thm 6.2):
  `∃ p q, IsDesignated (p ∧ σp) ∧ ¬ IsDesignated q`.
- `liar_ECQ_failure_from_Wave9` — the concrete non-explosion
  witness via the Liar's `Both` stabilisation.
- `classicalTruncation : Truth4 → Bool` — truth-order truncation
  sending `{N, F} ↦ false`, `{T, B} ↦ true` (= `forget` from
  `BooleanRecovery`).
- `classicalTruncation_preserves_meet/join` — the subquotient is
  a lattice homomorphism.
- `classicalTruncation_preserves_designation` — the subquotient
  sends `D` to `true`.
-/

set_option autoImplicit false

namespace Tau.Topos

open Tau.Logic Tau.Polarity Truth4

-- ============================================================
-- PART 1: The designated sector D = {T, B}
-- ============================================================

/-- **The designated sector** of `Truth4 = B_σ`
    (paper Def 6.4.i): `D = {T, B} = {e_+, 1}`, the Belnap–Dunn
    "truths and near-truths."  A formula is valid at a valuation
    iff its interpretation lands in `D`. -/
def IsDesignated : Truth4 → Prop
  | T => True
  | B => True
  | F => False
  | N => False

@[simp] theorem isDesignated_T : IsDesignated T := trivial
@[simp] theorem isDesignated_B : IsDesignated B := trivial
@[simp] theorem not_isDesignated_F : ¬ IsDesignated F := id
@[simp] theorem not_isDesignated_N : ¬ IsDesignated N := id

/-- Designation is decidable on `Truth4` (4-element finite-state
    check). -/
instance : DecidablePred IsDesignated := fun v => by
  cases v <;> simp [IsDesignated] <;> infer_instance

/-- Membership characterisation: `v ∈ D ↔ v = T ∨ v = B`. -/
theorem isDesignated_iff (v : Truth4) :
    IsDesignated v ↔ v = T ∨ v = B := by
  cases v <;> simp [IsDesignated]

-- ============================================================
-- PART 2: σ-implication (paper §6.3 Clause 5)
-- ============================================================

/-- The **σ-implication** on `Truth4 = B_σ`: paper §6.3 Clause (5),
    `φ → ψ ⟧ := σ(⟦ φ ⟧) ∨ ⟦ ψ ⟧`.  Distinct from `Truth4.impl`
    (which uses the diamond-lattice complement `Truth4.neg`); this
    is the paraconsistent implication of the τ-topos's internal
    logic. -/
def sigmaImpl (p q : Truth4) : Truth4 :=
  Truth4.join (sigmaSwap p) q

@[simp] theorem sigmaImpl_T_left (q : Truth4) :
    sigmaImpl T q = q := by
  cases q <;> rfl

@[simp] theorem sigmaImpl_F_left (q : Truth4) :
    sigmaImpl F q = T := by
  cases q <;> rfl

/-- σ-implication truth-table for the Liar/Curry template. -/
theorem sigmaImpl_B_left (q : Truth4) :
    sigmaImpl B q = match q with | T => T | F => B | B => B | N => T := by
  cases q <;> rfl

theorem sigmaImpl_N_left (q : Truth4) :
    sigmaImpl N q = match q with | T => T | F => N | B => T | N => N := by
  cases q <;> rfl

-- ============================================================
-- PART 3: FDE designated-preservation entailment (paper Def 6.4.ii)
-- ============================================================

/-- **FDE entailment** by designated-preservation
    (paper Def 6.4.ii): `a ⊨ b` iff every valuation that designates
    `a` also designates `b`.  At the propositional level with
    closed atoms, this reduces to
    `IsDesignated a → IsDesignated b`. -/
def Entails (a b : Truth4) : Prop :=
  IsDesignated a → IsDesignated b

@[simp] theorem entails_refl (a : Truth4) : Entails a a := fun h => h

theorem entails_trans {a b c : Truth4}
    (h_ab : Entails a b) (h_bc : Entails b c) : Entails a c :=
  fun ha => h_bc (h_ab ha)

/-- Entailment is decidable on `Truth4`. -/
instance : DecidableRel (Entails : Truth4 → Truth4 → Prop) :=
  fun a b => by unfold Entails; infer_instance

-- ============================================================
-- PART 4: Core soundness — meet designation preservation
-- ============================================================

/-- **Conjunction designation preservation** (the core soundness
    lemma, paper Thm 6.1 Step 2 `∧`-introduction): `a ∧ b` is
    designated iff both `a` and `b` are designated.  On the
    `Truth4`-finite state space this is a `decide` check. -/
theorem isDesignated_meet_iff (a b : Truth4) :
    IsDesignated (Truth4.meet a b) ↔ IsDesignated a ∧ IsDesignated b := by
  cases a <;> cases b <;> simp [IsDesignated, Truth4.meet]

/-- **Conjunction introduction is designation-preserving**. -/
theorem isDesignated_meet_intro (a b : Truth4)
    (h_a : IsDesignated a) (h_b : IsDesignated b) :
    IsDesignated (Truth4.meet a b) :=
  (isDesignated_meet_iff a b).mpr ⟨h_a, h_b⟩

/-- **Conjunction elimination** (left). -/
theorem isDesignated_meet_left (a b : Truth4)
    (h : IsDesignated (Truth4.meet a b)) : IsDesignated a :=
  ((isDesignated_meet_iff a b).mp h).1

/-- **Conjunction elimination** (right). -/
theorem isDesignated_meet_right (a b : Truth4)
    (h : IsDesignated (Truth4.meet a b)) : IsDesignated b :=
  ((isDesignated_meet_iff a b).mp h).2

-- ============================================================
-- PART 5: Disjunction introduction (designation-preserving)
-- ============================================================

/-- **Disjunction introduction (left)**: if `a` is designated,
    so is `a ∨ b`. -/
theorem isDesignated_join_of_left (a b : Truth4)
    (h : IsDesignated a) : IsDesignated (Truth4.join a b) := by
  cases a <;> cases b <;> simp_all [IsDesignated, Truth4.join]

/-- **Disjunction introduction (right)**: if `b` is designated,
    so is `a ∨ b`. -/
theorem isDesignated_join_of_right (a b : Truth4)
    (h : IsDesignated b) : IsDesignated (Truth4.join a b) := by
  cases a <;> cases b <;> simp_all [IsDesignated, Truth4.join]

/-- **Disjunction designation characterisation**: `a ∨ b` is
    designated iff at least one of `a`, `b` is designated. -/
theorem isDesignated_join_iff (a b : Truth4) :
    IsDesignated (Truth4.join a b) ↔ IsDesignated a ∨ IsDesignated b := by
  cases a <;> cases b <;> simp [IsDesignated, Truth4.join]

-- ============================================================
-- PART 6: σ De Morgan laws (paper Thm 6.1 Step 1)
-- ============================================================

/-- **σ De Morgan for meet**: `σ(a ∧ b) = σ(a) ∨ σ(b)`. -/
theorem sigmaSwap_meet_de_morgan (a b : Truth4) :
    sigmaSwap (Truth4.meet a b) = Truth4.join (sigmaSwap a) (sigmaSwap b) := by
  cases a <;> cases b <;> rfl

/-- **σ De Morgan for join**: `σ(a ∨ b) = σ(a) ∧ σ(b)`. -/
theorem sigmaSwap_join_de_morgan (a b : Truth4) :
    sigmaSwap (Truth4.join a b) = Truth4.meet (sigmaSwap a) (sigmaSwap b) := by
  cases a <;> cases b <;> rfl

/-- σ-involutivity (already in `CircularityResolution`, restated
    here for §6.5 Step 2 reference). -/
theorem sigmaSwap_involutive_restate (v : Truth4) :
    sigmaSwap (sigmaSwap v) = v :=
  sigmaSwap_involutive v

-- ============================================================
-- PART 7: σ designation behaviour (asymmetric: lobe-swap, fixed
--          on apex/zero)
-- ============================================================

/-- σ *flips* designation on the lobe pair `{T, F}` and *preserves*
    designation on the σ-fixed atoms `{B, N}`:

    - `σ T = F`  (T designated, F not) — flip
    - `σ F = T`  (F not, T designated) — flip
    - `σ B = B`  (both designated)      — preserve
    - `σ N = N`  (both not)             — preserve -/
theorem sigmaSwap_designation (v : Truth4) :
    IsDesignated (sigmaSwap v) ↔
      (v = F) ∨ (v = B) := by
  cases v <;> simp [sigmaSwap, IsDesignated]

/-- The apex `B = 1` is σ-fixed **and** designated — this is what
    makes the Liar's `L ∧ ¬L = B ∧ B = B` designated, which is
    the FDE non-explosion witness. -/
theorem sigmaSwap_B_designated : IsDesignated (sigmaSwap B) := by
  rw [sigmaSwap_B]; exact isDesignated_B

-- ============================================================
-- PART 8: The central non-explosion witness
-- ============================================================

/-- The structural identity `B ∧ σB = B`:  the Liar's `L ∧ ¬L`
    on `Truth4` lands at `B` (the Hegelian "unity of opposites" as
    an algebraic identity, *designated* because `B ∈ D`). -/
theorem meet_B_sigmaSwap_B : Truth4.meet B (sigmaSwap B) = B := rfl

/-- The apex's σ-fixed-and-designated property, packaged as the
    key non-explosion ingredient. -/
theorem meet_B_sigmaSwap_B_designated :
    IsDesignated (Truth4.meet B (sigmaSwap B)) := by
  rw [meet_B_sigmaSwap_B]; exact isDesignated_B

/-- **Failure of explosion** (paper Theorem 6.2 / paper ref
    `thm:non-explosion`).

    In `Cat_τ`'s internal logic, the classical rule
    `p ∧ ¬p ⊨ q` (*ex contradictione quodlibet*) **fails** under
    FDE designated-preservation: there exist closed propositions
    `p, q : Truth4` with `p ∧ σp` designated (so the premise is
    valid in `D`) while `q` is not designated (so the conclusion
    escapes `D`).

    Witness: `p = B` (the Liar's ω-germ stabilised value from
    Wave 9's `liar_stabilises_at_Both`), `q = N` (an unstabilised
    proposition, paper case (d) of `circularity-classification`).
    Then `p ∧ σp = B ∧ B = B ∈ D` but `q = N ∉ D`, so
    designated-preservation fails and hence `p ∧ ¬p ⊬ q`. -/
theorem non_explosion :
    ∃ p q : Truth4, IsDesignated (Truth4.meet p (sigmaSwap p)) ∧
                    ¬ IsDesignated q :=
  ⟨B, N, meet_B_sigmaSwap_B_designated, not_isDesignated_N⟩

/-- **Non-explosion, entailment form** (paper Remark
    `formula-vs-judgment`): for the witnesses `p = B`, `q = N`,
    designated-preservation `p ∧ σp ⊨ q` **fails**. -/
theorem non_explosion_entailment :
    ¬ Entails (Truth4.meet B (sigmaSwap B)) N := by
  intro h_entails
  have h_premise : IsDesignated (Truth4.meet B (sigmaSwap B)) :=
    meet_B_sigmaSwap_B_designated
  exact not_isDesignated_N (h_entails h_premise)

/-- **Liar-ECQ-failure from Wave 9**: the concrete instantiation
    of `non_explosion` via the Liar's stabilisation at `Both = B`
    (Wave 9's `liar_stabilises_at_Both`).

    This is the paper's narrative integration: the ω-germ
    stabilised Liar value `⟦ L ⟧ = B` (Wave 9) combined with
    `B ∧ σB = B ∈ D` (this module) gives the Liar's contradiction
    `L ∧ ¬L` designated status, and the existence of unstabilised
    `q` with `⟦ q ⟧ = N ∉ D` (Wave 9 case (d)) yields the
    designated-preservation failure. -/
theorem liar_ECQ_failure_from_Wave9 :
    -- The Liar's L ∧ ¬L is designated (lands at B = Both)
    IsDesignated (Truth4.meet B (sigmaSwap B)) ∧
    -- An unstabilised q is not designated (lands at N = Neither)
    ¬ IsDesignated N :=
  ⟨meet_B_sigmaSwap_B_designated, not_isDesignated_N⟩

-- ============================================================
-- PART 9: Classical subquotient (paper Theorem 6.3)
-- ============================================================

/-- **Classical-subquotient truncation** (paper Thm
    `thm:classical-subquotient-logic`): the truth-order
    truncation `B_σ → {0, 1}` sending `{N, F} ↦ false` and
    `{T, B} ↦ true`, the canonical two-valued quotient.

    Coincides with `Logic.BooleanRecovery.forget` (the
    "optimistic" B-sector projection).  Restated here under the
    paraconsistent-soundness reading: the map is the quotient
    functor `Q : Cat_τ → Cat_τ^cl` of paper Thm 6.3. -/
def classicalTruncation : Truth4 → Bool
  | T => true
  | B => true
  | F => false
  | N => false

/-- The truncation agrees with `Logic.BooleanRecovery.forget`. -/
theorem classicalTruncation_eq_forget (v : Truth4) :
    classicalTruncation v = Tau.Logic.forget v := by
  cases v <;> rfl

/-- **The truncation sends designated ↔ true**. -/
theorem classicalTruncation_preserves_designation (v : Truth4) :
    classicalTruncation v = true ↔ IsDesignated v := by
  cases v <;> simp [classicalTruncation, IsDesignated]

/-- **Lattice homomorphism**: truncation preserves meet. -/
theorem classicalTruncation_preserves_meet (a b : Truth4) :
    classicalTruncation (Truth4.meet a b) =
      (classicalTruncation a && classicalTruncation b) := by
  cases a <;> cases b <;> rfl

/-- **Lattice homomorphism**: truncation preserves join. -/
theorem classicalTruncation_preserves_join (a b : Truth4) :
    classicalTruncation (Truth4.join a b) =
      (classicalTruncation a || classicalTruncation b) := by
  cases a <;> cases b <;> rfl

/-- **σ-negation under truncation, on the classical lobes**.
    On `{T, F}` the truncation commutes with σ (up to Boolean
    negation); on `{B, N}` σ is fixed and the commutation fails.
    This is the precise locus where the classical subquotient
    identifies with Boolean logic (paper Thm 6.3 Clause 3). -/
theorem classicalTruncation_sigma_on_lobes (v : Truth4)
    (h : v = T ∨ v = F) :
    classicalTruncation (sigmaSwap v) = ! classicalTruncation v := by
  rcases h with rfl | rfl <;> rfl

/-- **σ on B/N is σ-fixed** (the non-classical fragment): the
    truncation does not commute with σ on `{B, N}`.  This witnesses
    why paraconsistent content is non-trivial — it lives in the
    subquotient's kernel. -/
theorem classicalTruncation_sigma_on_apex_kernel :
    classicalTruncation (sigmaSwap B) = classicalTruncation B ∧
    classicalTruncation (sigmaSwap N) = classicalTruncation N := by
  refine ⟨?_, ?_⟩ <;> rfl

-- ============================================================
-- PART 10: Propositional-level soundness (paper Thm 6.1, clauses)
-- ============================================================

/-- **σ-involutivity is designation-neutral** (the σ-involutivity
    clause of paper Thm 6.1 Step 2): `σ(σ v) = v`, so applying σ
    twice returns the original designation status.  Not that σ
    itself preserves designation (it doesn't on lobes), but the
    *double application* does. -/
theorem isDesignated_double_sigma (v : Truth4) :
    IsDesignated (sigmaSwap (sigmaSwap v)) ↔ IsDesignated v := by
  rw [sigmaSwap_involutive]

/-- **σ-implication designation at classical lobes**: on the
    classical fragment `{T, F}`, σ-implication recovers the
    classical material implication at the designation level:
    `sigmaImpl a b ∈ D ↔ (a ∈ D → b ∈ D)`. -/
theorem sigmaImpl_designated_on_lobes_T (b : Truth4) :
    IsDesignated (sigmaImpl T b) ↔ IsDesignated b := by
  rw [sigmaImpl_T_left]

theorem sigmaImpl_designated_on_lobes_F (b : Truth4) :
    IsDesignated (sigmaImpl F b) := by
  rw [sigmaImpl_F_left]; exact isDesignated_T

/-- **Bilattice-level Belnap–Dunn commutativity** (paper Thm 6.1
    Step 1): `∧` and `∨` are commutative.  Already proved in
    `Logic.Truth4`; restated here to locate the soundness-chain
    reference. -/
theorem bd_meet_comm (a b : Truth4) :
    Truth4.meet a b = Truth4.meet b a :=
  Truth4.meet_comm a b

theorem bd_join_comm (a b : Truth4) :
    Truth4.join a b = Truth4.join b a :=
  Truth4.join_comm a b

/-- **Bilattice-level Belnap–Dunn distributivity** (paper Thm 6.1
    Step 1). -/
theorem bd_meet_distrib_join (a b c : Truth4) :
    Truth4.meet a (Truth4.join b c) =
      Truth4.join (Truth4.meet a b) (Truth4.meet a c) :=
  Truth4.meet_distrib_join a b c

-- ============================================================
-- PART 11: Sanity checks (#eval smoke tests)
-- ============================================================

-- The central non-explosion witness
#eval (Truth4.meet B (sigmaSwap B))       -- B (designated)
#eval decide (IsDesignated B)              -- true
#eval decide (IsDesignated N)              -- false

-- σ-implication truth table (Liar row)
#eval sigmaImpl B T                        -- T
#eval sigmaImpl B F                        -- B
#eval sigmaImpl B B                        -- B
#eval sigmaImpl B N                        -- T

-- Entailment decidability
#eval decide (Entails B T)                 -- true (B des → T des)
#eval decide (Entails B N)                 -- false (B des → N not des)
#eval decide (Entails F N)                 -- true (F not des → vacuous)

-- Classical truncation
#eval classicalTruncation T                -- true
#eval classicalTruncation B                -- true (designated)
#eval classicalTruncation F                -- false
#eval classicalTruncation N                -- false (not designated)

end Tau.Topos
