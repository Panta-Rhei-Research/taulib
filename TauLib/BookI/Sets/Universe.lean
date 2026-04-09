import TauLib.BookI.Sets.Powerset

/-!
# TauLib.BookI.Sets.Universe

τ-Universe properties: countability, no Russell set, no infinite descent.

## Registry Cross-References

- [I.P13a] Countability — `tau_idx_countable`
- [I.P13b] No Russell Set — `no_russell_set`
- [I.P13c] No Infinite Descent — from `tau_strict_mem_wf`

## Ground Truth Sources
- chunk_0365_M003070: Universe properties of τ-arithmetic sets

## Mathematical Content

**τ as class**: τ is a proper class (a category), not a set. "x ∈ τ"
means x is an object of the category — class membership, not set
membership. The internal set theory developed here lives INSIDE τ,
encoded arithmetically on the α-orbit O_α ≅ ℕ⁺.

The τ-set universe (= O_α = ℕ⁺) has three fundamental properties that
distinguish it from naive set theory while maintaining computational power:

1. **Countability**: TauIdx ≅ ℕ⁺, so the universe is trivially countable.
   The identity function witnesses the bijection.

2. **No Russell Set**: There is no τ-set R such that for all a,
   a ∈_τ R iff a ∉_τ R. This follows from reflexivity of τ-membership
   (every a ∈_τ a since a | a), which means the "diagonal" argument
   produces a contradiction at a = R.

3. **No Infinite Descent**: From well-foundedness of strict τ-membership
   (Powerset.lean), there is no infinite descending chain of nonzero
   strict τ-members. This is the τ-analogue of the Foundation Axiom.
-/

namespace Tau.Sets

open Tau.Denotation Tau.Coordinates

-- ============================================================
-- COUNTABILITY [I.P13a]
-- ============================================================

/-- The τ-index universe is Nat itself (by definition). -/
theorem tau_idx_is_nat : TauIdx = Nat := rfl

/-- [I.P13a] The τ-set universe is countable: the identity function
    is a bijection TauIdx → Nat. -/
theorem tau_idx_countable : ∃ f : TauIdx → Nat, Function.Injective f :=
  ⟨id, fun _ _ h => h⟩

/-- The identity surjects onto Nat (universe is exactly Nat). -/
theorem tau_idx_surjective : ∀ n : Nat, ∃ a : TauIdx, a = n :=
  fun n => ⟨n, rfl⟩

-- ============================================================
-- NO RUSSELL SET [I.P13b]
-- ============================================================

/-- [I.P13b] No Russell Set: there is no τ-set R such that
    for all a, a ∈_τ R iff ¬(a ∈_τ R).

    Proof by contradiction: if such R existed, then applying
    the biconditional to a = R gives R ∈_τ R ↔ ¬(R ∈_τ R).
    But R ∈_τ R always holds (since R | R), so we get
    True ↔ False, a contradiction. -/
theorem no_russell_set :
    ¬ ∃ R : TauIdx, ∀ a : TauIdx, tau_mem a R ↔ ¬ tau_mem a R := by
  intro ⟨R, hR⟩
  have h := hR R
  have hRR : tau_mem R R := tau_mem_refl R
  exact (h.mp hRR) hRR

/-- Variant: no τ-set separates members from non-members via complement.
    There is no τ-set C that contains exactly the non-self-members. -/
theorem no_complement_of_self_mem :
    ¬ ∃ C : TauIdx, ∀ a : TauIdx, tau_mem a C ↔ ¬ tau_mem a a := by
  intro ⟨C, hC⟩
  have hCC : tau_mem C C := tau_mem_refl C
  exact (hC C).mp hCC hCC

-- ============================================================
-- NO INFINITE DESCENT [I.P13c]
-- ============================================================

/-- A descending chain is a function f : Nat → TauIdx such that
    f(n+1) is a strict nonzero member of f(n) for all n. -/
def is_descending_chain (f : Nat → TauIdx) : Prop :=
  ∀ n : Nat, tau_strict_mem_nz (f (n + 1)) (f n)

/-- [I.P13c] No Infinite Descent: there is no infinite descending
    chain of strict τ-membership through nonzero elements.

    Proof: from well-foundedness of tau_strict_mem_nz. An infinite
    descending chain would contradict the well-foundedness of the
    relation, since it would produce a sequence with no minimal element. -/
theorem no_infinite_descent : ¬ ∃ f : Nat → TauIdx, is_descending_chain f := by
  intro ⟨f, hchain⟩
  have hwf := tau_strict_mem_wf
  -- Extract the accessibility predicate at f 0
  have hacc : Acc tau_strict_mem_nz (f 0) := hwf.apply (f 0)
  -- Show by induction that f n is accessible for all n, but the chain never terminates
  suffices ∀ n : Nat, Acc tau_strict_mem_nz (f n) by
    -- Build a descending sequence witnessing non-well-foundedness
    -- Actually, we use the fact that Acc is well-founded induction:
    -- if f(n) is accessible and f(n+1) < f(n), then f(n+1) is also accessible.
    -- But this just shows all are accessible — we need to show the chain
    -- contradicts accessibility directly.
    exact absurd hwf (by
      intro hwf'
      -- A well-founded relation has no infinite descending chain.
      -- We build the contradiction by strong induction.
      have : ∀ a : TauIdx, Acc tau_strict_mem_nz a → ∀ g : Nat → TauIdx,
          g 0 = a → (∀ n, tau_strict_mem_nz (g (n + 1)) (g n)) → False := by
        intro a hacc
        induction hacc with
        | intro x _ ih =>
          intro g hg0 hg
          exact ih (g 1) (hg0 ▸ hg 0) (fun n => g (n + 1)) rfl (fun n => hg (n + 1))
      exact this (f 0) (hwf'.apply (f 0)) f rfl hchain)
  intro n
  induction n with
  | zero => exact hacc
  | succ n ih => exact ih.inv (hchain n)

-- ============================================================
-- UNIVERSE STRUCTURE SUMMARY
-- ============================================================

/-- The τ-universe is a preorder (reflexive + transitive membership). -/
theorem tau_mem_preorder :
    (∀ a : TauIdx, tau_mem a a) ∧
    (∀ a b c : TauIdx, tau_mem a b → tau_mem b c → tau_mem a c) :=
  ⟨tau_mem_refl, fun _ _ _ => tau_mem_trans⟩

/-- The τ-universe is a partial order (preorder + antisymmetry). -/
theorem tau_mem_partial_order :
    (∀ a : TauIdx, tau_mem a a) ∧
    (∀ a b : TauIdx, tau_mem a b → tau_mem b a → a = b) ∧
    (∀ a b c : TauIdx, tau_mem a b → tau_mem b c → tau_mem a c) :=
  ⟨tau_mem_refl, fun _ _ => tau_mem_antisymm, fun _ _ _ => tau_mem_trans⟩

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- The Russell set argument works for any specific index
example : tau_mem 5 5 := tau_mem_refl 5
example : tau_mem 1 1 := tau_mem_refl 1
example : tau_mem 7 7 := tau_mem_refl 7

-- Countability witness
#eval (id : TauIdx → Nat) 42  -- expected: 42

end Tau.Sets
