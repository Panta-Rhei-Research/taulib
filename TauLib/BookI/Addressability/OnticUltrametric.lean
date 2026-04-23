import TauLib.BookI.Addressability.CayleyMetric

/-!
# TauLib.BookI.Addressability.OnticUltrametric

The **ontic ultrametric** on canonical addresses: Hinge 7
`thm:main-ultrametric` from `papers/address-resolution/main.tex`.

## Registry Cross-References

- [I.D14] Instruction / Program
- [I.L02] NF Confluence
- [I.T-H7-Cayley] Cayley Word Metric (Wave 5a)
- [I.T-H7-Ultrametric] Ontic Ultrametric (this module)

## Mathematical Content

**Hinge 7 Wave 5b**.  The ontic ultrametric `OnticDist` is the
**discrete metric** induced by NF-equivalence: two normal forms are
at distance 0 iff they coincide componentwise (same ρ-count and
pointwise-equal seed-map), and at distance 1 otherwise.

The discrete metric is the simplest non-archimedean ultrametric, and
it precisely matches the paper's claims:
"non-archimedean and totally disconnected".  It is the τ-native
replacement for Euclidean distance throughout Books II–VII.

The Cayley pseudometric of Wave 5a captures the **fine-grained**
ρ-count drift (a metric, not ultrametric); the ontic ultrametric
captures the **coarse-grained** equivalence-class membership (an
ultrametric, but loses the magnitude information).  Together they
give the address space its full bi-graded structure.

We prove the four ultrametric axioms:

- `OnticDist nf nf = 0`.
- Symmetry.
- Identity-of-indiscernibles up to NF-equivalence.
- Strong ultrametric inequality:
  `OnticDist a c ≤ max (OnticDist a b) (OnticDist b c)`.
-/

set_option autoImplicit false

namespace Tau.Addressability

open Tau.Kernel
open Tau.Denotation

-- ============================================================
-- PART 1: Seed-map agreement (Prop, decidable)
-- ============================================================

/-- Pointwise equality of two seed-maps over the 5-generator enumeration. -/
def seedAgree (f g : Generator → Generator) : Prop :=
  f Generator.alpha = g Generator.alpha
    ∧ f Generator.pi = g Generator.pi
    ∧ f Generator.gamma = g Generator.gamma
    ∧ f Generator.eta = g Generator.eta
    ∧ f Generator.omega = g Generator.omega

instance (f g : Generator → Generator) : Decidable (seedAgree f g) := by
  unfold seedAgree; infer_instance

theorem seedAgree_refl (f : Generator → Generator) : seedAgree f f :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem seedAgree_symm {f g : Generator → Generator} (h : seedAgree f g) :
    seedAgree g f := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1.symm, h2.symm, h3.symm, h4.symm, h5.symm⟩

theorem seedAgree_trans {f g h : Generator → Generator}
    (hfg : seedAgree f g) (hgh : seedAgree g h) : seedAgree f h := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := hfg
  obtain ⟨b1, b2, b3, b4, b5⟩ := hgh
  exact ⟨a1.trans b1, a2.trans b2, a3.trans b3, a4.trans b4, a5.trans b5⟩

-- ============================================================
-- PART 2: NF-equivalence as a Prop
-- ============================================================

/-- Two normal forms are NF-equivalent iff they coincide
    componentwise: equal ρ-count AND seed-maps agree on every
    generator. -/
def nfEquiv (nf₁ nf₂ : NormalForm) : Prop :=
  nf₁.rhoCount = nf₂.rhoCount ∧ seedAgree nf₁.seedMap nf₂.seedMap

instance (nf₁ nf₂ : NormalForm) : Decidable (nfEquiv nf₁ nf₂) := by
  unfold nfEquiv; infer_instance

theorem nfEquiv_refl (nf : NormalForm) : nfEquiv nf nf :=
  ⟨rfl, seedAgree_refl _⟩

theorem nfEquiv_symm {nf₁ nf₂ : NormalForm} (h : nfEquiv nf₁ nf₂) :
    nfEquiv nf₂ nf₁ :=
  ⟨h.1.symm, seedAgree_symm h.2⟩

theorem nfEquiv_trans {nf₁ nf₂ nf₃ : NormalForm}
    (h12 : nfEquiv nf₁ nf₂) (h23 : nfEquiv nf₂ nf₃) : nfEquiv nf₁ nf₃ :=
  ⟨h12.1.trans h23.1, seedAgree_trans h12.2 h23.2⟩

-- ============================================================
-- PART 3: Ontic ultrametric — discrete metric on NF-equivalence
-- ============================================================

/-- The **ontic ultrametric** on normal forms: discrete metric induced
    by NF-equivalence.  Distance 0 iff `nfEquiv`, else 1. -/
def OnticDist (nf₁ nf₂ : NormalForm) : Nat :=
  if nfEquiv nf₁ nf₂ then 0 else 1

@[simp] theorem OnticDist_self (nf : NormalForm) : OnticDist nf nf = 0 := by
  unfold OnticDist; rw [if_pos (nfEquiv_refl nf)]

theorem OnticDist_symm (nf₁ nf₂ : NormalForm) :
    OnticDist nf₁ nf₂ = OnticDist nf₂ nf₁ := by
  unfold OnticDist
  by_cases h : nfEquiv nf₁ nf₂
  · rw [if_pos h, if_pos (nfEquiv_symm h)]
  · rw [if_neg h, if_neg (fun h21 => h (nfEquiv_symm h21))]

/-- `OnticDist = 0` iff the two NFs are NF-equivalent (same ρ-count
    and pointwise-equal seed maps). -/
theorem OnticDist_eq_zero_iff (nf₁ nf₂ : NormalForm) :
    OnticDist nf₁ nf₂ = 0 ↔ nfEquiv nf₁ nf₂ := by
  unfold OnticDist
  by_cases h : nfEquiv nf₁ nf₂
  · rw [if_pos h]; exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [if_neg h]
    constructor
    · intro h_zero; exact absurd h_zero (by omega)
    · intro h'; exact absurd h' h

/-- The **strong ultrametric inequality** —
    `OnticDist a c ≤ max (OnticDist a b) (OnticDist b c)`.

    Proof by case analysis on whether each pair is NF-equivalent.
    The only non-trivial case is when both `(a,b)` and `(b,c)` are
    equivalent — then `(a,c)` is too by transitivity, so the LHS is 0
    and the inequality holds.  Otherwise the RHS is at least 1. -/
theorem OnticDist_ultrametric (nf₁ nf₂ nf₃ : NormalForm) :
    OnticDist nf₁ nf₃ ≤ max (OnticDist nf₁ nf₂) (OnticDist nf₂ nf₃) := by
  unfold OnticDist
  by_cases h12 : nfEquiv nf₁ nf₂
  · by_cases h23 : nfEquiv nf₂ nf₃
    · have h13 : nfEquiv nf₁ nf₃ := nfEquiv_trans h12 h23
      rw [if_pos h12, if_pos h23, if_pos h13]
      simp
    · rw [if_pos h12, if_neg h23]
      split <;> omega
  · rw [if_neg h12]
    split <;> omega

-- ============================================================
-- PART 4: Profinite-style "totally disconnected" witness
-- ============================================================

/-- Distinct NF-equivalence classes are at maximum distance — a
    formal expression of *total disconnection* for the ontic
    ultrametric. -/
theorem OnticDist_distinct (nf₁ nf₂ : NormalForm) (h : ¬ nfEquiv nf₁ nf₂) :
    OnticDist nf₁ nf₂ = 1 := by
  unfold OnticDist; rw [if_neg h]

/-- Equivalent NFs are at distance 0 — the *zero* ball of the
    ontic ultrametric is the NF-equivalence class. -/
theorem OnticDist_equiv (nf₁ nf₂ : NormalForm) (h : nfEquiv nf₁ nf₂) :
    OnticDist nf₁ nf₂ = 0 := by
  unfold OnticDist; rw [if_pos h]

end Tau.Addressability
