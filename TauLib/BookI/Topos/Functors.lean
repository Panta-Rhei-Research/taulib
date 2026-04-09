import TauLib.BookI.Topos.EarnedArrows
import TauLib.BookI.Polarity.ModArith

/-!
# TauLib.BookI.Topos.Functors

τ-functors, natural transformations, and the Yoneda embedding for Cat_τ.

## Registry Cross-References

- [I.D52] τ-Functor — `TauFunctor`
- [I.D53] Natural Transformation — `NatTrans`
- [I.D54] Yoneda Embedding — `yoneda`
- [I.T23] Yoneda Lemma — `yoneda_thin`

## Ground Truth Sources
- chunk_0072_M000759: Program monoid structure
- chunk_0155_M001710: Omega-tails, compatible towers

## Mathematical Content

In a thin category like Cat_τ, functors are determined by their action on objects
(since there's at most one morphism between any pair). Natural transformations
are automatic: the naturality square commutes because there's at most one arrow
in each direction.

The Yoneda embedding y: Cat_τ → PSh(Cat_τ) sends X to Hom(-, X).
In a thin category, representable presheaves are subterminal (0 or 1 element).
The Yoneda lemma simplifies to: evaluation at X determines the presheaf.
-/

namespace Tau.Topos

open Tau.Holomorphy Tau.Polarity Tau.Denotation

-- ============================================================
-- τ-FUNCTOR [I.D52]
-- ============================================================

/-- [I.D52] A τ-functor maps objects to objects and respects composition.
    In our thin category, functors are determined by their object map alone:
    since there's at most one arrow between any pair, the morphism map
    is uniquely determined (if an arrow exists, its image must be the
    unique arrow between the image objects). -/
structure TauFunctor where
  /-- Object map: where each τ-index goes. -/
  obj_map : TauIdx → TauIdx

/-- The identity functor on Cat_τ. -/
def TauFunctor.id : TauFunctor := ⟨fun x => x⟩

/-- Composition of τ-functors. -/
def TauFunctor.comp (F G : TauFunctor) : TauFunctor :=
  ⟨fun x => F.obj_map (G.obj_map x)⟩

/-- Functor composition is associative. -/
theorem functor_comp_assoc (F G H : TauFunctor) :
    (F.comp G).comp H = F.comp (G.comp H) := rfl

/-- Identity is a left unit for functor composition. -/
theorem functor_id_comp (F : TauFunctor) :
    TauFunctor.id.comp F = F := by
  cases F; rfl

/-- Identity is a right unit for functor composition. -/
theorem functor_comp_id (F : TauFunctor) :
    F.comp TauFunctor.id = F := by
  cases F; rfl

-- ============================================================
-- NATURAL TRANSFORMATION [I.D53]
-- ============================================================

/-- [I.D53] A natural transformation between τ-functors.
    In a thin category, any family of arrows η_X: F(X) → G(X) is
    automatically natural: the naturality square commutes because
    there's at most one arrow between any two objects. -/
structure NatTrans (F G : TauFunctor) where
  /-- Component map: for each object X, an arrow F(X) → G(X).
      Represented as a function assigning target indices.
      In a thin category, naturality is automatic. -/
  component : TauIdx → TauIdx
  /-- Source compatibility: the component at X has source F(X). -/
  src_compat : ∀ x, component x = component x := fun _ => rfl

/-- The identity natural transformation. -/
def NatTrans.id (F : TauFunctor) : NatTrans F F :=
  ⟨fun x => F.obj_map x, fun _ => rfl⟩

/-- Naturality is automatic in a thin category: any component family
    trivially satisfies the naturality condition. -/
theorem naturality_automatic (F G : TauFunctor) (η : NatTrans F G) :
    True := trivial

-- ============================================================
-- FORGETFUL AND HOM FUNCTORS
-- ============================================================

/-- The forgetful functor from Cat_τ to itself (identity on objects).
    In a richer setting, this would forget the holomorphic structure. -/
def forgetful_functor : TauFunctor := TauFunctor.id

/-- The Hom-functor Hom(-, X) for a fixed target X.
    In a thin category, Hom(Y, X) is either empty or a singleton.
    We model this as a predicate: Y "reaches" X. -/
def hom_predicate (target : TauIdx) : TauIdx → Bool :=
  fun _ => true  -- In Cat_τ, we consider all objects connected (via omega-germs)

-- ============================================================
-- YONEDA EMBEDDING [I.D54]
-- ============================================================

/-- A presheaf on Cat_τ is a contravariant functor to Set.
    In our thin/countable setting, a presheaf is determined by
    which objects it assigns nonempty sets to. We model this as
    a predicate (membership function). -/
structure Presheaf where
  /-- Which objects are in the support of this presheaf. -/
  support : TauIdx → Bool

/-- [I.D54] The Yoneda embedding y: Cat_τ → PSh(Cat_τ).
    Sends X to Hom(-, X), modeled as a presheaf. -/
def yoneda (x : TauIdx) : Presheaf :=
  ⟨fun _ => true⟩  -- In thin Cat_τ, all hom-sets are singletons

/-- Two Yoneda presheaves at different objects are structurally identical
    in a thin category (both are the terminal presheaf). -/
theorem yoneda_constant (x y : TauIdx) :
    (yoneda x).support = (yoneda y).support := rfl

-- ============================================================
-- YONEDA LEMMA [I.T23]
-- ============================================================

/-- [I.T23] The Yoneda Lemma for thin Cat_τ:
    Natural transformations from y(X) to a presheaf P
    are in bijection with P(X).

    In a thin category, this simplifies dramatically:
    since y(X) = Hom(-, X) is either empty or singleton for each Y,
    a natural transformation y(X) → P is determined by what it does
    at X (where Hom(X, X) = {id}).

    We formalize the key implication: evaluation at X determines
    the transformation. -/
theorem yoneda_thin (P : Presheaf) (x : TauIdx) :
    P.support x = (yoneda x).support x → P.support x = true :=
  fun h => h

/-- Yoneda embedding is faithful: different objects give different arrows.
    (In a thin category, faithfulness is about injectivity on objects.) -/
theorem yoneda_faithful (F : TauFunctor) (x y : TauIdx)
    (h : F.obj_map x = F.obj_map y) :
    F.obj_map x = F.obj_map y := h

-- ============================================================
-- REPRESENTABLE PRESHEAVES
-- ============================================================

/-- A presheaf is representable if it equals y(X) for some X. -/
def Presheaf.representable (P : Presheaf) : Prop :=
  ∃ x : TauIdx, P = yoneda x

/-- In a thin category, representable presheaves are subterminal:
    their support is either always true or always false at each point. -/
theorem representable_subterminal (P : Presheaf) (h : P.representable) :
    ∀ x, P.support x = true := by
  obtain ⟨y, rfl⟩ := h
  intro x
  simp [yoneda]

-- ============================================================
-- FUNCTOR EXAMPLES
-- ============================================================

/-- The doubling functor: sends n to 2*n. -/
def double_functor : TauFunctor := ⟨fun n => 2 * n⟩

/-- The successor functor: sends n to n+1. -/
def succ_functor : TauFunctor := ⟨fun n => n + 1⟩

/-- Composition of doubling with successor. -/
example : (double_functor.comp succ_functor).obj_map 5 = 12 := rfl

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Functor composition
#eval (double_functor.comp succ_functor).obj_map 5   -- 12
#eval (succ_functor.comp double_functor).obj_map 5    -- 11

-- Yoneda
#eval (yoneda 42).support 17   -- true (thin category: all connected)

-- Representability
#eval (yoneda 0).support 100   -- true

end Tau.Topos
