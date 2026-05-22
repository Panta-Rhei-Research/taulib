import TauLib.BookIII.Bridge.TauCircleParam
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Compactness.Compact

/-!
# TauLib.BookIII.Bridge.LemniscateGraph

Experimental G5 spine: the lemniscate as two τ-native circle lobes glued at one
crossing point.

This module now separates two layers.  `LemniscatePoint` is the raw coproduct
with explicit lobe labels and basepoints.  `LemniscateCarrier` is the quotient
that performs the wedge gluing by identifying the two lobe basepoints with the
crossing node.  Topology, metric, compactness, and shortest-path realization
remain explicit context obligations; this module does not claim that the metric
graph, compactness, or operator theory has been completed.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

open Tau.Boundary

/-- The two split-complex sectors/lobes of the τ lemniscate. -/
inductive LemniscateSector where
  | plus
  | minus
  deriving Repr, DecidableEq

/-- A point on the experimental lemniscate carrier: either the crossing node or
    a τ-native circle point on one of the two lobes. -/
inductive LemniscatePoint where
  | crossing : LemniscatePoint
  | lobe : LemniscateSector → TauCirclePoint → LemniscatePoint

namespace LemniscatePoint

/-- The crossing node, named for readability in later interfaces. -/
def omega : LemniscatePoint :=
  .crossing

/-- The distinguished basepoint on a given lobe. -/
def lobeBase (s : LemniscateSector) : LemniscatePoint :=
  .lobe s TauCirclePoint.base

/-- Predicate: a point is the crossing node. -/
def IsCrossing : LemniscatePoint → Prop
  | .crossing => True
  | .lobe _ _ => False

/-- Predicate: a raw point belongs to the crossing equivalence class of the
    wedge quotient.  This class contains the explicit crossing node and the two
    lobe basepoints. -/
def InCrossingClass : LemniscatePoint → Prop
  | .crossing => True
  | .lobe _ p => p = TauCirclePoint.base

/-- Predicate: a point lies on a specific lobe away from the quotient
    interpretation of the crossing node. -/
def OnSector (s : LemniscateSector) : LemniscatePoint → Prop
  | .crossing => False
  | .lobe t _ => t = s

/-- The wedge relation identifying the two lobe basepoints with the crossing.
    This relation is a scaffold for the eventual quotient/carrier proof. -/
inductive WedgeRelated : LemniscatePoint → LemniscatePoint → Prop where
  | refl (x : LemniscatePoint) : WedgeRelated x x
  | plus_base_to_crossing : WedgeRelated (lobeBase .plus) omega
  | minus_base_to_crossing : WedgeRelated (lobeBase .minus) omega
  | crossing_to_plus_base : WedgeRelated omega (lobeBase .plus)
  | crossing_to_minus_base : WedgeRelated omega (lobeBase .minus)
  | base_glue : WedgeRelated (lobeBase .plus) (lobeBase .minus)

/-- Equivalence relation for the wedge quotient: raw equality, plus one
    crossing class containing the crossing node and both lobe basepoints. -/
def WedgeEquivalent (x y : LemniscatePoint) : Prop :=
  x = y ∨ (InCrossingClass x ∧ InCrossingClass y)

/-- Every raw point is wedge-equivalent to itself. -/
theorem WedgeEquivalent.refl (x : LemniscatePoint) :
    WedgeEquivalent x x :=
  Or.inl rfl

/-- Wedge equivalence is symmetric. -/
theorem WedgeEquivalent.symm {x y : LemniscatePoint}
    (h : WedgeEquivalent x y) :
    WedgeEquivalent y x := by
  cases h with
  | inl hxy =>
      exact Or.inl hxy.symm
  | inr hxy =>
      exact Or.inr ⟨hxy.right, hxy.left⟩

/-- Wedge equivalence is transitive. -/
theorem WedgeEquivalent.trans {x y z : LemniscatePoint}
    (hxy : WedgeEquivalent x y)
    (hyz : WedgeEquivalent y z) :
    WedgeEquivalent x z := by
  cases hxy with
  | inl hxy =>
      subst y
      exact hyz
  | inr hxyc =>
      cases hyz with
      | inl hyz =>
          subst z
          exact Or.inr hxyc
      | inr hyzc =>
          exact Or.inr ⟨hxyc.left, hyzc.right⟩

/-- The raw wedge relation is contained in the equivalence relation used for
    the quotient carrier. -/
theorem WedgeRelated.toEquivalent {x y : LemniscatePoint}
    (h : WedgeRelated x y) :
    WedgeEquivalent x y := by
  cases h with
  | refl x =>
      exact WedgeEquivalent.refl x
  | plus_base_to_crossing =>
      exact Or.inr ⟨rfl, trivial⟩
  | minus_base_to_crossing =>
      exact Or.inr ⟨rfl, trivial⟩
  | crossing_to_plus_base =>
      exact Or.inr ⟨trivial, rfl⟩
  | crossing_to_minus_base =>
      exact Or.inr ⟨trivial, rfl⟩
  | base_glue =>
      exact Or.inr ⟨rfl, rfl⟩

/-- Setoid implementing the two-lobe wedge quotient. -/
def wedgeSetoid : Setoid LemniscatePoint where
  r := WedgeEquivalent
  iseqv := ⟨WedgeEquivalent.refl, WedgeEquivalent.symm, WedgeEquivalent.trans⟩

end LemniscatePoint

/-- The actual G5 carrier spine: two τ-native circle lobes modulo the wedge
    relation that identifies both lobe basepoints with the crossing node. -/
abbrev LemniscateCarrier : Type :=
  Quotient LemniscatePoint.wedgeSetoid

namespace LemniscateCarrier

/-- Carrier crossing class. -/
def crossing : LemniscateCarrier :=
  Quotient.mk LemniscatePoint.wedgeSetoid LemniscatePoint.omega

/-- Carrier point from a labeled lobe and τ-circle point. -/
def lobe (s : LemniscateSector) (p : TauCirclePoint) : LemniscateCarrier :=
  Quotient.mk LemniscatePoint.wedgeSetoid (LemniscatePoint.lobe s p)

/-- Carrier-level lobe membership.  The crossing class belongs to both lobes
    through the quotient identification of the lobe basepoints. -/
def OnSector (s : LemniscateSector) (x : LemniscateCarrier) : Prop :=
  ∃ p : TauCirclePoint, x = lobe s p

/-- Every constructed lobe point lies on its labeled carrier sector. -/
theorem lobe_onSector (s : LemniscateSector) (p : TauCirclePoint) :
    OnSector s (lobe s p) :=
  ⟨p, rfl⟩

/-- The basepoint on each lobe is the crossing class in the quotient carrier. -/
theorem lobe_base_eq_crossing (s : LemniscateSector) :
    lobe s TauCirclePoint.base = crossing := by
  apply Quotient.sound
  exact Or.inr ⟨rfl, trivial⟩

/-- The crossing class lies on either carrier sector. -/
theorem crossing_onSector (s : LemniscateSector) :
    OnSector s crossing :=
  ⟨TauCirclePoint.base, (lobe_base_eq_crossing s).symm⟩

/-- The crossing class is exactly the lobe intersection currently available at
    the carrier level.  Proving that this is the only intersection is a future
    separatedness/quotient obligation, not a fact assumed here. -/
theorem crossing_on_both_sectors :
    OnSector .plus crossing ∧ OnSector .minus crossing :=
  ⟨crossing_onSector .plus, crossing_onSector .minus⟩

/-- The two lobe basepoints are equal in the quotient carrier. -/
theorem plus_base_eq_minus_base :
    lobe .plus TauCirclePoint.base = lobe .minus TauCirclePoint.base := by
  apply Quotient.sound
  exact Or.inr ⟨rfl, rfl⟩

/-- Raw wedge-related points have the same carrier class. -/
theorem sound_wedge_related {x y : LemniscatePoint}
    (h : LemniscatePoint.WedgeRelated x y) :
    Quotient.mk LemniscatePoint.wedgeSetoid x =
      Quotient.mk LemniscatePoint.wedgeSetoid y := by
  exact Quotient.sound h.toEquivalent

end LemniscateCarrier

/-- Placeholder graph distance for the carrier.  Once the metric graph is
    proved, this should be replaced by the lobe-arc/wedge shortest-path
    distance. -/
noncomputable def lemniscateGraphDist
    (_x _y : LemniscateCarrier) : ℝ :=
  0

/-- Status labels for the G5 carrier layer. -/
inductive LemniscateCarrierStatus where
  | definition
  | explicitObligation
  | theoremBacked
  deriving Repr, DecidableEq

/-- Explicit G5 context for the lemniscate carrier.  This replaces the previous
    typeclass placeholders: topology, metric, compactness, and compatibility
    must be supplied as named data before any downstream theorem may consume
    them. -/
structure LemniscateCarrierContext where
  topology : TopologicalSpace LemniscateCarrier
  metric : MetricSpace LemniscateCarrier
  compact : CompactSpace LemniscateCarrier
  topologyIsWedgeQuotient : Prop
  metricIsGraphMetric : Prop
  compactnessFromWedge : Prop
  topologyMetricAgreement : Prop
  graphDistanceRealizesMetric : Prop
  status : LemniscateCarrierStatus := .explicitObligation

/-- The topology/metric agreement obligation for the G5 carrier.  The present
    statement intentionally records the interface rather than pretending the
    proof is complete. -/
def LemniscateTopologyMetricAgreement (ctx : LemniscateCarrierContext) : Prop :=
  ctx.topologyMetricAgreement

/-- Compact metric-graph carrier readiness is explicit: no theorem downstream
    should infer this from ambient typeclasses. -/
def LemniscateCarrierReady (ctx : LemniscateCarrierContext) : Prop :=
  ctx.topologyIsWedgeQuotient ∧
  ctx.metricIsGraphMetric ∧
  ctx.compactnessFromWedge ∧
  LemniscateTopologyMetricAgreement ctx ∧
  ctx.graphDistanceRealizesMetric ∧
  ctx.status = .theoremBacked

/-- Metric sanity for the zero-distance scaffold.  This theorem is intentionally
    weaker than a real metric-graph statement; the future shortest-path
    distance must replace it. -/
theorem lemniscateGraphDist_self (x : LemniscateCarrier) :
    lemniscateGraphDist x x = 0 :=
  rfl

end Tau.BookIII.Bridge
