import TauLib.BookVI.Sectors.Hallmarks

/-!
# TauLib.BookVI.Sectors.Absence

Failure modes: NoDist and NoSelfDesc. Virus, neutron, NS counterexamples.

## Registry Cross-References

- [VI.D21] NoDist — `NoDist`
- [VI.D22] NoSelfDesc — `NoSelfDesc`
- [VI.T15] Virus NoDist — `virus_nodist`
- [VI.L06] NS-NoSelfDesc — `ns_noselfdesc`
- [VI.L07] Consumer Bridge to E₃ — `consumer_bridge_e3`
- [VI.P09] Circadian 24h = τ¹ Rotation — `circadian_rotation`

## Ground Truth Sources
- Book VI Chapter 10 (2nd Edition): Predictions by Absence
-/

namespace Tau.BookVI.Absence

/-- [VI.D21] NoDist: system fails τ-Distinction. -/
structure NoDist where
  conditions_failed : Nat
  at_least_one : conditions_failed ≥ 1
  deriving Repr

/-- [VI.D22] NoSelfDesc: has Distinction but fails SelfDesc. -/
structure NoSelfDesc where
  has_distinction : Bool := true
  selfdesc_fails : Bool := true
  failure_reason : String
  deriving Repr

/-- [VI.T15] Virus NoDist: fails 3/5 distinction conditions outside host. -/
structure VirusNoDist where
  conditions_failed : Nat
  three_fail : conditions_failed = 3
  host_dependent : Bool := true
  deriving Repr

def virus : VirusNoDist where
  conditions_failed := 3
  three_fail := rfl

theorem virus_nodist :
    virus.conditions_failed = 3 ∧
    virus.host_dependent = true :=
  ⟨rfl, rfl⟩

/-- [VI.L06] NS-NoSelfDesc: 5/5 distinction, fails SelfDesc. -/
structure NSNoSelfDesc where
  distinction_passed : Nat
  all_five : distinction_passed = 5
  selfdesc_fails : Bool := true
  deriving Repr

def ns_nosd : NSNoSelfDesc where
  distinction_passed := 5
  all_five := rfl

theorem ns_noselfdesc :
    ns_nosd.distinction_passed = 5 ∧
    ns_nosd.selfdesc_fails = true :=
  ⟨rfl, rfl⟩

/-- [VI.L07] Consumer sector is unique bridge-head to E₃. -/
structure ConsumerBridgeE3 where
  has_eval_squared : Bool := true
  consumer_only : Bool := true
  deriving Repr

def consumer_bridge : ConsumerBridgeE3 := {}

theorem consumer_bridge_e3 :
    consumer_bridge.has_eval_squared = true ∧
    consumer_bridge.consumer_only = true :=
  ⟨rfl, rfl⟩

/-- [VI.P09] Circadian 24h = one full α-rotation on τ¹. -/
structure CircadianRotation where
  period_hours : Nat := 24
  winding_number : Nat := 1
  deriving Repr

def circadian : CircadianRotation := {}

theorem circadian_rotation :
    circadian.period_hours = 24 ∧
    circadian.winding_number = 1 :=
  ⟨rfl, rfl⟩

end Tau.BookVI.Absence
