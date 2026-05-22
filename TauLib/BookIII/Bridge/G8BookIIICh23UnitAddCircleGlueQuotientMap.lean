import TauLib.BookIII.Bridge.G8BookIIICh23UnitAddCircleGluedMetricSource

/-!
# TauLib.BookIII.Bridge.G8BookIIICh23UnitAddCircleGlueQuotientMap

First theorem-backed map between the concrete Ch.23 quotient wedge carrier and
Mathlib's glued metric model.

The previous metric source constructs the glued metric space for two
`UnitAddCircle` lobes.  This module builds the canonical map from the quotient
wedge carrier into that glued metric model, proves that it is well-defined with
respect to the wedge quotient relation, and proves that it is surjective.

The injectivity comparison is now theorem-backed: equality in the glued metric
model forces equality in the concrete wedge quotient.  The remaining
load-bearing work for the full metric transfer is topology/metric agreement,
shortest-path realization, and the later tau-native carrier transfer.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- QUOTIENT-CARRIER MAP INTO THE GLUED METRIC MODEL
-- ============================================================

/-- Raw map from the concrete wedge-point presentation into Mathlib's glued
    metric model.  The explicit crossing is sent to the plus-lobe basepoint;
    the basepoint-gluing theorem then makes this compatible with the minus
    basepoint as well. -/
def g8Ch23UnitAddCircleWedgePointToGlue :
    G8Ch23UnitAddCircleWedgePoint →
      G8Ch23UnitAddCircleGluedMetricSpace
  | .crossing =>
      g8Ch23UnitAddCirclePlusToGlue
        G8Ch23UnitAddCircleWedgePoint.basepoint
  | .lobe .plus p =>
      g8Ch23UnitAddCirclePlusToGlue p
  | .lobe .minus p =>
      g8Ch23UnitAddCircleMinusToGlue p

/-- The raw representative in the pre-gluing disjoint sum used by
    `Metric.GlueSpace`. -/
def g8Ch23UnitAddCircleWedgePointToGlueSum :
    G8Ch23UnitAddCircleWedgePoint →
      UnitAddCircle ⊕ UnitAddCircle
  | .crossing =>
      .inl G8Ch23UnitAddCircleWedgePoint.basepoint
  | .lobe .plus p =>
      .inl p
  | .lobe .minus p =>
      .inr p

/-- The raw point map is the separation quotient class of its disjoint-sum
    representative. -/
theorem g8Ch23UnitAddCircleWedgePointToGlue_eq_mk
    (x : G8Ch23UnitAddCircleWedgePoint) :
    g8Ch23UnitAddCircleWedgePointToGlue x =
      (Quotient.mk''
        (g8Ch23UnitAddCircleWedgePointToGlueSum x) :
          G8Ch23UnitAddCircleGluedMetricSpace) := by
  cases x with
  | crossing =>
      rfl
  | lobe s p =>
      cases s <;> rfl

/-- Every raw point in the wedge crossing class maps to the glued crossing
    point. -/
theorem g8Ch23UnitAddCircleWedgePointToGlue_inCrossingClass
    {x : G8Ch23UnitAddCircleWedgePoint}
    (hx : G8Ch23UnitAddCircleWedgePoint.InCrossingClass x) :
    g8Ch23UnitAddCircleWedgePointToGlue x =
      g8Ch23UnitAddCircleWedgePointToGlue
        G8Ch23UnitAddCircleWedgePoint.crossing := by
  cases x with
  | crossing =>
      rfl
  | lobe s p =>
      cases s with
      | plus =>
          simp [G8Ch23UnitAddCircleWedgePoint.InCrossingClass] at hx
          subst p
          rfl
      | minus =>
          simp [G8Ch23UnitAddCircleWedgePoint.InCrossingClass] at hx
          subst p
          exact g8Ch23UnitAddCircleGlue_basepoints_eq.symm

/-- Equality in the glued metric model forces the underlying raw wedge points
    to be equivalent for the concrete wedge quotient. -/
theorem g8Ch23UnitAddCircleWedgeEquivalent_of_toGlue_eq
    {x y : G8Ch23UnitAddCircleWedgePoint}
    (h :
      g8Ch23UnitAddCircleWedgePointToGlue x =
        g8Ch23UnitAddCircleWedgePointToGlue y) :
    G8Ch23UnitAddCircleWedgePoint.WedgeEquivalent x y := by
  letI : PseudoMetricSpace (UnitAddCircle ⊕ UnitAddCircle) :=
    Metric.gluePremetric
      g8Ch23UnitAddCircleCrossingToPlus_isometry
      g8Ch23UnitAddCircleCrossingToMinus_isometry
  letI : TopologicalSpace (UnitAddCircle ⊕ UnitAddCircle) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  have hmk :
      (SeparationQuotient.mk
          (g8Ch23UnitAddCircleWedgePointToGlueSum x) :
        G8Ch23UnitAddCircleGluedMetricSpace) =
      SeparationQuotient.mk
          (g8Ch23UnitAddCircleWedgePointToGlueSum y) := by
    calc
      (SeparationQuotient.mk
          (g8Ch23UnitAddCircleWedgePointToGlueSum x) :
        G8Ch23UnitAddCircleGluedMetricSpace) =
          g8Ch23UnitAddCircleWedgePointToGlue x :=
        (g8Ch23UnitAddCircleWedgePointToGlue_eq_mk x).symm
      _ = g8Ch23UnitAddCircleWedgePointToGlue y :=
        h
      _ =
          SeparationQuotient.mk
            (g8Ch23UnitAddCircleWedgePointToGlueSum y) :=
        g8Ch23UnitAddCircleWedgePointToGlue_eq_mk y
  have hdist :
      dist (g8Ch23UnitAddCircleWedgePointToGlueSum x)
        (g8Ch23UnitAddCircleWedgePointToGlueSum y) = 0 :=
    Metric.inseparable_iff.1 (SeparationQuotient.mk_eq_mk.1 hmk)
  change
      Metric.glueDist
        g8Ch23UnitAddCircleCrossingToPlus
        g8Ch23UnitAddCircleCrossingToMinus
        0
        (g8Ch23UnitAddCircleWedgePointToGlueSum x)
        (g8Ch23UnitAddCircleWedgePointToGlueSum y) = 0 at hdist
  cases x with
  | crossing =>
      cases y with
      | crossing =>
          exact Or.inl rfl
      | lobe sy q =>
          cases sy with
          | plus =>
              have hq :
                  q = G8Ch23UnitAddCircleWedgePoint.basepoint := by
                have hqdist :
                    dist G8Ch23UnitAddCircleWedgePoint.basepoint q = 0 := by
                  simpa [g8Ch23UnitAddCircleWedgePointToGlueSum,
                    Metric.glueDist] using hdist
                exact (dist_eq_zero.1 hqdist).symm
              exact Or.inr ⟨trivial, hq⟩
          | minus =>
              have hq :
                  q = G8Ch23UnitAddCircleWedgePoint.basepoint := by
                have hqdist :
                    dist q G8Ch23UnitAddCircleWedgePoint.basepoint = 0 := by
                  simpa [g8Ch23UnitAddCircleWedgePointToGlueSum,
                    Metric.glueDist,
                    g8Ch23UnitAddCircleCrossingToPlus,
                    g8Ch23UnitAddCircleCrossingToMinus,
                    G8Ch23UnitAddCircleWedgePoint.basepoint,
                    ciInf_unique] using hdist
                exact dist_eq_zero.1 hqdist
              exact Or.inr ⟨trivial, hq⟩
  | lobe sx p =>
      cases sx with
      | plus =>
          cases y with
          | crossing =>
              have hp :
                  p = G8Ch23UnitAddCircleWedgePoint.basepoint := by
                have hpdist :
                    dist p G8Ch23UnitAddCircleWedgePoint.basepoint = 0 := by
                  simpa [g8Ch23UnitAddCircleWedgePointToGlueSum,
                    Metric.glueDist] using hdist
                exact dist_eq_zero.1 hpdist
              exact Or.inr ⟨hp, trivial⟩
          | lobe sy q =>
              cases sy with
              | plus =>
                  have hpq : p = q := by
                    have hpqdist : dist p q = 0 := by
                      simpa [g8Ch23UnitAddCircleWedgePointToGlueSum,
                        Metric.glueDist] using hdist
                    exact dist_eq_zero.1 hpqdist
                  exact Or.inl (by subst q; rfl)
              | minus =>
                  have hsum :
                      dist p G8Ch23UnitAddCircleWedgePoint.basepoint +
                          dist q G8Ch23UnitAddCircleWedgePoint.basepoint =
                        0 := by
                    simpa [g8Ch23UnitAddCircleWedgePointToGlueSum,
                      Metric.gluePremetric,
                      Metric.glueDist,
                      g8Ch23UnitAddCircleCrossingToPlus,
                      g8Ch23UnitAddCircleCrossingToMinus,
                      G8Ch23UnitAddCircleWedgePoint.basepoint,
                      ciInf_unique] using hdist
                  have hpdist :
                      dist p G8Ch23UnitAddCircleWedgePoint.basepoint = 0 := by
                    have hp_nonneg :
                        0 ≤ dist p
                          G8Ch23UnitAddCircleWedgePoint.basepoint :=
                      dist_nonneg
                    have hq_nonneg :
                        0 ≤ dist q
                          G8Ch23UnitAddCircleWedgePoint.basepoint :=
                      dist_nonneg
                    nlinarith
                  have hqdist :
                      dist q G8Ch23UnitAddCircleWedgePoint.basepoint = 0 := by
                    have hp_nonneg :
                        0 ≤ dist p
                          G8Ch23UnitAddCircleWedgePoint.basepoint :=
                      dist_nonneg
                    have hq_nonneg :
                        0 ≤ dist q
                          G8Ch23UnitAddCircleWedgePoint.basepoint :=
                      dist_nonneg
                    nlinarith
                  exact Or.inr
                    ⟨dist_eq_zero.1 hpdist, dist_eq_zero.1 hqdist⟩
      | minus =>
          cases y with
          | crossing =>
              have hp :
                  p = G8Ch23UnitAddCircleWedgePoint.basepoint := by
                have hpdist :
                    dist p G8Ch23UnitAddCircleWedgePoint.basepoint = 0 := by
                  simpa [g8Ch23UnitAddCircleWedgePointToGlueSum,
                    Metric.glueDist,
                    g8Ch23UnitAddCircleCrossingToPlus,
                    g8Ch23UnitAddCircleCrossingToMinus,
                    G8Ch23UnitAddCircleWedgePoint.basepoint,
                    ciInf_unique] using hdist
                exact dist_eq_zero.1 hpdist
              exact Or.inr ⟨hp, trivial⟩
          | lobe sy q =>
              cases sy with
              | plus =>
                  have hsum :
                      dist q G8Ch23UnitAddCircleWedgePoint.basepoint +
                          dist p G8Ch23UnitAddCircleWedgePoint.basepoint =
                        0 := by
                    simpa [g8Ch23UnitAddCircleWedgePointToGlueSum,
                      Metric.gluePremetric,
                      Metric.glueDist,
                      g8Ch23UnitAddCircleCrossingToPlus,
                      g8Ch23UnitAddCircleCrossingToMinus,
                      G8Ch23UnitAddCircleWedgePoint.basepoint,
                      ciInf_unique] using hdist
                  have hpdist :
                      dist p G8Ch23UnitAddCircleWedgePoint.basepoint = 0 := by
                    have hq_nonneg :
                        0 ≤ dist q
                          G8Ch23UnitAddCircleWedgePoint.basepoint :=
                      dist_nonneg
                    have hp_nonneg :
                        0 ≤ dist p
                          G8Ch23UnitAddCircleWedgePoint.basepoint :=
                      dist_nonneg
                    nlinarith
                  have hqdist :
                      dist q G8Ch23UnitAddCircleWedgePoint.basepoint = 0 := by
                    have hq_nonneg :
                        0 ≤ dist q
                          G8Ch23UnitAddCircleWedgePoint.basepoint :=
                      dist_nonneg
                    have hp_nonneg :
                        0 ≤ dist p
                          G8Ch23UnitAddCircleWedgePoint.basepoint :=
                      dist_nonneg
                    nlinarith
                  exact Or.inr
                    ⟨dist_eq_zero.1 hpdist, dist_eq_zero.1 hqdist⟩
              | minus =>
                  have hpq : p = q := by
                    have hpqdist : dist p q = 0 := by
                      simpa [g8Ch23UnitAddCircleWedgePointToGlueSum,
                        Metric.glueDist] using hdist
                    exact dist_eq_zero.1 hpqdist
                  exact Or.inl (by subst q; rfl)

/-- The raw map into the glued metric model respects the concrete wedge
    quotient relation. -/
theorem g8Ch23UnitAddCircleWedgePointToGlue_respects_wedgeEquivalent
    {x y : G8Ch23UnitAddCircleWedgePoint}
    (h : G8Ch23UnitAddCircleWedgePoint.WedgeEquivalent x y) :
    g8Ch23UnitAddCircleWedgePointToGlue x =
      g8Ch23UnitAddCircleWedgePointToGlue y := by
  cases h with
  | inl hxy =>
      subst y
      rfl
  | inr hxy =>
      calc
        g8Ch23UnitAddCircleWedgePointToGlue x =
            g8Ch23UnitAddCircleWedgePointToGlue
              G8Ch23UnitAddCircleWedgePoint.crossing :=
          g8Ch23UnitAddCircleWedgePointToGlue_inCrossingClass hxy.left
        _ = g8Ch23UnitAddCircleWedgePointToGlue y :=
          (g8Ch23UnitAddCircleWedgePointToGlue_inCrossingClass
            hxy.right).symm

/-- Canonical map from the concrete quotient wedge carrier to Mathlib's glued
    metric space. -/
noncomputable def g8Ch23UnitAddCircleWedgeCarrierToGlue :
    G8Ch23UnitAddCircleWedgeCarrier →
      G8Ch23UnitAddCircleGluedMetricSpace :=
  Quotient.lift g8Ch23UnitAddCircleWedgePointToGlue
    (by
      intro x y h
      exact g8Ch23UnitAddCircleWedgePointToGlue_respects_wedgeEquivalent h)

@[simp] theorem g8Ch23UnitAddCircleWedgeCarrierToGlue_crossing :
    g8Ch23UnitAddCircleWedgeCarrierToGlue
        G8Ch23UnitAddCircleWedgeCarrier.crossing =
      g8Ch23UnitAddCirclePlusToGlue
        G8Ch23UnitAddCircleWedgePoint.basepoint :=
  rfl

@[simp] theorem g8Ch23UnitAddCircleWedgeCarrierToGlue_lobe_plus
    (p : UnitAddCircle) :
    g8Ch23UnitAddCircleWedgeCarrierToGlue
        (G8Ch23UnitAddCircleWedgeCarrier.lobe .plus p) =
      g8Ch23UnitAddCirclePlusToGlue p :=
  rfl

@[simp] theorem g8Ch23UnitAddCircleWedgeCarrierToGlue_lobe_minus
    (p : UnitAddCircle) :
    g8Ch23UnitAddCircleWedgeCarrierToGlue
        (G8Ch23UnitAddCircleWedgeCarrier.lobe .minus p) =
      g8Ch23UnitAddCircleMinusToGlue p :=
  rfl

/-- The quotient-carrier-to-glue map is surjective: every glued point comes
    from one of the two raw lobe summands. -/
theorem g8Ch23UnitAddCircleWedgeCarrierToGlue_surjective :
    Function.Surjective g8Ch23UnitAddCircleWedgeCarrierToGlue := by
  intro q
  letI : PseudoMetricSpace (UnitAddCircle ⊕ UnitAddCircle) :=
    Metric.gluePremetric
      g8Ch23UnitAddCircleCrossingToPlus_isometry
      g8Ch23UnitAddCircleCrossingToMinus_isometry
  letI : TopologicalSpace (UnitAddCircle ⊕ UnitAddCircle) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  rcases SeparationQuotient.surjective_mk q with ⟨u, hu⟩
  subst q
  cases u with
  | inl p =>
      exact ⟨G8Ch23UnitAddCircleWedgeCarrier.lobe .plus p, rfl⟩
  | inr p =>
      exact ⟨G8Ch23UnitAddCircleWedgeCarrier.lobe .minus p, rfl⟩

-- ============================================================
-- MAP SOURCE AND INJECTIVITY REDUCTION
-- ============================================================

/-- The theorem-backed quotient-to-glue map source.  This source closes the
    well-definedness and surjectivity side of the quotient/glue comparison.
    Injectivity is closed separately below; the remaining open work is the
    exact metric/topology transfer. -/
structure G8BookIIICh23UnitAddCircleGlueQuotientMapSource where
  glueSource : G8BookIIICh23UnitAddCircleGluedMetricGraphSource
  toGlue :
    G8Ch23UnitAddCircleWedgeCarrier →
      G8Ch23UnitAddCircleGluedMetricSpace :=
        g8Ch23UnitAddCircleWedgeCarrierToGlue
  crossing_to_basepoint :
    toGlue G8Ch23UnitAddCircleWedgeCarrier.crossing =
      g8Ch23UnitAddCirclePlusToGlue
        G8Ch23UnitAddCircleWedgePoint.basepoint
  plus_lobe_to_glue :
    ∀ p : UnitAddCircle,
      toGlue (G8Ch23UnitAddCircleWedgeCarrier.lobe .plus p) =
        g8Ch23UnitAddCirclePlusToGlue p
  minus_lobe_to_glue :
    ∀ p : UnitAddCircle,
      toGlue (G8Ch23UnitAddCircleWedgeCarrier.lobe .minus p) =
        g8Ch23UnitAddCircleMinusToGlue p
  toGlue_surjective :
    Function.Surjective toGlue
  metricTransferStillOpen : Prop
  metricTransferStillOpenEvidence : metricTransferStillOpen
  status : SpineStatus := .conditional_interface

/-- Closed source for the theorem-backed quotient-to-glue map. -/
noncomputable def g8BookIIICh23UnitAddCircleGlueQuotientMapSource :
    G8BookIIICh23UnitAddCircleGlueQuotientMapSource where
  glueSource :=
    g8BookIIICh23UnitAddCircleGluedMetricGraphSource
  crossing_to_basepoint :=
    g8Ch23UnitAddCircleWedgeCarrierToGlue_crossing
  plus_lobe_to_glue :=
    g8Ch23UnitAddCircleWedgeCarrierToGlue_lobe_plus
  minus_lobe_to_glue :=
    g8Ch23UnitAddCircleWedgeCarrierToGlue_lobe_minus
  toGlue_surjective :=
    g8Ch23UnitAddCircleWedgeCarrierToGlue_surjective
  metricTransferStillOpen :=
    True
  metricTransferStillOpenEvidence :=
    trivial
  status := .conditional_interface

/-- Target for the theorem-backed quotient-to-glue map source. -/
def G8BookIIICh23UnitAddCircleGlueQuotientMapTarget : Prop :=
  Nonempty G8BookIIICh23UnitAddCircleGlueQuotientMapSource

/-- The quotient-to-glue map target is closed. -/
theorem g8BookIIICh23UnitAddCircleGlueQuotientMap_closed :
    G8BookIIICh23UnitAddCircleGlueQuotientMapTarget :=
  ⟨g8BookIIICh23UnitAddCircleGlueQuotientMapSource⟩

/-- Injectivity of the quotient-to-glue map is the exact next comparison
    theorem needed for a bijective glue/quotient transfer. -/
def G8BookIIICh23UnitAddCircleGlueQuotientInjectivityTarget : Prop :=
  Function.Injective g8Ch23UnitAddCircleWedgeCarrierToGlue

/-- The quotient-to-glue map is injective.  Equality in Mathlib's glued metric
    model descends to equality in the concrete wedge quotient because the only
    zero-distance cross-lobe identifications are the two basepoints. -/
theorem g8Ch23UnitAddCircleWedgeCarrierToGlue_injective :
    G8BookIIICh23UnitAddCircleGlueQuotientInjectivityTarget := by
  intro a b h
  refine Quotient.inductionOn₂ a b ?_ h
  intro x y hxy
  exact
    Quotient.sound
      (g8Ch23UnitAddCircleWedgeEquivalent_of_toGlue_eq hxy)

/-- The injectivity target for the quotient-to-glue comparison is closed. -/
theorem g8BookIIICh23UnitAddCircleGlueQuotientInjectivity_closed :
    G8BookIIICh23UnitAddCircleGlueQuotientInjectivityTarget :=
  g8Ch23UnitAddCircleWedgeCarrierToGlue_injective

/-- Injectivity plus the already theorem-backed surjectivity gives the exact
    equivalence from Mathlib's glued metric model to the concrete quotient
    wedge carrier. -/
noncomputable def
    g8Ch23UnitAddCircleGlueToQuotientCarrierEquiv_of_injective
    (hInjective :
      G8BookIIICh23UnitAddCircleGlueQuotientInjectivityTarget) :
    G8Ch23UnitAddCircleGluedMetricSpace ≃
      G8Ch23UnitAddCircleWedgeCarrier :=
  (Equiv.ofBijective g8Ch23UnitAddCircleWedgeCarrierToGlue
    ⟨hInjective, g8Ch23UnitAddCircleWedgeCarrierToGlue_surjective⟩).symm

/-- Once injectivity is proved, the concrete quotient wedge carrier receives
    the metric induced from Mathlib's glued metric space. -/
noncomputable def
    g8Ch23UnitAddCircleWedgeCarrierMetricFromGlue
    (hInjective :
      G8BookIIICh23UnitAddCircleGlueQuotientInjectivityTarget) :
    MetricSpace G8Ch23UnitAddCircleWedgeCarrier :=
  MetricSpace.induced
    g8Ch23UnitAddCircleWedgeCarrierToGlue
    hInjective
    inferInstance

/-- The raw quotient-to-glue representative is continuous for the compact
    raw wedge topology. -/
theorem g8Ch23UnitAddCircleWedgePointToGlue_continuous :
    @Continuous G8Ch23UnitAddCircleWedgePoint
      G8Ch23UnitAddCircleGluedMetricSpace
      g8Ch23UnitAddCircleWedgePointCompactTopology
      inferInstance
      g8Ch23UnitAddCircleWedgePointToGlue := by
  refine continuous_coinduced_dom.mpr ?_
  have hCross :
      Continuous
        (fun _ : Unit =>
          g8Ch23UnitAddCirclePlusToGlue
            G8Ch23UnitAddCircleWedgePoint.basepoint) :=
    continuous_const
  have hPlus :
      Continuous g8Ch23UnitAddCirclePlusToGlue :=
    g8Ch23UnitAddCirclePlusToGlue_isometry.continuous
  have hMinus :
      Continuous g8Ch23UnitAddCircleMinusToGlue :=
    g8Ch23UnitAddCircleMinusToGlue_isometry.continuous
  have hRaw :
      Continuous
        (Sum.elim
          (fun _ : Unit =>
            g8Ch23UnitAddCirclePlusToGlue
              G8Ch23UnitAddCircleWedgePoint.basepoint)
          (Sum.elim
            g8Ch23UnitAddCirclePlusToGlue
            g8Ch23UnitAddCircleMinusToGlue)) :=
    Continuous.sumElim hCross (Continuous.sumElim hPlus hMinus)
  convert hRaw using 1
  funext x
  cases x with
  | inl u =>
      cases u
      rfl
  | inr y =>
      cases y with
      | inl p => rfl
      | inr p => rfl

/-- The quotient-carrier-to-glue map is continuous from the concrete quotient
    topology into Mathlib's glued metric space. -/
theorem g8Ch23UnitAddCircleWedgeCarrierToGlue_continuous :
    @Continuous G8Ch23UnitAddCircleWedgeCarrier
      G8Ch23UnitAddCircleGluedMetricSpace
      g8Ch23UnitAddCircleWedgeCarrierQuotientTopology
      inferInstance
      g8Ch23UnitAddCircleWedgeCarrierToGlue :=
  by
    letI : TopologicalSpace G8Ch23UnitAddCircleWedgePoint :=
      g8Ch23UnitAddCircleWedgePointCompactTopology
    exact
      g8Ch23UnitAddCircleWedgePointToGlue_continuous.quotient_lift
        (by
          intro x y h
          exact
            g8Ch23UnitAddCircleWedgePointToGlue_respects_wedgeEquivalent h)

/-- The quotient-carrier-to-glue map is a homeomorphism once equipped with the
    compact quotient topology. -/
theorem g8Ch23UnitAddCircleWedgeCarrierToGlue_isHomeomorph :
    @IsHomeomorph G8Ch23UnitAddCircleWedgeCarrier
      G8Ch23UnitAddCircleGluedMetricSpace
      g8Ch23UnitAddCircleWedgeCarrierQuotientTopology
      inferInstance
      g8Ch23UnitAddCircleWedgeCarrierToGlue := by
  letI : TopologicalSpace G8Ch23UnitAddCircleWedgeCarrier :=
    g8Ch23UnitAddCircleWedgeCarrierQuotientTopology
  letI : CompactSpace G8Ch23UnitAddCircleWedgeCarrier :=
    g8Ch23UnitAddCircleWedgeCarrierQuotientCompactSpace
  rw [isHomeomorph_iff_continuous_bijective]
  exact
    ⟨g8Ch23UnitAddCircleWedgeCarrierToGlue_continuous,
      ⟨g8BookIIICh23UnitAddCircleGlueQuotientInjectivity_closed,
        g8Ch23UnitAddCircleWedgeCarrierToGlue_surjective⟩⟩

/-- The quotient-carrier-to-glue map embeds the quotient topology into the
    glued metric topology. -/
theorem g8Ch23UnitAddCircleWedgeCarrierToGlue_isEmbedding :
    @Topology.IsEmbedding G8Ch23UnitAddCircleWedgeCarrier
      G8Ch23UnitAddCircleGluedMetricSpace
      g8Ch23UnitAddCircleWedgeCarrierQuotientTopology
      inferInstance
      g8Ch23UnitAddCircleWedgeCarrierToGlue :=
  by
    letI : TopologicalSpace G8Ch23UnitAddCircleWedgeCarrier :=
      g8Ch23UnitAddCircleWedgeCarrierQuotientTopology
    exact
      g8Ch23UnitAddCircleWedgeCarrierToGlue_isHomeomorph.isEmbedding

/-- The induced glued metric, with its topology replaced by the already closed
    quotient topology. -/
noncomputable def
    g8Ch23UnitAddCircleWedgeCarrierQuotientMetricFromGlue :
    MetricSpace G8Ch23UnitAddCircleWedgeCarrier := by
  letI : TopologicalSpace G8Ch23UnitAddCircleWedgeCarrier :=
    g8Ch23UnitAddCircleWedgeCarrierQuotientTopology
  exact
    Topology.IsEmbedding.comapMetricSpace
      g8Ch23UnitAddCircleWedgeCarrierToGlue
      g8Ch23UnitAddCircleWedgeCarrierToGlue_isEmbedding

/-- The quotient-topology-compatible metric has exactly the closed quotient
    topology, expressed as the induced-metric embedding into the glued metric
    model. -/
theorem
    g8Ch23UnitAddCircleWedgeCarrierQuotientMetricFromGlue_topology :
    @Topology.IsEmbedding G8Ch23UnitAddCircleWedgeCarrier
      G8Ch23UnitAddCircleGluedMetricSpace
      g8Ch23UnitAddCircleWedgeCarrierQuotientTopology
      inferInstance
      g8Ch23UnitAddCircleWedgeCarrierToGlue :=
  g8Ch23UnitAddCircleWedgeCarrierToGlue_isEmbedding

/-- The transported metric realizes the distance inherited from Mathlib's
    glued metric space. -/
theorem
    g8Ch23UnitAddCircleWedgeCarrierQuotientMetricFromGlue_dist
    (x y : G8Ch23UnitAddCircleWedgeCarrier) :
    let _ : MetricSpace G8Ch23UnitAddCircleWedgeCarrier :=
      g8Ch23UnitAddCircleWedgeCarrierQuotientMetricFromGlue
    dist
        x y =
      dist (g8Ch23UnitAddCircleWedgeCarrierToGlue x)
        (g8Ch23UnitAddCircleWedgeCarrierToGlue y) := by
  dsimp
  rfl

/-- The plus lobe remains isometric for the quotient metric transported from
    the glued metric model. -/
theorem g8Ch23UnitAddCircleWedgeCarrier_plusLobe_isometry_fromGlue :
    let _ : MetricSpace G8Ch23UnitAddCircleWedgeCarrier :=
      g8Ch23UnitAddCircleWedgeCarrierQuotientMetricFromGlue
    Isometry
      (G8Ch23UnitAddCircleWedgeCarrier.lobe .plus) := by
  dsimp
  letI : MetricSpace G8Ch23UnitAddCircleWedgeCarrier :=
    g8Ch23UnitAddCircleWedgeCarrierQuotientMetricFromGlue
  refine Isometry.of_dist_eq ?_
  intro x y
  change
    dist (g8Ch23UnitAddCircleWedgeCarrierToGlue
        (G8Ch23UnitAddCircleWedgeCarrier.lobe .plus x))
        (g8Ch23UnitAddCircleWedgeCarrierToGlue
          (G8Ch23UnitAddCircleWedgeCarrier.lobe .plus y)) =
      dist x y
  simpa using g8Ch23UnitAddCirclePlusToGlue_isometry.dist_eq x y

/-- The minus lobe remains isometric for the quotient metric transported from
    the glued metric model. -/
theorem g8Ch23UnitAddCircleWedgeCarrier_minusLobe_isometry_fromGlue :
    let _ : MetricSpace G8Ch23UnitAddCircleWedgeCarrier :=
      g8Ch23UnitAddCircleWedgeCarrierQuotientMetricFromGlue
    Isometry
      (G8Ch23UnitAddCircleWedgeCarrier.lobe .minus) := by
  dsimp
  letI : MetricSpace G8Ch23UnitAddCircleWedgeCarrier :=
    g8Ch23UnitAddCircleWedgeCarrierQuotientMetricFromGlue
  refine Isometry.of_dist_eq ?_
  intro x y
  change
    dist (g8Ch23UnitAddCircleWedgeCarrierToGlue
        (G8Ch23UnitAddCircleWedgeCarrier.lobe .minus x))
        (g8Ch23UnitAddCircleWedgeCarrierToGlue
          (G8Ch23UnitAddCircleWedgeCarrier.lobe .minus y)) =
      dist x y
  simpa using g8Ch23UnitAddCircleMinusToGlue_isometry.dist_eq x y

/-- The theorem-backed shortest-path/glued-metric evidence used by the
    concrete compact graph source. -/
def G8BookIIICh23UnitAddCircleShortestPathGraphMetricFromGlue : Prop :=
  let _ : MetricSpace G8Ch23UnitAddCircleWedgeCarrier :=
    g8Ch23UnitAddCircleWedgeCarrierQuotientMetricFromGlue
  Isometry (G8Ch23UnitAddCircleWedgeCarrier.lobe .plus) ∧
    Isometry (G8Ch23UnitAddCircleWedgeCarrier.lobe .minus) ∧
    G8Ch23UnitAddCircleWedgeCarrier.lobe .plus
        G8Ch23UnitAddCircleWedgePoint.basepoint =
      G8Ch23UnitAddCircleWedgeCarrier.lobe .minus
        G8Ch23UnitAddCircleWedgePoint.basepoint

/-- The transported glued metric is the exact two-lobe graph metric evidence:
    each lobe embeds isometrically and the basepoints are glued. -/
theorem
    g8BookIIICh23UnitAddCircleShortestPathGraphMetricFromGlue :
    G8BookIIICh23UnitAddCircleShortestPathGraphMetricFromGlue := by
  dsimp [G8BookIIICh23UnitAddCircleShortestPathGraphMetricFromGlue]
  letI : MetricSpace G8Ch23UnitAddCircleWedgeCarrier :=
    g8Ch23UnitAddCircleWedgeCarrierQuotientMetricFromGlue
  exact
    ⟨g8Ch23UnitAddCircleWedgeCarrier_plusLobe_isometry_fromGlue,
      g8Ch23UnitAddCircleWedgeCarrier_minusLobe_isometry_fromGlue,
      G8Ch23UnitAddCircleWedgeCarrier.plus_base_eq_minus_base⟩

/-- Topology/metric agreement for the transported glued metric. -/
def G8BookIIICh23UnitAddCircleTopologyMetricAgreementFromGlue : Prop :=
  @Topology.IsEmbedding G8Ch23UnitAddCircleWedgeCarrier
    G8Ch23UnitAddCircleGluedMetricSpace
    g8Ch23UnitAddCircleWedgeCarrierQuotientTopology
    inferInstance
    g8Ch23UnitAddCircleWedgeCarrierToGlue

/-- The transported glued metric has the already closed quotient topology. -/
theorem
    g8BookIIICh23UnitAddCircleTopologyMetricAgreementFromGlue :
    G8BookIIICh23UnitAddCircleTopologyMetricAgreementFromGlue :=
  g8Ch23UnitAddCircleWedgeCarrierQuotientMetricFromGlue_topology

/-- Graph-distance realization for the transported quotient metric. -/
def G8BookIIICh23UnitAddCircleGraphDistanceRealizesGlueMetric : Prop :=
  ∀ x y : G8Ch23UnitAddCircleWedgeCarrier,
    let _ : MetricSpace G8Ch23UnitAddCircleWedgeCarrier :=
      g8Ch23UnitAddCircleWedgeCarrierQuotientMetricFromGlue
    dist
        x y =
      dist (g8Ch23UnitAddCircleWedgeCarrierToGlue x)
        (g8Ch23UnitAddCircleWedgeCarrierToGlue y)

/-- The graph-distance field is realized by the transported glued metric. -/
theorem
    g8BookIIICh23UnitAddCircleGraphDistanceRealizesGlueMetric :
    G8BookIIICh23UnitAddCircleGraphDistanceRealizesGlueMetric :=
  g8Ch23UnitAddCircleWedgeCarrierQuotientMetricFromGlue_dist

/-- Exact glue-to-quotient transfer with the equivalence and metric reduced to
    injectivity of the theorem-backed quotient-to-glue map.  The topology and
    graph-distance agreement fields remain load-bearing proof obligations. -/
structure G8BookIIICh23UnitAddCircleGlueQuotientMetricTransferFromInjectiveSource where
  mapSource : G8BookIIICh23UnitAddCircleGlueQuotientMapSource
  toGlue_injective :
    G8BookIIICh23UnitAddCircleGlueQuotientInjectivityTarget
  quotientTopology :
    TopologicalSpace G8Ch23UnitAddCircleWedgeCarrier :=
      g8Ch23UnitAddCircleWedgeCarrierQuotientTopology
  quotientCompact :
    @CompactSpace G8Ch23UnitAddCircleWedgeCarrier quotientTopology
  quotientTopologyIsTwoCircleWedge : Prop
  quotientTopologyIsTwoCircleWedgeEvidence :
    quotientTopologyIsTwoCircleWedge
  compactnessFromCircleWedge : Prop
  compactnessFromCircleWedgeEvidence :
    compactnessFromCircleWedge
  shortestPathGraphMetric : Prop
  shortestPathGraphMetricEvidence :
    shortestPathGraphMetric
  topologyMetricAgreement : Prop
  topologyMetricAgreementEvidence :
    topologyMetricAgreement
  graphDistanceRealizesMetric : Prop
  graphDistanceRealizesMetricEvidence :
    graphDistanceRealizesMetric
  status : SpineStatus := .conditional_interface

namespace
  G8BookIIICh23UnitAddCircleGlueQuotientMetricTransferFromInjectiveSource

/-- The injectivity-reduced transfer source supplies the previous exact
    glue-to-quotient metric transfer source. -/
noncomputable def toGlueToQuotientMetricTransferSource
    (source :
      G8BookIIICh23UnitAddCircleGlueQuotientMetricTransferFromInjectiveSource) :
    G8BookIIICh23UnitAddCircleGlueToQuotientMetricTransferSource where
  glueSource :=
    source.mapSource.glueSource
  carrierEquiv :=
    g8Ch23UnitAddCircleGlueToQuotientCarrierEquiv_of_injective
      source.toGlue_injective
  quotientMetric :=
    g8Ch23UnitAddCircleWedgeCarrierMetricFromGlue source.toGlue_injective
  quotientTopology :=
    source.quotientTopology
  quotientCompact :=
    source.quotientCompact
  quotientTopologyIsTwoCircleWedge :=
    source.quotientTopologyIsTwoCircleWedge
  quotientTopologyIsTwoCircleWedgeEvidence :=
    source.quotientTopologyIsTwoCircleWedgeEvidence
  compactnessFromCircleWedge :=
    source.compactnessFromCircleWedge
  compactnessFromCircleWedgeEvidence :=
    source.compactnessFromCircleWedgeEvidence
  shortestPathGraphMetric :=
    source.shortestPathGraphMetric
  shortestPathGraphMetricEvidence :=
    source.shortestPathGraphMetricEvidence
  topologyMetricAgreement :=
    source.topologyMetricAgreement
  topologyMetricAgreementEvidence :=
    source.topologyMetricAgreementEvidence
  graphDistanceRealizesMetric :=
    source.graphDistanceRealizesMetric
  graphDistanceRealizesMetricEvidence :=
    source.graphDistanceRealizesMetricEvidence
  status := source.status

end G8BookIIICh23UnitAddCircleGlueQuotientMetricTransferFromInjectiveSource

/-- Target for the injectivity-reduced glue/quotient metric transfer. -/
def
    G8BookIIICh23UnitAddCircleGlueQuotientMetricTransferFromInjectiveTarget :
    Prop :=
  Nonempty
    G8BookIIICh23UnitAddCircleGlueQuotientMetricTransferFromInjectiveSource

/-- The injectivity-reduced transfer target implies the full concrete compact
    metric graph target through the previous transfer adapter. -/
theorem
    g8BookIIICh23UnitAddCircleGlueQuotientMetricTransferFromInjectiveTarget_toConcreteTarget
    (target :
      G8BookIIICh23UnitAddCircleGlueQuotientMetricTransferFromInjectiveTarget) :
    G8BookIIICh23ConcreteCompactMetricGraphTarget := by
  rcases target with ⟨source⟩
  exact
    g8BookIIICh23UnitAddCircleGlueToQuotientMetricTransferTarget_toConcreteTarget
      ⟨source.toGlueToQuotientMetricTransferSource⟩

/-- The injectivity-reduced glue/quotient metric transfer is now closed from
    the theorem-backed quotient topology, compactness, induced glued metric,
    lobe isometries, topology/metric embedding, and graph-distance
    realization. -/
noncomputable def
    g8BookIIICh23UnitAddCircleGlueQuotientMetricTransferFromInjectiveSource :
    G8BookIIICh23UnitAddCircleGlueQuotientMetricTransferFromInjectiveSource
    where
  mapSource :=
    g8BookIIICh23UnitAddCircleGlueQuotientMapSource
  toGlue_injective :=
    g8BookIIICh23UnitAddCircleGlueQuotientInjectivity_closed
  quotientTopology :=
    g8Ch23UnitAddCircleWedgeCarrierQuotientTopology
  quotientCompact :=
    g8Ch23UnitAddCircleWedgeCarrierQuotientCompactSpace
  quotientTopologyIsTwoCircleWedge :=
    G8BookIIICh23UnitAddCircleQuotientCompactTopologySource.quotientTopologyIsTwoCircleWedge
      g8BookIIICh23UnitAddCircleQuotientCompactTopologySource
  quotientTopologyIsTwoCircleWedgeEvidence :=
    G8BookIIICh23UnitAddCircleQuotientCompactTopologySource.quotientTopologyIsTwoCircleWedgeEvidence
      g8BookIIICh23UnitAddCircleQuotientCompactTopologySource
  compactnessFromCircleWedge :=
    G8BookIIICh23UnitAddCircleQuotientCompactTopologySource.compactnessFromCircleWedge
      g8BookIIICh23UnitAddCircleQuotientCompactTopologySource
  compactnessFromCircleWedgeEvidence :=
    G8BookIIICh23UnitAddCircleQuotientCompactTopologySource.compactnessFromCircleWedgeEvidence
      g8BookIIICh23UnitAddCircleQuotientCompactTopologySource
  shortestPathGraphMetric :=
    G8BookIIICh23UnitAddCircleShortestPathGraphMetricFromGlue
  shortestPathGraphMetricEvidence :=
    g8BookIIICh23UnitAddCircleShortestPathGraphMetricFromGlue
  topologyMetricAgreement :=
    G8BookIIICh23UnitAddCircleTopologyMetricAgreementFromGlue
  topologyMetricAgreementEvidence :=
    g8BookIIICh23UnitAddCircleTopologyMetricAgreementFromGlue
  graphDistanceRealizesMetric :=
    G8BookIIICh23UnitAddCircleGraphDistanceRealizesGlueMetric
  graphDistanceRealizesMetricEvidence :=
    g8BookIIICh23UnitAddCircleGraphDistanceRealizesGlueMetric
  status := .conditional_interface

/-- The injectivity-reduced glue/quotient metric transfer target is closed. -/
theorem
    g8BookIIICh23UnitAddCircleGlueQuotientMetricTransferFromInjective_closed :
    G8BookIIICh23UnitAddCircleGlueQuotientMetricTransferFromInjectiveTarget :=
  ⟨g8BookIIICh23UnitAddCircleGlueQuotientMetricTransferFromInjectiveSource⟩

/-- The concrete Ch.23 `UnitAddCircle` compact metric graph target is closed
    by the injectivity-reduced glued-metric transfer. -/
theorem
    g8BookIIICh23ConcreteCompactMetricGraphTarget_from_glueQuotientMetricTransfer :
    G8BookIIICh23ConcreteCompactMetricGraphTarget :=
  g8BookIIICh23UnitAddCircleGlueQuotientMetricTransferFromInjectiveTarget_toConcreteTarget
    g8BookIIICh23UnitAddCircleGlueQuotientMetricTransferFromInjective_closed

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- A hypothetical surjective-but-not-injective comparison is incompatible with
    the closed injectivity theorem. -/
structure G8BookIIICh23GlueQuotientSurjectiveWithoutInjective where
  mapSource : G8BookIIICh23UnitAddCircleGlueQuotientMapSource
  noInjectivity :
    ¬ G8BookIIICh23UnitAddCircleGlueQuotientInjectivityTarget

/-- Missing injectivity refutes the closed injectivity theorem. -/
theorem
    G8BookIIICh23GlueQuotientSurjectiveWithoutInjective.refutesInjectivity
    (gap : G8BookIIICh23GlueQuotientSurjectiveWithoutInjective) :
    ¬ G8BookIIICh23UnitAddCircleGlueQuotientInjectivityTarget :=
  gap.noInjectivity

/-- The closed injectivity theorem rules out a surjective-only gap object. -/
theorem
    G8BookIIICh23GlueQuotientSurjectiveWithoutInjective.contradiction
    (gap : G8BookIIICh23GlueQuotientSurjectiveWithoutInjective) :
    False :=
  gap.noInjectivity
    g8BookIIICh23UnitAddCircleGlueQuotientInjectivity_closed

/-- A candidate injectivity-reduced transfer with wrong shortest-path metric
    evidence refutes the concrete source it is trying to assemble. -/
structure G8BookIIICh23GlueQuotientWrongShortestPathMetric
    (source :
      G8BookIIICh23UnitAddCircleGlueQuotientMetricTransferFromInjectiveSource)
    where
  noShortestPathMetric : ¬ source.shortestPathGraphMetric

/-- The shortest-path metric field is load-bearing in the transfer. -/
theorem
    G8BookIIICh23GlueQuotientWrongShortestPathMetric.refutesTransfer
    {source :
      G8BookIIICh23UnitAddCircleGlueQuotientMetricTransferFromInjectiveSource}
    (gap :
      G8BookIIICh23GlueQuotientWrongShortestPathMetric source) :
    False :=
  gap.noShortestPathMetric source.shortestPathGraphMetricEvidence

end Tau.BookIII.Bridge
