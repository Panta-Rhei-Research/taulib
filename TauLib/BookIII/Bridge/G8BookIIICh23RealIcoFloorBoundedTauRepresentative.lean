import TauLib.BookIII.Bridge.G8BookIIICh23RealIcoBoundedTauLiftSource

/-!
# TauLib.BookIII.Bridge.G8BookIIICh23RealIcoFloorBoundedTauRepresentative

Theorem-backed bounded Cauchy tau-angle representatives for real-Ico periods.

For a period `x ∈ [0,1)`, the lower grid representatives

```text
q_n = floor (x * (n + 1)) / (n + 1)
```

lie in `[0,1]` and converge to `x`.  Transporting this rational Cauchy
sequence through the established `ℚ → TauRatQ → TauRealQ` bridge gives a
bounded tau-angle representative of `tauRealQRingEquivReal.symm x`.

The zero period is selected by the previously theorem-backed zero
representative, so the source is definitionally basepoint-preserving.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

open Tau.Boundary

-- ============================================================
-- FLOOR APPROXIMANTS IN THE REAL HALF-OPEN UNIT INTERVAL
-- ============================================================

/-- Lower rational grid approximant for a real-Ico period. -/
noncomputable def g8BookIIICh23RealIcoFloorApprox
    (x : G8BookIIICh23UnitRealIco) (n : ℕ) : ℚ :=
  (Nat.floor (x.1 * ((n + 1 : ℕ) : ℝ)) : ℚ) /
    ((n + 1 : ℕ) : ℚ)

/-- The floor approximants are nonnegative. -/
theorem g8BookIIICh23RealIcoFloorApprox_nonneg
    (x : G8BookIIICh23UnitRealIco) (n : ℕ) :
    0 ≤ g8BookIIICh23RealIcoFloorApprox x n := by
  dsimp [g8BookIIICh23RealIcoFloorApprox]
  apply div_nonneg
  · exact_mod_cast Nat.zero_le
      (Nat.floor (x.1 * ((n + 1 : ℕ) : ℝ)))
  · exact_mod_cast Nat.zero_le (n + 1)

/-- The floor approximants stay below one. -/
theorem g8BookIIICh23RealIcoFloorApprox_le_one
    (x : G8BookIIICh23UnitRealIco) (n : ℕ) :
    g8BookIIICh23RealIcoFloorApprox x n ≤ 1 := by
  have hxlt : x.1 < 1 := by
    simpa using x.2.2
  have hden_pos : 0 < ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_pos n
  have ha_nonneg :
      0 ≤ x.1 * ((n + 1 : ℕ) : ℝ) := by
    exact mul_nonneg x.2.1 hden_pos.le
  have ha_lt :
      x.1 * ((n + 1 : ℕ) : ℝ) < ((n + 1 : ℕ) : ℝ) := by
    nlinarith [mul_lt_mul_of_pos_right hxlt hden_pos]
  have hfloor_lt :
      Nat.floor (x.1 * ((n + 1 : ℕ) : ℝ)) < n + 1 := by
    exact (Nat.floor_lt ha_nonneg).2 ha_lt
  have hfloor_le :
      (Nat.floor (x.1 * ((n + 1 : ℕ) : ℝ)) : ℚ) ≤
        ((n + 1 : ℕ) : ℚ) := by
    exact_mod_cast Nat.le_of_lt hfloor_lt
  have hden_pos_q : 0 < ((n + 1 : ℕ) : ℚ) := by
    exact_mod_cast Nat.succ_pos n
  dsimp [g8BookIIICh23RealIcoFloorApprox]
  rw [div_le_iff₀ hden_pos_q]
  simpa using hfloor_le

/-- The lower grid approximant is below the target real period. -/
theorem g8BookIIICh23RealIcoFloorApprox_cast_le_period
    (x : G8BookIIICh23UnitRealIco) (n : ℕ) :
    ((g8BookIIICh23RealIcoFloorApprox x n : ℚ) : ℝ) ≤ x.1 := by
  have hden_pos : 0 < ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_pos n
  have ha_nonneg :
      0 ≤ x.1 * ((n + 1 : ℕ) : ℝ) := by
    exact mul_nonneg x.2.1 hden_pos.le
  have hfloor_le :
      (Nat.floor (x.1 * ((n + 1 : ℕ) : ℝ)) : ℝ) ≤
        x.1 * ((n + 1 : ℕ) : ℝ) :=
    Nat.floor_le ha_nonneg
  have hdiv :
      (Nat.floor (x.1 * ((n + 1 : ℕ) : ℝ)) : ℝ) /
          ((n + 1 : ℕ) : ℝ) ≤ x.1 := by
    rw [div_le_iff₀ hden_pos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hfloor_le
  simpa [g8BookIIICh23RealIcoFloorApprox] using hdiv

/-- The floor approximant is within one mesh length from the target period. -/
theorem g8BookIIICh23RealIcoPeriod_sub_floorApprox_lt
    (x : G8BookIIICh23UnitRealIco) (n : ℕ) :
    x.1 - ((g8BookIIICh23RealIcoFloorApprox x n : ℚ) : ℝ) <
      (((n + 1 : ℕ) : ℝ))⁻¹ := by
  have hden_pos : 0 < ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_pos n
  have hfloor :
      x.1 * ((n + 1 : ℕ) : ℝ) <
        (Nat.floor (x.1 * ((n + 1 : ℕ) : ℝ)) : ℝ) + 1 :=
    Nat.lt_floor_add_one (x.1 * ((n + 1 : ℕ) : ℝ))
  have htarget :
      x.1 <
        ((Nat.floor (x.1 * ((n + 1 : ℕ) : ℝ)) : ℝ) + 1) /
          ((n + 1 : ℕ) : ℝ) := by
    rw [lt_div_iff₀ hden_pos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hfloor
  have hmesh :
      ((Nat.floor (x.1 * ((n + 1 : ℕ) : ℝ)) : ℝ) + 1) /
          ((n + 1 : ℕ) : ℝ) =
        ((Nat.floor (x.1 * ((n + 1 : ℕ) : ℝ)) : ℝ) /
          ((n + 1 : ℕ) : ℝ)) +
        (((n + 1 : ℕ) : ℝ))⁻¹ := by
    field_simp [ne_of_gt hden_pos]
  rw [hmesh] at htarget
  have hsub :
      x.1 -
          ((Nat.floor (x.1 * ((n + 1 : ℕ) : ℝ)) : ℝ) /
            ((n + 1 : ℕ) : ℝ)) <
        (((n + 1 : ℕ) : ℝ))⁻¹ := by
    linarith
  simpa [g8BookIIICh23RealIcoFloorApprox] using hsub

/-- The floor approximants converge to the target real period. -/
theorem g8BookIIICh23RealIcoFloorApprox_near
    (x : G8BookIIICh23UnitRealIco) :
    ∀ ε > 0, ∃ i, ∀ j ≥ i,
      |((g8BookIIICh23RealIcoFloorApprox x j : ℚ) : ℝ) - x.1| < ε := by
  intro ε hε
  obtain ⟨m, hm_pos, hm_inv_lt⟩ := Real.exists_nat_pos_inv_lt hε
  refine ⟨m, ?_⟩
  intro j hj
  have hle_period :=
    g8BookIIICh23RealIcoFloorApprox_cast_le_period x j
  have habs :
      |((g8BookIIICh23RealIcoFloorApprox x j : ℚ) : ℝ) - x.1| =
        x.1 - ((g8BookIIICh23RealIcoFloorApprox x j : ℚ) : ℝ) := by
    rw [abs_of_nonpos]
    · ring
    · exact sub_nonpos.mpr hle_period
  have hmesh :=
    g8BookIIICh23RealIcoPeriod_sub_floorApprox_lt x j
  have hm_pos_real : 0 < (m : ℝ) := by
    exact_mod_cast hm_pos
  have hm_le_j_succ : (m : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.le_trans hj (Nat.le_succ j))
  have hinv_le :
      (((j + 1 : ℕ) : ℝ))⁻¹ ≤ (m : ℝ)⁻¹ := by
    simpa [one_div] using
      one_div_le_one_div_of_le hm_pos_real hm_le_j_succ
  rw [habs]
  exact lt_of_lt_of_le hmesh (le_trans hinv_le (le_of_lt hm_inv_lt))

-- ============================================================
-- TRANSPORT THROUGH THE TAU CAUCHY BRIDGE
-- ============================================================

/-- Cauchy rational sequence carried by the floor approximants. -/
noncomputable def g8BookIIICh23RealIcoFloorApproxCauSeq
    (x : G8BookIIICh23UnitRealIco) :
    CauSeq ℚ (abs : ℚ → ℚ) :=
  ⟨fun n => g8BookIIICh23RealIcoFloorApprox x n,
    (Real.of_near
      (fun n => g8BookIIICh23RealIcoFloorApprox x n)
      x.1
      (g8BookIIICh23RealIcoFloorApprox_near x)).choose⟩

/-- The floor Cauchy sequence represents the original real period. -/
theorem g8BookIIICh23RealIcoFloorApproxCauSeq_real_mk
    (x : G8BookIIICh23UnitRealIco) :
    Real.mk (g8BookIIICh23RealIcoFloorApproxCauSeq x) = x.1 :=
  (Real.of_near
    (fun n => g8BookIIICh23RealIcoFloorApprox x n)
    x.1
    (g8BookIIICh23RealIcoFloorApprox_near x)).choose_spec

/-- TauRatQ Cauchy sequence obtained from the floor rational sequence. -/
noncomputable def g8BookIIICh23RealIcoFloorTauRatQCauSeq
    (x : G8BookIIICh23UnitRealIco) :
    CauSeq TauRatQ (abs : TauRatQ → TauRatQ) :=
  cauSeqTauRatQOfCauSeqQ
    (g8BookIIICh23RealIcoFloorApproxCauSeq x)

/-- Cauchy tau-real obtained from the transported floor sequence. -/
noncomputable def g8BookIIICh23RealIcoFloorCauchyTauReal
    (x : G8BookIIICh23UnitRealIco) : CauchyTauReal :=
  cauchyTauRealOfCauSeq
    (g8BookIIICh23RealIcoFloorTauRatQCauSeq x)

/-- The transported TauRat representative at index `n` has the expected
    rational value. -/
theorem g8BookIIICh23RealIcoFloorTauRatApprox_toRat
    (x : G8BookIIICh23UnitRealIco) (n : ℕ) :
    ((g8BookIIICh23RealIcoFloorCauchyTauReal x).val.approx n).toRat =
      g8BookIIICh23RealIcoFloorApprox x n := by
  dsimp [g8BookIIICh23RealIcoFloorCauchyTauReal,
    g8BookIIICh23RealIcoFloorTauRatQCauSeq]
  have hq :
      (Quotient.out
          ((cauSeqTauRatQOfCauSeqQ
              (g8BookIIICh23RealIcoFloorApproxCauSeq x)) n)).toQ =
        (cauSeqTauRatQOfCauSeqQ
              (g8BookIIICh23RealIcoFloorApproxCauSeq x)) n :=
    Quotient.out_eq _
  have hrat :
      (Quotient.out
          ((cauSeqTauRatQOfCauSeqQ
              (g8BookIIICh23RealIcoFloorApproxCauSeq x)) n)).toRat =
        ((cauSeqTauRatQOfCauSeqQ
              (g8BookIIICh23RealIcoFloorApproxCauSeq x)) n).toRat :=
    congrArg TauRatQ.toRat hq
  have hseq :
      ((cauSeqTauRatQOfCauSeqQ
              (g8BookIIICh23RealIcoFloorApproxCauSeq x)) n).toRat =
        g8BookIIICh23RealIcoFloorApprox x n := by
    rw [cauSeqTauRatQOfCauSeqQ_apply, TauRatQ.symm_toRat]
    rfl
  change
    (Quotient.out
        ((cauSeqTauRatQOfCauSeqQ
            (g8BookIIICh23RealIcoFloorApproxCauSeq x)) n)).toRat =
      g8BookIIICh23RealIcoFloorApprox x n
  exact hrat.trans hseq

/-- The floor Cauchy tau-real is a bounded tau angle. -/
noncomputable def g8BookIIICh23RealIcoFloorBoundedTauAngle
    (x : G8BookIIICh23UnitRealIco) : BoundedTauAngle where
  angle := (g8BookIIICh23RealIcoFloorCauchyTauReal x).val
  bounded_one := by
    intro n
    rw [TauRat.toRat_abs,
      g8BookIIICh23RealIcoFloorTauRatApprox_toRat]
    have hnonneg :=
      g8BookIIICh23RealIcoFloorApprox_nonneg x n
    have hle_one :=
      g8BookIIICh23RealIcoFloorApprox_le_one x n
    exact abs_le.mpr ⟨by linarith, hle_one⟩

/-- The floor bounded tau angle is Cauchy. -/
theorem g8BookIIICh23RealIcoFloorBoundedTauAngle_cauchy
    (x : G8BookIIICh23UnitRealIco) :
    BoundedTauAngle.IsCauchy
      (g8BookIIICh23RealIcoFloorBoundedTauAngle x) :=
  (g8BookIIICh23RealIcoFloorCauchyTauReal x).isCauchy

/-- The floor bounded tau angle represents the canonical `TauRealQ` value. -/
theorem g8BookIIICh23RealIcoFloorBoundedTauAngle_quotient_eq
    (x : G8BookIIICh23UnitRealIco) :
    G8BookIIICh23BoundedCauchyAngleRepresentsTauRealQ
      x
      (g8BookIIICh23RealIcoFloorBoundedTauAngle x)
      (g8BookIIICh23RealIcoFloorBoundedTauAngle_cauchy x) := by
  dsimp [G8BookIIICh23BoundedCauchyAngleRepresentsTauRealQ,
    G8BookIIICh23CauchyBoundedAngle.toTauRealQ,
    g8BookIIICh23RealIcoFloorBoundedTauAngle,
    g8BookIIICh23UnitRealIcoTauRealQ]
  have hCauchy :
      Real.ringEquivCauchy x.1 =
        CauSeq.Completion.mk
          (g8BookIIICh23RealIcoFloorApproxCauSeq x) := by
    rw [← g8BookIIICh23RealIcoFloorApproxCauSeq_real_mk x]
    rfl
  rw [tauRealQRingEquivReal_symm_apply, hCauchy]
  rfl

/-- Pointwise bounded Cauchy representative from floor approximants. -/
noncomputable def g8BookIIICh23RealIcoFloorBoundedTauRepresentative
    (x : G8BookIIICh23UnitRealIco) :
    G8BookIIICh23BoundedCauchyTauRepresentative x where
  angle := g8BookIIICh23RealIcoFloorBoundedTauAngle x
  cauchy := g8BookIIICh23RealIcoFloorBoundedTauAngle_cauchy x
  quotient_eq := g8BookIIICh23RealIcoFloorBoundedTauAngle_quotient_eq x

-- ============================================================
-- BASEPOINT-PRESERVING GLOBAL SOURCE
-- ============================================================

/-- The global representative chooses the exact zero representative at the
    basepoint and the floor representative elsewhere. -/
noncomputable def g8BookIIICh23RealIcoBoundedTauRepresentative
    (x : G8BookIIICh23UnitRealIco) :
    G8BookIIICh23BoundedCauchyTauRepresentative x :=
  if h : x = g8BookIIICh23UnitRealIcoZero then
    h.symm ▸ g8BookIIICh23UnitRealIcoZeroBoundedTauRepresentative
  else
    g8BookIIICh23RealIcoFloorBoundedTauRepresentative x

/-- The selected global representative preserves the basepoint definitionally. -/
theorem g8BookIIICh23RealIcoBoundedTauRepresentative_zero :
    g8BookIIICh23RealIcoBoundedTauRepresentative
        g8BookIIICh23UnitRealIcoZero =
      g8BookIIICh23UnitRealIcoZeroBoundedTauRepresentative := by
  dsimp [g8BookIIICh23RealIcoBoundedTauRepresentative]
  simp

/-- The selected global representative has zero angle at the basepoint. -/
theorem g8BookIIICh23RealIcoBoundedTauRepresentative_zero_angle :
    (g8BookIIICh23RealIcoBoundedTauRepresentative
        g8BookIIICh23UnitRealIcoZero).angle =
      BoundedTauAngle.zero := by
  rw [g8BookIIICh23RealIcoBoundedTauRepresentative_zero]
  rfl

/-- The theorem-backed bounded representative source for every real-Ico
    period. -/
noncomputable def
    g8BookIIICh23RealIcoBoundedCauchyTauRepresentativeSource :
    G8BookIIICh23RealIcoBoundedCauchyTauRepresentativeSource where
  representative := g8BookIIICh23RealIcoBoundedTauRepresentative
  zero_preserving :=
    g8BookIIICh23RealIcoBoundedTauRepresentative_zero_angle
  boundedRepresentativeConstruction :=
    ∀ x : G8BookIIICh23UnitRealIco,
      Nonempty (G8BookIIICh23BoundedCauchyTauRepresentative x)
  boundedRepresentativeConstructionEvidence := by
    intro x
    exact ⟨g8BookIIICh23RealIcoBoundedTauRepresentative x⟩
  quotientRepresentativeAgreement :=
    ∀ x : G8BookIIICh23UnitRealIco,
      G8BookIIICh23BoundedCauchyAngleRepresentsTauRealQ
        x
        (g8BookIIICh23RealIcoBoundedTauRepresentative x).angle
        (g8BookIIICh23RealIcoBoundedTauRepresentative x).cauchy
  quotientRepresentativeAgreementEvidence := by
    intro x
    exact (g8BookIIICh23RealIcoBoundedTauRepresentative x).quotient_eq
  status := .definition

/-- Closed target: bounded Cauchy tau representatives exist for all real-Ico
    periods, with the basepoint preserved. -/
theorem
    g8BookIIICh23RealIcoBoundedCauchyTauRepresentativeSourceTarget_closed :
    G8BookIIICh23RealIcoBoundedCauchyTauRepresentativeSourceTarget :=
  ⟨g8BookIIICh23RealIcoBoundedCauchyTauRepresentativeSource⟩

/-- Closed controlled real-Ico bounded tau-angle lift target obtained from the
    constructed representatives. -/
theorem
    g8BookIIICh23RealIcoCauchyBoundedTauAngleLiftTarget_closed :
    G8BookIIICh23RealIcoCauchyBoundedTauAngleLiftTarget :=
  g8BookIIICh23RealIcoBoundedCauchyTauRepresentativeSourceTarget_toLiftTarget
    g8BookIIICh23RealIcoBoundedCauchyTauRepresentativeSourceTarget_closed

end Tau.BookIII.Bridge
