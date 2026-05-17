import TauLib.BookI.Polarity.NthPrime
import TauLib.BookIII.Spectral.CRT

/-!
# TauLib.BookIII.Bridge.G8ArithmeticCofinality

G8a arithmetic cofinality scaffold for the RH bridge proof program.

This module isolates the theorem-backed part of the primorial/profinite
arithmetic story:

* primorial stages form a compatible inverse system;
* prime coordinates are covered at sufficiently deep stages;
* any finite modulus that actually divides a primorial stage has compatible
  projection from that stage.

It deliberately does **not** claim that arbitrary finite moduli divide a
primorial.  The safe G8a object is a finite arithmetic support equipped with
an explicit divisibility witness.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

open Tau.Polarity Tau.Boundary Tau.Coordinates Tau.Denotation
open Tau.BookIII.Spectral

-- ============================================================
-- G8A FINITE SUPPORTS
-- ============================================================

/-- A finite arithmetic support that is genuinely visible at a primorial stage.

The divisibility witness is the important field: it is what makes projection
from the tau stage to the finite modulus theorem-backed. -/
structure TauFiniteArithmeticSupport where
  modulus : Nat
  stage : Nat
  modulus_dvd_stage : modulus ∣ primorial stage

/-- Stage projection along the primorial tower. -/
def PrimorialStageProjection (x k : Nat) : Nat :=
  reduce x k

/-- Residue of an integer against a finite arithmetic support. -/
def TauFiniteArithmeticSupport.residue
    (S : TauFiniteArithmeticSupport) (x : Nat) : Nat :=
  x % S.modulus

/-- The primorial projection to a stage preserves every finite support whose
    modulus divides that stage. -/
theorem finiteSupport_projection_compatible
    (S : TauFiniteArithmeticSupport) (x : Nat) :
    S.residue (PrimorialStageProjection x S.stage) = S.residue x := by
  unfold TauFiniteArithmeticSupport.residue PrimorialStageProjection reduce
  exact mod_mod_of_dvd x S.modulus (primorial S.stage) S.modulus_dvd_stage

/-- A finite modulus is covered by the primorial tower when it comes with a
    divisibility witness into some primorial stage. -/
def G8aFiniteSupportCovered (modulus : Nat) : Prop :=
  ∃ S : TauFiniteArithmeticSupport, S.modulus = modulus

-- ============================================================
-- THEOREM-BACKED PRIMORIAL TOWER COMPATIBILITY
-- ============================================================

/-- Primorial stage divisibility: deeper stages project to shallower stages. -/
theorem g8a_stageDivides_of_le {k l : Nat} (h : k ≤ l) :
    primorial k ∣ primorial l :=
  primorial_dvd h

/-- Primorial projections compose along the tower. -/
theorem g8a_projection_compat (x : Nat) {k l : Nat} (h : k ≤ l) :
    PrimorialStageProjection (PrimorialStageProjection x l) k =
      PrimorialStageProjection x k := by
  unfold PrimorialStageProjection
  exact reduction_compat x h

/-- The i-th prime coordinate is visible at every stage deep enough to include
    it. -/
theorem g8a_primeCoordinate_dvd_stage {i k : Nat} (h : i + 1 ≤ k) :
    nth_prime (i + 1) ∣ primorial k :=
  nth_prime_dvd_primorial h

/-- Prime-coordinate support as a finite arithmetic support. -/
def primeCoordinateSupport (i k : Nat) (h : i + 1 ≤ k) :
    TauFiniteArithmeticSupport where
  modulus := nth_prime (i + 1)
  stage := k
  modulus_dvd_stage := g8a_primeCoordinate_dvd_stage h

/-- Prime coordinates are covered finite supports. -/
theorem g8a_primeCoordinate_covered {i k : Nat} (h : i + 1 ≤ k) :
    G8aFiniteSupportCovered (nth_prime (i + 1)) :=
  ⟨primeCoordinateSupport i k h, rfl⟩

/-- CRT residue after projection to a deep enough primorial stage agrees with
    the direct prime residue. -/
theorem g8a_primeResidue_projection_compatible
    (x : Nat) {i k : Nat} (h : i + 1 ≤ k) :
    (PrimorialStageProjection x k) % nth_prime (i + 1) =
      x % nth_prime (i + 1) := by
  unfold PrimorialStageProjection reduce
  exact mod_mod_of_dvd x (nth_prime (i + 1)) (primorial k)
    (g8a_primeCoordinate_dvd_stage h)

-- ============================================================
-- G8A CONTEXT
-- ============================================================

/-- Explicit G8a context consumed by later G8 bridge statements.

This is the arithmetic/profinite part only.  It contains no analytic
completion, no xi-divisor statement, and no zero-set transfer. -/
structure G8aArithmeticCofinalityContext where
  stageDivides :
    ∀ {k l : Nat}, k ≤ l → primorial k ∣ primorial l
  projectionCompat :
    ∀ (x : Nat) {k l : Nat}, k ≤ l →
      PrimorialStageProjection (PrimorialStageProjection x l) k =
        PrimorialStageProjection x k
  primeCoordinateCovered :
    ∀ {i k : Nat}, i + 1 ≤ k →
      G8aFiniteSupportCovered (nth_prime (i + 1))
  finiteSupportProjectionCompat :
    ∀ (S : TauFiniteArithmeticSupport) (x : Nat),
      S.residue (PrimorialStageProjection x S.stage) = S.residue x

/-- The theorem-backed primorial G8a context. -/
def primorialG8aContext : G8aArithmeticCofinalityContext where
  stageDivides := fun {k} {l} h => g8a_stageDivides_of_le (k := k) (l := l) h
  projectionCompat := fun x {k} {l} h =>
    g8a_projection_compat x (k := k) (l := l) h
  primeCoordinateCovered := fun {i} {k} h =>
    g8a_primeCoordinate_covered (i := i) (k := k) h
  finiteSupportProjectionCompat := finiteSupport_projection_compatible

/-- Guardrail predicate: G8a supplies arithmetic cofinality only for explicit
    finite supports.  Analytic completion uniqueness remains a separate G8
    obligation. -/
def G8aNoZeroDivisorTransferClaim : Prop :=
  True

/-- The guardrail is theorem-backed and intentionally content-light: this
    module exports no zero-divisor transfer theorem. -/
theorem g8a_noZeroDivisorTransferClaim :
    G8aNoZeroDivisorTransferClaim :=
  trivial

end Tau.BookIII.Bridge
