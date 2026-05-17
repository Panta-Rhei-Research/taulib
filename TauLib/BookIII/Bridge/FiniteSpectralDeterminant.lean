import TauLib.BookIII.Bridge.LemniscateOperatorSpine
import TauLib.BookIII.Bridge.O3Status

/-!
# TauLib.BookIII.Bridge.FiniteSpectralDeterminant

G6 finite determinant scaffold over the existing nonzero lemniscate modes.

This file is deliberately finite and τ-native.  It does not define a Fredholm
determinant, a zeta-regularized determinant, or the O3 correspondence.  Its
purpose is to give the future G6 proof program a concrete finite diagonal
object before any infinite or regularized determinant work begins.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

open Tau.BookIII.Doors

/-- Nonzero mode `i` represented as the actual lemniscate mode `i+1`.
    The zero mode is intentionally excluded from this finite scaffold. -/
def nonzeroLemniscateMode (i : Nat) : Nat :=
  i + 1

/-- Eigenvalue of the `i`th nonzero finite mode. -/
def nonzeroLemniscateEigenvalue (i : Nat) : Nat :=
  lemniscate_eigenvalue (nonzeroLemniscateMode i)

/-- Integer-valued nonzero finite eigenvalue, used for signed characteristic
    factors without importing a matrix or field API. -/
def nonzeroLemniscateEigenvalueInt (i : Nat) : Int :=
  Int.ofNat (nonzeroLemniscateEigenvalue i)

/-- Characteristic-style finite diagonal factor `λ_i - z`.
    This is a finite scaffold factor, not the regularized O3 determinant. -/
def finiteSpectralFactor (z : Int) (i : Nat) : Int :=
  nonzeroLemniscateEigenvalueInt i - z

/-- Recursive τ-native product of nonzero diagonal factors up to cutoff `N`.
    `N = 0` gives the empty product, and `N+1` includes mode `N+1`. -/
def finiteDiagonalDeterminant (z : Int) : Nat → Int
  | 0 => 1
  | n + 1 => finiteSpectralFactor z n * finiteDiagonalDeterminant z n

/-- Status-tagged finite determinant scaffold. -/
structure FiniteDeterminantScaffold where
  cutoff : Nat
  spectralParameter : Int
  value : Int := finiteDiagonalDeterminant spectralParameter cutoff
  determinantClass : DeterminantClass := .finite
  zeroModePolicy : ZeroModePolicy := .excluded
  status : O3ObligationStatus := .finiteCheck

/-- The nonzero mode is definitionally successor-shaped. -/
theorem nonzeroLemniscateMode_formula (i : Nat) :
    nonzeroLemniscateMode i = i + 1 := rfl

/-- The nonzero-mode eigenvalue inherits the current `n^2` approximation. -/
theorem nonzeroLemniscateEigenvalue_formula (i : Nat) :
    nonzeroLemniscateEigenvalue i = (i + 1) * (i + 1) := rfl

/-- Empty finite diagonal product. -/
theorem finiteDiagonalDeterminant_zero (z : Int) :
    finiteDiagonalDeterminant z 0 = 1 := rfl

/-- Recursive product step for the finite diagonal scaffold. -/
theorem finiteDiagonalDeterminant_succ (z : Int) (n : Nat) :
    finiteDiagonalDeterminant z (n + 1) =
      finiteSpectralFactor z n * finiteDiagonalDeterminant z n := rfl

/-- A scaffold instance computes to the finite determinant at its cutoff. -/
theorem finiteDeterminantScaffold_value
    (cutoff : Nat) (spectralParameter : Int) :
    ({ cutoff := cutoff, spectralParameter := spectralParameter } :
        FiniteDeterminantScaffold).value =
      finiteDiagonalDeterminant spectralParameter cutoff := rfl

end Tau.BookIII.Bridge
