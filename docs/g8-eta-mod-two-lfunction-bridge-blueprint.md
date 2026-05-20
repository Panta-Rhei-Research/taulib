# G8 Eta Mod-Two L-Function Bridge Blueprint

This note records the Lane A zero-height eta bridge as ordinary proof
scaffolding. It is private implementation guidance, not a new public theorem
claim.

## Lemma Chain

1. Define the mod-two eta coefficient by odd positive indices carrying `+1`
   and even positive indices carrying `-1`.
2. The signed partial sums over `1..N` are binary:
   `A(2m) = 0` and `A(2m+1) = 1`, hence `A(N) = O(1)`.
3. The shifted mod-two coefficient satisfies
   `g8EtaModTwoNatCoeff (n + 1) = (-1)^n`, so the naive conditional eta
   partial sums are exactly the complexification of the concrete real eta
   partial sums already used in the zero-height corridor.
4. Therefore the concrete conditional eta-series agreement is theorem-backed:
   it follows from the existing alternating-series convergence proof.
5. On the safe half-plane `1 < Re(s)`, Mathlib gives
   `ZMod.LFunction_eq_LSeries`, so the mod-two L-function agrees with the
   ordinary Dirichlet series for the mod-two coefficients.
6. The remaining product algebra is the half-plane identity
   `LSeries g8EtaModTwoNatCoeff s = (1 - 2^(1-s)) * riemannZeta s`.
7. The remaining analytic continuation step is to transport that product
   identity from `1 < Re(s)` to the real open unit interval `0 < x < 1`.
8. Once the product identity and the L-function/conditional-series identity
   hold on the open unit, the existing sign algebra gives
   `riemannZeta (x : ℂ) ≠ 0`, then the zero-height axis guard.

## Guardrails

- Do not use `RiemannHypothesis`, final live hinge, accepted coverage, O3,
  full divisor transfer, or analytic-completion uniqueness.
- Do not use Mathlib `LSeriesSummable` as the open-unit eta convergence
  object; it is absolute convergence.
- Keep the denominator convention `1 - 2^(1-x)` and the positive-index
  coefficient convention odd `+1`, even `-1`.
