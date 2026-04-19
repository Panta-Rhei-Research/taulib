/-!
# TauLib.BookVII.Meta.Commitment

Structural-commitment encoding for Book VII.

## Registry Cross-References

- [VII.T46] ω-Point commitment — `omega_point_theorem`
  (encoded as a `Commitment` def in
  `TauLib.BookVII.Logos.Sector`)
- [VII.P29] Science-Faith Boundary — `science_faith_boundary`
  (encoded as a `Commitment` def in
  `TauLib.BookVII.Logos.Sector`)
- [VII.T47] No-Forced-Stance commitment — `no_forced_stance`
  (encoded as a `Commitment` def in
  `TauLib.BookVII.Final.Boundary`)

## Ground Truth Sources

- Book VII (2nd Edition), chapters 120–122
- Book VII Appendix: TauLib Formalization

## History: why this structure exists

TauLib v2 shipped three methodological markers in Book VII as
`theorem` declarations of type `True` closed by `sorry` — one for
each of `omega_point_theorem`, `science_faith_boundary`, and
`no_forced_stance`. (Historical syntax form quoted inline in the
monograph's Appendix: `theorem <name> : True` followed by `:=`
then the `sorry` keyword.)

Pre-publication simulated peer review on the companion paper
identified this encoding as performative on two counts. First,
the goal type `True` is inhabited by `trivial`; a `sorry` on
`True` is a marker with no formal content — the sorry names an
unprovable obligation that is in fact trivially provable.
Second, the `no_forced_stance` declaration was being justified,
in surrounding docstring prose, by citation of registry
`VII.T47` — which was itself `no_forced_stance`. The
methodological license to leave the sorry was self-referential.

This file introduces the `Commitment` structure as an
inspectable, non-performative replacement. A structural
commitment is represented as a `def` value carrying three
String fields — the commitment's statement, warrant, and
registry identifier — rather than as an unproven `sorry`-closed
theorem on a trivially-provable `True` goal.

## Design rationale

A `Commitment` is data, not an axiom or a theorem:

- **Not an axiom.** `#print axioms <commitment-name>` reports no
  axioms (a `def` adds no axioms to the theory). The library's
  `axiom` count is therefore unaffected by declaring commitments.

- **Not a theorem.** A commitment does not assert a proposition;
  it records that Book VII has declined to force a stance via
  proof, for reasons given in the `warrant` field.

- **Data.** The `statement` and `warrant` fields are readable
  via `#eval` (the structure derives `Repr`). A reader
  traversing the Lean source can inspect what is being
  committed to and why, without needing to reverse-engineer
  performative source comments.

The `no_forced_stance` commitment is cited by the other two in
their `warrant` fields. This is intentional: Book VII argues
(via its No-Forced-Stance discipline) that certain structural
questions cannot be closed by proof within the framework, and
the remaining Book VII commitments name this same discipline
as their warrant. The reference is explicit prose inside a
String field, rather than an implicit dependency between
sorry-closed theorems; a reader can see the reference, judge
it, and disagree with it, but cannot mistake it for a formal
proof.

## Adversarial-use caveat

The `Commitment` pattern could be misused as a sorry-laundering
mechanism if a contributor encoded genuine proof debt as a
"commitment." A future CI guard will require any new
`Commitment` value's `warrant` to match an approved discipline
(No-Forced-Stance, or an explicit new methodological category
added via PR review). Until that guard ships, the three
commitment values declared alongside this file are the only
approved uses of the pattern. New commitments MUST NOT be
introduced without discussion.
-/

namespace Tau.BookVII.Meta.Commitment

/-- A structural commitment in the Panta Rhei framework:
    a place where the monograph explicitly declines to force
    a stance via proof, for reasons given in the warrant.

    Commitments are inspectable data (`def` values), not
    performative `sorry`-closed propositions. A `Commitment`
    adds no axioms, asserts no proposition, and cannot be used
    as a premise in any theorem; it is a structured record.

    Fields:
    - `statement`: the commitment claim, verbatim from the monograph.
    - `warrant`: the methodological justification for declining
      to force a stance, explicitly traceable to Book VII's
      No-Forced-Stance discipline (`VII.T47`).
    - `registry_id`: the canonical registry identifier
      (e.g., `"VII.T46"`) for cross-reference with the
      monograph's LaTeX source. -/
structure Commitment where
  statement : String
  warrant : String
  registry_id : String
  deriving Repr, Inhabited

end Tau.BookVII.Meta.Commitment
