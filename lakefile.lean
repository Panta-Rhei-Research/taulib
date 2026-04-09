import Lake
open Lake DSL

/--
  TauLib: Mechanized Formalization of Category τ

  A Lean 4 library formalizing Category τ — a categorical framework built from
  5 generators and axioms K0–K6, deriving all structure from the sole primitive
  iterator ρ. Companion to the 7-book Panta Rhei series (https://panta-rhei.site).

  DEPENDENCY POLICY:
  - Mathlib is required for TACTICS ONLY (simp, omega, ring, aesop, decide, etc.)
  - NEVER import Mathlib mathematical content (Order, Algebra, CategoryTheory, ...)
  - All mathematical structures are built from scratch within TauLib
  - Lean 4 core library types (Nat, Prop, etc.) are allowed for metaprogramming only
-/
package «TauLib» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩    -- Require explicit variable declarations
  ]

@[default_target]
lean_lib «TauLib» where
  globs := #[.submodules `TauLib]
  roots := #[`TauLib]

-- Mathlib for TACTICS ONLY (simp, omega, ring, aesop, norm_num, decide, linarith, ...)
-- ╔══════════════════════════════════════════════════════════════════╗
-- ║  NEVER import Mathlib.Order, Mathlib.Algebra,                  ║
-- ║  Mathlib.CategoryTheory, Mathlib.Topology, Mathlib.Analysis,   ║
-- ║  Mathlib.Data.Nat, or Mathlib.Logic.                           ║
-- ║  All mathematical content is built from scratch in TauLib.     ║
-- ╚══════════════════════════════════════════════════════════════════╝
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
