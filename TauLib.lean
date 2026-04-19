/-!
# TauLib — Mechanized Formalization of Category τ

A 126,000-line Lean 4 library formalizing Category τ — a categorical framework
built from 7 axioms (K0–K6) on 5 generators (α, π, γ, η, ω) with a single
primitive iterator ρ. All mathematical structures are built from scratch;
Mathlib is used for proof tactics only.

Companion to the 7-book Panta Rhei series (https://panta-rhei.site)
by Thorsten Fuchs and Anna-Sophie Fuchs (2nd Edition, 2026).

## Book-Level Organization

450 modules organized under seven book namespaces:

- **Book I** (Categorical Foundations): 94 files — Kernel, Orbit, Denotation,
  Coordinates, Polarity, Boundary, Sets, Logic, Holomorphy, Topos, MetaLogic, CF
- **Book II** (Categorical Holomorphy): 65 files — τ³ fibration, Central Theorem
- **Book III** (Categorical Spectrum): 70 files — 8 spectral forces, Millennium Problems
- **Book IV** (Categorical Microcosm): 89 files — QM, particle spectrum, electroweak
- **Book V** (Categorical Macrocosm): 80 files — Gravity, cosmology, dark sector
- **Book VI** (Categorical Life): 30 files — Biology, consciousness
- **Book VII** (Categorical Metaphysics): 7 files — Philosophy, ethics
  (three structural commitments encoded as `def : Commitment`, not `sorry`;
  see `TauLib/BookVII/Meta/Commitment.lean`)

## Key Metrics

4,332 theorems · 3,542 definitions · 3,721 `#eval` computations
3 axioms (all conjectural, all Book III) · 0 sorry across all seven books
(as of v2.0.0, peer-review-fixes-v1 merged 2026-04-19)
-/

-- ================================================================
-- SEVEN BOOKS — Complete Library
-- ================================================================

import TauLib.BookI
import TauLib.BookII
import TauLib.BookIII
import TauLib.BookIV
import TauLib.BookV
import TauLib.BookVI
import TauLib.BookVII
