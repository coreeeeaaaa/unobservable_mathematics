# Proof Assistant Roadmap

The following tasks describe how to migrate the current proof sketches to certified proofs. Each item tracks prerequisites, suggested tools, and current status.

## Environment
- **Ambient theory**: Lean 4 (mathlib) or Isabelle/HOL with measure theory and geometric measure theory libraries.
- **Current status (2025-09-18)**: Lean 4.8.0 project scaffolded under `formalization/lean`; `lake update`, `lake build`, and `lake exe uemCli` succeed with mathlib v4.8.0 pinned. `OverlapSystem` exposes the ambient pseudo-metric, support sets, perimeter, and the function $g$; `src/UEM/Measure.lean` provides the σ-cover-based `MeasureContext` with a quasi-additivity bound; `src/UEM/AxiomA2.lean` packages the analytic error control against the spec function $g(P(A),P(B))$.
- **Next encoding step**: Derive explicit kernel/perimeter estimates to instantiate the error bound and complete the thickness lemma.

## Tasks

| ID | Statement | Status | Notes |
|----|-----------|--------|-------|
| P1 | Projection–overlap exchange | in progress | Spec §5.2; realised as `OverlapSystem.projectionOverlapExchange` in `src/UEM/Projection.lean`. Metric/measure scaffolding (`MeasureContext` with $g(P(A),P(B))$ bound) is in place; remaining work is to derive the explicit kernel-based inequality and finish the Lean proof. |
| P2 | Margin persistence | pending | Needs divergence-free flow formalisation; reuse `measure_preserving` lemmas. |
| P3 | Syllable monoid completeness | pending | Formalise `Γ` and show surjectivity via monoid homomorphism in Lean. |
| P4 | σ-finiteness of margins | pending | Depends on mapping object measures to the ambient σ-cover and proving finite mass results. |
| P5 | Observer bound | pending | Translate observers as finite predicates; prove combinatorial bound. |
| P6 | Scenario composition stability | pending | Formalise counterfactual scenarios (`docs/UEM_counterfactual_framework.md`) and show overlap/parallel operators preserve axioms. |

## Workflow
1. Grow the core algebra and measure structures under `src/UEM/` (e.g., future `Flow.lean`).
2. Port each proposition into Lean files `src/UEM/<proposition>.lean` with docstrings referencing the spec.
3. Run `lake build`/`lake exe uemCli` to generate proof artefacts after each milestone.
4. Update the table above with links to the formal files once progress is made.
