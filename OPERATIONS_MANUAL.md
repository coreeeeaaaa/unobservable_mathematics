# Operations Manual — Formalisation Track

This manual defines the working conventions inside `formalization/`.

## 1. Scope & Responsibilities
- Maintain the canonical statement of axioms and proofs for the UEM/YJG system.
- Ensure all formal artefacts (Lean/Isabelle code, proof scripts, build tooling) reference `docs/UEM_formal_spec_v2.md`.
- Keep documentation synchronised with the codebase (proof status, TODOs, open questions).

## 2. Directory Layout
- `axiomatics.md`: compact restatement of definitions/axioms.
- `implementation_notes.md`: translation guidance between informal descriptions and code/tests.
- `proof_plan.md`: status table for machine-checked proofs.
- `lean/`: Lean 4 project (toolchain files, source modules, Lake build artefacts ignored via `.gitignore`).
- `tools/`: automation helpers (e.g., `record_toolchain.py` for logging build runs).

## 3. Workflow Checklist
1. Review the authoritative specification (`docs/UEM_formal_spec_v2.md`).
2. Update `axiomatics.md` if new symbols/axioms are introduced.
3. Capture outstanding questions in `open_questions.md` (TBD) before attempting proofs.
4. Implement or adjust proof scripts/tests.
5. Run relevant build/tests, capture outputs in `reports/` when milestones are met (use `tools/record_toolchain.py` where possible).
6. Update `TODO.md`, `proof_plan.md`, and `README.md` with progress notes.

## 4. Documentation Hygiene
- Keep docstrings in Lean/Isabelle referencing spec sections (e.g., “Spec §3.4”).
- Add a breadcrumb in each proof file linking back to the proposition identifier in `docs/UEM_proof_sketches_v2.md`.
- Document open questions in `formalization/` (e.g., as `open_questions.md`).
- For handovers, add a `### Hand-off` section summarising status.

## 5. Logging & Reporting
- All significant operations should end with an entry in a dated report under `reports/`.
- File naming convention: `reports/UEM_meta_review_YYYYMMDD.md` for daily or milestone reviews.
- Include: achieved milestones, outstanding risks, next steps, references to modified files.
- Use `tools/record_toolchain.py` to capture outputs from `lake update`, `lake build`, `lake exe uemCli`, etc., and append them to `reports/toolchain_log_YYYYMMDD.md` for traceability.

## 6. Tooling & Environment
- Proof assistants: Lean 4 (current: 4.8.0 with mathlib v4.8.0 under `formalization/lean`) or Isabelle if parity features are required.
- Installation record (2025-09-17): `elan toolchain install leanprover/lean4:4.8.0`, `lake update`, `lake build`, `lake exe uemCli` executed successfully; see `formalization/lean/README.md` for reproducible steps.
- Python ≥ 3.11 for tests; avoid external dependencies without updating `requirements.txt`.
- Editing helpers (optional): `apply_patch`, explicit cat redirects; avoid editors that change encoding.

## 7. Escalation & Quality Assurance
- If a task cannot be completed due to missing definitions or contradictions, mark the TODO and open an issue in `formalization/open_questions.md` (to be created).
- Maintainers should periodically review `formalization/TODO.md` and reports to ensure alignment.

This manual must be kept up to date whenever the workflow changes.
