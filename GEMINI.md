# Project Agent Charter

This document defines how we work in `lean-itrees`. It is optimized for
kernel-safe formalization and long-lived proof maintenance.

## Context

- Project goals and status: `README.md`, `ROADMAP.md`.
- This repo targets a **kernel-safe** Lean 4 development of Interaction Trees
  (ITrees), with `eutt` as the core semantic equivalence and `QITree` as the
  public quotient interface.

## Repository Layout

- `ITree/` — Core library (definitions, theorems, instances).
  - Should be stable, reusable, and fully proven (no `sorry`).
- `ITree/Spec/` — Specifications or alternative semantics (e.g., Dijkstra-style).
- `ITree/Examples/` — Small examples and smoke tests.
- `ITree/Experimental/` — Scratch/unstable work; do not depend on this.
- `Examples.lean` — Top-level examples and demos.

## Core Principles

- **Kernel safety first.** No `unsafe` or axioms for core semantics.
- **No `sorry` on main.** If unavoidable, open an issue and quarantine in
  `ITree/Experimental/`.
- **eutt is the semantic equality.** Prefer proofs and laws up to `eutt`.
- **Small, composable lemmas.** Favor lemma libraries over large proofs.
- **Proofs are code.** Keep them readable and maintainable.

## Workflow

- Work on branches; no direct pushes to `main`.
- Branch names: `feat/<issue>-<slug>`, `fix/<issue>-<slug>`, `docs/<issue>-<slug>`.
- Keep commits small and logically scoped.
- Use Conventional Commits where possible: `type(scope): subject`.

## Proof & Code Standards

- Prefer **Prop-only recursors** when working with `Quot`.
- Any new definition that should respect `eutt` must include a congruence lemma.
- Add explicit universe levels when generalizing for `interp`.
- Avoid proof terms that depend on definitional equality across `Quot`.
- Use `simp` only with curated lemma sets; avoid brittle global simp extensions.

## Quality Gates

- Build before pushing: `lake build`.
- If examples change, ensure `Examples.lean` still builds.
- Do not leave compilation warnings unresolved.

## Documentation

- Update `README.md` or `ROADMAP.md` when adding new core features.
- Document non-obvious proof strategies in short comments.

## Quick Checklist

- No `sorry` in core files.
- `eutt`-compatibility lemmas included.
- `lake build` passes.
- Documentation updated if public APIs changed.
