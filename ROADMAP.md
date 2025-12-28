# Kernel-Safe Lean ITree Roadmap

This roadmap targets a kernel-safe Lean 4 development of Interaction Trees with
a public quotient type (QITree) that identifies tau-weak bisimilar trees. The
focus is on enabling MLIR denotational semantics and proof work (eutt, interp,
iter) without unsafe axioms.

## Goals
- Kernel-safe core (no unsafe, no axioms for corecursion).
- Public semantics use eutt (weak bisimulation) as the main equivalence.
- Full ITree API: ret/tau/vis, bind, iter, interp, and congruence laws.
- Universe-polymorphic definitions so interp is implementable.

## Current Status (as of Dec 2025)
- Raw ITree defined via MvQPF.Cofix in `ITree/ITree.lean`.
- Eutt defined in `ITree/Eutt.lean`, but key lemmas are incomplete.
- QITree skeleton in `ITree/QITree.lean`, but `vis` and recursor are unfinished.
- Monad/Iter exist for raw ITree, but laws are `sorry`.
- README notes missing universe-polymorphism and coinductive theorems.

## Phase 0: Scope Decisions
- Public type is `QITree` (Quotient by eutt); raw `ITree` is internal.
- QITree recursor: use Prop-only recursor when necessary to stay kernel-safe.
- Eutt is weak bisimulation (tau-closure) matching the ITree paper.

## Phase 1: Core Computation Rules (Raw ITree)
Files: `ITree/ITree.lean`
- Complete `cases_tau` and `cases_vis`.
- Ensure `dest` / `cases` computation rules are stable and usable.
- Add minimal helper lemmas needed by eutt proofs.

## Phase 2: Eutt Closure and Equivalence
Files: `ITree/Eutt.lean`
- Finish `Eutt.trans` proof.
- Complete tau lemmas: `taul`, `taur`, `tau`, `tau_congr`.
- Add `vis_congr`, `bind_congr` (raw ITree) as needed.
- Ensure `Setoid` instance is fully valid.

## Phase 3: Quotient (QITree) Stabilization
Files: `ITree/QITree.lean`
- Implement `QITree.vis` using `Quot.liftOn` with proof of eutt-compatibility.
- Provide constructors: `ret`, `tau`, `vis` with congruence lemmas.
- Provide Prop-only `cases` (or document recursor limits explicitly).
- Define QITree-level tau laws and extensionality via eutt.

## Phase 4: Monad and Iter on QITree
Files: `ITree/Monad.lean`, `ITree/Iter.lean`
- Prove raw `bind` respects eutt, then lift to QITree.
- Prove `LawfulMonad` and `LawfulIter` for QITree.
- Provide `iter_fp` and core equational laws under eutt.

## Phase 5: Universe-Polymorphism for Interp
Files: `ITree/ITree.lean`, `ITree/Effect.lean`, future `ITree/Interp.lean`
- Generalize universes: `E : Type u -> Type v`, `A : Type w`.
- Resolve `ULift` / `Sigma` / `MvQPF` universe constraints.
- Implement `interp` and prove eutt-compatibility.

## Phase 6: MLIR Semantics Integration
- Define core effects for dialect semantics (memory, control, nondet, etc.).
- Provide reusable interpretation lemmas for translation validation.
- Add example dialect semantics and a small validation proof.

## Notes and Risks
- Quotient recursors are limited in Lean; prefer Prop-only recursors for
  proofs, and keep computational content in raw ITree where possible.
- eutt proofs are lemma-heavy; plan for dedicated lemma libraries.
- Universe-polymorphism work is prerequisite for a general `interp`.

## Suggested Next Steps
- Phase 1: complete `cases_tau` and `cases_vis`.
- Phase 2: finish `Eutt.trans` and tau-related lemmas.
- Phase 3: implement `QITree.vis` and Prop-recursion.
