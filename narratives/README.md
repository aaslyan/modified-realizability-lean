# Narratives

Reader-facing explainers built on top of the formalization — the "give
someone something tangible" companions to STATUS.md's technical record.
Each is a self-contained HTML page (open it in a browser; no build step).

## Pages

- **[anatomy-of-an-extracted-function.html](anatomy-of-an-extracted-function.html)**
  — *The Anatomy of an Extracted Function.* A four-rung ladder from the
  two-variable iterative Fibonacci everyone knows, up through the extracted
  term's λ-structure, its type-2 continuous functional, and its `CtQ 2`
  extensional collapse. The through-line: the extract literally carries the
  loop's pair-state `(0,1) → (1,1) → (1,2) → (2,3)`, read straight off the
  realizer (`fib_pair_spec`, build-`#guard`ed in `FibonacciExtraction.lean`).

- **[the-proof-and-the-program.html](the-proof-and-the-program.html)**
  — *The Proof, and the Program It Realizes.* Goodstein's actual proof term
  (`GoodsteinTheorem.lean`) rendered as an annotated AST, each `Deriv` node
  paired with the combinator `extract` maps it to (`tiEps0 → tiC`,
  `orE → orEC`, `exI → exIC`; the equality-bookkeeping nodes erased to `·`).
  It also draws the precise line between **Curry–Howard** (true at Lean's
  meta level — the derivation *is* a λ-term) and **modified realizability**
  (the fragment's proof→program map: `extract` into a separate `PureType`,
  correctness by an external `soundness` theorem, content selection, and the
  constructive-extract / classical-proof firewall).

## Scope

These are expositional. Every claim on a page is a declaration checked in
the repository; where a page simplifies syntax for readability (e.g. a
`for`-comprehension gloss of a `List.map`), the exact source line is named.
Out-of-scope claims (PA-independence, 2D Sperner, classical Hanoi
minimality) are fenced in STATUS.md and are not asserted here.
