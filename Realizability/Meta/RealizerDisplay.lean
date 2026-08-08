/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import Realizability.Common.Exists

/-!
# `#realizer` — a structural view of an extracted realizer

The extractor turns a derivation into a realizer that lives in the `PureType`
tower. For anything past the very smallest example that realizer is invisible:
`#reduce (extract goodsteinTheorem …)` never returns, because it forces the
transfinite recursor `tiRecC` — the same wall that stops `gcdWitness 0 0`. And
even where reduction *does* terminate, it over-reduces: the smallest realizer,
`extract goodThreeExDeriv`, collapses under `#reduce` to `fun n z => 30`
(that is `Nat.pair 5 0`), so the witness `5` the proof supplies is gone.

`#realizer d` shows the realizer's structure instead of its value. It walks the
**derivation** `d` — a finite constructor tree — and never calls `extract`,
never builds a `PureType`, and never runs a recursion combinator. So it
terminates on `goodsteinTheorem` and `hydraTheorem` (a 29-node skeleton each)
exactly where evaluation cannot, and it keeps the interesting scaffolding
visible: the `∀`-binders, the case split, the `exI` witness read-off, the
transfinite recursion node, the descent discharged against the induction
hypothesis.

## Usage

```
#realizer goodThreeExDeriv
-- exI  ⟨witness = 5, ·⟩
--    · ⟨contentless⟩  good(3,5) = 0
```

## The collapse rule

A realizer of an equation (or `⊥`) is contentless: its value is junk and the
`MR` clause ignores it. So any sub-derivation whose *conclusion* is an equation
or `⊥` is rendered as a single `·` leaf, however it was proved — this is what
folds `goodComputeDeriv`'s long equational chain into one node. The rule keys on
the conclusion `φ`, not on which constructor was used.

## Per-rule completeness

`toSkel` matches on every `Deriv` constructor with no wildcard, so adding a rule
to the fragment produces a missing-case error here, exactly as it does in
`extract` / `soundness` / `derivBound` / `extract_tracked`. This is the fifth
per-rule site; keep it in step with the other four.

This module is a display tool: `partial def`s and a macro, no theorems. It is
imported by the root module so `lake build` type-checks it and runs the pinned
regression `#guard`, but it introduces no axioms and changes no certified
declaration.
-/

namespace Realizability.RealizerDisplay

open Realizability

/-- Display tree: a named combinator node with children, or a leaf. -/
inductive Skel where
  | node : String → List Skel → Skel
  | leaf : String → Skel
  deriving Inhabited

/-- Recognise a numeral `succ^k zero` and return `k`. -/
partial def numLit? : Term → Option Nat
  | .zero   => some 0
  | .succ t => (numLit? t).map (· + 1)
  | _       => none

/-- Compact one-line rendering of a term; numerals print as their value. -/
partial def termStr : Term → String
  | t =>
    match numLit? t with
    | some k => toString k
    | none =>
      match t with
      | .var i           => s!"x{i}"
      | .zero            => "0"
      | .succ a          => s!"S({termStr a})"
      | .plus a b        => s!"({termStr a}+{termStr b})"
      | .times a b       => s!"({termStr a}·{termStr b})"
      | .pred a          => s!"pred({termStr a})"
      | .exp a b         => s!"exp({termStr a},{termStr b})"
      | .bump a b        => s!"bump({termStr a},{termStr b})"
      | .good a b        => s!"good({termStr a},{termStr b})"
      | .prec a b        => s!"prec({termStr a},{termStr b})"
      | .ord a b         => s!"ord({termStr a},{termStr b})"
      | .hcut a b        => s!"hcut({termStr a},{termStr b})"
      | .hydra a b       => s!"hydra({termStr a},{termStr b})"
      | .hord a          => s!"hord({termStr a})"
      | .hcons a b       => s!"hcons({termStr a},{termStr b})"
      | .happ a b        => s!"happ({termStr a},{termStr b})"
      | .mvcount a       => s!"mvcount({termStr a})"
      | .solves a b c d e =>
          s!"solves({termStr a},{termStr b},{termStr c},{termStr d},{termStr e})"
      | .xor a b         => s!"xor({termStr a},{termStr b})"
      | .pas a b         => s!"pas({termStr a},{termStr b})"
      | .look a b        => s!"look({termStr a},{termStr b})"
      | .fib a           => s!"fib({termStr a})"

/-- Compact one-line rendering of a formula. -/
def formulaStr : Formula → String
  | .bot     => "⊥"
  | .eq s t  => s!"{termStr s} = {termStr t}"
  | .and a b => s!"({formulaStr a} ∧ {formulaStr b})"
  | .or a b  => s!"({formulaStr a} ∨ {formulaStr b})"
  | .imp a b => s!"({formulaStr a} → {formulaStr b})"
  | .all y a => s!"∀x{y}.{formulaStr a}"
  | .ex y a  => s!"∃x{y}.{formulaStr a}"

/-- A conclusion whose realizer carries no information. -/
def isContentless : Formula → Bool
  | .eq _ _ => true
  | .bot    => true
  | _       => false

/-- The contentless leaf for a conclusion `φ`. -/
def contentlessLeaf (φ : Formula) : Skel :=
  .leaf s!"· ⟨contentless⟩  {formulaStr φ}"

/-- Walk the derivation into a display skeleton.

Collapse-by-conclusion fires first: any sub-derivation proving an equation or
`⊥` becomes one leaf, however it was built. Otherwise dispatch on the rule.
Every constructor has a case (no wildcard) — see the per-rule note in the
module header. -/
partial def toSkel {Γ : List Formula} {φ : Formula} (D : Deriv Γ φ) : Skel :=
  if isContentless φ then contentlessLeaf φ else
  match D with
  -- structural rules (carry computational content)
  | .ax             => .leaf "ax  (head hypothesis)"
  | .wk D           => .node "wk  (weaken)" [toSkel D]
  | .andI D₁ D₂     => .node "andI  ⟨_,_⟩" [toSkel D₁, toSkel D₂]
  | .andE₁ D        => .node "andE₁  (π₁)" [toSkel D]
  | .andE₂ D        => .node "andE₂  (π₂)" [toSkel D]
  | .orI₁ D         => .node "orI₁  (inl, tag 0)" [toSkel D]
  | .orI₂ D         => .node "orI₂  (inr, tag 1)" [toSkel D]
  | .orE D D₁ D₂    => .node "orE  (case)" [toSkel D, toSkel D₁, toSkel D₂]
  | .impI D         => .node "impI  (λ)" [toSkel D]
  | .impE D₁ D₂     => .node "impE  (app)" [toSkel D₁, toSkel D₂]
  | .botE D         => .node "botE  (ex falso)" [toSkel D]
  | .allI D _       => .node "allI  (Λk)" [toSkel D]
  | .allE u D _     => .node s!"allE[{termStr u}]  (inst)" [toSkel D]
  | .ind D₁ D₂ _    => .node "ind / indRecC  (recurse on succ)" [toSkel D₁, toSkel D₂]
  | @Deriv.tiEps0 _ _ _ _ D _ _ _ =>
        .node "tiEps0 / tiRecC  (recurse along ≺)" [toSkel D]
  | .exI u D _      => .node s!"exI  ⟨witness = {termStr u}, ·⟩" [toSkel D]
  | @Deriv.exE _ _ _ _ D₁ D₂ _ _ =>
        .node "exE  (let ⟨w,p⟩ := …)" [toSkel D₁, toSkel D₂]
  -- the one content-bearing axiom: a decidable equality carries a tag
  | .eqDec s t      => .leaf s!"eqDec  ⟨decide {termStr s} = {termStr t}⟩"
  -- contentless axiom / equation schemas: every one collapses to a leaf
  | .succNeZero ..   => contentlessLeaf φ
  | .succInj ..      => contentlessLeaf φ
  | .eqRefl ..       => contentlessLeaf φ
  | .eqSymm ..       => contentlessLeaf φ
  | .eqTrans ..      => contentlessLeaf φ
  | .eqCongSucc ..   => contentlessLeaf φ
  | .eqCongPlus ..   => contentlessLeaf φ
  | .eqCongTimes ..  => contentlessLeaf φ
  | .zeroPlus ..     => contentlessLeaf φ
  | .succPlus ..     => contentlessLeaf φ
  | .zeroTimes ..    => contentlessLeaf φ
  | .succTimes ..    => contentlessLeaf φ
  | .predZero        => contentlessLeaf φ
  | .predSucc ..     => contentlessLeaf φ
  | .expZero ..      => contentlessLeaf φ
  | .expSucc ..      => contentlessLeaf φ
  | .bumpZero ..     => contentlessLeaf φ
  | .bumpNum ..      => contentlessLeaf φ
  | .goodZero ..     => contentlessLeaf φ
  | .goodSucc ..     => contentlessLeaf φ
  | .eqCongPred ..   => contentlessLeaf φ
  | .eqCongExp ..    => contentlessLeaf φ
  | .eqCongBump ..   => contentlessLeaf φ
  | .eqCongGood ..   => contentlessLeaf φ
  | .precNum ..      => contentlessLeaf φ
  | .eqCongPrec ..   => contentlessLeaf φ
  | .ordBump ..      => contentlessLeaf φ
  | .ordPredLt ..    => contentlessLeaf φ
  | .bumpNeZero ..   => contentlessLeaf φ
  | .eqCongOrd ..    => contentlessLeaf φ
  | .hydraZero ..    => contentlessLeaf φ
  | .hydraSucc ..    => contentlessLeaf φ
  | .hordCutLt ..    => contentlessLeaf φ
  | .hcutNum ..      => contentlessLeaf φ
  | .eqCongHcut ..   => contentlessLeaf φ
  | .eqCongHydra ..  => contentlessLeaf φ
  | .eqCongHord ..   => contentlessLeaf φ
  | .solvesZero ..   => contentlessLeaf φ
  | .solvesSucc ..   => contentlessLeaf φ
  | .mvcountNil      => contentlessLeaf φ
  | .mvcountApp ..   => contentlessLeaf φ
  | .eqCongHcons ..  => contentlessLeaf φ
  | .eqCongHapp ..   => contentlessLeaf φ
  | .eqCongMvcount .. => contentlessLeaf φ
  | .pasZeroZero     => contentlessLeaf φ
  | .pasZeroSucc ..  => contentlessLeaf φ
  | .pasSuccZero ..  => contentlessLeaf φ
  | .pasSuccSucc ..  => contentlessLeaf φ
  | .xorNum ..       => contentlessLeaf φ
  | .eqCongXor ..    => contentlessLeaf φ
  | .eqCongPas ..    => contentlessLeaf φ
  | .lookNum ..      => contentlessLeaf φ
  | .eqCongLook ..   => contentlessLeaf φ
  | .eqCongSolves .. => contentlessLeaf φ
  | .fibZero         => contentlessLeaf φ
  | .fibOne          => contentlessLeaf φ
  | .fibSucc ..      => contentlessLeaf φ
  | .eqCongFib ..    => contentlessLeaf φ

/-- Indent by `n` spaces. -/
def pad (n : Nat) : String := String.ofList (List.replicate n ' ')

/-- Render a skeleton as an indented tree. -/
partial def render (depth : Nat) : Skel → String
  | .leaf s    => pad (depth * 3) ++ s ++ "\n"
  | .node s ch => pad (depth * 3) ++ s ++ "\n" ++
                    (ch.map (render (depth + 1))).foldl (· ++ ·) ""

/-- The realizer skeleton of a derivation, as a multi-line string. -/
def realizerSkeleton {Γ : List Formula} {φ : Formula} (D : Deriv Γ φ) : String :=
  render 0 (toSkel D)

/-! ## Pseudocode decompilation

`#program` is a readability layer over the same extracted skeleton.  It does
not inspect the reduced `PureType` value — reduction can hide witnesses in
numeric pair encodings or force huge recursors.  Instead it reuses `toSkel`,
whose cases mirror the extractor's rule-by-rule structure, and renders the
extracted combinators as pseudocode.

The output is therefore not the certified artifact.  The certified artifact is
still `extract D`, with correctness from `soundness` and continuity from
`extract_continuous`.  The pseudocode is the generated reader-facing view of
that artifact.
-/

def isPrefix (p s : String) : Bool :=
  p.length ≤ s.length && s.take p.length = p

def bracketPayload (s : String) : String :=
  match s.splitOn "[" with
  | _ :: rest =>
      match (String.intercalate "[" rest).splitOn "]" with
      | u :: _ => u
      | _ => "?"
  | _ => "?"

def witnessPayload (s : String) : String :=
  match s.splitOn "witness = " with
  | _ :: rest =>
      match (String.intercalate "witness = " rest).splitOn "," with
      | u :: _ => u
      | _ => "?"
  | _ => "?"

def contentlessPayload (s : String) : String :=
  match s.splitOn "  " with
  | _ :: rest => String.intercalate "  " rest
  | _ => s

def eqDecPayload (s : String) : String :=
  match s.splitOn "⟨decide " with
  | _ :: rest =>
      match (String.intercalate "⟨decide " rest).splitOn "⟩" with
      | u :: _ => u
      | _ => s
  | _ => s

def leafPseudo (s : String) : String :=
  if isPrefix "· ⟨contentless⟩" s then
    s!"erase({contentlessPayload s})"
  else if isPrefix "eqDec" s then
    s!"decide({eqDecPayload s})"
  else if isPrefix "ax" s then
    "recursive_or_hypothesis_value"
  else
    s

def pseudoHeader (s : String) : String :=
  if isPrefix "allI" s then
    "fun k =>"
  else if isPrefix "impI" s then
    "fun proof_arg =>"
  else if isPrefix "impE" s then
    "apply"
  else if isPrefix "allE[" s then
    s!"instantiate {bracketPayload s}"
  else if isPrefix "andI" s then
    "pair"
  else if isPrefix "andE₁" s then
    "fst"
  else if isPrefix "andE₂" s then
    "snd"
  else if isPrefix "orI₁" s then
    "return tag 0 with"
  else if isPrefix "orI₂" s then
    "return tag 1 with"
  else if isPrefix "orE" s then
    "case split"
  else if isPrefix "exI" s then
    s!"return witness {witnessPayload s} with certificate"
  else if isPrefix "exE" s then
    "let ⟨witness, certificate⟩ ="
  else if isPrefix "ind / indRecC" s then
    "natRec"
  else if isPrefix "tiEps0 / tiRecC" s then
    "wellFoundedRecOnPrec"
  else if isPrefix "wk" s then
    "weaken"
  else if isPrefix "botE" s then
    "absurd"
  else
    s

/-- Render an extracted skeleton as pseudocode. -/
partial def renderPseudo (depth : Nat) : Skel → String
  | .leaf s => pad (depth * 2) ++ leafPseudo s ++ "\n"
  | .node s ch =>
      let here := pad (depth * 2) ++ pseudoHeader s ++ "\n"
      let body := (ch.map (renderPseudo (depth + 1))).foldl (· ++ ·) ""
      here ++ body

/-- Pseudocode view of the extracted realizer. -/
def decompiledProgram {Γ : List Formula} {φ : Formula} (D : Deriv Γ φ) : String :=
  "decompiled extracted realizer (pseudocode)\n" ++
  "------------------------------------------\n" ++
  renderPseudo 0 (toSkel D)

/-! ## The Curry–Howard view

`#realizerCH` renders the same walk as three columns per node — the **program
operation**, the **logic rule** it corresponds to, and the **proposition** that
rule proves — so the extraction map (rule ↦ program operation) is legible line
by line. Extraction is structure-preserving: modified realizability is
Curry–Howard with the map made explicit, and this is a picture of the map.

Completeness is enforced by `toSkel` above (no wildcard); `toCH` may use a
wildcard for the contentless tail, since a new content-bearing rule would break
`toSkel`'s build first. -/

/-- A node of the correspondence view: program op, logic rule, proposition. -/
inductive CHNode where
  | mk : (op rule prop : String) → List CHNode → CHNode
  deriving Inhabited

/-- Truncate a string to width `w` with an ellipsis. -/
def trunc (w : Nat) (s : String) : String :=
  if s.length ≤ w then s else s.take (w - 1) ++ "…"

/-- Annotate each rule with its program operation and the proposition it proves. -/
partial def toCH {Γ : List Formula} {φ : Formula} (D : Deriv Γ φ) : CHNode :=
  let p := formulaStr φ
  if isContentless φ then .mk "·" "equation (proof-irrelevant)" p [] else
  match D with
  | .ax          => .mk "var" "hypothesis / IH" p []
  | .wk D        => .mk "(weaken)" "weakening" p [toCH D]
  | .andI D₁ D₂  => .mk "⟨_,_⟩" "∧-intro" p [toCH D₁, toCH D₂]
  | .andE₁ D     => .mk "π₁" "∧-elim₁" p [toCH D]
  | .andE₂ D     => .mk "π₂" "∧-elim₂" p [toCH D]
  | .orI₁ D      => .mk "inl" "∨-intro₁" p [toCH D]
  | .orI₂ D      => .mk "inr" "∨-intro₂" p [toCH D]
  | .orE D D₁ D₂ => .mk "case" "∨-elim" p [toCH D, toCH D₁, toCH D₂]
  | .impI D      => .mk "λh." "→-intro" p [toCH D]
  | .impE D₁ D₂  => .mk "apply" "→-elim" p [toCH D₁, toCH D₂]
  | .botE D      => .mk "absurd" "⊥-elim" p [toCH D]
  | .allI D _    => .mk "λk." "∀-intro" p [toCH D]
  | .allE u D _  => .mk s!"apply @ {termStr u}" "∀-elim" p [toCH D]
  | .ind D₁ D₂ _ => .mk "rec (fold on succ)" "induction" p [toCH D₁, toCH D₂]
  | @Deriv.tiEps0 _ _ _ _ D _ _ _ =>
        .mk "rec (well-founded on ≺)" "TI(ε₀)" p [toCH D]
  | .exI u D _   => .mk s!"return ⟨{termStr u}, ·⟩" "∃-intro" p [toCH D]
  | @Deriv.exE _ _ _ _ D₁ D₂ _ _ => .mk "let ⟨w,p⟩ :=" "∃-elim" p [toCH D₁, toCH D₂]
  | .eqDec s t   => .mk s!"decide {termStr s}={termStr t}" "decidable-eq" p []
  | _            => .mk "·" "axiom (proof-irrelevant)" p []

/-- Render the correspondence tree, one `op — rule ⟦prop⟧` line per node. -/
partial def renderCH (depth : Nat) : CHNode → String
  | .mk op rule prop ch =>
      pad (depth * 3) ++ op ++ "  — " ++ rule ++ "  ⟦" ++ trunc 44 prop ++ "⟧\n" ++
        (ch.map (renderCH (depth + 1))).foldl (· ++ ·) ""

/-- The Curry–Howard correspondence view of a derivation, as a string. -/
def realizerCorrespondence {Γ : List Formula} {φ : Formula} (D : Deriv Γ φ) : String :=
  "PROGRAM  —  LOGIC RULE  ⟦ PROPOSITION ⟧\n" ++ renderCH 0 (toCH D)

end Realizability.RealizerDisplay

/-- `#realizer d` prints the extracted realizer skeleton of the derivation `d`
(see `Realizability/Meta/RealizerDisplay.lean`). It reads the derivation
structurally, so it works on realizers that `#reduce` cannot evaluate. -/
macro "#realizer " t:term : command =>
  `(command| #eval IO.println (Realizability.RealizerDisplay.realizerSkeleton $t))

/-- `#program d` prints generated pseudocode for the extracted realizer of `d`.
It is a decompiled display view, not the certified artifact itself. -/
macro "#program " t:term : command =>
  `(command| #eval IO.println (Realizability.RealizerDisplay.decompiledProgram $t))

/-- `#realizerCH d` prints the derivation as the Curry–Howard correspondence:
each line is `program-operation — logic-rule ⟦proposition⟧`, exhibiting the
extraction map rule-by-rule. -/
macro "#realizerCH " t:term : command =>
  `(command| #eval IO.println (Realizability.RealizerDisplay.realizerCorrespondence $t))

-- Pinned regression: the smallest realizer renders as the paper's ⟨5, contentless⟩.
#guard Realizability.RealizerDisplay.realizerSkeleton Realizability.goodThreeExDeriv ==
  "exI  ⟨witness = 5, ·⟩\n   · ⟨contentless⟩  good(3,5) = 0\n"

-- Pinned regression: the correspondence view maps ∃-intro to `return ⟨5, ·⟩`.
#guard ((Realizability.RealizerDisplay.realizerCorrespondence
    Realizability.goodThreeExDeriv).splitOn "\n").getD 1 "" ==
  "return ⟨5, ·⟩  — ∃-intro  ⟦∃x1.good(3,x1) = 0⟧"

#guard ((Realizability.RealizerDisplay.decompiledProgram
    Realizability.goodThreeExDeriv).splitOn "\n").getD 2 "" ==
  "return witness 5 with certificate"
