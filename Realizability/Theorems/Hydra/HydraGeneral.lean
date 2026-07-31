/-
# Phase H7: Hercules wins *whatever he does*

Phase H5 proved termination inside the fragment, for the battle the
fragment can name: leftmost head, `s + 1` copies at step `s`.  That is
Kirby–Paris's own schedule, but it is one play.  The real theorem is
stronger and is not first-order expressible — a strategy is a *function*,
and the fragment has no function variables — so it is proved here, in the
metatheory, from the same ordinal assignment.

## What is proved

`Play n h h'` is the **legal-move relation**: some head of `h` — any head,
at any position — is chopped, and if its parent is not the root, `n`
copies of the modified parent grow at the grandparent.  Nothing selects
*which* head; the relation holds for every choice, and `n` is arbitrary at
every step.

* `play_descends` — every legal move strictly decreases the assigned
  ordinal.  H3's `cutH_descends` is the special case where the head is
  the leftmost one.
* **`hercules_wins`** — the move relation is well-founded.  Every play
  from every hydra is finite, whatever Hercules chops and however many
  heads grow at each step.
* `no_infinite_play` — the same fact in sequence form: there is no
  `F : ℕ → Hydra` with a legal move at every index.
* `play_stuck_iff_leaf` — the only position with no legal move is the
  dead hydra.  This is what makes "the play is finite" mean "the hydra
  dies" rather than "the play gets stuck somewhere".
* `hydraStep_play` — the fragment's battle is one of these plays, so H5's
  theorem is an instance of this one and not a different claim about a
  differently-defined game.

## What it costs

Nothing new mathematically: the three descent lemmas are exactly the ones
H3 proved, and each maps to one constructor of the relation.

| constructor | what it does | lemma |
|---|---|---|
| `CutF.here` | a head hangs off this node | `precB_insertExp_self` |
| `CutF.there` | …off a later sibling | `precB_insertExp_mono` |
| `MoveF.grand` | this node is the grandparent; `n` copies grow | `precB_insertIter_lt` |
| `MoveF.deep` | the move is deeper inside a child | `precB_insertExp_mono_exp` |
| `MoveF.tail` | …inside a later child | `precB_insertExp_mono` |

That the *second-argument* monotonicity `precB_insertExp_mono` — the hard
lemma of H3, which `cutH_descends` never needed — is what the two
"later sibling" constructors consume is the one thing this phase adds to
the picture: chopping the leftmost head is the case where it can be
avoided.

## Scope

Still the metatheory, not the fragment.  The fragment cannot state this:
quantifying over plays means quantifying over functions.  And independence
from PA remains unformalized and unclaimed, exactly as in H5.
-/
import Realizability.Signature.Hydra

namespace Realizability

/-! ## The legal-move relation

Three inductives, mirroring the three things a move can be relative to the
node you are standing on: the head hangs off you (`CutF`), you are the
grandparent and must grow copies (`MoveF.grand`), or it happened further
down (`MoveF.deep`/`MoveF.tail`). -/

/-- `CutF f f'` — `f'` is `f` with one **head** removed: a member of `f`
that is a bare leaf.  The node owning `f` is the chopped head's parent, so
this is the case where the *caller* is the grandparent. -/
inductive CutF : Forest → Forest → Prop
  | here {f : Forest} : CutF (.cons Hydra.leaf f) f
  | there {h : Hydra} {f f' : Forest} : CutF f f' → CutF (.cons h f) (.cons h f')

/-- `MoveF n f f'` — one legal move somewhere inside `f`, with all the
regrowth it triggers contained in `f`.  `grand` is the Kirby–Paris clause:
the chopped head hung off the member `.node g`, so the node owning `f` is
the grandparent and `n` copies of the modified member grow beside it. -/
inductive MoveF (n : ℕ) : Forest → Forest → Prop
  | grand {g g' f : Forest} : CutF g g' →
      MoveF n (.cons (.node g) f)
        (.cons (.node g') (Forest.append (Forest.replicate n (.node g')) f))
  | deep {g g' f : Forest} : MoveF n g g' →
      MoveF n (.cons (.node g) f) (.cons (.node g') f)
  | tail {c : Hydra} {f f' : Forest} : MoveF n f f' →
      MoveF n (.cons c f) (.cons c f')

/-- **One legal move on a whole hydra.**  Either the chopped head hangs
off the root — and then nothing regrows, since the root has no parent —
or it is deeper, and the regrowth is inside. -/
inductive Play (n : ℕ) : Hydra → Hydra → Prop
  | root {f f' : Forest} : CutF f f' → Play n (.node f) (.node f')
  | inner {f f' : Forest} : MoveF n f f' → Play n (.node f) (.node f')

/-! ## The descent, for every move

One case per constructor, each discharged by one H3 lemma. -/

/-- Chopping a head off this node lowers its ordinal. -/
theorem CutF_descends {f f' : Forest} (h : CutF f f') :
    precB (ordOfForest f') (ordOfForest f) = true := by
  induction h with
  | here => exact precB_insertExp_self _ _
  | @there c f f' _ ih =>
    exact precB_insertExp_mono (nfB_ordOfHydra c) _ _ (nfB_ordOfForest f')
      (nfB_ordOfForest f) ih

/-- Any move inside a forest lowers the forest's ordinal. -/
theorem MoveF_descends {n : ℕ} {f f' : Forest} (h : MoveF n f f') :
    precB (ordOfForest f') (ordOfForest f) = true := by
  induction h with
  | @grand g g' rest hcut =>
    -- the regrown copies become an iterate, and the iterate lemma is
    -- insensitive to how many there are
    have hd := CutF_descends hcut
    show precB (ordOfForest (.cons (.node g')
      (Forest.append (Forest.replicate n (.node g')) rest))) _ = true
    rw [ordOfForest_cons, ordOfForest_append_replicate]
    exact precB_insertIter_lt (nfB_ordOfForest g') (nfB_ordOfForest g) hd _
      (nfB_ordOfForest rest) (n + 1)
  | @deep g g' rest _ ih =>
    exact precB_insertExp_mono_exp (nfB_ordOfForest g') (nfB_ordOfForest g)
      ih _ (nfB_ordOfForest rest)
  | @tail c f f' _ ih =>
    exact precB_insertExp_mono (nfB_ordOfHydra c) _ _ (nfB_ordOfForest f')
      (nfB_ordOfForest f) ih

/-- **Every legal move strictly decreases the ordinal** — whichever head
is chopped, and however many copies grow. -/
theorem play_descends {n : ℕ} {h h' : Hydra} (hp : Play n h h') :
    OLt (ordOfHydra h') (ordOfHydra h) := by
  refine olt_of (nfB_ordOfHydra _) (nfB_ordOfHydra _) ?_
  cases hp with
  | root hc => exact CutF_descends hc
  | inner hm => exact MoveF_descends hm

/-! ## Termination -/

/-- `h'` is reachable from `h` by one move, for *some* replication factor.
This is the relation "Hercules moved", with both the head and the number
of regrown copies left to the players. -/
def PlayRel (h' h : Hydra) : Prop := ∃ n, Play n h h'

/-- **Hercules wins.**  The move relation is well-founded: from every
hydra, every sequence of legal moves is finite — whatever head Hercules
chops at each step, and however many heads grow back.

This is `oLt_wf` pulled back along the ordinal assignment; the entire
mathematical content is `play_descends`. -/
theorem hercules_wins : WellFounded PlayRel :=
  Subrelation.wf (fun {_ _} ⟨_, hp⟩ => play_descends hp)
    (InvImage.wf ordOfHydra oLt_wf)

/-- The same fact in sequence form: **no infinite play exists**. -/
theorem no_infinite_play (F : ℕ → Hydra)
    (hF : ∀ i, ∃ n, Play n (F i) (F (i + 1))) : False := by
  suffices H : ∀ h : Hydra, Acc PlayRel h → ∀ G : ℕ → Hydra, G 0 = h →
      (∀ i, ∃ n, Play n (G i) (G (i + 1))) → False from
    H (F 0) (hercules_wins.apply _) F rfl hF
  intro h hacc
  induction hacc with
  | intro x _ ih =>
    intro G hG0 hG
    refine ih (G 1) ?_ (fun i => G (i + 1)) rfl (fun i => hG (i + 1))
    obtain ⟨n, hstep⟩ := hG 0
    exact ⟨n, hG0 ▸ hstep⟩

/-! ## The terminal position is the dead hydra

Well-foundedness says a play stops; these two say it stops *at the bare
head*, which is what "Hercules wins" means. -/

/-- Nothing moves from a bare head. -/
theorem not_play_leaf {n : ℕ} {h' : Hydra} : ¬ Play n Hydra.leaf h' := by
  intro hp
  cases hp with
  | root hc => cases hc
  | inner hm => cases hm

/-- The fragment's move is a legal play, in the `.2 = true` case: `cutH`
reports "the head I chopped was a direct child of me", and that is exactly
a `CutF`. -/
theorem cutH_flag_cut (n : ℕ) : ∀ g : Forest, (cutH n (.node g)).2 = true →
    ∃ g', (cutH n (.node g)).1 = .node g' ∧ CutF g g'
  | .nil, hf => by simp [cutH] at hf
  | .cons (.node .nil) rest, _ => ⟨rest, rfl, CutF.here⟩
  | .cons (.node (.cons c₀ cs)) rest, hf => by
    rcases decEm ((cutH n (Hydra.node (.cons c₀ cs))).2 = true) with hc | hc
    · simp [cutH, hc] at hf
    · simp only [Bool.not_eq_true] at hc
      simp [cutH, hc] at hf

/-- And in the `.2 = false` case it is a `MoveF`: the chopped head was
deeper, so whatever regrowth it triggered happened inside. -/
theorem cutH_flag_move (n : ℕ) : ∀ h : Hydra, h ≠ Hydra.leaf →
    (cutH n h).2 = false →
    ∃ g g' : Forest, h = .node g ∧ (cutH n h).1 = .node g' ∧ MoveF n g g'
  | .node .nil, hne, _ => absurd rfl hne
  | .node (.cons (.node .nil) rest), _, hf => by simp [cutH] at hf
  | .node (.cons (.node (.cons c₀ cs)) rest), _, _ => by
    rcases decEm ((cutH n (Hydra.node (.cons c₀ cs))).2 = true) with hc | hc
    · -- the child reports a direct cut, so *this* node is the grandparent
      obtain ⟨g'', hg₁, hg₂⟩ := cutH_flag_cut n (.cons c₀ cs) hc
      refine ⟨_, _, rfl, ?_, MoveF.grand hg₂⟩
      simp [cutH, hc, hg₁]
    · -- the cut was deeper still
      simp only [Bool.not_eq_true] at hc
      have hchild : (Hydra.node (.cons c₀ cs)) ≠ Hydra.leaf := by
        intro hEq
        exact absurd hEq (by simp [Hydra.leaf])
      obtain ⟨g₁, g₂, hEq, hg₁, hg₂⟩ := cutH_flag_move n (.node (.cons c₀ cs)) hchild hc
      injection hEq with hg
      subst hg
      refine ⟨_, _, rfl, ?_, MoveF.deep hg₂⟩
      simp [cutH, hc, hg₁]

/-- **The fragment's battle is one of these plays.**  So Phase H5's
theorem is an instance of `hercules_wins`, not a separate claim about a
differently-defined game. -/
theorem hydraStep_play (n : ℕ) (h : Hydra) (hne : h ≠ Hydra.leaf) :
    Play n h (hydraStep n h) := by
  rcases decEm ((cutH n h).2 = true) with hf | hf
  · obtain ⟨g, hg⟩ : ∃ g, h = .node g := by cases h with | node g => exact ⟨g, rfl⟩
    subst hg
    obtain ⟨g', hg₁, hg₂⟩ := cutH_flag_cut n g hf
    show Play n (.node g) (cutH n (.node g)).1
    rw [hg₁]
    exact Play.root hg₂
  · simp only [Bool.not_eq_true] at hf
    obtain ⟨g, g', hEq, hg₁, hg₂⟩ := cutH_flag_move n h hne hf
    subst hEq
    show Play n (.node g) (cutH n (.node g)).1
    rw [hg₁]
    exact Play.inner hg₂

/-- Every live hydra has a legal move (the fragment's, for instance), and a
dead one has none.  With `hercules_wins`, this is the full statement: the
play is finite **and** it ends at the bare head. -/
theorem play_stuck_iff_leaf {n : ℕ} {h : Hydra} :
    (¬ ∃ h', Play n h h') ↔ h = Hydra.leaf := by
  constructor
  · intro hstuck
    cases h with
    | node g =>
      cases g with
      | nil => rfl
      | cons c f =>
        exact absurd ⟨_, hydraStep_play n _ (by simp [Hydra.leaf])⟩ hstuck
  · intro hleaf
    subst hleaf
    exact fun ⟨_, hp⟩ => not_play_leaf hp

/-! ## The relation is genuinely nondeterministic

Worth checking rather than assuming, since a relation that accidentally
described only the leftmost strategy would make `hercules_wins` a
restatement of H3 rather than a generalization.

The hydra below is a root with a head *and* a child carrying a head:

    •──┬── head
       └── •── head

Hercules may chop either.  Taking the first, nothing regrows (its parent
is the root).  Taking the second, its parent is the middle node and the
grandparent is the root, so the emptied middle node is replicated `n`
times at the root.  The two results are different hydras, from the same
position, at the same `n`. -/
private abbrev demoHydra : Hydra :=
  .node (.cons Hydra.leaf (.cons (.node (.cons Hydra.leaf .nil)) .nil))

/-- Both moves are legal, and they lead to different hydras. -/
theorem play_two_choices (n : ℕ) :
    Play n demoHydra (.node (.cons (.node (.cons Hydra.leaf .nil)) .nil))
  ∧ Play n demoHydra (.node (.cons Hydra.leaf (.cons (.node .nil)
        (Forest.append (Forest.replicate n (.node .nil)) .nil)))) :=
  ⟨Play.root CutF.here, Play.inner (MoveF.tail (MoveF.grand CutF.here))⟩

/-- …and both descend, by the general theorem — the point being that the
second one is the move `cutH` would never make. -/
theorem play_two_choices_descend (n : ℕ) :
    OLt (ordOfHydra (.node (.cons (.node (.cons Hydra.leaf .nil)) .nil)))
      (ordOfHydra demoHydra)
  ∧ OLt (ordOfHydra (.node (.cons Hydra.leaf (.cons (.node .nil)
        (Forest.append (Forest.replicate n (.node .nil)) .nil)))))
      (ordOfHydra demoHydra) :=
  ⟨play_descends (play_two_choices n).1, play_descends (play_two_choices n).2⟩

#print axioms play_two_choices
#print axioms play_descends
#print axioms hercules_wins
#print axioms no_infinite_play
#print axioms hydraStep_play
#print axioms play_stuck_iff_leaf

end Realizability
