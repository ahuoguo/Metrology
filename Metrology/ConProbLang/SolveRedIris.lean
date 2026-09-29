module

public import Metrology.ConProbLang.Lang
public import Iris.ProofMode

/-!
# Proof-mode cases of `solve_red`

Ported from clutch/theories/con_prob_lang/tactics.v (the Iris cases of `solve_red`).

`Metrology.ConProbLang.Lang` defines `solve_red` for pure `reducible` / `head_reducible` goals.
This module extends it (by further `macro_rules`, which Lean tries in addition to the earlier
ones) with the two proof-mode cases of Rocq's `solve_red`:
* `envs_entails _ (⌜_⌝ ∗ _)`: `iSplitR; [by (iPureIntro; solve_red) |]` becomes
  `isplitr` followed by `ipureintro; solve_red` on the first goal;
* `envs_entails _ (_ ∗ ⌜_⌝)`: `iSplitL; [by (iPureIntro; solve_red) |]` becomes
  `isplitl` followed by `ipureintro; solve_red` on the second goal.
As in Rocq, the remaining (non-pure) conjunct is left as the only goal.

The Rocq `Hint Extern 2 (head_reducible _ _) => solve_red : typeclass_instances` has no
counterpart: `head_reducible` is not a class in the Lean port.
-/

@[expose] public section

namespace ConProbLang

macro_rules
  | `(tactic| solve_red) => `(tactic| (isplitr; focus (ipureintro; solve_red; done)))
macro_rules
  | `(tactic| solve_red) => `(tactic| (isplitl; pick_goal 2; focus (ipureintro; solve_red; done)))

open Iris Iris.BI con_prob_lang

example {PROP : Type _} [BI PROP] (σ : state) (P : PROP) :
    P ⊢ ⌜reducible (Λ := con_prob_lang) (Pair (Val (LitV LitUnit)) (Val (LitV LitUnit))) σ⌝ ∗ P := by
  iintro HP
  solve_red
  iexact HP

example {PROP : Type _} [BI PROP] (σ : state) (P : PROP) :
    P ⊢ P ∗ ⌜reducible (Λ := con_prob_lang) (Pair (Val (LitV LitUnit)) (Val (LitV LitUnit))) σ⌝ := by
  iintro HP
  solve_red
  iexact HP

example (σ : state) :
    reducible (Λ := con_prob_lang) (Pair (Val (LitV LitUnit)) (Val (LitV LitUnit))) σ := by
  solve_red

end ConProbLang
