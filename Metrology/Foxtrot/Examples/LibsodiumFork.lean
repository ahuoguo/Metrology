module

public import Metrology.Foxtrot.Examples.Libsodium

/-!
# `randombytes_uniform`: `rbu_fork ≤ctx≤ ideal_uniform`

Ported from clutch/theories/foxtrot/examples/libsodium.v (part 2a: the first `last first` goal
of `randombytes_uniform_refines_ideal`).

The LHS forks a thread sampling `rand (MAX quot n - 1)` (run to completion with `wp_rand`),
and its `rand (n - 1)` is coupled with the RHS's `rand (n - 1)` by `wp_couple_rand_rand`.

## Rocq → Lean map
* `rbu_fork_refines_ideal` (Rocq: anonymous subgoal).

## Deviations
* Rocq's `wp_couple_rand_rand` finds the bijection `id` by instance search; here `f := id`
  explicitly (as in `Foxtrot.Lib.Sampler`).
* Rocq's `case_bool_decide` is `by_cases` + `simp only [h, decide_true/decide_false]`.
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE COFE ConProbLang ConProbLang.con_prob_lang
open Foxtrot.BinaryRel

namespace Foxtrot.Examples.Libsodium

theorem rbu_fork_refines_ideal (MAX : ℕ) :
    (∅ : varmap type) ⊨ Val (rbu_fork MAX) ≤ctx≤ Val (ideal_uniform MAX) : TArrow TNat TNat := by
  apply start
  intro _ n K j
  iintro Hspec
  unfold rbu_fork ideal_uniform
  wp_pures
  tp_pures j
  by_cases h : MAX ≤ n
  · simp only [h, decide_true]
    tp_pures j
    wp_pures
    iexists 0
    iframe Hspec
    ipureintro
    rfl
  · simp only [h, decide_false]
    tp_pures j
    by_cases hn : n = 0
    · simp only [hn, decide_true]
      tp_pures j
      wp_pures
      iexists 0
      iframe Hspec
      ipureintro
      rfl
    · simp only [hn, decide_false]
      tp_pures j
      wp_pures
      simp only [hn, decide_false]
      wp_pures
      wp_bind (Fork _)
      iapply wp_fork
      · iintro !>
        wp_pures
        wp_apply wp_rand _ _ rfl
        · itrivial
        · iintro %_ _
          itrivial
      iintro !>
      wp_pures
      wp_apply wp_couple_rand_rand _ id Function.bijective_id j _ K rfl (fun _ h => h) $$ Hspec
        with %m ⟨%Hm, Hspec⟩
      simp only [id]
      iexists m
      iframe Hspec
      ipureintro
      rfl

end Foxtrot.Examples.Libsodium
