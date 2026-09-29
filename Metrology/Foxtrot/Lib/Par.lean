module

public import Metrology.Foxtrot.Lib.Spawn

/-!
# Parallel composition

Ported from clutch/theories/foxtrot/lib/par.v

The left-hand-side part follows iris-lean's `Iris/HeapLang/Lib/Par.lean` (the port of the same
file of Rocq Iris's heap_lang), with the Foxtrot weakest precondition.

## Rocq → Lean map
* `parN`, `par`, `par_spec`, `wp_par`, `tp_par`: same names.
* The notation `e1 ||| e2` (Rocq: `par (λ: <>, e1)%E (λ: <>, e2)%E` in `expr_scope`) is the
  scoped program notation `e1 ‖ e2` inside `cpl(..)` (the token `|||` is the bitwise `or` of
  the `cpl` notation; `‖` as in iris-lean). The `val_scope` variant
  `par (λ: <>, e1)%V (λ: <>, e2)%V` is written out, `cpl(&par v(λ _, &e1) v(λ _, &e2))`.

## Deviations
* WPs are at mask `⊤` (Rocq: no mask); `(v1, v2)%V` is `PairV v1 v2`.
* Rocq's `P -∗ Q -∗ R -∗ WP ..` statements are `⊢ P -∗ Q -∗ R -∗ WP ..`; Rocq's
  `j ⤇ fill K e -∗ pupd E E (..)` is the entailment `j ⤇ fill K e ⊢ pupd E E (..)`.
* `Local Set Default Proof Using "Type*"` and `From iris.prelude Require Import options` have no
  Lean counterpart.
-/

@[expose] public section

open Iris Iris.BI Iris.Std Iris.ProofMode OFE ConProbLang ConProbLang.con_prob_lang
open Foxtrot.Lib.Spawn

namespace Foxtrot.Lib.Par

/-- Rocq: `parN`. -/
def parN : Namespace := nroot.@ "par"

/-- Rocq: `par`. -/
def par : val := cpl_val(
  λ e1 e2,
    let handle := &spawn e1 in
    let v2 := e2 #() in
    let v1 := &join handle in
    (v1, v2))

/-- Rocq: `e1 ||| e2` (in `expr_scope`), parallel composition of two expressions. -/
scoped syntax:55 cpl_exp:56 " ‖ " cpl_exp:55 : cpl_exp

macro_rules
  | `(cpl($e1 ‖ $e2)) => `(cpl(&par (λ _, $e1) (λ _, $e2)))

section proof

variable {GF : BundledGFunctors} [foxtrotGS GF] [spawnG GF]
variable {s : Stuckness}

/-- Rocq: `par_spec`. Notice that this allows us to strip a later *after* the two `Ψ` have been
brought together. That is strictly stronger than first stripping a later and then merging
them. This is why these are not Texan triples. -/
theorem par_spec (Ψ1 Ψ2 : val → IProp GF) (f1 f2 : val) (Φ : val → IProp GF) :
    ⊢ WP cpl(&f1 #()) @ s; ⊤ {{ Ψ1 }} -∗ WP cpl(&f2 #()) @ s; ⊤ {{ Ψ2 }} -∗
      (▷ ∀ v1 v2, Ψ1 v1 ∗ Ψ2 v2 -∗ ▷ Φ (PairV v1 v2)) -∗
      WP cpl(&par &f1 &f2) @ s; ⊤ {{ Φ }} := by
  iintro Hf1 Hf2 HΦ
  unfold par
  wp_pures
  wp_apply spawn_spec parN $$ Hf1 with %l Hl
  wp_pures
  wp_bind cpl(&f2 #())
  iapply wp_wand $$ Hf2
  iintro %v H2
  wp_pures
  wp_apply join_spec parN $$ Hl with %w H1
  ispecialize HΦ $$ [H1 H2]
  · iframe H1 H2
  wp_pures
  iexact HΦ

/-- Rocq: `wp_par`. -/
theorem wp_par (Ψ1 Ψ2 : val → IProp GF) (e1 e2 : expr) (Φ : val → IProp GF) :
    ⊢ WP e1 @ s; ⊤ {{ Ψ1 }} -∗ WP e2 @ s; ⊤ {{ Ψ2 }} -∗
      (∀ v1 v2, Ψ1 v1 ∗ Ψ2 v2 -∗ ▷ Φ (PairV v1 v2)) -∗
      WP cpl(&par v(λ _, &e1) v(λ _, &e2)) @ s; ⊤ {{ Φ }} := by
  iintro H1 H2 H
  iapply par_spec Ψ1 Ψ2 $$ [H1] [H2] [H]
  · wp_pures
    iexact H1
  · wp_pures
    iexact H2
  · inext
    iexact H

end proof

section proof'

variable {GF : BundledGFunctors} [foxtrotGS GF]

/-- Rocq: `tp_par`. -/
theorem tp_par (j : ℕ) (K : List ectx_item) (e1 e2 : expr) (E : CoPset) :
    j ⤇ fill K cpl(&e1 ‖ &e2) ⊢@{IProp GF}
      pupd E E iprop(∃ j1 j2 K1 K2, j1 ⤇ fill K1 e1 ∗ j2 ⤇ fill K2 e2 ∗
        (∀ (v1 v2 : val) E', j1 ⤇ fill K1 (Val v1) ∗ j2 ⤇ fill K2 (Val v2) -∗
          pupd E' E' (j ⤇ fill K (Val (PairV v1 v2))))) := by
  unfold par
  iintro Hspec
  unfold spawn
  tp_pures j
  tp_alloc j as l Hl
  tp_pures j
  tp_fork j as j' Hspec'
  tp_pures j'
  tp_pures j
  tp_bind j e2
  tp_bind j' e1
  imodintro
  iexists j', j, _, _
  iframe Hspec' Hspec
  iintro %v1 %v2 %E' ⟨Hspec', Hspec⟩
  tp_pures j
  tp_pures j'
  tp_store j'
  unfold join
  tp_pures j
  tp_load j
  tp_pures j
  imodintro
  iexact Hspec

end proof'

end Foxtrot.Lib.Par
