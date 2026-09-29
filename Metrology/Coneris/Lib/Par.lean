module

public import Metrology.Coneris.Lib.Spawn

/-!
# Parallel composition

Ported from clutch/theories/coneris/lib/par.v

## Rocq → Lean mapping
* `parN`, `par`, `par_spec`, `wp_par`: same names. `par` is transcribed with the `cpl`
  notation.
* The Rocq notations `e1 ||| e2` (in `expr_scope`: `par (λ: <>, e1)%E (λ: <>, e2)%E`; in
  `val_scope`: `par (λ: <>, e1)%V (λ: <>, e2)%V`) are the definitions `par_E e1 e2` and
  `par_V e1 e2` (with an arrow notation `e1 |||ₑ e2` / `e1 |||ᵥ e2` at term level): inside
  `cpl(...)`, `|||` is already the bitwise `or`, and at term level `|||` is Lean's `HOr`.
* `(v1, v2)%V` is `PairV v1 v2`.
* `spawnG Σ` is `spawnG GF` from `Coneris.Lib.Spawn`.
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang
open Coneris.Lib.Spawn

namespace Coneris.Lib.Par

/-- Rocq: `parN`. -/
def parN : Namespace := ndot nroot "par"

/-- Rocq: `par`. -/
def par : val := cpl_val(
  λ e1 e2,
    let handle := &spawn e1;
    let v2 := e2 #();
    let v1 := &join handle;
    (v1, v2))

/-- Rocq: `e1 ||| e2` in `expr_scope`, i.e. `par (λ: <>, e1)%E (λ: <>, e2)%E`. -/
def par_E (e1 e2 : expr) : expr := cpl(&par (λ <>, &e1) (λ <>, &e2))

/-- Rocq: `e1 ||| e2` in `val_scope`, i.e. `par (λ: <>, e1)%V (λ: <>, e2)%V`. -/
def par_V (e1 e2 : expr) : expr := cpl(&par v(λ <>, &e1) v(λ <>, &e2))

@[inherit_doc] scoped infixl:55 " |||ₑ " => par_E
@[inherit_doc] scoped infixl:55 " |||ᵥ " => par_V

section proof

variable {GF : BundledGFunctors} [conerisGS GF] [spawnG GF]

/-- Rocq: `par_spec`. Notice that this allows us to strip a later *after* the two `Ψ` have
been brought together. That is strictly stronger than first stripping a later and then merging
them, as demonstrated by [tests/joining_existentials.v]. This is why these are not Texan
triples. -/
theorem par_spec (Ψ1 Ψ2 : val → IProp GF) (f1 f2 : val) (Φ : val → IProp GF) :
    ⊢ WP (App (Val f1) (Val (LitV LitUnit))) {{ Ψ1 }} -∗
      WP (App (Val f2) (Val (LitV LitUnit))) {{ Ψ2 }} -∗
      (▷ ∀ v1 v2, Ψ1 v1 ∗ Ψ2 v2 -∗ ▷ Φ (PairV v1 v2)) -∗
      WP (App (App (Val par) (Val f1)) (Val f2)) {{ Φ }} := by
  iintro Hf1 Hf2 HΦ
  wp_lam
  wp_let
  wp_apply spawn_spec parN $$ Hf1 with %l Hl
  wp_let
  wp_bind (App (Val f2) _)
  iapply pgl_wp_wand $$ Hf2
  iintro %v H2
  wp_let
  wp_apply join_spec $$ Hl with %w H1
  ispecialize HΦ $$ %w %v [H1 H2]
  · iframe
  wp_pures
  iexact HΦ

/-- Rocq: `wp_par`. -/
theorem wp_par (Ψ1 Ψ2 : val → IProp GF) (e1 e2 : expr) (Φ : val → IProp GF) :
    ⊢ WP e1 {{ Ψ1 }} -∗ WP e2 {{ Ψ2 }} -∗
      (∀ v1 v2, Ψ1 v1 ∗ Ψ2 v2 -∗ ▷ Φ (PairV v1 v2)) -∗
      WP (e1 |||ᵥ e2) {{ Φ }} := by
  iintro H1 H2 H
  unfold par_V
  iapply par_spec Ψ1 Ψ2 $$ [H1] [H2] [H]
  · wp_lam; iexact H1
  · wp_lam; iexact H2
  · inext; iexact H

end proof

end Coneris.Lib.Par
