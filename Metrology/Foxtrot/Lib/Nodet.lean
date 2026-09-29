module

public import Metrology.Foxtrot.SpecProofMode

/-!
# A nondeterministic natural number

Ported from clutch/theories/foxtrot/lib/nodet.v

`nodet #()` forks a thread incrementing a fresh counter forever and reads the counter: it
returns some natural number (`wp_nodet`), and on the right-hand side it can be made to return
any natural number (`tp_nodet`), by scheduling the forked thread `n` times first.

## Rocq → Lean map
* `nodetN`, `nodet`, `wp_nodet`, `tp_nodet`: same names.

## Deviations
* Texan triples are iris-lean's `{{ P }} (e) @ s; ⊤ {{ (x : ℕ), RET v; Q }}` (Rocq: no mask,
  i.e. `⊤`); `#x` for `x : ℕ` is `LitV (LitInt (x : ℤ))`.
* Rocq's `j ⤇ fill K e -∗ pupd E E (..)` is the entailment `j ⤇ fill K e ⊢ pupd E E (..)`.
* The Rocq proof of `tp_nodet` does an `iInduction n` inside an `iAssert`; here the induction
  is the separate lemma `tp_nodet_loop` (about the forked loop, with `#l` for `"x"`).
* `Local Set Default Proof Using "Type*"` has no Lean counterpart.

## Added
* `tp_nodet_loop` (the induction of `tp_nodet`).
-/

@[expose] public section

open Iris Iris.BI Iris.Std Iris.ProofMode OFE ConProbLang ConProbLang.con_prob_lang

namespace Foxtrot.Lib.Nodet

/-- Rocq: `nodetN`. -/
def nodetN : Namespace := nroot.@ "nodet"

/-- Rocq: `nodet`. -/
def nodet : val := cpl_val(
  λ _,
    let x := ref(#0) in
    fork((rec f _ :=
             x ← !x + #1;
             f #()
          ) #());
    !x)

section proof

variable {GF : BundledGFunctors} [foxtrotGS GF]
variable {s : Stuckness}

/-- Rocq: `wp_nodet`. -/
theorem wp_nodet :
    {{ True }} (cpl(&nodet #())) @ s; ⊤ {{ (x : ℕ), RET LitV (LitInt (x : ℤ)); (True : IProp GF) }} := by
  unfold nodet
  iintro %Φ - HΦ
  wp_pures
  wp_alloc l as Hl
  wp_pures
  imod inv_alloc nodetN ⊤ iprop(∃ n : ℕ, l ↦ LitV (LitInt (n : ℤ))) $$ [Hl] with #Hinv
  · inext
    iexists 0
    iexact Hl
  wp_apply wp_fork $$ [] [HΦ]
  · wp_pure
    iloeb as IH
    wp_pures
    wp_bind (Load _)
    iinv Hinv with ⟨%n, >Hl⟩ Hclose
    wp_load
    imod Hclose $$ [Hl]
    · inext
      iexists n
      iexact Hl
    imodintro
    wp_pures
    wp_bind (Store _ _)
    iinv Hinv with ⟨%m, >Hl⟩ Hclose
    wp_store
    rw [show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by push_cast; rfl]
    imod Hclose $$ [Hl]
    · inext
      iexists n + 1
      iexact Hl
    imodintro
    wp_pure
    wp_pure
    iexact IH
  · wp_pures
    iinv Hinv with ⟨%n, >Hl⟩ Hclose
    wp_load
    imod Hclose $$ [Hl]
    · inext
      iexists n
      iexact Hl
    imodintro
    iapply HΦ $$ %n []
    itrivial

end proof

section proof'

variable {GF : BundledGFunctors} [foxtrotGS GF]

/-- Added: the induction of Rocq's `tp_nodet` (inside its `iAssert`): running the forked loop
`n` times on the right-hand side. -/
theorem tp_nodet_loop (E : CoPset) (j' : ℕ) (l : Loc) (n : ℕ) :
    l ↦ₛ LitV (LitInt 0) ∗ j' ⤇ cpl(v(rec f _ := #l ← !#l + #1; f #()) #()) ⊢@{IProp GF}
      pupd E E iprop(l ↦ₛ LitV (LitInt (n : ℤ)) ∗ j' ⤇ cpl(v(rec f _ := #l ← !#l + #1; f #()) #())) := by
  induction n with
  | zero =>
    iintro ⟨Hl, Hspec'⟩
    imodintro
    iframe Hl Hspec'
  | succ n IH =>
    iintro H
    imod IH $$ H with ⟨Hl, Hspec'⟩
    tp_pures j'
    tp_load j'
    tp_pures j'
    tp_store j'
    tp_pure j'
    tp_pure j'
    rw [show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by push_cast; rfl]
    imodintro
    iframe Hl Hspec'

/-- Rocq: `tp_nodet`. -/
theorem tp_nodet (j : ℕ) (K : List ectx_item) (E : CoPset) (n : ℕ) :
    j ⤇ fill K cpl(&nodet #()) ⊢@{IProp GF} pupd E E (j ⤇ fill K (Val (LitV (LitInt (n : ℤ))))) := by
  unfold nodet
  iintro Hspec
  tp_pures j
  tp_alloc j as l Hl
  tp_pures j
  tp_fork j as j' Hspec'
  tp_pures j
  tp_pure j'
  imod tp_nodet_loop E j' l n $$ [$Hl $Hspec'] with ⟨Hl, Hspec'⟩
  tp_load j
  imodintro
  iexact Hspec

end proof'

end Foxtrot.Lib.Nodet
