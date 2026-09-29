module

public import Metrology.ConProbLang.Spec.SpecTactics
public import Metrology.Foxtrot.ProofMode

/-!
# Proof mode for the right-hand side of Foxtrot

Ported from clutch/theories/foxtrot/proofmode.v (the `rel_logic_tptactics_*` instances)

Instantiates the generic `tp_*` tactics of `Metrology.ConProbLang.Spec.SpecTactics` (Rocq:
`con_prob_lang/spec/spec_tactics.v`) for Foxtrot's update modality `pupd`.

## Rocq → Lean mapping
* `rel_logic_tptactics_pure : UpdPure pupd`, `rel_logic_tptactics_heap : UpdHeap pupd`,
  `rel_logic_tptactics_concurrency : UpdAtomicConcurrency pupd`,
  `rel_logic_tptactics_tapes : UpdTapes pupd`: same names. The fields are the theorems
  `rel_logic_tptactics_upd_*` of `Metrology.Foxtrot.ProofMode`.

## Added
* Tests (Rocq: `test_wp_tp_pures` of `proofmode.v`, with `tp_pures j`, and further tests of
  the `tp_*` tactics on small RHS programs, with the goal a WP or a `pupd`).
-/

open Iris Iris.BI Iris.Std Iris.ProofMode OFE ConProbLang ConProbLang.con_prob_lang

namespace Foxtrot

section instances

variable {GF : BundledGFunctors} [foxtrotGS GF]

/-- Rocq: `rel_logic_tptactics_pure`. -/
public instance rel_logic_tptactics_pure : UpdPure GF (pupd (GF := GF)) where
  tptac_upd_pure_step j E e1 e2 φ n H Hφ := rel_logic_tptactics_upd_pure_step j E e1 e2 φ n H Hφ

/-- Rocq: `rel_logic_tptactics_heap`. -/
public instance rel_logic_tptactics_heap : UpdHeap GF (pupd (GF := GF)) where
  tptac_upd_alloc := rel_logic_tptactics_upd_alloc
  tptac_upd_load := rel_logic_tptactics_upd_load
  tptac_upd_store := rel_logic_tptactics_upd_store

/-- Rocq: `rel_logic_tptactics_concurrency`. -/
public instance rel_logic_tptactics_concurrency : UpdAtomicConcurrency GF (pupd (GF := GF)) where
  tptac_upd_cmpxchg_fail := rel_logic_tptactics_upd_cmpxchg_fail
  tptac_upd_cmpxchg_suc := rel_logic_tptactics_upd_cmpxchg_suc
  tptac_upd_xchg := rel_logic_tptactics_upd_xchg
  tptac_upd_faa := rel_logic_tptactics_upd_faa
  tptac_upd_fork := rel_logic_tptactics_upd_fork

/-- Rocq: `rel_logic_tptactics_tapes`. -/
public instance rel_logic_tptactics_tapes : UpdTapes GF (pupd (GF := GF)) where
  tptac_upd_alloctape := rel_logic_tptactics_upd_alloctape

end instances

/-! ## Tests -/

section tests

variable {GF : BundledGFunctors} [foxtrotGS GF]
variable {s : Stuckness}

/-- Rocq: `test_wp_tp_pures`. -/
example (j : ℕ) (E : CoPset) (K : List ectx_item) :
    {{ j ⤇ fill K (BinOp PlusOp (BinOp PlusOp (Val (LitV (LitInt 2))) (Val (LitV (LitInt 2))))
        (Val (LitV (LitInt 2)))) }}
      (BinOp PlusOp (Val (LitV (LitInt 3))) (Val (LitV (LitInt 3)))) @ s; E
    {{ RET LitV (LitInt 6); (j ⤇ fill K (Val (LitV (LitInt 6))) : IProp GF) }} := by
  iintro %Ψ Hs HΨ
  tp_pures j
  wp_pures
  iapply HΨ $$ Hs

example (j : ℕ) (E : CoPset) :
    j ⤇ cpl(let x := #1 + #2; if x = #3 then (x, #true) else (#0, #false)) ⊢@{IProp GF}
      pupd E E (j ⤇ Val (PairV (LitV (LitInt 3)) (LitV (LitBool true)))) := by
  iintro Hj
  tp_pures j
  iexact Hj

example (j : ℕ) (E : CoPset) :
    j ⤇ cpl(let l := ref(#1); l ← !l + #1; !l) ⊢@{IProp GF}
      pupd E E (j ⤇ Val (LitV (LitInt 2))) := by
  iintro Hj
  tp_alloc j as l Hl
  tp_pures j
  tp_load j
  tp_pures j
  tp_store j
  tp_pures j
  tp_load j
  iexact Hj

example (j : ℕ) (E : CoPset) (l : Loc) :
    ⊢ (l ↦ₛ LitV (LitInt 1) : IProp GF) -∗ j ⤇ cpl(faa(#l, #2)) -∗
      pupd E E iprop(l ↦ₛ LitV (LitInt 3) ∗ j ⤇ Val (LitV (LitInt 1))) := by
  iintro Hl Hj
  tp_faa j
  imodintro
  iframe Hl Hj

example (j : ℕ) (E : CoPset) (l : Loc) :
    ⊢ (l ↦ₛ LitV (LitInt 1) : IProp GF) -∗ j ⤇ cpl(faa(#l, #2); cmpXchg(#l, #3, #5)) -∗
      WP (Val (LitV LitUnit)) @ E {{ v, ⌜v = LitV LitUnit⌝ ∗
        l ↦ₛ LitV (LitInt 5) ∗ j ⤇ Val (PairV (LitV (LitInt 3)) (LitV (LitBool true))) }} := by
  iintro Hl Hj
  tp_faa j
  tp_pures j
  tp_cmpxchg_suc j
  wp_pures
  iframe Hl Hj
  ipureintro
  rfl

example (j : ℕ) (E : CoPset) (l : Loc) :
    ⊢ l ↦ₛ LitV (LitInt 1) -∗ j ⤇ cpl(cmpXchg(#l, #3, #5)) -∗
      pupd (GF := GF) E E iprop(l ↦ₛ LitV (LitInt 1) ∗
        j ⤇ Val (PairV (LitV (LitInt 1)) (LitV (LitBool false)))) := by
  iintro Hl Hj
  tp_cmpxchg_fail j
  imodintro
  iframe Hl Hj

example (j : ℕ) (E : CoPset) (l : Loc) :
    ⊢ l ↦ₛ LitV (LitInt 1) -∗ j ⤇ cpl(xchg(#l, #2); !#l) -∗
      pupd (GF := GF) E E (j ⤇ Val (LitV (LitInt 2))) := by
  iintro Hl Hj
  tp_xchg j
  tp_pures j
  tp_load j
  iexact Hj

example (j : ℕ) (E : CoPset) :
    ⊢ j ⤇ cpl(fork(#1 + #1); #0) -∗
      pupd (GF := GF) E E iprop(∃ k, k ⤇ Val (LitV (LitInt 2)) ∗ j ⤇ Val (LitV (LitInt 0))) := by
  iintro Hj
  tp_fork j as k Hk
  tp_pures j
  tp_pures k
  imodintro
  iexists k
  iframe Hj Hk

example (j : ℕ) (E : CoPset) :
    ⊢ j ⤇ cpl(fork(#1); #0) -∗ pupd (GF := GF) E E (j ⤇ Val (LitV (LitInt 0))) := by
  iintro Hj
  tp_fork j
  iintro %k -
  tp_pures j
  iexact Hj

example (j : ℕ) (E : CoPset) :
    ⊢ j ⤇ cpl(alloc(#1)) -∗
      pupd (GF := GF) E E iprop(∃ α, α ↪ₛN (1; []) ∗ j ⤇ Val (LitV (LitLbl α))) := by
  iintro Hj
  tp_allocnattape j α as Hα
  imodintro
  iexists α
  iframe Hj Hα

example (j : ℕ) (E : CoPset) (K : List ectx_item) :
    ⊢ j ⤇ fill K (Snd cpl((#1 + #2, #3))) -∗ pupd (GF := GF) E E (j ⤇ fill K cpl(#3)) := by
  iintro Hj
  tp_bind j (Pair _ _)
  tp_pure j
  tp_pure j
  tp_normalise j
  tp_snd j
  iexact Hj

example (j : ℕ) (E : CoPset) :
    ⊢ j ⤇ If (Val (LitV (LitBool true))) (Case (Val (InjLV (LitV (LitInt 1))))
        (Val (LitV (LitInt 5))) (Val (LitV (LitInt 6)))) (Val (LitV (LitInt 0))) -∗
      pupd (GF := GF) E E (j ⤇ App (Val (LitV (LitInt 5))) (Val (LitV (LitInt 1)))) := by
  iintro Hj
  tp_if_true j
  tp_case_inl j
  iexact Hj

example (j : ℕ) (E : CoPset) :
    ⊢ j ⤇ App (Val (RecV .BAnon (.BNamed "x") (BinOp PlusOp (Var "x") (Val (LitV (LitInt 1))))))
        (Val (LitV (LitInt 1))) -∗
      pupd (GF := GF) E E (j ⤇ Val (LitV (LitInt 2))) := by
  iintro Hj
  tp_rec j
  tp_pures j
  iexact Hj

end tests

end Foxtrot
