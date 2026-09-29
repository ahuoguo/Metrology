module

public import Metrology.Coneris.ProofMode
public import Iris.Instances.Lib.Invariants
public import Iris.Instances.Lib.Token

/-!
# Spawn and join

Ported from clutch/theories/coneris/lib/spawn.v

## Rocq → Lean mapping
* The programs `spawn` and `join` keep their names and are transcribed with the `cpl`
  notation (`SOME e` is `some(e)`, `match: .. with SOME "x" => .. | NONE => .. end` is
  `match .. with | some(x) => .. | none() => ..`).
* `spawnG Σ := SpawnG { spawn_tokG : inG Σ (exclR unitO) }` is the class `spawnG GF` with the
  field `spawn_tokG : TokenG GF` (a local instance here). iris-lean's `TokenG GF` is exactly
  `ElemG GF (constOF (Excl Unit))` (Rocq: `inG Σ (exclR unitO)`), and `own γ (Excl ())` is
  iris-lean's `token γ` (by definition `iOwn γ (excl ())`), so we use the token API
  (`token_alloc`, the `CombineSepGives` instance for `token γ ∗ token γ`) for `own_alloc` and
  `iCombine .. gives %[]`.
* `spawnΣ`, `subG_spawnΣ`: superseded by iris-lean's `ElemG` instance search; any `TokenG GF`
  gives `spawnG GF` by the instance `spawnG_of_tokenG`.
* The section variable `(N : namespace)` is an explicit argument `N : Namespace` of
  `join_handle`, `spawn_spec` and `join_spec` (it does not occur in `spawn_inv`, as in Rocq
  where it is dropped by `Section` generalization).
* `spawn_inv_ne`, `join_handle_ne` (Rocq `Proper (pointwise_relation val (dist n) ==> dist n)`)
  are `OFE.NonExpansive` instances, as in iris-lean's `HeapLang.Spawn`.
* The Texan triples are iris-lean's (at mask `⊤`).
* `Global Typeclasses Opaque join_handle`: `join_handle` is a plain `def`, which instance
  search does not unfold anyway.
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang

namespace Coneris.Lib.Spawn

/-- Rocq: `spawn`. -/
def spawn : val := cpl_val(
  λ f,
    let c := ref(none());
    fork(c ← some(f #())); c)

/-- Rocq: `join`. -/
def join : val := cpl_val(
  rec join c :=
    match !c with
    | some(x) => x
    | none() => join c)

/-- Rocq: `spawnG`. The CMRA & functor we need. -/
class spawnG (GF : BundledGFunctors) where
  spawn_tokG : TokenG GF

attribute [instance_reducible] spawnG.spawn_tokG
attribute [local instance] spawnG.spawn_tokG

/-- Replaces Rocq's `subG_spawnΣ`. -/
instance spawnG_of_tokenG {GF : BundledGFunctors} [TokenG GF] : spawnG GF := ⟨inferInstance⟩

section proof

variable {GF : BundledGFunctors} [conerisGS GF] [spawnG GF] (N : Namespace)

/-- Rocq: `spawn_inv`. -/
def spawn_inv (γ : GName) (l : Loc) (Ψ : val → IProp GF) : IProp GF :=
  iprop(∃ lv : val, l ↦ lv ∗ (⌜lv = NONEV⌝ ∨
                  ∃ w : val, ⌜lv = SOMEV w⌝ ∗ (Ψ w ∨ token γ)))

/-- Rocq: `join_handle`. -/
def join_handle (l : Loc) (Ψ : val → IProp GF) : IProp GF :=
  iprop(∃ γ : GName, token γ ∗ inv N (spawn_inv γ l Ψ))

/-- Rocq: `spawn_inv_ne`. -/
instance spawn_inv_ne (γ : GName) (l : Loc) :
    OFE.NonExpansive (spawn_inv γ l : (val → IProp GF) → _) where
  ne _ _ _ HΨ :=
    exists_ne fun _ =>
      sep_ne.ne .rfl <|
        or_ne.ne .rfl <| exists_ne fun w =>
          sep_ne.ne .rfl <| or_ne.ne (HΨ w) .rfl

/-- Rocq: `join_handle_ne`. -/
instance join_handle_ne (l : Loc) :
    OFE.NonExpansive (join_handle N l : (val → IProp GF) → _) where
  ne _ _ _ HΨ :=
    exists_ne fun γ =>
      sep_ne.ne .rfl <| (inv_ne N).ne <| (spawn_inv_ne γ l).ne HΨ

/-- Rocq: `spawn_spec`. -/
theorem spawn_spec (Ψ : val → IProp GF) (f : val) :
    {{ WP (App (Val f) (Val (LitV LitUnit))) {{ Ψ }} }} (App (Val spawn) (Val f))
    {{ l, RET LitV (LitLoc l); join_handle N l Ψ }} := by
  iintro %Φ Hf HΦ
  wp_lam
  wp_alloc l as Hl
  imod token_alloc with ⟨%γ, Hγ⟩
  imod inv_alloc N ⊤ (spawn_inv γ l Ψ) $$ [Hl] with #Hinv
  · inext
    unfold spawn_inv
    iexists _
    iframe
    ileft; itrivial
  wp_smart_apply wp_fork $$ [Hf] [HΦ Hγ]
  · wp_bind (App _ _)
    iapply pgl_wp_wand $$ Hf
    iintro %v HΨ
    wp_inj
    iinv Hinv with G
    unfold spawn_inv
    icases G with ⟨%v', Hl, -⟩
    wp_store
    isplitl
    · imodintro; inext
      iexists (SOMEV v)
      iframe Hl
      iright
      iexists v
      isplit
      · itrivial
      · ileft; iexact HΨ
    · itrivial
  · wp_pures
    iapply HΦ
    unfold join_handle
    iexists γ
    iframe Hγ Hinv

/-- Rocq: `join_spec`. -/
theorem join_spec (Ψ : val → IProp GF) (l : Loc) :
    {{ join_handle N l Ψ }} (App (Val join) (Val (LitV (LitLoc l)))) {{ v, RET v; Ψ v }} := by
  iintro %Φ H HΦ
  unfold join_handle
  icases H with ⟨%γ, Hγ, #Hinv⟩
  iloeb as IH
  wp_rec
  wp_bind (Load _)
  iinv Hinv with G
  unfold spawn_inv
  icases G with ⟨%v, Hl, Hcond⟩
  wp_load
  icases Hcond with (%Heq | ⟨%w, %Heq, (HΨ | Hγ')⟩) <;> subst Heq
  · imodintro
    isplitl [Hl]
    · inext; iexists _; iframe Hl; ileft; itrivial
    wp_pures
    iapply IH $$ [HΦ] Hγ
    inext; iexact HΦ
  · imodintro
    isplitl [Hl Hγ]
    · inext; iexists _; iframe Hl; iright; iexists w; isplit
      · itrivial
      · iright; iexact Hγ
    wp_pures
    iapply HΦ $$ HΨ
  · icombine Hγ Hγ' gives %H
    exact H.elim

end proof

end Coneris.Lib.Spawn
