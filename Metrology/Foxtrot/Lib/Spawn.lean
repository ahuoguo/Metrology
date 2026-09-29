module

public import Metrology.Foxtrot.SpecProofMode
public import Iris.Instances.Lib.Token
public import Iris.Instances.Lib.Invariants

/-!
# Spawning a thread and joining it

Ported from clutch/theories/foxtrot/lib/spawn.v

The file follows iris-lean's `Iris/HeapLang/Lib/Spawn.lean` (the port of the same file of Rocq
Iris's heap_lang), with the Foxtrot weakest precondition.

## Rocq → Lean map
* `spawn`, `join`, `spawnG` (field `spawn_tokG`), `spawn_inv`, `join_handle`, `spawn_inv_ne`,
  `join_handle_ne`, `spawn_spec`, `join_spec`: same names.

## Deviations
* `spawnG Σ := { spawn_tokG : inG Σ (exclR unitO) }` is a class with the iris-lean instance
  field `spawn_tokG : ElemG GF TokenF`, where `TokenF = constOF (Excl Unit)` is iris-lean's
  functor for `exclR unitO`. `Local Existing Instance spawn_tokG` is the instance
  `spawnG_tokenG : TokenG GF`, so that `own γ (Excl ())` is iris-lean's `token γ`
  (`iOwn γ (excl ())`), with `token_alloc` (Rocq: `own_alloc (Excl ())`) and `token_exclusive`
  (Rocq: `iCombine .. gives %[]`).
* The section variable `N : namespace` is an explicit argument of `join_handle`, `spawn_spec`
  and `join_spec` (as in iris-lean).
* `spawn_inv_ne`/`join_handle_ne` (Rocq: `Proper (pointwise_relation val (dist n) ==> dist n)`)
  are `OFE.NonExpansive` instances (as in iris-lean).
* Texan triples are iris-lean's `{{ P }} (e) @ s; ⊤ {{ l, RET v; Q }}` (Rocq: no mask, `⊤`).
* `Global Typeclasses Opaque join_handle`: `join_handle` is a `def`, hence already opaque to
  instance search.

## Omitted
* `spawnΣ` and `subG_spawnΣ`: iris-lean has no `gFunctors` lists / `subG` (the `ElemG` instances
  are found directly), as in iris-lean's `Spawn.lean` and in `Coneris.Adequacy`.
-/

@[expose] public section

open Iris Iris.BI Iris.Std Iris.ProofMode OFE ConProbLang ConProbLang.con_prob_lang

namespace Foxtrot.Lib.Spawn

/-- Rocq: `spawn`. -/
def spawn : val := cpl_val(
  λ f,
    let c := ref(none()) in
    fork(c ← some(f #())); c)

/-- Rocq: `join`. -/
def join : val := cpl_val(
  rec join c :=
    match !c with
    | some(x) => x
    | none() => join c)

/-- Rocq: `spawnG`. The CMRA we need (Rocq: `inG Σ (exclR unitO)`). -/
class spawnG (GF : BundledGFunctors) where
  [spawn_tokG : ElemG GF TokenF]

/-- Rocq: `Local Existing Instance spawn_tokG`: the token ghost state of `spawnG`. -/
instance spawnG_tokenG {GF : BundledGFunctors} [spawnG GF] : TokenG GF where
  elemG := spawnG.spawn_tokG

/-! ## The Iris part of the proof -/

section proof

variable {GF : BundledGFunctors} [foxtrotGS GF] [spawnG GF] (N : Namespace)
variable {s : Stuckness}

/-- Rocq: `spawn_inv`. -/
def spawn_inv (γ : GName) (l : Loc) (Ψ : val → IProp GF) : IProp GF :=
  iprop(∃ lv, l ↦ lv ∗ (⌜lv = NONEV⌝ ∨
                  ∃ w, ⌜lv = SOMEV w⌝ ∗ (Ψ w ∨ token γ)))

/-- Rocq: `join_handle`. -/
def join_handle (l : Loc) (Ψ : val → IProp GF) : IProp GF :=
  iprop(∃ γ, token γ ∗ inv N (spawn_inv γ l Ψ))

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
    {{ WP cpl(&f #()) @ s; ⊤ {{ Ψ }} }} (cpl(&spawn &f)) @ s; ⊤
    {{ l, RET LitV (LitLoc l); join_handle N l Ψ }} := by
  iintro %Φ Hf HΦ
  unfold spawn
  wp_pures
  wp_alloc l as Hl
  imod token_alloc with ⟨%γ, Hγ⟩
  imod inv_alloc N ⊤ (spawn_inv γ l Ψ) $$ [Hl] with #Hinv
  · inext
    unfold spawn_inv
    iexists NONEV
    iframe Hl
    ileft
    itrivial
  wp_pures
  wp_smart_apply wp_fork $$ [Hf] [HΦ Hγ]
  · wp_bind (App _ _)
    iapply wp_wand $$ Hf
    iintro %v Hv
    wp_pures
    iinv Hinv with Hpt Hclose
    unfold spawn_inv
    icases Hpt with ⟨%v', Hl, -⟩
    wp_store
    imod Hclose $$ [Hl Hv]
    · inext
      iexists SOMEV v
      iframe Hl
      iright
      iexists v
      isplitr
      · ipureintro
        rfl
      · ileft
        iexact Hv
    imodintro
    itrivial
  · wp_pures
    iapply HΦ $$ %l
    unfold join_handle
    iexists γ
    iframe Hγ Hinv

/-- Rocq: `join_spec`. -/
theorem join_spec (Ψ : val → IProp GF) (l : Loc) :
    {{ join_handle N l Ψ }} (cpl(&join #l)) @ s; ⊤ {{ v, RET v; Ψ v }} := by
  iintro %Φ H HΦ
  unfold join_handle
  icases H with ⟨%γ, Hγ, #Hinv⟩
  iloeb as IH
  unfold join
  wp_pure
  wp_bind (Load _)
  iinv Hinv with Hpt Hclose
  unfold spawn_inv
  icases Hpt with ⟨%v, Hl, Hinv'⟩
  wp_load
  icases Hinv' with (%Heq | ⟨%v', %Heq, (HΨ | Hγ')⟩) <;> subst Heq
  · imod Hclose $$ [Hl]
    · inext
      iexists NONEV
      iframe Hl
      ileft
      itrivial
    imodintro
    wp_smart_apply IH $$ [HΦ] Hγ
    iexact HΦ
  · imod Hclose $$ [Hl Hγ]
    · inext
      iexists SOMEV v'
      iframe Hl
      iright
      iexists v'
      isplitr
      · ipureintro
        rfl
      · iright
        iexact Hγ
    imodintro
    wp_pures
    iapply HΦ $$ HΨ
  · icombine Hγ Hγ' gives %⟨⟩

end proof

end Foxtrot.Lib.Spawn
