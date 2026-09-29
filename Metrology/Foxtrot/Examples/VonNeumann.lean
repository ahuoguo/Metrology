module

public import Metrology.Foxtrot.Lib.Conversion
public import Metrology.Foxtrot.Lib.Min
public import Metrology.Foxtrot.Lib.Par
public import Metrology.Foxtrot.CouplingRulesMisc
public import Metrology.Foxtrot.CouplingRulesVonNeumann
public import Metrology.Foxtrot.BinaryRel.BinarySoundness
public import Metrology.Foxtrot.BinaryRel.BinaryRelTactics
public import Metrology.Foxtrot.BinaryRel.BinaryFundamentalPart4
public import Metrology.Foxtrot.UnaryRel.UnaryFundamental
public import Metrology.Foxtrot.AdequacyInstance

/-!
# The von Neumann trick: programs and the first refinement step

Ported from clutch/theories/foxtrot/examples/von_neumann.v (part 1: definitions,
`length_bind`, `wp_von_neumann_prog_von_neumann_prog'`).

The von Neumann trick turns a biased coin (here: `rand #(S N) ≤ bias`, where the bias is read
from a location that a typed adversary `ad` may concurrently modify) into a fair coin: flip twice
until the outcomes differ, and return the first one. The final theorem
`von_neumann_prog_eq_rand_prog` (in `VonNeumannPart5`) shows that the program is contextually
equivalent to a fair coin flip.

The port is split into five modules:
* `VonNeumann` (this file): the programs, `length_bind`, the functor list, and
  `wp_von_neumann_prog_von_neumann_prog'`;
* `VonNeumannPart2`: `wp_von_neumann_prog'_rand_prog`;
* `VonNeumannPart3`: `wp_rand_prog_rand_prog'`, `wp_rand_prog'_von_neumann_con_prog`;
* `VonNeumannPart4`: `wp_von_neumann_con_prog_von_neumann_con_prog'`;
* `VonNeumannPart5`: `wp_von_neumann_con_prog'_von_neumann_prog`, and the contextual refinements
  `von_neumann_prog_refines_rand_prog`, `rand_prog_refines_von_neumann_prog`,
  `von_neumann_prog_eq_rand_prog`.

## Rocq → Lean map
* `flipL`, `flip`, `length_bind`, `Htyped`, `von_neumann_prog`, `von_neumann_prog'`,
  `von_neumann_con_prog`, `von_neumann_con_prog'`, `rand_prog`, `rand_prog'` and all the lemmas:
  same names (namespace `Foxtrot.Examples.VonNeumann`).
* The section variables `N : nat` and `ad : val` are explicit arguments (each definition only
  takes the variables it uses, as Rocq abstracts over the used section variables only). The
  hypothesis `Htyped ad` (Rocq: `Htyped -> ...`) is an explicit argument `Ht`.
* Rocq's `l1 ≫= (λ x, (λ y, (x, y)) <$> l2)` is `l1.flatMap (fun x => l2.map (fun y => (x, y)))`.
* `#[spawnΣ; foxtrotRΣ]` is the concrete functor list `vonNeumannSigma` (with the instances
  `foxtrotRGpreS_vonNeumannSigma`, `spawnG_vonNeumannSigma`), `#[foxtrotRΣ]` is `foxtrotSigma`
  (with the instance `foxtrotRGpreS_foxtrotSigma`).
* `binary_fundamental.refines_typed` is `Foxtrot.BinaryRel.refines_typed`; `typed_safe` (of
  `unary_fundamental`) is `Foxtrot.UnaryRel.typed_safe`.

## Deviations
* `#(S N)` is `#((N + 1 : ℕ))`; `#1%nat` is `#((1 : ℕ))`; `(e1 ||| e2)` is `e1 ‖ e2` (scoped
  notation of `Foxtrot.Lib.Par`); `let, ("x", "y") := e1 in e2` is `let ("x", "y") := e1; e2`.
* `Htyped` is a `def` of `ad` (Rocq: a `Definition` inside the section); `TRef TNat → TUnit` is
  `TArrow (TRef TNat) TUnit` and `(() → lrel_bool)%lrel` is `lrel_arr lrel_unit lrel_bool`.
* The `wp_*` lemmas are stated as `⊢ j ⤇ fill K e' -∗ WP e {{ .. }}` (mask `⊤`).
* The invariant allocated by `inv_alloc _ _ ..` gets the namespace `logN.@ (l, l')` of
  `lrel_ref` explicitly (Rocq: an evar unified later).
* Rocq's `iMod (pupd_fork with "[$]") as "[Hspec [%j' Hspec']]"` is `tp_fork j as j' Hspec'`.
* The couplings take the bijection `id` explicitly (Rocq: inferred).
* `bool_decide_eq_true_2` / `bool_decide_eq_false_2` / `case_bool_decide` are
  `decide_eq_true` / `decide_eq_false` / `by_cases`.

## Added
* `vonNeumannSigma`, `foxtrotRGpreS_vonNeumannSigma`, `spawnG_vonNeumannSigma`,
  `foxtrotRGpreS_foxtrotSigma` (the Rocq functor lists with their `subG` instances; iris-lean
  has no `gFunctors` lists); `fill_nil'` (Rocq: `fill_empty`, for `con_prob_lang`'s `fill`),
  `fill_app_rctx`.
* `wp_ad_fork`: the forked-adversary part of the proofs of
  `wp_von_neumann_prog_von_neumann_prog'`, `wp_von_neumann_con_prog_von_neumann_con_prog'` and
  `wp_von_neumann_con_prog'_von_neumann_prog` (inlined three times in Rocq).

## Omitted
None.
-/

@[expose] public section

noncomputable section

open scoped ENNReal NNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE ConProbLang ConProbLang.con_prob_lang
open Foxtrot Foxtrot.BinaryRel Foxtrot.Lib.Spawn Foxtrot.Lib.Par Foxtrot.Lib.Min
open Foxtrot.Lib.Conversion

namespace Foxtrot.Examples.VonNeumann

/-! ## Functor lists -/

/-- The functor list of Rocq's `#[spawnΣ; foxtrotRΣ]`: `foxtrotSigma` (Rocq: `foxtrotRΣ`
is `foxtrotΣ`) extended with the token functor of `spawnΣ`. -/
def vonNeumannSigma : BundledGFunctors
  | 0 => ⟨InvMapF, by infer_instance⟩
  | 1 => ⟨constOF CoPsetDisjL, by infer_instance⟩
  | 2 => ⟨constOF (DisjointLeibnizSet PosSet), by infer_instance⟩
  | 3 => ⟨Auth.AuthURF (constOF Credit), by infer_instance⟩
  | 4 => ⟨constOF (HeapView Loc (Agree (DiscreteO val)) locF), by infer_instance⟩
  | 5 => ⟨constOF (HeapView Loc (Agree (DiscreteO tape)) locF), by infer_instance⟩
  | 6 => ⟨constOF (HeapView ℕ (Agree (DiscreteO expr)) tpoolF), by infer_instance⟩
  | 7 => ⟨constOF (Auth ErrorCredit), by infer_instance⟩
  | 8 => ⟨TokenF, by infer_instance⟩
  | _ => ⟨constOF Unit, by infer_instance⟩

/-- Rocq: `subG_foxtrotRGPreS` (at `vonNeumannSigma`). -/
instance foxtrotRGpreS_vonNeumannSigma : foxtrotRGpreS vonNeumannSigma where
  foxtrotRGpreS_foxtrot := {
    foxtrotGpreS_iris := {
      toWsatGpreS := ⟨⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩⟩
      toLcGpreS := ⟨⟨3, rfl⟩⟩ }
    foxtrotGpreS_heap := ⟨⟨4, rfl⟩⟩
    foxtrotGpreS_tapes := ⟨⟨5, rfl⟩⟩
    foxtrotGpreS_spec := ⟨⟨⟨6, rfl⟩⟩, ⟨⟨4, rfl⟩⟩, ⟨⟨5, rfl⟩⟩⟩
    foxtrotGpreS_err := ⟨⟨7, rfl⟩⟩ }

/-- Rocq: `subG_foxtrotRGPreS` (at `foxtrotSigma`, Rocq's `foxtrotRΣ`). -/
instance foxtrotRGpreS_foxtrotSigma : foxtrotRGpreS foxtrotSigma := ⟨inferInstance⟩

/-- Rocq: `subG_spawnΣ` (at `vonNeumannSigma`). -/
instance spawnG_vonNeumannSigma : spawnG vonNeumannSigma where
  spawn_tokG := ⟨8, rfl⟩

/-! ## Programs -/

/-- Rocq: `flipL`. -/
def flipL : val := cpl_val(λ "e", &int_to_bool (rand("e") #((1 : ℕ))))

/-- Rocq: `flip`. -/
def flip : expr := cpl(&flipL #())

/-- Rocq: `length_bind`. -/
theorem length_bind {A : Type} (l1 l2 : List A) :
    (l1.flatMap (fun x => l2.map (fun y => (x, y)))).length = l1.length * l2.length := by
  induction l1 with
  | nil => simp
  | cons a l1 IH =>
    simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_cons] at *
    rw [IH, Nat.succ_mul, Nat.add_comm]

section von_neumann

variable (N : ℕ) (ad : val)

/-- Rocq: `Htyped`. -/
def Htyped : Prop := (∅ ⊢ₜ Val ad : TArrow (TRef TNat) TUnit)

/-- Rocq: `von_neumann_prog`. -/
def von_neumann_prog : val := cpl_val(
  λ "ad",
    let "l" := ref(#0) in
    fork("ad" "l");
    (rec "f" "_" :=
       let "bias" := &min_prog (!"l") #N in
       let "x" := (rand(#((N + 1 : ℕ)))) ≤ "bias" in
       let "y" := (rand(#((N + 1 : ℕ)))) ≤ "bias" in
       if "x" = "y" then "f" #() else "x"))

/-- Rocq: `von_neumann_prog'`. -/
def von_neumann_prog' : val := cpl_val(
  λ "ad",
    let "l" := ref(#0) in
    fork("ad" "l");
    (rec "f" "_" :=
       let "bias" := &min_prog (!"l") #N in
       let "α" := alloc(#((N + 1 : ℕ))) in
       let "β" := alloc(#((N + 1 : ℕ))) in
       let "x" := (rand("α") #((N + 1 : ℕ))) ≤ "bias" in
       let "y" := (rand("β") #((N + 1 : ℕ))) ≤ "bias" in
       if "x" = "y" then "f" #() else "x"))

/-- Rocq: `von_neumann_con_prog`. -/
def von_neumann_con_prog : val := cpl_val(
  λ "ad",
    let "l" := ref(#0) in
    fork("ad" "l");
    (rec "f" "_" :=
       let "bias" := &min_prog (!"l") #N in
       let ("x", "y") := (((rand(#((N + 1 : ℕ)))) ≤ "bias") ‖ ((rand(#((N + 1 : ℕ)))) ≤ "bias"));
       if "x" = "y" then "f" #() else "x"))

/-- Rocq: `von_neumann_con_prog'`. -/
def von_neumann_con_prog' : val := cpl_val(
  λ "ad",
    let "l" := ref(#0) in
    fork("ad" "l");
    (rec "f" "_" :=
       let "bias" := &min_prog (!"l") #N in
       let "α" := alloc(#((N + 1 : ℕ))) in
       let "β" := alloc(#((N + 1 : ℕ))) in
       let ("x", "y") :=
         (((rand("α") #((N + 1 : ℕ))) ≤ "bias") ‖ ((rand("β") #((N + 1 : ℕ))) ≤ "bias"));
       if "x" = "y" then "f" #() else "x"))

/-- Rocq: `rand_prog`. -/
def rand_prog : val := cpl_val(
  λ "_" "_", &flip)

/-- Rocq: `rand_prog'`. -/
def rand_prog' : val := cpl_val(
  λ "_" "_", let "x" := alloc(#((1 : ℕ))) in &flipL "x")

end von_neumann

/-- Helper (Rocq: `fill_empty`): `fill [] e = e`, for the `con_prob_lang` `fill` of the spec
points-to. -/
theorem fill_nil' (e : expr) : fill [] e = e := rfl

/-- Helper (Rocq: implicit, `fill` computes): plugging into `AppRCtx f :: K`. -/
theorem fill_app_rctx (f : val) (K : List ectx_item) (e : expr) :
    fill ([AppRCtx f] ++ K) e = fill K (App (Val f) e) := fill_app' _ _ _

section proof

variable (N : ℕ) (ad : val)
variable {GF : BundledGFunctors} [foxtrotRGS GF]

/-- Added (Rocq: the forked-thread part of the proofs of `wp_von_neumann_prog_von_neumann_prog'`,
`wp_von_neumann_con_prog_von_neumann_con_prog'` and `wp_von_neumann_con_prog'_von_neumann_prog`,
done inline three times in Rocq): by the binary fundamental theorem, the typed adversary `ad`
applied to the related locations `l`, `l'` is safe on the left, while running `ad #l'` on the
right. -/
theorem wp_ad_fork (Ht : Htyped ad) (l l' : Loc) (j' : ℕ) :
    ⊢ inv (logN.@ (l, l'))
        iprop(∃ v0 v3 : val, l ↦ v0 ∗ l' ↦ₛ v3 ∗ (lrel_nat : lrel GF) v0 v3) -∗
      j' ⤇ cpl(&ad #l') -∗ WP cpl(&ad #l) {{ _v, True }} := by
  iintro #Hinv Hspec'
  ihave H := refines_typed (GF := GF) _ [] _ Ht
  wp_bind (Val ad)
  tp_bind j' (Val ad)
  unfold BinaryRel.refines BinaryRel.refines_def
  iapply wp_wand $$ [Hspec']
  · iapply H $$ Hspec'
  iintro %v ⟨%v', Hspec', #Hrel⟩
  dsimp only [interp, lrel_arr, lrel_ref, lrel_unit]
  ihave H2 := Hrel $$ %_ %_ []
  · iexists l, l'
    isplit
    · ipureintro; rfl
    isplit
    · ipureintro; rfl
    iexact Hinv
  unfold BinaryRel.refines BinaryRel.refines_def
  ihave H3 := H2 $$ %([] : List ectx_item) %j' [Hspec']
  · rw [show fill [] (App (Val v') (Val (LitV (LitLoc l')))) =
        fill [AppLCtx (LitV (LitLoc l'))] (Val v') from rfl]
    iexact Hspec'
  iapply wp_wand $$ H3
  iintro %_ -
  itrivial

/-- Rocq: `wp_von_neumann_prog_von_neumann_prog'`. -/
theorem wp_von_neumann_prog_von_neumann_prog' (Ht : Htyped ad) (K : List ectx_item) (j : ℕ) :
    ⊢ j ⤇ fill K cpl(&(von_neumann_prog' N) &ad) -∗
      WP cpl(&(von_neumann_prog N) &ad)
        {{ v, ∃ v' : val, j ⤇ fill K (Val v') ∗
          (lrel_arr lrel_unit lrel_bool : lrel GF) v v' }} := by
  iintro Hspec
  unfold von_neumann_prog' von_neumann_prog
  wp_pures
  tp_pures j
  wp_alloc l as Hl
  wp_pures
  tp_alloc j as l' Hl'
  tp_pures j
  imod inv_alloc (logN.@ (l, l')) ⊤
      iprop(∃ v0 v3 : val, l ↦ v0 ∗ l' ↦ₛ v3 ∗ (lrel_nat : lrel GF) v0 v3) $$ [Hl Hl']
    with #Hinv
  · inext
    iexists _, _
    iframe Hl Hl'
    dsimp only [lrel_nat]
    iexists 0
    ipureintro
    exact ⟨rfl, rfl⟩
  tp_fork j as j' Hspec'
  wp_apply wp_fork $$ [Hspec']
  · iapply wp_ad_fork ad Ht $$ Hinv Hspec'
  tp_pures j
  wp_pures
  iexists _
  iframe Hspec
  imodintro
  dsimp only [lrel_arr, lrel_unit]
  imodintro
  iintro %v1 %v2 %⟨h1, h2⟩
  subst h1 h2
  unfold BinaryRel.refines BinaryRel.refines_def
  iintro %K' %j'' Hspec
  iloeb as IH generalizing Hspec
  wp_pures
  tp_pures j''
  wp_bind (Load _)
  dsimp only [lrel_nat]
  iinv Hinv with ⟨%v0, %v3, >Hl, >Hl', >⟨%n, %h1, %h2⟩⟩ Hclose
  subst h1 h2
  tp_load j''
  wp_load
  imod Hclose $$ [Hl Hl']
  · inext
    iexists _, _
    iframe Hl Hl'
    iexists n
    ipureintro
    exact ⟨rfl, rfl⟩
  imodintro
  tp_bind j'' (App (App (Val min_prog) _) _)
  imod spec_min_prog ⊤ j'' _ (n : ℤ) (N : ℤ) $$ Hspec with Hspec
  wp_apply wp_min_prog (n : ℤ) (N : ℤ) ⊤ $$ [] with %z %Hz
  · itrivial
  subst Hz
  wp_pures
  tp_pures j''
  tp_allocnattape j'' α as Hα
  tp_pures j''
  tp_allocnattape j'' β as Hβ
  tp_pures j''
  tp_bind j'' (Rand _ _)
  wp_bind (Rand _ _)
  wp_apply wp_couple_rand_rand_lbl (N + 1) id Function.bijective_id ((N + 1 : ℕ) : ℤ) _ α j''
    (by simp) (fun n hn => hn) $$ [Hα Hspec] with %x ⟨-, Hspec, %Hx⟩
  · iframe Hα Hspec
  simp only [id]
  wp_pures
  tp_pures j''
  tp_bind j'' (Rand _ _)
  wp_bind (Rand _ _)
  wp_apply wp_couple_rand_rand_lbl (N + 1) id Function.bijective_id ((N + 1 : ℕ) : ℤ) _ β j''
    (by simp) (fun n hn => hn) $$ [Hβ Hspec] with %y ⟨-, Hspec, %Hy⟩
  · iframe Hβ Hspec
  simp only [id]
  tp_pures j''
  wp_pures
  by_cases h : (x ≤ n ∧ x ≤ N ↔ y ≤ n ∧ y ≤ N)
  · simp only [← Bool.decide_and, decide_eq_decide.mpr h, decide_true]
    tp_pure j''
    wp_pure
    iapply IH $$ Hspec
  · simp only [← Bool.decide_and, decide_eq_decide, h, decide_false]
    tp_pures j''
    wp_pure
    iexists _
    iframe Hspec
    dsimp only [lrel_bool]
    iexists _
    ipureintro
    exact ⟨rfl, rfl⟩

end proof

end Foxtrot.Examples.VonNeumann
