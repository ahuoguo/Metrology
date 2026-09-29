module

public import Metrology.Foxtrot.Examples.BatchSampling

/-!
# Sequential version of the batch sampler

Ported from clutch/theories/foxtrot/examples/batch_sampling_seq.v

## Rocq → Lean map
* `seq_batch_prog`, `seq_batch_prog'`, `rand_prog`, `wp_seq_batch_prog_seq_batch_prog'`,
  `wp_seq_batch_prog'_rand_prog`, `wp_batch_prog'_seq_batch_prog`,
  `seq_batch_prog_refines_rand_prog`, `rand_prog_refines_seq_batch_prog`,
  `seq_batch_prog_eq_rand_prog`: same names (namespace `Foxtrot.Examples.BatchSamplingSeq`).
  `rand_prog` is a new definition (as in Rocq, which redefines it), equal by `rfl` to
  `Foxtrot.Examples.BatchSampling.rand_prog`.
* The section variables `N M : nat` are explicit arguments.
* `#[foxtrotRΣ]` is `foxtrotSigma` (with the local instance `foxtrotRGpreS_foxtrotSigma`), `#[spawnΣ; foxtrotRΣ]` is `BatchSampling.batchSigma`.

## Deviations
* As in `Metrology.Foxtrot.Examples.BatchSampling` (masks, `id` bijections, `rewrite /interp/=`,
  `lia`).
* In `rand_prog_refines_seq_batch_prog`, the step through `wp_batch_prog_batch_prog'` uses
  `wp_apply` (Rocq: `iApply (.. with "[$]"); iNext; by iIntros`), which is the same proof.

## Omitted
None.
-/

@[expose] public section

noncomputable section

open Iris Iris.BI Iris.Std Iris.ProofMode OFE ConProbLang ConProbLang.con_prob_lang
open Foxtrot Foxtrot.BinaryRel Foxtrot.Lib.Spawn Foxtrot.Lib.Par
open Foxtrot.Examples.BatchSampling (coupling_f coupling_f_cond1 coupling_f_cond2
  coupling_f_cond3 batch_prog batch_prog' batchSigma wp_batch_prog_batch_prog'
  rand_prog_refines_batch_prog)

namespace Foxtrot.Examples.BatchSamplingSeq

/-- Rocq: `subG_foxtrotRGPreS` (at `foxtrotSigma`, Rocq's `foxtrotRΣ`). Local, as in the other
examples, so that importing several examples does not create duplicate global instances. -/
local instance foxtrotRGpreS_foxtrotSigma : foxtrotRGpreS foxtrotSigma := ⟨inferInstance⟩

section batch

variable (N M : ℕ)

/-- Rocq: `seq_batch_prog`. -/
def seq_batch_prog : val := cpl_val(
  λ "_",
    let "x" := rand(#N) in
    let "y" := rand(#M) in
    "x" * #((M + 1 : ℕ)) + "y")

/-- Rocq: `seq_batch_prog'`. -/
def seq_batch_prog' : val := cpl_val(
  λ "_",
    let "α" := alloc(#N) in
    let "α'" := alloc(#M) in
    let "x" := rand("α") #N in
    let "y" := rand("α'") #M in
    "x" * #((M + 1 : ℕ)) + "y")

/-- Rocq: `rand_prog`. -/
def rand_prog : val := cpl_val(λ "_", rand(#(((N + 1) * (M + 1) - 1 : ℕ))))

section proof

variable {GF : BundledGFunctors} [foxtrotRGS GF]

/-- Rocq: `wp_seq_batch_prog_seq_batch_prog'`. -/
theorem wp_seq_batch_prog_seq_batch_prog' (K : List ectx_item) (j : ℕ) :
    {{ j ⤇ fill K cpl(&(seq_batch_prog' N M) #()) }}
      (cpl(&(seq_batch_prog N M) #()))
    {{ v, RET v; ∃ v' : val, j ⤇ fill K (Val v') ∗ (lrel_nat : lrel GF) v v' }} := by
  iintro %Φ Hspec HΦ
  unfold seq_batch_prog' seq_batch_prog
  wp_pures
  tp_pures j
  tp_allocnattape j α as Hα
  tp_pures j
  tp_allocnattape j α' as Hα'
  tp_pures j
  tp_bind j (Rand _ _)
  wp_apply wp_couple_rand_rand_lbl N id Function.bijective_id (N : ℤ) _ α j (by simp)
    (fun n hn => hn) $$ [Hspec Hα] with %n ⟨-, Hspec, -⟩
  · iframe Hα Hspec
  simp only [id]
  wp_pures
  tp_pures j
  tp_bind j (Rand _ _)
  wp_apply wp_couple_rand_rand_lbl M id Function.bijective_id (M : ℤ) _ α' j (by simp)
    (fun n hn => hn) $$ [Hspec Hα'] with %m ⟨-, Hspec, -⟩
  · iframe Hα' Hspec
  simp only [id]
  tp_pures j
  wp_pures
  iapply HΦ
  iexists _
  iframe Hspec
  dsimp only [lrel_nat]
  iexists n * (M + 1) + m
  ipureintro
  constructor <;> push_cast <;> rfl

/-- Rocq: `wp_seq_batch_prog'_rand_prog`. -/
theorem wp_seq_batch_prog'_rand_prog (K : List ectx_item) (j : ℕ) :
    {{ j ⤇ fill K cpl(&(rand_prog N M) #()) }}
      (cpl(&(seq_batch_prog' N M) #()))
    {{ v, RET v; ∃ v' : val, j ⤇ fill K (Val v') ∗ (lrel_nat : lrel GF) v v' }} := by
  iintro %Φ Hspec HΦ
  unfold seq_batch_prog' rand_prog
  wp_pures
  wp_alloctape α as Hα
  wp_pures
  wp_alloctape α' as Hα'
  wp_pures
  tp_pures j
  imod pupd_couple_two_tapes_rand N M (coupling_f M) K ⊤ α α' N M _ [] [] j (by simp) (by simp)
    rfl (coupling_f_cond1 N M) (coupling_f_cond2 N M) (coupling_f_cond3 N M)
    $$ [Hα] [Hα'] [Hspec] with ⟨%n, %m, Hα, Hα', Hspec, %Hn, %Hm⟩
  · inext; iexact Hα
  · inext; iexact Hα'
  · iexact Hspec
  simp only [List.nil_append]
  unfold coupling_f
  wp_randtape as %H
  wp_pures
  wp_randtape as %H'
  wp_pures
  iapply HΦ
  iexists _
  iframe Hspec
  dsimp only [lrel_nat]
  iexists n * (M + 1) + m
  ipureintro
  constructor <;> push_cast <;> rfl

end proof

section proof'

variable {GF : BundledGFunctors} [foxtrotRGS GF] [spawnG GF]

/-- Rocq: `wp_batch_prog'_seq_batch_prog`. -/
theorem wp_batch_prog'_seq_batch_prog (K : List ectx_item) (j : ℕ) :
    {{ j ⤇ fill K cpl(&(seq_batch_prog N M) #()) }}
      (cpl(&(batch_prog' N M) #()))
    {{ v, RET v; ∃ v' : val, j ⤇ fill K (Val v') ∗ (lrel_nat : lrel GF) v v' }} := by
  iintro %Φ Hspec HΦ
  unfold seq_batch_prog batch_prog'
  wp_pures
  wp_alloctape α as Hα
  wp_pures
  wp_alloctape α' as Hα'
  wp_pures
  tp_pures j
  tp_bind j (Rand _ _)
  imod pupd_couple_tape_rand N id Function.bijective_id _ ⊤ α N [] j (by simp) (fun n hn => hn)
    $$ [Hα] [Hspec] with ⟨%n, Hα, Hspec, %Hn⟩
  · inext; iexact Hα
  · iexact Hspec
  simp only [id]
  tp_pures j
  tp_bind j (Rand _ _)
  imod pupd_couple_tape_rand M id Function.bijective_id _ ⊤ α' M [] j (by simp) (fun n hn => hn)
    $$ [Hα'] [Hspec] with ⟨%m, Hα', Hspec, %Hm⟩
  · inext; iexact Hα'
  · iexact Hspec
  simp only [id, List.nil_append]
  tp_pures j
  wp_apply wp_par (fun x => iprop(⌜x = LitV (LitInt (n : ℤ))⌝))
    (fun y => iprop(⌜y = LitV (LitInt (m : ℤ))⌝)) $$ [Hα] [Hα']
  · wp_randtape
    imodintro
    ipureintro
    rfl
  · wp_randtape
    imodintro
    ipureintro
    rfl
  · iintro %v1 %v2 ⟨%H1, %H2⟩
    subst H1 H2
    inext
    wp_pures
    iapply HΦ
    iexists _
    iframe Hspec
    dsimp only [lrel_nat]
    iexists n * (M + 1) + m
    ipureintro
    constructor <;> push_cast <;> rfl

end proof'

/-- Rocq: `seq_batch_prog_refines_rand_prog`. -/
theorem seq_batch_prog_refines_rand_prog :
    (∅ : varmap type) ⊨ Val (seq_batch_prog N M) ≤ctx≤ Val (rand_prog N M) :
      TArrow TUnit TNat := by
  refine ctx_refines_transitive _ _ _ (Val (seq_batch_prog' N M)) _ ?_ ?_ <;>
    refine refines_sound foxtrotSigma _ _ _ fun Δ => ?_
  · unfold_rel
    iintro %K %j Hspec
    wp_pures
    iexists _
    iframe Hspec
    imodintro
    dsimp only [interp, lrel_arr, lrel_unit]
    imodintro
    iintro %v1 %v2 %⟨h1, h2⟩
    subst h1 h2
    unfold_rel
    iintro %K' %j' Hspec
    wp_apply wp_seq_batch_prog_seq_batch_prog' N M K' j' $$ Hspec with %v ⟨%v', Hspec, Hv⟩
    iexists v'
    iframe Hspec Hv
  · unfold_rel
    iintro %K %j Hspec
    wp_pures
    iexists _
    iframe Hspec
    imodintro
    dsimp only [interp, lrel_arr, lrel_unit]
    imodintro
    iintro %v1 %v2 %⟨h1, h2⟩
    subst h1 h2
    unfold_rel
    iintro %K' %j' Hspec
    wp_apply wp_seq_batch_prog'_rand_prog N M K' j' $$ Hspec with %v ⟨%v', Hspec, Hv⟩
    iexists v'
    iframe Hspec Hv

/-- Rocq: `rand_prog_refines_seq_batch_prog`. -/
theorem rand_prog_refines_seq_batch_prog :
    (∅ : varmap type) ⊨ Val (rand_prog N M) ≤ctx≤ Val (seq_batch_prog N M) :
      TArrow TUnit TNat := by
  refine ctx_refines_transitive _ _ _ (Val (batch_prog N M)) _
    (rand_prog_refines_batch_prog N M) ?_
  refine ctx_refines_transitive _ _ _ (Val (batch_prog' N M)) _ ?_ ?_ <;>
    refine refines_sound batchSigma _ _ _ fun Δ => ?_
  · unfold_rel
    iintro %K %j Hspec
    wp_pures
    iexists _
    iframe Hspec
    imodintro
    dsimp only [interp, lrel_arr, lrel_unit]
    imodintro
    iintro %v1 %v2 %⟨h1, h2⟩
    subst h1 h2
    unfold_rel
    iintro %K' %j' Hspec
    wp_apply wp_batch_prog_batch_prog' N M K' j' $$ Hspec with %v ⟨%v', Hspec, Hv⟩
    iexists v'
    iframe Hspec Hv
  · unfold_rel
    iintro %K %j Hspec
    wp_pures
    iexists _
    iframe Hspec
    imodintro
    dsimp only [interp, lrel_arr, lrel_unit]
    imodintro
    iintro %v1 %v2 %⟨h1, h2⟩
    subst h1 h2
    unfold_rel
    iintro %K' %j' Hspec
    wp_apply wp_batch_prog'_seq_batch_prog N M K' j' $$ Hspec with %v ⟨%v', Hspec, Hv⟩
    iexists v'
    iframe Hspec Hv

/-- Rocq: `seq_batch_prog_eq_rand_prog`. -/
theorem seq_batch_prog_eq_rand_prog :
    (∅ : varmap type) ⊨ Val (seq_batch_prog N M) =ctx= Val (rand_prog N M) :
      TArrow TUnit TNat :=
  ⟨seq_batch_prog_refines_rand_prog N M, rand_prog_refines_seq_batch_prog N M⟩

end batch

end Foxtrot.Examples.BatchSamplingSeq
