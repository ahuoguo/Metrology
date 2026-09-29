module

public import Metrology.Coneris.Examples.ConTwoAdd

/-!
# Two concurrent additions of random numbers (part 2)

Ported from clutch/theories/coneris/examples/con_two_add.v (second part:
`complex_parallel_add_spec'`, the paper-style invariant `parallel_add_inv` and its equivalence
with `parallel_add_inv'`, and the adequacy corollary `two_add_prog'_verification`)

## Rocq → Lean map
* Names kept: `complex_parallel_add_spec'`, `gs`, `parallel_add_inv`, `state_side_extract_gs`,
  `samp_side_extract_gs`, `parallel_add_inv_equiv`, `two_add_prog'_verification`.
* `1/2/2 : Qp` is `¼ := Qp.half (Qp.half 1)` (scoped notation); `∗-∗` is `⊣⊢`.
* `#[spawnΣ; ghost_varΣ T; conerisΣ]` is the concrete functor list `conTwoAddSigma` (iris-lean
  has no `gFunctors` lists / `subG`), with instances `conerisGpreS_conTwoAddSigma`,
  `spawnG_conTwoAddSigma`, `GhostVarG_conTwoAddSigma` (Rocq: `subG_*` instances).
  `two_add_prog'_verification` is stated at this `Σ`; the `[DecidableEq]` needed by
  `wp_pgl_lim` is discharged by `classical`. The bound is `(1/16 : ℝ≥0∞)`.

## Proofs that differ from Rocq
* The fractional splits/merges of `ghost_var` (Rocq: automatic through `Fractional` in
  `iDestruct`/`iFrame`) are the helpers `ghost_var_halves` and `ghost_var_quarters`.
* `iFrame. eauto.` / `eauto with iFrame` are spelled out case by case.

## Added
`¼` notation, `ghost_var_halves`, `ghost_var_quarters` (helpers); `conTwoAddSigma` and its
instances (Rocq: `Σ` list and `subG` instances).

## Omitted
Nothing (from either part).
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE COFE Prob ConProbLang ConProbLang.con_prob_lang
open Coneris Coneris.Lib.Spawn Coneris.Lib.Par

namespace Coneris.Examples.ConTwoAdd

open T

/-- `1/2/2 : Qp`. -/
scoped notation "¼" => Qp.half (Qp.half (1 : Qp))

section complex'

variable {GF : BundledGFunctors} [conerisGS GF] [spawnG GF] [GhostVarG GF T]

/-- Helper: `ghost_var γ 1 a ⊢ ghost_var γ (1/2) a ∗ ghost_var γ (1/2) a` (Rocq: by
`Fractional`, in `iDestruct .. as "[Hauth Hfrag]"`). -/
theorem ghost_var_halves (γ : GName) (a : T) :
    (γ ↪VAR a) ⊢@{IProp GF} (γ ↪VAR{.own ½} a) ∗ (γ ↪VAR{.own ½} a) := by
  have h := ghost_var_split (GF := GF) γ a ½ ½
  rw [Qp.half_add_half] at h
  iintro H
  iapply h $$ H

/-- Helper: `ghost_var γ (1/2) a ⊣⊢ ghost_var γ (1/2/2) a ∗ ghost_var γ (1/2/2) a` (Rocq: by
`Fractional`). -/
theorem ghost_var_quarters (γ : GName) (a : T) :
    (γ ↪VAR{.own ½} a) ⊣⊢@{IProp GF} (γ ↪VAR{.own ¼} a) ∗ (γ ↪VAR{.own ¼} a) := by
  have h := (ghost_var_fractional (GF := GF) γ a).fractional ¼ ¼
  rw [Qp.half_add_half] at h
  exact h

/-- Rocq: `complex_parallel_add_spec'`. -/
theorem complex_parallel_add_spec' :
    {{ ↯ (1 / 16) }} two_add_prog'
    {{ (n : ℕ), RET LitV (LitInt (n : ℤ)); (⌜0 < n⌝ : IProp GF) }} := by
  iintro %Φ Herr HΦ
  imod ghost_var_alloc (GF := GF) S0 with ⟨%γ1, H1⟩
  ihave ⟨Hauth1, Hfrag1⟩ := ghost_var_halves γ1 S0 $$ H1
  imod ghost_var_alloc (GF := GF) S0 with ⟨%γ2, H2⟩
  ihave ⟨Hauth2, Hfrag2⟩ := ghost_var_halves γ2 S0 $$ H2
  unfold two_add_prog'
  wp_alloc l as Hl
  wp_pures
  imod inv_alloc nroot ⊤ (parallel_add_inv' γ1 γ2 l) $$ [Hauth1 Hauth2 Herr Hl] with #I
  · inext
    unfold parallel_add_inv'
    iexists S0, S0
    iframe Hauth1 Hauth2
    isplitl [Hl]
    · ileft
      iframe Hl
      ipureintro
      trivial
    · ileft
      iframe Herr
      ipureintro
      trivial
  wp_apply wp_par' (fun _ => iprop(∃ n : ℕ, γ1 ↪VAR{.own ½} (S2 n)))
    (fun _ => iprop(∃ n : ℕ, γ2 ↪VAR{.own ½} (S2 n))) $$ [Hfrag1] [Hfrag2]
  · wp_apply rand_step γ1 γ2 l $$ [Hfrag1] with %n Hfrag1
    · iframe
      iexact I
    wp_apply faa_step γ1 γ2 l n $$ [Hfrag1] with %v Hfrag1
    · iframe
      iexact I
    iexists n
    iexact Hfrag1
  · ihave #I' := inv_iff nroot _ (parallel_add_inv' γ2 γ1 l) $$ I []
    · inext
      imodintro
      isplit
      · iintro H
        iapply parallel_add_inv'_symmetric $$ H
      · iintro H
        iapply parallel_add_inv'_symmetric $$ H
    iclear I
    wp_apply rand_step γ2 γ1 l $$ [Hfrag2] with %n Hfrag2
    · iframe
      iexact I'
    wp_apply faa_step γ2 γ1 l n $$ [Hfrag2] with %v Hfrag2
    · iframe
      iexact I'
    iexists n
    iexact Hfrag2
  · iintro %v1 %v2 ⟨⟨%n1, H1⟩, ⟨%n2, H2⟩⟩
    inext
    wp_pures
    unfold parallel_add_inv'
    iinv I with ⟨%s1, %s2, >Hauth1, >Hauth2, >Hstate, >Hsamp⟩ Hclose
    ihave %Heq1 := ghost_var_agree γ1 _ _ _ _ $$ Hauth1 H1
    ihave %Heq2 := ghost_var_agree γ2 _ _ _ _ $$ Hauth2 H2
    subst Heq1 Heq2
    icases Hstate with (⟨_, %Hp⟩ | ⟨%n, _, %Hp⟩ | ⟨%n, Hl, %Hgt0, %Hp⟩)
    · exact absurd Hp (by simp [no_thread_added])
    · exact absurd Hp (by simp [one_thread_added])
    wp_load
    imod Hclose $$ [Hauth1 Hauth2 Hl Hsamp]
    · inext
      iexists S2 n1, S2 n2
      iframe Hauth1 Hauth2 Hsamp
      iright
      iright
      iexists n
      iframe Hl
      ipureintro
      exact ⟨Hgt0, Hp⟩
    imodintro
    iapply HΦ
    ipureintro
    exact Hgt0

/-- Rocq: `gs`. -/
def gs (γ1 γ2 : GName) (P : T → T → Prop) : IProp GF :=
  iprop(∃ (s1 s2 : T), (γ1 ↪VAR{.own ¼} s1) ∗ (γ2 ↪VAR{.own ¼} s2) ∗ ⌜P s1 s2⌝)

/-- Rocq: `parallel_add_inv`. In the paper we do not have leading existentials in the
descriptions of the invariant. This alternate version matching the paper is equivalent to what
we used above. Essentially, in the paper each clause beginning with `gs γ1 γ2 [...]` is
omitted. -/
def parallel_add_inv (γ1 γ2 : GName) (l : Loc) : IProp GF :=
  iprop((((l ↦ LitV (LitInt 0) ∗ gs γ1 γ2 no_thread_added) ∨
      (∃ n : ℕ, l ↦ LitV (LitInt (n : ℤ)) ∗ gs γ1 γ2 (one_thread_added n)) ∨
      (∃ n : ℕ, l ↦ LitV (LitInt (n : ℤ)) ∗ ⌜n > 0⌝ ∗ gs γ1 γ2 (both_threads_added n))) ∗
    ((↯ (1 / 16) ∗ gs γ1 γ2 no_thread_sampled) ∨
      (↯ (1 / 4) ∗ gs γ1 γ2 one_thread_sampled_zero) ∨
      (↯ 1 ∗ gs γ1 γ2 (fun _ _ => True)) ∨
      (↯ 0 ∗ gs γ1 γ2 at_least_one_thread_sampled_non_zero))))

/-! We now prove that the `parallel_add_inv` and `parallel_add_inv'` are equivalent. -/

/-- Rocq: `state_side_extract_gs`. -/
theorem state_side_extract_gs (γ1 γ2 : GName) (l : Loc) :
    ((l ↦ LitV (LitInt 0) ∗ gs γ1 γ2 no_thread_added) ∨
      (∃ n : ℕ, l ↦ LitV (LitInt (n : ℤ)) ∗ gs γ1 γ2 (one_thread_added n)) ∨
      (∃ n : ℕ, l ↦ LitV (LitInt (n : ℤ)) ∗ ⌜n > 0⌝ ∗ gs γ1 γ2 (both_threads_added n)))
    ⊢@{IProp GF}
    ∃ (s1 s2 : T), (γ1 ↪VAR{.own ¼} s1) ∗ (γ2 ↪VAR{.own ¼} s2) ∗
      ((l ↦ LitV (LitInt 0) ∗ ⌜no_thread_added s1 s2⌝) ∨
        (∃ n : ℕ, l ↦ LitV (LitInt (n : ℤ)) ∗ ⌜one_thread_added n s1 s2⌝) ∨
        (∃ n : ℕ, l ↦ LitV (LitInt (n : ℤ)) ∗ ⌜n > 0⌝ ∗ ⌜both_threads_added n s1 s2⌝)) := by
  unfold gs
  iintro (⟨Hl, %s1, %s2, H1, H2, %Hp⟩ | ⟨%n, Hl, %s1, %s2, H1, H2, %Hp⟩ |
    ⟨%n, Hl, %Hgt, %s1, %s2, H1, H2, %Hp⟩)
  · iexists s1, s2
    iframe H1 H2
    ileft
    iframe Hl
    ipureintro
    exact Hp
  · iexists s1, s2
    iframe H1 H2
    iright
    ileft
    iexists n
    iframe Hl
    ipureintro
    exact Hp
  · iexists s1, s2
    iframe H1 H2
    iright
    iright
    iexists n
    iframe Hl
    ipureintro
    exact ⟨Hgt, Hp⟩

/-- Rocq: `samp_side_extract_gs`. -/
theorem samp_side_extract_gs (γ1 γ2 : GName) :
    ((↯ (1 / 16) ∗ gs γ1 γ2 no_thread_sampled) ∨
      (↯ (1 / 4) ∗ gs γ1 γ2 one_thread_sampled_zero) ∨
      (↯ 1 ∗ gs γ1 γ2 (fun _ _ => True)) ∨
      (↯ 0 ∗ gs γ1 γ2 at_least_one_thread_sampled_non_zero))
    ⊢@{IProp GF}
    ∃ (s1 s2 : T), (γ1 ↪VAR{.own ¼} s1) ∗ (γ2 ↪VAR{.own ¼} s2) ∗
      ((↯ (1 / 16) ∗ ⌜no_thread_sampled s1 s2⌝) ∨
        (↯ (1 / 4) ∗ ⌜one_thread_sampled_zero s1 s2⌝) ∨
        (↯ 1) ∨ -- both_thread_sampled_zero
        (↯ 0 ∗ ⌜at_least_one_thread_sampled_non_zero s1 s2⌝)) := by
  unfold gs
  iintro (⟨Herr, %s1, %s2, H1, H2, %Hp⟩ | ⟨Herr, %s1, %s2, H1, H2, %Hp⟩ |
    ⟨Herr, %s1, %s2, H1, H2, -⟩ | ⟨Herr, %s1, %s2, H1, H2, %Hp⟩)
  · iexists s1, s2
    iframe H1 H2
    ileft
    iframe Herr
    ipureintro
    exact Hp
  · iexists s1, s2
    iframe H1 H2
    iright
    ileft
    iframe Herr
    ipureintro
    exact Hp
  · iexists s1, s2
    iframe H1 H2
    iright
    iright
    ileft
    iexact Herr
  · iexists s1, s2
    iframe H1 H2
    iright
    iright
    iright
    iframe Herr
    ipureintro
    exact Hp

/-- Rocq: `parallel_add_inv_equiv`. -/
theorem parallel_add_inv_equiv (γ1 γ2 : GName) (l : Loc) :
    parallel_add_inv (GF := GF) γ1 γ2 l ⊣⊢ parallel_add_inv' γ1 γ2 l := by
  constructor
  · unfold parallel_add_inv parallel_add_inv'
    iintro ⟨Hstate, Hsamp⟩
    ihave ⟨%s1, %s2, H1, H2, Hstate⟩ := state_side_extract_gs γ1 γ2 l $$ Hstate
    ihave ⟨%s1', %s2', H1', H2', Hsamp⟩ := samp_side_extract_gs γ1 γ2 $$ Hsamp
    ihave %Heq1 := ghost_var_agree γ1 _ _ _ _ $$ H1 H1'
    ihave %Heq2 := ghost_var_agree γ2 _ _ _ _ $$ H2 H2'
    subst Heq1 Heq2
    iexists s1, s2
    iframe Hstate Hsamp
    isplitl [H1 H1']
    · iapply (ghost_var_quarters γ1 s1).mpr
      iframe
    · iapply (ghost_var_quarters γ2 s2).mpr
      iframe
  · unfold parallel_add_inv parallel_add_inv' gs
    iintro ⟨%s1, %s2, Hauth1, Hauth2, Hstate, Hsamp⟩
    ihave ⟨Hauth1, Hauth1'⟩ := (ghost_var_quarters γ1 s1).mp $$ Hauth1
    ihave ⟨Hauth2, Hauth2'⟩ := (ghost_var_quarters γ2 s2).mp $$ Hauth2
    isplitl [Hauth1 Hauth2 Hstate]
    · icases Hstate with (⟨Hl, %Hp⟩ | ⟨%n, Hl, %Hp⟩ | ⟨%n, Hl, %Hgt, %Hp⟩)
      · ileft
        iframe Hl
        iexists s1, s2
        iframe Hauth1 Hauth2
        ipureintro
        exact Hp
      · iright
        ileft
        iexists n
        iframe Hl
        iexists s1, s2
        iframe Hauth1 Hauth2
        ipureintro
        exact Hp
      · iright
        iright
        iexists n
        iframe Hl
        isplitr
        · ipureintro
          exact Hgt
        iexists s1, s2
        iframe Hauth1 Hauth2
        ipureintro
        exact Hp
    · icases Hsamp with (⟨Herr, %Hp⟩ | ⟨Herr, %Hp⟩ | Herr | ⟨Herr, %Hp⟩)
      · ileft
        iframe Herr
        iexists s1, s2
        iframe Hauth1' Hauth2'
        ipureintro
        exact Hp
      · iright
        ileft
        iframe Herr
        iexists s1, s2
        iframe Hauth1' Hauth2'
        ipureintro
        exact Hp
      · iright
        iright
        ileft
        iframe Herr
        iexists s1, s2
        iframe Hauth1' Hauth2'
      · iright
        iright
        iright
        iframe Herr
        iexists s1, s2
        iframe Hauth1' Hauth2'
        ipureintro
        exact Hp

end complex'

/-- Rocq: `#[spawnΣ; ghost_varΣ T; conerisΣ]` (the `Σ` of `two_add_prog'_verification`).
iris-lean has no `gFunctors` lists: this is a concrete `BundledGFunctors` listing the functors of
`conerisGpreS` (invariants, later credits, heap, tapes, error credits), the spawn token
(`Excl ()`) and `ghost_var T`, following `Foxtrot.foxtrotSigma`. As in Rocq the heap and tape
functors are distinct entries. -/
def conTwoAddSigma : BundledGFunctors
  | 0 => ⟨InvMapF, by infer_instance⟩
  | 1 => ⟨constOF CoPsetDisjL, by infer_instance⟩
  | 2 => ⟨constOF (DisjointLeibnizSet PosSet), by infer_instance⟩
  | 3 => ⟨Auth.AuthURF (constOF Credit), by infer_instance⟩
  | 4 => ⟨constOF (HeapView Loc (Agree (DiscreteO val)) loc_map), by infer_instance⟩
  | 5 => ⟨constOF (HeapView Loc (Agree (DiscreteO tape)) loc_map), by infer_instance⟩
  | 6 => ⟨constOF (Auth ErrorCredit), by infer_instance⟩
  | 7 => ⟨TokenF, by infer_instance⟩
  | 8 => ⟨GhostVarF T, by infer_instance⟩
  | _ => ⟨constOF Unit, by infer_instance⟩

/-- Rocq: `subG_conerisGPreS` (at `conTwoAddSigma`). -/
instance conerisGpreS_conTwoAddSigma : conerisGpreS conTwoAddSigma where
  conerisGpreS_iris := {
    toWsatGpreS := ⟨⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩⟩
    toLcGpreS := ⟨⟨3, rfl⟩⟩ }
  conerisGpreS_heap := ⟨⟨4, rfl⟩⟩
  conerisGpreS_tapes := ⟨⟨5, rfl⟩⟩
  conerisGpreS_err := ⟨⟨6, rfl⟩⟩

/-- Rocq: `subG_spawnΣ` (at `conTwoAddSigma`). -/
instance spawnG_conTwoAddSigma : spawnG conTwoAddSigma where
  spawn_tokG := { elemG := ⟨7, rfl⟩ }

/-- Rocq: `subG_ghost_varΣ` (at `conTwoAddSigma`). -/
instance GhostVarG_conTwoAddSigma : GhostVarG conTwoAddSigma T where
  elemG := ⟨8, rfl⟩

/-- Rocq: `two_add_prog'_verification`, at the concrete `Σ := conTwoAddSigma`
(Rocq: `#[spawnΣ; ghost_varΣ T; conerisΣ]`). The `DecidableEq` that `wp_pgl_lim` needs on the
scheduler state (Rocq's `Countable` bundles `EqDecision`) is obtained classically, so the
hypotheses are exactly the Rocq ones. -/
theorem two_add_prog'_verification {sch_int_state : Type}
    [Countable sch_int_state] (ζ : sch_int_state) (σ : state)
    (sch : scheduler con_prob_lang_mdp sch_int_state) [TapeOblivious sch_int_state sch] :
    pgl (sch_lim_exec sch (ζ, ([two_add_prog'], σ)))
      (fun x => ∃ n : ℕ, x = LitV (LitInt (n : ℤ)) ∧ 0 < n) (1 / 16) := by
  classical
  refine wp_pgl_lim (GF := conTwoAddSigma) ζ two_add_prog' σ (1 / 16) sch _ ?_
  intro _
  iintro Herr
  wp_apply complex_parallel_add_spec' $$ Herr with %n %Hn
  ipureintro
  exact ⟨n, rfl, Hn⟩

end Coneris.Examples.ConTwoAdd
