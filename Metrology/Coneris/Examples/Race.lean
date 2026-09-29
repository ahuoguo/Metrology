module

public import Metrology.Coneris.Lib.Par
public import Metrology.Coneris.Lib.HocapRandAtomic
public import Iris.Algebra.Lib.ExclAuth

/-!
# A race on a shared tape

Ported from clutch/theories/coneris/examples/race.v

Two threads race (with a `CAS` on a shared flag `r`) to be the one that writes a sample of a
shared hocap tape `α` (a `rand_atomic_spec 1`) into the result reference `res`. By presampling
the tape with `↯ (1/2)` before the threads start, the result is `1` with certainty.

## Rocq → Lean map
* Namespace `Coneris.Examples.Race`; all names are kept: `T` (constructors `S1 .. S5`), `TO`,
  `ghost_var_alloc`, `ghost_var_agree`, `ghost_var_update` (section `lemmas`), `race_prog`,
  `winning`, `check_invalid`, `value_of_r`, `value_of_res`, `tape_elem`, `inv_pred`,
  `race_prog_spec` (section `race`).
* `TO := leibnizO T` is `DiscreteO T` (iris-lean's discrete/Leibniz OFE); `inG Σ (excl_authR TO)`
  is `ElemG GF excl_authTF` with `excl_authTF := constOF (ExclAuthR (A := TO))`;
  `own γ (●E b)` / `own γ (◯E b)` are `iOwn γ (●E ⟨b⟩)` / `iOwn γ (◯E ⟨b⟩)`.
* `conerisGS Σ`, `spawnG Σ`, `rand_atomic_spec 1` are `[conerisGS GF] [spawnG GF]
  [r : rand_atomic_spec 1 GF]` (`Coneris.Lib.HocapRandAtomic`); the class fields are used as
  `r.rand_allocate_tape`, `r.rand_tape`, `r.rand_tapes`, ...
* `e1 ||| e2` (Rocq, `expr_scope`: `par (λ: <>, e1)%E (λ: <>, e2)%E`) is the scoped program
  notation `e1 ‖ e2` defined here (as in `Foxtrot.Lib.Par`; inside `cpl(..)` the token `|||` is
  the bitwise `or`), elaborating to `&par (λ <>, e1) (λ <>, e2)`. In Rocq the `;;` binds looser
  than `|||` (the proof continues with `!"res"` after `wp_par`); the Lean program has explicit
  parentheses.
* `check_invalid` is a `Prop` (a `match` returning `False`/`True`), as in Rocq; `value_of_res`
  returns `ℤ`, `tape_elem` returns `List ℕ`.
* `inv_pred` takes `r' res : Loc` (Rocq: `r res`, whose type is inferred as `loc`).
* `{{{ ↯ (1/2) }}} race_prog {{{ (z:Z), RET #z; ⌜z = 1⌝ }}}` is the iris-lean Texan triple
  `{{ ↯ (1 / 2) }} race_prog {{ (z : ℤ), RET LitV (LitInt z); ⌜z = 1⌝ }}` (mask `⊤`).
* The presampling error function `λ x, if bool_decide (fin_to_nat x = 0) then nnreal_one else
  nnreal_zero` is `fun x => if (x : ℕ) = 0 then 1 else 0` in `ℝ≥0∞` (its nonnegativity side
  condition vanishes).

## Proofs that differ from Rocq
* `wp_cmpxchg`, `wp_store` and `wp_load` are applied as the lemmas `wp_cmpxchg_suc`,
  `wp_cmpxchg_fail`, `wp_store`, `wp_load` with the points-to named explicitly (`$$ Hr`): the
  generic tactics search the context for `l ↦ ?v`, and unifying `r' ↦ ?v` against the
  hypothesis `res ↦ ..` times out (see the report / `upstream_needs`). Consequently the CAS
  is preceded by a case split on the (generalized) value `value_of_r ..` of `r`.
* `awp_apply rand_tape_spec_some` is applied at the (inner-mask) `E := ∅`. Opening the
  invariant inside the atomic update with `iinv`, the laters in front of the invariant
  contents cannot be stripped with `>` patterns there (the proof-mode instance
  `elim_modal_acc` does not fire), so the atomic accessor is unfolded (`iunfold atomic_acc`)
  and proved by hand (Rocq: `iAaccIntro with "Hα"`): the laters are stripped with `imod`, the
  telescope is instantiated with `⟨1, [], ⟨⟩⟩` and simplified with `tele_simp`.
* `destruct s2; by iFrame` is `cases s2 <;> simp only [..] at Hc1 <;> dsimp only [..] <;> iframe`.
* `wp_par` is applied through the local helper `wp_par'` (the same statement with `par_V`
  unfolded, since `wp_apply` does not unfold `par_V`).

## Added
* `wp_par'` (helper, see above); the `‖` program notation; `deriving DecidableEq, Inhabited` for
  `T` (`Inhabited` lets the proof mode commute `▷` with `∃ s1 s2`, as Rocq's `iInv` does).

## Omitted
Nothing.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang
open Coneris Coneris.Lib.Spawn Coneris.Lib.Par Coneris.Lib.HocapRandAtomic
open Iris.ExclAuth

namespace Coneris.Examples.Race

/-- Rocq: `T`. -/
inductive T : Type where
  | S1 | S2 | S3 | S4 | S5
  deriving DecidableEq, Inhabited

open T

/-- Rocq: `TO` (`leibnizO T`). -/
abbrev TO : Type := DiscreteO T

/-- Rocq: the functor of `inG Σ (excl_authR TO)`. -/
abbrev excl_authTF : COFE.OFunctorPre := constOF (ExclAuthR (A := TO))

section lemmas

variable {GF : BundledGFunctors} [ElemG GF excl_authTF]

/-- Rocq: `ghost_var_alloc`. -/
theorem ghost_var_alloc (b : T) :
    ⊢@{IProp GF} |==> ∃ γ, iOwn (F := excl_authTF) γ (●E (⟨b⟩ : TO)) ∗
      iOwn (F := excl_authTF) γ (◯E (⟨b⟩ : TO)) := by
  imod iOwn_alloc (F := excl_authTF) ((●E (⟨b⟩ : TO)) • (◯E (⟨b⟩ : TO))) ExclAuth.valid
    with ⟨%γ, H1, H2⟩
  imodintro
  iexists γ
  iframe

/-- Rocq: `ghost_var_agree`. -/
theorem ghost_var_agree (γ : GName) (b c : T) :
    ⊢@{IProp GF} iOwn (F := excl_authTF) γ (●E (⟨b⟩ : TO)) -∗
      iOwn (F := excl_authTF) γ (◯E (⟨c⟩ : TO)) -∗ ⌜b = c⌝ := by
  iintro H1 H2
  icombine H1 H2 gives %H
  ipureintro
  exact DiscreteO.eqv_inj (ExclAuth.agree H)

/-- Rocq: `ghost_var_update`. -/
theorem ghost_var_update (γ : GName) (b' b c : T) :
    ⊢@{IProp GF} iOwn (F := excl_authTF) γ (●E (⟨b⟩ : TO)) -∗
      iOwn (F := excl_authTF) γ (◯E (⟨c⟩ : TO)) ==∗
      iOwn (F := excl_authTF) γ (●E (⟨b'⟩ : TO)) ∗ iOwn (F := excl_authTF) γ (◯E (⟨b'⟩ : TO)) := by
  iintro H1 H2
  ihave H := (iOwn_op (F := excl_authTF)).2 $$ [H1 H2]
  · iframe
  imod iOwn_update ExclAuth.update $$ H with ⟨H1, H2⟩
  imodintro
  iframe

end lemmas

/-! ## The race -/

/-- `e1 ||| e2` (Rocq: `par (λ: <>, e1)%E (λ: <>, e2)%E` in `expr_scope`) as a program
notation. -/
scoped syntax:55 cpl_exp:56 " ‖ " cpl_exp:55 : cpl_exp

macro_rules
  | `(cpl($e1 ‖ $e2)) => `(cpl(&par (λ <>, $e1) (λ <>, $e2)))

/-- Helper (not in Rocq): `wp_par` with `par_V` unfolded, so that `wp_apply` finds it. -/
theorem wp_par' {GF : BundledGFunctors} [conerisGS GF] [spawnG GF]
    (Ψ1 Ψ2 : val → IProp GF) (e1 e2 : expr) (Φ : val → IProp GF) :
    ⊢ WP e1 {{ Ψ1 }} -∗ WP e2 {{ Ψ2 }} -∗
      (∀ v1 v2, Ψ1 v1 ∗ Ψ2 v2 -∗ ▷ Φ (PairV v1 v2)) -∗
      WP cpl(&par v(λ <>, &e1) v(λ <>, &e2)) {{ Φ }} :=
  wp_par Ψ1 Ψ2 e1 e2 Φ

section race

variable {GF : BundledGFunctors} [conerisGS GF] [spawnG GF] [r : rand_atomic_spec 1 GF]
  [ElemG GF excl_authTF]

/-- Rocq: `race_prog`. -/
def race_prog : expr := cpl(
  let r := ref(#false) in
  let res := ref(#(-1)) in
  let α := v(&r.rand_allocate_tape) #() in
  ((if cas(r, #false, #true) then res ← v(&r.rand_tape) α else #())
   ‖
   (if cas(r, #false, #true) then res ← v(&r.rand_tape) α else #()));
  !res)

/-- Rocq: `winning`. -/
def winning : T → Option Bool
  | S2 | S3 | S4 => some true
  | S5 => some false
  | _ => none

/-- Rocq: `check_invalid`. -/
def check_invalid (s1 s2 : T) : Prop :=
  match winning s1, winning s2 with
  | some true, some true | some false, none | none, some false | some false, some false => False
  | _, _ => True

/-- Rocq: `value_of_r`. -/
def value_of_r (s1 s2 : T) : Bool :=
  match winning s1, winning s2 with
  | some true, _ | _, some true => true
  | _, _ => false

/-- Rocq: `value_of_res`. -/
def value_of_res (s1 s2 : T) : ℤ :=
  match s1, s2 with
  | S4, _ | _, S4 => 1
  | _, _ => -1

/-- Rocq: `tape_elem`. -/
def tape_elem (s1 s2 : T) : List ℕ :=
  match s1, s2 with
  | S3, _ | _, S3 | S4, _ | _, S4 => []
  | _, _ => [1]

/-- Rocq: `inv_pred`. -/
def inv_pred (r' res : Loc) (α : val) (γ1 γ2 : GName) : IProp GF :=
  iprop(∃ s1 s2,
    iOwn (F := excl_authTF) γ1 (●E (⟨s1⟩ : TO)) ∗ iOwn (F := excl_authTF) γ2 (●E (⟨s2⟩ : TO)) ∗
    ⌜check_invalid s1 s2⌝ ∗
    r' ↦ LitV (LitBool (value_of_r s1 s2)) ∗
    res ↦ LitV (LitInt (value_of_res s1 s2)) ∗
    r.rand_tapes α (tape_elem s1 s2))

/-- Rocq: `race_prog_spec`. We want to upper bound the probability we get a 0 (error).
Here we use one tape which is placed in a shared invariant, we only need 1/2.

One can possibly use two local tapes, one for each thread, but the presampling must be done
only after the CAS. -/
theorem race_prog_spec :
    {{ ↯ (1 / 2) }} (race_prog (GF := GF))
    {{ (z : ℤ), RET LitV (LitInt z); (⌜z = 1⌝ : IProp GF) }} := by
  iintro %Φ Herr HΦ
  unfold race_prog
  wp_alloc r' as Hr
  wp_pures
  wp_alloc res as Hres
  wp_pures
  wp_apply r.rand_allocate_tape_spec ⊤ $$ [] with %α Hα
  · itrivial
  wp_pures
  imod ghost_var_alloc S1 with ⟨%γ1, Hauth1, Hfrag1⟩
  imod ghost_var_alloc S1 with ⟨%γ2, Hauth2, Hfrag2⟩
  imod r.rand_tapes_presample ⊤ α [] _ (fun x => if (x : ℕ) = 0 then 1 else 0) ?_ $$ Hα Herr
    with ⟨%n, Herr, Hα⟩
  · rw [tsum_fintype, Fin.sum_univ_two]; norm_num
  by_cases hn : (n : ℕ) = 0
  · simp only [hn, ↓reduceIte]
    iexfalso
    iapply ErrorCredit.contradict le_rfl $$ Herr
  simp only [hn, ↓reduceIte, List.nil_append]
  have hn1 : (n : ℕ) = 1 := by have := n.isLt; omega
  rw [hn1]
  imod inv_alloc nroot ⊤ (inv_pred r' res α γ1 γ2) $$ [Hauth1 Hauth2 Hr Hres Hα] with #Hinv
  · inext
    unfold inv_pred
    iexists S1, S1
    dsimp only [check_invalid, value_of_r, value_of_res, tape_elem, winning]
    iframe
  unfold inv_pred
  wp_apply wp_par' (fun _ => iprop(iOwn (F := excl_authTF) γ1 (◯E (⟨S4⟩ : TO)) ∨
      iOwn (F := excl_authTF) γ1 (◯E (⟨S5⟩ : TO))))
    (fun _ => iprop(iOwn (F := excl_authTF) γ2 (◯E (⟨S4⟩ : TO)) ∨
      iOwn (F := excl_authTF) γ2 (◯E (⟨S5⟩ : TO)))) $$ [Hfrag1] [Hfrag2]
  · wp_bind (CmpXchg _ _ _)
    iinv Hinv with ⟨%s1, %s2, >Hauth1, >Hauth2, >%Hc1, >Hr, >Hres, >Hα⟩ Hclose
    ihave %Heq := ghost_var_agree $$ Hauth1 Hfrag1
    subst Heq
    generalize hb : value_of_r S1 s2 = b
    cases b
    · -- success
      wp_apply (wp_cmpxchg_suc (LitV (LitBool false)) (LitV (LitBool false))
        (LitV (LitBool true)) r' (Or.inl trivial) rfl) $$ Hr with Hr
      have hs2 : s2 = S1 := by cases s2 <;> simp_all [check_invalid, winning, value_of_r]
      subst hs2
      imod ghost_var_update γ1 S2 _ _ $$ Hauth1 Hfrag1 with ⟨Hauth1, Hfrag1⟩
      imod Hclose $$ [Hauth1 Hauth2 Hr Hres Hα]
      · inext
        iexists S2, S1
        dsimp only [check_invalid, value_of_r, value_of_res, tape_elem, winning]
        iframe
      imodintro
      wp_pures
      awp_apply r.rand_tape_spec_some ∅ α
      iinv Hinv with ⟨%s1, %s2, Hauth1, Hauth2, Hc1, Hr, Hres, Hα⟩
      iunfold atomic_acc
      imod Hauth1; imod Hauth2; imod Hc1 with %Hc1; imod Hr; imod Hres; imod Hα
      ihave %Heq := ghost_var_agree $$ Hauth1 Hfrag1
      subst Heq
      have htape : tape_elem S2 s2 = [1] := by
        cases s2 <;> simp_all [check_invalid, winning, tape_elem]
      rw [htape]
      iapply fupd_mask_intro (by exact LawfulSet.empty_subset)
      iintro Hclose
      iexists ⟨1, [], ⟨⟩⟩
      tele_simp
      iframe Hα
      isplit
      · iintro Hα
        imod Hclose
        imodintro
        iframe Hfrag1
        inext
        iexists S2, s2
        rw [htape]
        iframe
        ipureintro
        exact Hc1
      · iintro Hα
        imod Hclose
        imod ghost_var_update γ1 S3 _ _ $$ Hauth1 Hfrag1 with ⟨Hauth1, Hfrag1⟩
        imodintro
        isplitl [Hauth1 Hauth2 Hr Hres Hα]
        · inext
          iexists S3, s2
          cases s2 <;> simp only [check_invalid, winning] at Hc1 <;>
            dsimp only [check_invalid, value_of_r, value_of_res, tape_elem, winning] <;> iframe
        iinv Hinv with ⟨%s1, %s2, >Hauth1, >Hauth2, >%Hc1, >Hr, >Hres, >Hα⟩ Hclose
        ihave %Heq := ghost_var_agree $$ Hauth1 Hfrag1
        subst Heq
        wp_apply (wp_store res _ (LitV (LitInt ((1 : ℕ) : ℤ)))) $$ Hres with Hres
        imod ghost_var_update γ1 S4 _ _ $$ Hauth1 Hfrag1 with ⟨Hauth1, Hfrag1⟩
        imod Hclose $$ [Hauth1 Hauth2 Hr Hres Hα]
        · inext
          iexists S4, s2
          cases s2 <;> simp only [check_invalid, winning] at Hc1 <;>
            dsimp only [check_invalid, value_of_r, value_of_res, tape_elem, winning] <;> iframe
        imodintro
        ileft
        iexact Hfrag1
    · -- failure
      wp_apply (wp_cmpxchg_fail (LitV (LitBool true)) (LitV (LitBool false)) (LitV (LitBool true))
        r' _ (Or.inl trivial) (by decide)) $$ Hr with Hr
      imod ghost_var_update γ1 S5 _ _ $$ Hauth1 Hfrag1 with ⟨Hauth1, Hfrag1⟩
      imod Hclose $$ [Hauth1 Hauth2 Hr Hres Hα]
      · inext
        iexists S5, s2
        cases s2 <;> simp only [check_invalid, winning, value_of_r, Bool.false_eq_true] at Hc1 hb <;>
          dsimp only [check_invalid, value_of_r, value_of_res, tape_elem, winning] <;> iframe
      imodintro
      wp_pures
      iright
      iexact Hfrag1
  · wp_bind (CmpXchg _ _ _)
    iinv Hinv with ⟨%s1, %s2, >Hauth1, >Hauth2, >%Hc1, >Hr, >Hres, >Hα⟩ Hclose
    ihave %Heq := ghost_var_agree $$ Hauth2 Hfrag2
    subst Heq
    generalize hb : value_of_r s1 S1 = b
    cases b
    · -- success
      wp_apply (wp_cmpxchg_suc (LitV (LitBool false)) (LitV (LitBool false))
        (LitV (LitBool true)) r' (Or.inl trivial) rfl) $$ Hr with Hr
      have hs1 : s1 = S1 := by cases s1 <;> simp_all [check_invalid, winning, value_of_r]
      subst hs1
      imod ghost_var_update γ2 S2 _ _ $$ Hauth2 Hfrag2 with ⟨Hauth2, Hfrag2⟩
      imod Hclose $$ [Hauth1 Hauth2 Hr Hres Hα]
      · inext
        iexists S1, S2
        dsimp only [check_invalid, value_of_r, value_of_res, tape_elem, winning]
        iframe
      imodintro
      wp_pures
      awp_apply r.rand_tape_spec_some ∅ α
      iinv Hinv with ⟨%s1, %s2, Hauth1, Hauth2, Hc1, Hr, Hres, Hα⟩
      iunfold atomic_acc
      imod Hauth1; imod Hauth2; imod Hc1 with %Hc1; imod Hr; imod Hres; imod Hα
      ihave %Heq := ghost_var_agree $$ Hauth2 Hfrag2
      subst Heq
      have htape : tape_elem s1 S2 = [1] := by
        cases s1 <;> simp_all [check_invalid, winning, tape_elem]
      rw [htape]
      iapply fupd_mask_intro (by exact LawfulSet.empty_subset)
      iintro Hclose
      iexists ⟨1, [], ⟨⟩⟩
      tele_simp
      iframe Hα
      isplit
      · iintro Hα
        imod Hclose
        imodintro
        iframe Hfrag2
        inext
        iexists s1, S2
        rw [htape]
        iframe
        ipureintro
        exact Hc1
      · iintro Hα
        imod Hclose
        imod ghost_var_update γ2 S3 _ _ $$ Hauth2 Hfrag2 with ⟨Hauth2, Hfrag2⟩
        imodintro
        isplitl [Hauth1 Hauth2 Hr Hres Hα]
        · inext
          iexists s1, S3
          cases s1 <;> simp only [check_invalid, winning] at Hc1 <;>
            dsimp only [check_invalid, value_of_r, value_of_res, tape_elem, winning] <;> iframe
        iinv Hinv with ⟨%s1, %s2, >Hauth1, >Hauth2, >%Hc1, >Hr, >Hres, >Hα⟩ Hclose
        ihave %Heq := ghost_var_agree $$ Hauth2 Hfrag2
        subst Heq
        wp_apply (wp_store res _ (LitV (LitInt ((1 : ℕ) : ℤ)))) $$ Hres with Hres
        imod ghost_var_update γ2 S4 _ _ $$ Hauth2 Hfrag2 with ⟨Hauth2, Hfrag2⟩
        imod Hclose $$ [Hauth1 Hauth2 Hr Hres Hα]
        · inext
          iexists s1, S4
          cases s1 <;> simp only [check_invalid, winning] at Hc1 <;>
            dsimp only [check_invalid, value_of_r, value_of_res, tape_elem, winning] <;> iframe
        imodintro
        ileft
        iexact Hfrag2
    · -- failure
      wp_apply (wp_cmpxchg_fail (LitV (LitBool true)) (LitV (LitBool false)) (LitV (LitBool true))
        r' _ (Or.inl trivial) (by decide)) $$ Hr with Hr
      imod ghost_var_update γ2 S5 _ _ $$ Hauth2 Hfrag2 with ⟨Hauth2, Hfrag2⟩
      imod Hclose $$ [Hauth1 Hauth2 Hr Hres Hα]
      · inext
        iexists s1, S5
        cases s1 <;> simp only [check_invalid, winning, value_of_r, Bool.false_eq_true] at Hc1 hb <;>
          dsimp only [check_invalid, value_of_r, value_of_res, tape_elem, winning] <;> iframe
      imodintro
      wp_pures
      iright
      iexact Hfrag2
  · iintro %v1 %v2 ⟨Hfrag1, Hfrag2⟩
    inext
    wp_pures
    iinv Hinv with ⟨%s1, %s2, >Hauth1, >Hauth2, >%Hc1, >Hr, >Hres, >Hα⟩ Hclose
    icases Hfrag1 with (Hfrag1 | Hfrag1) <;> icases Hfrag2 with (Hfrag2 | Hfrag2) <;>
      ihave %Heq1 := ghost_var_agree $$ Hauth1 Hfrag1 <;>
      ihave %Heq2 := ghost_var_agree $$ Hauth2 Hfrag2 <;> subst Heq1 Heq2 <;>
      (try (simp only [check_invalid, winning] at Hc1; done)) <;>
      wp_apply (wp_load res _ _) $$ Hres with Hres <;>
      imod Hclose $$ [Hauth1 Hauth2 Hr Hres Hα] <;>
      first
        | (inext; iexists _, _; iframe; ipureintro; exact Hc1)
        | (imodintro; iapply HΦ; ipureintro; rfl)

end race

end Coneris.Examples.Race
