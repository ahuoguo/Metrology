module

public import Metrology.Foxtrot.Examples.PresampleRhs
public import Metrology.Foxtrot.CouplingRulesMisc
public import Metrology.Foxtrot.AdequacyInstance

/-!
# Counterexample to presampling on the right-hand side

Ported from clutch/theories/foxtrot/examples/presample_rhs.v (section `counterexample` and the
lemmas `presample_RHS_is_unsound'`, `presample_RHS_is_unsound`). The programs and the
termination lemmas are in `Metrology.Foxtrot.Examples.PresampleRhs`.

If presampling on the right-hand side were allowed (`unsound_presample_RHS`: a `rand #z` on the
left-hand side may record its result on a right-hand side tape), then the chain of refinements
`prog0 ≤ prog1 ≤ prog2 ≤ prog3` (via `foxtrot_adequacy`) would give that `prog3` terminates with
probability `1`, while it terminates with probability at most `1/2` (`prog3_termination`).

## Rocq → Lean map
* `unsound_presample_RHS`, `presample_RHS_is_unsound'`, `presample_RHS_is_unsound`: same names
  (namespace `Foxtrot.Examples.PresampleRhs`).

## Deviations
* `unsound_presample_RHS` takes the ghost-functor bundle `GF` explicitly (Rocq: the section's
  `Σ` with `foxtrotGS Σ`); `TCEq N (Z.to_nat z)` is `N = z.toNat`. The Texan triple is
  iris-lean's `{{ P }} e @ NotStuck; E {{ (n : ℕ), RET #n; Q }}` (Rocq: `@ E`, i.e. not stuck);
  `#n` for `n : ℕ` is `LitV (LitInt (n : ℤ))`.
* The hypothesis `∀ `{H: foxtrotGS Σ} N z E α ns, unsound_presample_RHS N z E α ns` is
  `∀ (GF : BundledGFunctors) [foxtrotGS GF] N z E α ns, unsound_presample_RHS GF N z E α ns`.
* `foxtrot_adequacy (#[foxtrotΣ]) (λ _ _, True)` is `foxtrot_adequacy_closed (fun _ _ => True)`
  (at the concrete functor list `foxtrotSigma` of `Metrology.Foxtrot.AdequacyInstance`), with
  `ε = 0`; Rocq's `Rbar_plus _ 0` is `_ + 0` in `ℝ≥0∞`.
* `inhabitant` (of `state`) is `default`.
* In the third refinement, the bijection of the Rocq case `n = 0` is the same
  (`λ x, if x ≤ 1 then 1 - x else x`); in the cases `n = 1` and `n ≥ 2` the bijection (an evar
  in Rocq) is `id`.
* The three WP proofs are the helpers `prog0_prog1`, `prog1_prog2`, `prog2_prog3` (inline in
  Rocq).

## Added
* `prog0_prog1`, `prog1_prog2`, `prog2_prog3`, `flip01`, `flip01_bij`, and the local tactic
  `case_bool_decide` (Rocq: stdpp's `case_bool_decide`).

## Omitted
None.
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang
open Foxtrot Foxtrot.Lib.Diverge Foxtrot.Lib.Nodet

namespace Foxtrot.Examples.PresampleRhs

/-- Rocq: `case_bool_decide` (stdpp). Case-splits on the proposition `P` of the first
`decide P` of the goal, rewriting `decide P` to `true` (resp. `false`). -/
syntax (name := caseBoolDecide) "case_bool_decide" (" as " ident)? : tactic

open Lean Elab Tactic Meta in
@[tactic caseBoolDecide] meta def evalCaseBoolDecide : Tactic := fun stx => do
  let tgt ← instantiateMVars (← getMainTarget)
  let some d := tgt.find? (fun e => e.isAppOfArity ``Decidable.decide 2 && !e.hasLooseBVars)
    | throwError "case_bool_decide: no `decide` in the goal"
  let P := d.appFn!.appArg!
  let hId : Ident := if stx[1].getNumArgs == 2 then ⟨stx[1][1]⟩ else mkIdent `Hdec
  let Pstx ← Term.exprToSyntax P
  let hT : Term := ⟨hId.raw⟩
  evalTactic (← `(tactic| by_cases $hId : $Pstx <;>
    first | rw [decide_eq_true $hT] | rw [decide_eq_false $hT]))

section counterexample

variable (GF : BundledGFunctors) [foxtrotGS GF]

/-- Rocq: `unsound_presample_RHS`. -/
def unsound_presample_RHS (N : ℕ) (z : ℤ) (E : CoPset) (α : Loc) (ns : List ℕ) : Prop :=
  N = z.toNat →
  {{ (α ↪ₛN (N; ns) : IProp GF) }}
    (Rand (Val (LitV (LitInt z))) (Val (LitV LitUnit))) @ Stuckness.NotStuck; E
  {{ (n : ℕ), RET LitV (LitInt (n : ℤ)); α ↪ₛN (N; ns ++ [n]) ∗ ⌜n ≤ N⌝ }}

end counterexample

section proofs

variable {GF : BundledGFunctors} [foxtrotGS GF]

/-- Helper (Rocq: the first bullet of `presample_RHS_is_unsound'`). -/
theorem prog0_prog1 :
    ⊢@{IProp GF} ↯ 0 -∗ 0 ⤇ prog1 -∗
      WP prog0 {{ _v, ∃ v' : val, 0 ⤇ Val v' ∗ ⌜True⌝ }} := by
  iintro - Hspec
  unfold prog1 prog0
  tp_bind 0 (Rand _ _)
  imod pupd_rand 0 _ 1 1 ⊤ rfl $$ Hspec with ⟨%n, Hspec, %hn⟩
  tp_bind 0 (App _ _)
  imod tp_nodet 0 _ ⊤ n $$ Hspec with Hspec
  tp_pures 0
  wp_pures
  iexists _
  iframe Hspec

/-- Helper (Rocq: the second bullet of `presample_RHS_is_unsound'`). -/
theorem prog1_prog2
    (H : ∀ (N : ℕ) (z : ℤ) (E : CoPset) (α : Loc) (ns : List ℕ),
      unsound_presample_RHS GF N z E α ns) :
    ⊢@{IProp GF} ↯ 0 -∗ 0 ⤇ prog2 -∗
      WP prog1 {{ _v, ∃ v' : val, 0 ⤇ Val v' ∗ ⌜True⌝ }} := by
  iintro - Hspec
  unfold prog1 prog2
  tp_bind 0 (AllocTape _)
  imod pupd_alloc_tape ⊤ _ 0 1 1 rfl $$ Hspec with ⟨%α, Htape, Hspec⟩
  tp_pures 0
  wp_bind (Rand _ _)
  wp_apply (H 1 1 ⊤ α [] rfl) $$ Htape with %n ⟨Htape, %hn⟩
  simp only [List.nil_append]
  tp_bind 0 (App _ _)
  imod tp_nodet 0 _ ⊤ n $$ Hspec with Hspec
  tp_bind 0 (Rand _ _)
  imod pupd_rand_tape 0 _ 1 1 ⊤ n [] α rfl $$ Hspec Htape with ⟨Hspec, Htape⟩
  tp_pures 0
  wp_apply wp_nodet with %m -
  · itrivial
  wp_pures
  case_bool_decide
  · wp_pures
    iexists _
    iframe Hspec
  · wp_pures
    wp_apply wp_diverge with %v Hfalse
    · itrivial
    iexfalso
    iexact Hfalse

/-- Helper: the bijection of the case `n = 0` of Rocq's third bullet (Rocq: inline
`λ x, if bool_decide (x <= 1) then 1 - x else x`). -/
def flip01 (x : ℕ) : ℕ := if x ≤ 1 then 1 - x else x

/-- Helper: `flip01` is a bijection (Rocq: the inline `Bij` proof `hbij`). -/
theorem flip01_bij : Function.Bijective flip01 := by
  constructor
  · intro a b h
    unfold flip01 at h
    split_ifs at h <;> omega
  · intro y
    by_cases hy : y ≤ 1
    · exact ⟨1 - y, by unfold flip01; split_ifs <;> omega⟩
    · exact ⟨y, by simp [flip01, hy]⟩

/-- Helper (Rocq: the third bullet of `presample_RHS_is_unsound'`). -/
theorem prog2_prog3 :
    ⊢@{IProp GF} ↯ 0 -∗ 0 ⤇ prog3 -∗
      WP prog2 {{ _v, ∃ v' : val, 0 ⤇ Val v' ∗ ⌜True⌝ }} := by
  iintro - Hspec
  unfold prog3 prog2
  wp_alloctape α as Hα
  wp_pures
  wp_apply wp_nodet with %n -
  · itrivial
  rcases n with _ | _ | n
  · tp_bind 0 (Rand _ _)
    imod pupd_couple_tape_rand 1 flip01 flip01_bij _ ⊤ α 1 [] 0 rfl
      (fun n hn => by unfold flip01; split_ifs <;> omega) $$ Hα Hspec with ⟨%m, Hα, Hspec, %hm⟩
    simp only [List.nil_append]
    wp_randtape
    wp_pures
    case_bool_decide as Hm
    · subst Hm
      rw [show flip01 0 = 1 from rfl]
      tp_pures 0
      wp_pures
      iexists _
      iframe Hspec
    · wp_pures
      wp_apply wp_diverge with %v Hfalse
      · itrivial
      iexfalso
      iexact Hfalse
  · tp_bind 0 (Rand _ _)
    imod pupd_couple_tape_rand 1 _root_.id Function.bijective_id _ ⊤ α 1 [] 0 rfl
      (fun n hn => hn) $$ Hα Hspec with ⟨%m, Hα, Hspec, %hm⟩
    simp only [List.nil_append, id_eq]
    wp_randtape
    wp_pures
    tp_pures 0
    case_bool_decide as Hm
    · tp_pures 0
      wp_pures
      iexists _
      iframe Hspec
    · wp_pures
      wp_apply wp_diverge with %v Hfalse
      · itrivial
      iexfalso
      iexact Hfalse
  · tp_bind 0 (Rand _ _)
    imod pupd_couple_tape_rand 1 _root_.id Function.bijective_id _ ⊤ α 1 [] 0 rfl
      (fun n hn => hn) $$ Hα Hspec with ⟨%m, Hα, Hspec, %hm⟩
    simp only [List.nil_append, id_eq]
    wp_randtape
    wp_pures
    rw [decide_eq_false (by omega)]
    wp_pures
    wp_apply wp_diverge with %v Hfalse
    · itrivial
    iexfalso
    iexact Hfalse

end proofs

/-- Rocq: `presample_RHS_is_unsound'`. -/
theorem presample_RHS_is_unsound' (σ : state)
    (H : ∀ (GF : BundledGFunctors) [foxtrotGS GF] (N : ℕ) (z : ℤ) (E : CoPset) (α : Loc)
      (ns : List ℕ), unsound_presample_RHS GF N z E α ns) :
    1 ≤ lub_termination_prob prog3 σ := by
  calc (1 : ℝ≥0∞) ≤ lub_termination_prob prog0 σ := prog0_termination σ
    _ ≤ lub_termination_prob prog1 σ + 0 :=
        foxtrot_adequacy_closed (fun _ _ => True) prog0 prog1 σ σ 0 prog0_prog1
    _ = lub_termination_prob prog1 σ := add_zero _
    _ ≤ lub_termination_prob prog2 σ + 0 :=
        foxtrot_adequacy_closed (fun _ _ => True) prog1 prog2 σ σ 0 (prog1_prog2 (H _))
    _ = lub_termination_prob prog2 σ := add_zero _
    _ ≤ lub_termination_prob prog3 σ + 0 :=
        foxtrot_adequacy_closed (fun _ _ => True) prog2 prog3 σ σ 0 prog2_prog3
    _ = lub_termination_prob prog3 σ := add_zero _

/-- Rocq: `presample_RHS_is_unsound`. -/
theorem presample_RHS_is_unsound
    (H : ∀ (GF : BundledGFunctors) [foxtrotGS GF] (N : ℕ) (z : ℤ) (E : CoPset) (α : Loc)
      (ns : List ℕ), unsound_presample_RHS GF N z E α ns) : False := by
  have H' : (1 : ℝ≥0∞) ≤ 1 / 2 :=
    (presample_RHS_is_unsound' default H).trans (prog3_termination default)
  norm_num at H'

end Foxtrot.Examples.PresampleRhs
