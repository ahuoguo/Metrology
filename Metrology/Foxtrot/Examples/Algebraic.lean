module

public import Metrology.Foxtrot.AdequacyInstance
public import Metrology.Foxtrot.BinaryRel.BinarySoundness
public import Metrology.Foxtrot.Lib.Toss
public import Metrology.Foxtrot.Lib.Or
public import Metrology.Foxtrot.Lib.Diverge
public import Metrology.Foxtrot.Lib.Par

/-!
# Algebraic theory of `toss` and `or` (part 1: setup, `eq1`, `eq2`)

Ported from clutch/theories/foxtrot/examples/algebraic.v

The Rocq file is split into several modules (all in namespace `Foxtrot.Examples.Algebraic`):
* `Algebraic` (this file): functor lists, the local tactics, `eq1`, `eq2`;
* `AlgebraicEq3Steps`, `AlgebraicEq3Assoc`, `AlgebraicEq3Par`: the intermediate refinements
  of the Rocq proofs of `eq3_1`/`eq3_2`;
* `AlgebraicEq3`: `eq3_1`, `eq3_2`, `eq3`;
* `AlgebraicOr`: `eq4` … `eq8`.

## Rocq → Lean map
* `eq1`, `eq2`, `eq3_1`, `eq3_2`, `eq3`, `eq4`, `eq5`, `eq6`, `eq7`, `eq8`, `empty_gamma`:
  same names. The section `Variable`s are explicit arguments (all of them, as with Rocq's
  `Default Proof Using "Type*"`, e.g. the unused `Hineq` of `eq2`).
* `apply (refines_sound #[foxtrotRΣ])` is `apply refines_sound foxtrotSigma` (with the instance
  `foxtrotRGpreS_foxtrotSigma`, Rocq: `subG_foxtrotRGPreS`); `#[spawnΣ; foxtrotRΣ]` is
  `spawnFoxtrotRSigma` (a copy of `foxtrotSigma` with iris-lean's `TokenF` at index 8, with
  instances `foxtrotRGpreS_spawnFoxtrotRSigma`, `spawnG_spawnFoxtrotRSigma`).
* `iPoseProof (binary_fundamental.refines_typed _ _ _ H) as "H"` is
  `ihave H := refines_typed τ Δ e H`; `unfold_rel` is the `unfold_rel` macro.
* `case_bool_decide` (stdpp) is the local tactic `case_bool_decide` (a `by_cases` on the first
  `decide P` of the goal, rewriting it by `decide_eq_true`/`decide_eq_false`).
* The Rocq `Ltac solve_subst` is the local macro `solve_subst` (a `simp only` with
  `subst_is_closed_empty` and `typed_closed_empty` for the hypotheses `H1`, `H2`, `H3`).
* The in-proof Rocq assertions `Bij (λ x, if bool_decide (x<=q) then q-x else x)` are the
  definition `flip_bij` with `flip_bij_bij` (and `flip_bij_dom`, `flip_bij_le` for the
  side conditions solved by `lia` in Rocq).
* `wp_couple_rand_rand` / `wp_couple_rand_rand_lbl` / `pupd_couple_tape_rand` used without an
  explicit bijection in Rocq (the `Bij` instance found by typeclass search is the identity) are
  applied to `id`/`Function.bijective_id`.

## Deviations
* The Rocq proofs of `eq3_1` and `eq3_2` are chains of `ctx_refines_transitive` whose steps are
  inlined (and repeated, up to renaming). Here each step is a named lemma (`eq3_step_tapes`,
  `eq3_step_assoc`, `eq3_step_par_tapes`, `eq3_step_untape`, `eq3_step_flip`,
  `eq3_step_toss_toss`), stated for arbitrary parameters with the bounds of the Rocq
  intermediate programs given by equations, and `eq3_1`/`eq3_2` instantiate them. The Rocq
  arithmetic of the last step of `eq3_2` is `eq3_arith`.
* Texan-triple applications `wp_apply (lem with "[$]")` are `wp_apply lem $$ H`; framing with
  `[$Hα $Hspec]` is `$$ [Hα Hspec]` followed by `iframe`.
* The Rocq `rewrite bool_decide_eq_true_2; last lia` are `case_bool_decide <;> try omega`.
-/

@[expose] public section

noncomputable section

open Iris Iris.BI Iris.Std Iris.ProofMode OFE COFE ConProbLang ConProbLang.con_prob_lang
open Foxtrot.BinaryRel Foxtrot.Lib.Toss Foxtrot.Lib.Or Foxtrot.Lib.Diverge Foxtrot.Lib.Par
open Foxtrot.Lib.Spawn

namespace Foxtrot.Examples.Algebraic

/-- Rocq: `foxtrotRΣ` / `subG_foxtrotRGPreS` (at `foxtrotSigma`). -/
instance foxtrotRGpreS_foxtrotSigma : foxtrotRGpreS foxtrotSigma :=
  ⟨foxtrotGpreS_foxtrotSigma⟩

/-- Rocq: `#[spawnΣ; foxtrotRΣ]`. -/
def spawnFoxtrotRSigma : BundledGFunctors
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

instance foxtrotRGpreS_spawnFoxtrotRSigma : foxtrotRGpreS spawnFoxtrotRSigma where
  foxtrotRGpreS_foxtrot := {
    foxtrotGpreS_iris := {
      toWsatGpreS := ⟨⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩⟩
      toLcGpreS := ⟨⟨3, rfl⟩⟩ }
    foxtrotGpreS_heap := ⟨⟨4, rfl⟩⟩
    foxtrotGpreS_tapes := ⟨⟨5, rfl⟩⟩
    foxtrotGpreS_spec := ⟨⟨⟨6, rfl⟩⟩, ⟨⟨4, rfl⟩⟩, ⟨⟨5, rfl⟩⟩⟩
    foxtrotGpreS_err := ⟨⟨7, rfl⟩⟩ }

instance spawnG_spawnFoxtrotRSigma : spawnG spawnFoxtrotRSigma where
  spawn_tokG := ⟨8, rfl⟩

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

/-- Rocq: `empty_gamma`. -/
theorem empty_gamma : (∅ : stringset) = dom (∅ : varmap type) := by
  rw [dom_empty]

/-- Rocq: `typed_is_closed_expr` at the empty context (as used by the Rocq `solve_subst`). -/
theorem typed_closed_empty {e : expr} {τ : type} (H : ∅ ⊢ₜ e : τ) :
    is_closed_expr ∅ e = true := by
  simpa using typed_is_closed_expr _ _ _ H

set_option hygiene false in
/-- Rocq: the `Ltac solve_subst` of section `eq3`: removes the substitutions into the closed
expressions `e1`, `e2`, `e3` (typed by the Lean hypotheses `H1`, `H2`, `H3`). -/
macro "solve_subst" : tactic => `(tactic| try simp only [
    subst_is_closed_empty _ _ _ (typed_closed_empty H1),
    subst_is_closed_empty _ _ _ (typed_closed_empty H2),
    subst_is_closed_empty _ _ _ (typed_closed_empty H3)])

section eq1

/-- Rocq: `eq1`. -/
theorem eq1 (e : expr) (τ : type) (p q : ℕ) (H : ∅ ⊢ₜ e : τ) :
    ∅ ⊨ toss p q e e =ctx= e : τ := by
  constructor
  · apply refines_sound foxtrotSigma
    intro _ Δ
    refine (refines_typed τ Δ e H).trans ?_
    unfold_rel
    iintro H %K %j Hspec
    unfold toss
    wp_apply (wp_rand q q (Int.toNat_natCast _).symm) with %n %Hn
    · itrivial
    wp_pures
    case_bool_decide <;> wp_pures <;> iapply H $$ Hspec
  · apply refines_sound foxtrotSigma
    intro _ Δ
    refine (refines_typed τ Δ e H).trans ?_
    unfold_rel
    iintro H %K %j Hspec
    unfold toss
    tp_bind j (Rand _ _)
    imod pupd_rand j _ q q ⊤ (Int.toNat_natCast _).symm $$ Hspec with ⟨%n, Hspec, %Hn⟩
    tp_pures j
    case_bool_decide <;> tp_pures j <;> iapply H $$ Hspec

end eq1

section eq2

/-- The bijection `λ x, if bool_decide (x ≤ q) then q - x else x` of the Rocq proofs of `eq2`
and `eq3_2` (Rocq: the local assertions `Hbij`, `Hbij1`, `Hbij2`). -/
def flip_bij (q : ℕ) (x : ℕ) : ℕ := if x ≤ q then q - x else x

theorem flip_bij_bij (q : ℕ) : Function.Bijective (flip_bij q) := by
  constructor
  · intro x y h
    unfold flip_bij at h
    split_ifs at h <;> omega
  · intro y
    by_cases hy : y ≤ q
    · exact ⟨q - y, by simp only [flip_bij, show q - y ≤ q by omega, ↓reduceIte]; omega⟩
    · exact ⟨y, by simp only [flip_bij, hy, ↓reduceIte]⟩

theorem flip_bij_dom (q : ℕ) : ∀ n : ℕ, n < q + 1 → flip_bij q n < q + 1 := by
  intro n hn
  unfold flip_bij
  split_ifs <;> omega

theorem flip_bij_le (q n : ℕ) (hn : n ≤ q) : flip_bij q n = q - n := by
  simp only [flip_bij, hn, ↓reduceIte]

/-- Rocq: `eq2`. -/
theorem eq2 (e1 e2 : expr) (τ : type) (p q : ℕ) (Hineq : p ≤ q + 1)
    (H1 : ∅ ⊢ₜ e1 : τ) (H2 : ∅ ⊢ₜ e2 : τ) :
    ∅ ⊨ toss p q e1 e2 =ctx= toss (q + 1 - p) q e2 e1 : τ := by
  constructor
  · apply refines_sound foxtrotSigma
    intro _ Δ
    ihave H1 := refines_typed τ Δ e1 H1
    ihave H2 := refines_typed τ Δ e2 H2
    unfold_rel
    iintro %K %j Hspec
    unfold toss
    tp_bind j (Rand _ _)
    wp_apply (wp_couple_rand_rand q (flip_bij q) (flip_bij_bij q) j q _
      (Int.toNat_natCast _).symm (flip_bij_dom q)) $$ Hspec with %n ⟨%Hn, Hspec⟩
    rw [flip_bij_le q n Hn]
    wp_pures
    tp_pures j
    case_bool_decide <;> case_bool_decide <;> try omega
    all_goals wp_pures; tp_pures j
    · iapply H2 $$ Hspec
    · iapply H1 $$ Hspec
  · apply refines_sound foxtrotSigma
    intro _ Δ
    ihave H1 := refines_typed τ Δ e1 H1
    ihave H2 := refines_typed τ Δ e2 H2
    unfold_rel
    iintro %K %j Hspec
    unfold toss
    tp_bind j (Rand _ _)
    wp_apply (wp_couple_rand_rand q (flip_bij q) (flip_bij_bij q) j q _
      (Int.toNat_natCast _).symm (flip_bij_dom q)) $$ Hspec with %n ⟨%Hn, Hspec⟩
    rw [flip_bij_le q n Hn]
    wp_pures
    tp_pures j
    case_bool_decide <;> case_bool_decide <;> try omega
    all_goals wp_pures; tp_pures j
    · iapply H1 $$ Hspec
    · iapply H2 $$ Hspec

end eq2

end Foxtrot.Examples.Algebraic
