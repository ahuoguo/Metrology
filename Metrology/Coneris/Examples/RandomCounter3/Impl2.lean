module

public import Metrology.Coneris.Examples.RandomCounter3.RandomCounter
public import Metrology.Coneris.Lib.HocapFlip
public import Mathlib.Tactic.IntervalCases

/-!
# Random counter, implementation 2 (two presampled flips)

Ported from clutch/theories/coneris/examples/random_counter3/impl2.v

## Rocq → Lean mapping
* The `Local` definitions and lemmas `expander`, `expander_eta`, `expander_inj`, `decoder`,
  `decoder_correct`, `decoder_inj`, `decoder_ineq`, `decoder_None`, `decoder_Some_length` keep
  their names (they are public here, in the namespace of this file).
  - `l ≫= (λ x, [2<=?x; Nat.odd x])` is `l.flatMap (fun x => [Nat.ble 2 x, Nat.bodd x])`
    (`Nat.odd` of Rocq is Mathlib's `Nat.bodd`).
  - `Z.b2z` is `Bool.toInt`; `Forall (λ x, x < 4) l` is `∀ x ∈ l, x < 4`.
  - `res ← decoder ls; Some (...)` is `Option.bind`-`do` notation.
  - `bool_to_nat` is the helper of `Coneris.Lib.Flip`.
  - `decoder_None` is proved through the helper `decoder_None_aux` (structural recursion on
    the list instead of Rocq's well-founded induction on `p`).
* Section `impl2`: the context `F: flip_spec Σ`, `L:!flipG Σ`, `!inG Σ (frac_authR natR)` is
  `[F : flip_spec GF] (L : F.flipG GF) [HE : ElemG GF frac_auth_natF]`. As in
  `Coneris.Lib.HocapFlip`, `L` is an explicit argument; it is taken only by the statements that
  use it (`counter_tapes_presample2`, `incr_counter_spec2`).
* `new_counter2`, `incr_counter2`, `read_counter2`: transcribed with the `cpl` notation;
  `flip_allocate_tape`, `flip_tape` are `F.flip_allocate_tape`, `F.flip_tape`;
  `conversion.bool_to_int` is `Coneris.Lib.Conversion.bool_to_int`.
* `counterG2` (Rocq `Class` with the instance field `counterG2_frac_authR ::` and the field
  `counterG2_flipG`) is a Lean class with the same fields; `counterG2_to_flipG` takes the
  `counterG2` argument explicitly.
* `counter_inv_pred2`, `is_counter2`, `new_counter_spec2`, `counter_tapes_presample2`,
  `incr_counter_spec2`, `read_counter_spec2`: same names. Errors are `ℝ≥0∞` (see
  `RandomCounter`): the hypotheses `∀ x, 0 <= ε2 x` are dropped. `state_update E E` is
  `state_update E E`.
* `random_counter2` (a `Program Definition`) is a definition; its `Next Obligation`s are the
  theorems `random_counter2_counter_content_*` (proved by the shared `frac_auth_nat_*`
  helpers of `RandomCounter`).

## Proofs that differ from Rocq
* The `lra`/`SeriesC_finite_foldr` side conditions of the two `flip_tapes_presample` calls are
  the helpers `presample2_first_le`, `presample2_second_le`.
* `rewrite /expander -!app_assoc/= ... Nat.OddT_odd` is a `rfl` rewrite of the concrete tapes.

## Added
* `counter_auth2`, `counter_frag2` (the `own` assertions), `decoder_None_aux`,
  `presample2_first_le`, `presample2_second_le`, `expander_singleton`.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE CMRA Prob ConProbLang ConProbLang.con_prob_lang
open Coneris Coneris.Lib.Conversion Coneris.Lib.Flip Coneris.Lib.HocapFlip
open Coneris.Examples.RandomCounter3.RandomCounter

namespace Coneris.Examples.RandomCounter3.Impl2

/-! ## Expander and decoder -/

/-- Rocq: `expander` (`Local`). -/
def expander (l : List ℕ) : List Bool :=
  l.flatMap (fun x => [Nat.ble 2 x, Nat.bodd x])

/-- Rocq: `expander_eta` (`Local`). -/
theorem expander_eta (x : ℕ) (h : x < 4) :
    (x : ℤ) = ((2 : ℕ) : ℤ) * (Nat.ble 2 x).toInt + (Nat.bodd x).toInt := by
  interval_cases x <;> rfl

/-- Rocq: `expander_inj` (`Local`). -/
theorem expander_inj (l1 l2 : List ℕ) (H1 : ∀ x ∈ l1, x < 4) (H2 : ∀ y ∈ l2, y < 4)
    (H : expander l1 = expander l2) : l1 = l2 := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => rfl
    | cons y ys => simp [expander] at H
  | cons x xs IH =>
    cases l2 with
    | nil => simp [expander] at H
    | cons y ys =>
      simp only [expander, List.flatMap_cons, List.cons_append, List.nil_append,
        List.cons.injEq] at H
      obtain ⟨Ha, Hb, Hrest⟩ := H
      have hx := H1 x List.mem_cons_self
      have hy := H2 y List.mem_cons_self
      have hxy : x = y := by
        interval_cases x <;> interval_cases y <;> simp_all
      subst hxy
      rw [IH ys (fun z hz => H1 z (List.mem_cons_of_mem _ hz))
        (fun z hz => H2 z (List.mem_cons_of_mem _ hz)) Hrest]

/-- Rocq: `decoder` (`Local`). -/
def decoder : List Bool → Option (List ℕ)
  | [] => some []
  | b :: b' :: ls => do
      let res ← decoder ls
      some (((bool_to_nat b) * 2 + (bool_to_nat b')) :: res)
  | _ => none

/-- Rocq: `decoder_correct` (`Local`). -/
theorem decoder_correct (bs : List Bool) (ns : List ℕ) (H : decoder bs = some ns) :
    expander ns = bs := by
  induction ns generalizing bs with
  | nil =>
    match bs, H with
    | [], _ => rfl
    | [_], H => simp [decoder] at H
    | _ :: _ :: _, H =>
      simp only [decoder, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at H
      obtain ⟨_, _, H⟩ := H
      simp at H
  | cons n ns IH =>
    match bs, H with
    | [], H => simp [decoder] at H
    | [_], H => simp [decoder] at H
    | b :: b' :: ls, H =>
      simp only [decoder, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
        List.cons.injEq] at H
      obtain ⟨res, Hres, Hn, Hns⟩ := H
      subst Hn Hns
      simp only [expander, List.flatMap_cons, List.cons_append, List.nil_append] at IH ⊢
      rw [IH ls Hres]
      cases b <;> cases b' <;> rfl

/-- Rocq: `decoder_inj` (`Local`). -/
theorem decoder_inj (x y : List Bool) (z : List ℕ) (H1 : decoder x = some z)
    (H2 : decoder y = some z) : x = y := by
  rw [← decoder_correct x z H1, ← decoder_correct y z H2]

/-- Rocq: `decoder_ineq` (`Local`). -/
theorem decoder_ineq (bs : List Bool) (xs : List ℕ) (H : decoder bs = some xs) :
    ∀ x ∈ xs, x < 4 := by
  induction xs generalizing bs with
  | nil => simp
  | cons x xs IH =>
    match bs, H with
    | [], H => simp [decoder] at H
    | [_], H => simp [decoder] at H
    | b :: b' :: ls, H =>
      simp only [decoder, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
        List.cons.injEq] at H
      obtain ⟨res, Hres, Hn, Hns⟩ := H
      subst Hn Hns
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · cases b <;> cases b' <;> simp [bool_to_nat]
      · exact IH ls Hres y hy

/-- Helper: `decoder_None` without the length parameter. -/
theorem decoder_None_aux : ∀ bs : List Bool, decoder bs = none →
    ¬ ∃ num, bs.length = 2 * num
  | [], H => by simp [decoder] at H
  | [_], _ => by
    rintro ⟨num, h⟩
    simp at h
    omega
  | _ :: _ :: ls, H => by
    simp only [decoder, Option.bind_eq_bind, Option.bind_eq_none_iff] at H
    have H' : decoder ls = none := by
      cases h : decoder ls with
      | none => rfl
      | some r => exact absurd (H r h) (by simp)
    rintro ⟨num, hnum⟩
    simp only [List.length_cons] at hnum
    exact decoder_None_aux ls H' ⟨num - 1, by omega⟩

/-- Rocq: `decoder_None` (`Local`). -/
theorem decoder_None (p : ℕ) (bs : List Bool) (_Hlen : bs.length = p)
    (H : decoder bs = none) : ¬ ∃ num, bs.length = 2 * num :=
  decoder_None_aux bs H

/-- Rocq: `decoder_Some_length` (`Local`). -/
theorem decoder_Some_length (bs : List Bool) (xs : List ℕ) (H : decoder bs = some xs) :
    bs.length = 2 * xs.length := by
  rw [← decoder_correct bs xs H]
  clear H
  induction xs with
  | nil => rfl
  | cons x xs IH =>
    simp only [expander, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil] at IH ⊢
    omega

/-- Helper: `expander [n]` computed. -/
theorem expander_singleton (n : ℕ) : expander [n] = [Nat.ble 2 n, Nat.bodd n] := by
  simp [expander]

/-! ## Error arithmetic of the presampling -/

/-- Helper: the side condition of the first `flip_tapes_presample` of
`counter_tapes_presample2`. -/
theorem presample2_first_le (ε : ℝ≥0∞) (ε2 : Fin 4 → ℝ≥0∞)
    (Hineq : ∑' n, 1 / 4 * ε2 n ≤ ε) :
    ((1 / 2 * (if true then ε2 2 + ε2 3 else ε2 0 + ε2 1)) +
      (1 / 2 * (if false then ε2 2 + ε2 3 else ε2 0 + ε2 1))) / 2 ≤ ε := by
  rw [tsum_fintype, ← Finset.mul_sum, Fin.sum_univ_four] at Hineq
  refine le_trans (le_of_eq ?_) Hineq
  have h4 : (4 : ℝ≥0∞)⁻¹ = 2⁻¹ * 2⁻¹ := by
    rw [← ENNReal.mul_inv (by norm_num) (by norm_num)]
    norm_num
  simp only [↓reduceIte, Bool.false_eq_true, div_eq_mul_inv, one_mul, h4]
  ring

/-- Helper: the side condition of the second `flip_tapes_presample` of
`counter_tapes_presample2`. -/
theorem presample2_second_le (a b : ℝ≥0∞) :
    ((if true then b else a) + (if false then b else a)) / 2 ≤ 1 / 2 * (a + b) := by
  simp only [↓reduceIte, Bool.false_eq_true]
  rw [div_eq_mul_inv, one_div, mul_comm, add_comm]

/-! ## Implementation -/

section impl2

variable {GF : BundledGFunctors} [conerisGS GF] [F : flip_spec GF]

/-- Rocq: `new_counter2`. -/
def new_counter2 : val := cpl_val(λ "_", ref(#0))

/-- Rocq: `incr_counter2`. -/
def incr_counter2 : val := cpl_val(
  λ "l", let "α" := (v(&F.flip_allocate_tape) #()) in
         let "n" :=
           &bool_to_int (v(&F.flip_tape) "α")
         in
         let "n'" :=
           &bool_to_int (v(&F.flip_tape) "α")
         in
         let "x" := #2 * "n" + "n'" in
         (faa("l", "x"), "x"))

/-- Rocq: `read_counter2`. -/
def read_counter2 : val := cpl_val(λ "l", !"l")

/-- Rocq: `counterG2`. -/
class counterG2 (GF' : BundledGFunctors) : Type where
  counterG2_frac_authR : ElemG GF' frac_auth_natF
  counterG2_flipG : F.flipG GF'

variable [HE : ElemG GF frac_auth_natF]

/-- `own γ (●F z)`. -/
abbrev counter_auth2 (γ : GName) (z : ℕ) : IProp GF := iOwn (F := frac_auth_natF) γ (●F z)

/-- `own γ (◯F{f} z)`. -/
abbrev counter_frag2 (γ : GName) (f : Qp) (z : ℕ) : IProp GF :=
  iOwn (F := frac_auth_natF) γ (◯F{f} z)

/-- Rocq: `counter_inv_pred2`. -/
def counter_inv_pred2 (c : val) (γ : GName) : IProp GF :=
  iprop(∃ (l : Loc) (z : ℕ), ⌜c = LitV (LitLoc l)⌝ ∗ l ↦ LitV (LitInt (z : ℤ)) ∗
    counter_auth2 γ z)

/-- Rocq: `is_counter2`. -/
def is_counter2 (N : Namespace) (c : val) (γ1 : GName) : IProp GF :=
  inv N (counter_inv_pred2 c γ1)

instance is_counter2_persistent (N : Namespace) (c : val) (γ1 : GName) :
    Persistent (is_counter2 (GF := GF) N c γ1) := by
  unfold is_counter2; infer_instance

/-- Rocq: `new_counter_spec2`. -/
theorem new_counter_spec2 (E : CoPset) (N : Namespace) :
    {{ True }} cpl(v(&new_counter2) #()) @ E
    {{ c, RET c; ∃ γ1, is_counter2 (GF := GF) N c γ1 ∗ counter_frag2 γ1 1 0 }} := by
  iintro %Φ - HΦ
  unfold new_counter2
  wp_pures
  wp_alloc l as Hl
  imod iOwn_alloc (F := frac_auth_natF) (CMRA.op (●F (0 : ℕ)) (◯F (0 : ℕ))) with ⟨%γ1, H5, H6⟩
  · exact FracAuth.valid trivial
  imod inv_alloc N E (counter_inv_pred2 (LitV (LitLoc l)) γ1) $$ [Hl H5] with #Hinv'
  · inext
    unfold counter_inv_pred2
    iexists l, 0
    iframe
    ipureintro
    rfl
  imodintro
  iapply HΦ
  iexists γ1
  unfold is_counter2
  iframe
  iexact Hinv'

/-- Rocq: `counter_tapes_presample2`. -/
theorem counter_tapes_presample2 (L : F.flipG GF) (N : Namespace) (E : CoPset) (γ1 : GName)
    (c α : val) (ε : ℝ≥0∞) (ε2 : Fin 4 → ℝ≥0∞) (Hineq : ∑' n, 1 / 4 * ε2 n ≤ ε) :
    ⊢ is_counter2 N c γ1 -∗
      (F.flip_tapes L α (expander []) ∗ ⌜∀ x ∈ ([] : List ℕ), x < 4⌝) -∗
      ↯ ε -∗
      state_update E E iprop(∃ n : Fin 4, ↯ (ε2 n) ∗
        (F.flip_tapes L α (expander [(n : ℕ)]) ∗ ⌜∀ x ∈ [(n : ℕ)], x < 4⌝)) := by
  iintro #Hinv' ⟨Hfrag, %Hforall⟩ Herr
  imod F.flip_tapes_presample L E α (expander []) ε
    (fun b => 1 / 2 * if b then ε2 2 + ε2 3 else ε2 0 + ε2 1)
    (presample2_first_le ε ε2 Hineq) $$ Hfrag Herr with ⟨%b, Herr, Hfrag⟩
  cases b
  · ihave Herr := ErrorCredit.ext (ε₂ := 1 / 2 * (ε2 0 + ε2 1)) (by simp) $$ Herr
    imod F.flip_tapes_presample L E α _ _ (fun b => if b then ε2 1 else ε2 0)
      (presample2_second_le _ _) $$ Hfrag Herr with ⟨%b, Herr, Hfrag⟩
    cases b
    · ihave Herr := ErrorCredit.ext (ε₂ := ε2 0) (by simp) $$ Herr
      rw [show expander [] ++ [false] ++ [false] = expander [((0 : Fin 4) : ℕ)] from rfl]
      imodintro
      iexists 0
      iframe Herr
      isplitl
      · iexact Hfrag
      · ipureintro
        simp
    · ihave Herr := ErrorCredit.ext (ε₂ := ε2 1) (by simp) $$ Herr
      rw [show expander [] ++ [false] ++ [true] = expander [((1 : Fin 4) : ℕ)] from rfl]
      imodintro
      iexists 1
      iframe Herr
      isplitl
      · iexact Hfrag
      · ipureintro
        simp
  · ihave Herr := ErrorCredit.ext (ε₂ := 1 / 2 * (ε2 2 + ε2 3)) (by simp) $$ Herr
    imod F.flip_tapes_presample L E α _ _ (fun b => if b then ε2 3 else ε2 2)
      (presample2_second_le _ _) $$ Hfrag Herr with ⟨%b, Herr, Hfrag⟩
    cases b
    · ihave Herr := ErrorCredit.ext (ε₂ := ε2 2) (by simp) $$ Herr
      rw [show expander [] ++ [true] ++ [false] = expander [((2 : Fin 4) : ℕ)] from rfl]
      imodintro
      iexists 2
      iframe Herr
      isplitl
      · iexact Hfrag
      · ipureintro
        simp
    · ihave Herr := ErrorCredit.ext (ε₂ := ε2 3) (by simp) $$ Herr
      rw [show expander [] ++ [true] ++ [true] = expander [((3 : Fin 4) : ℕ)] from rfl]
      imodintro
      iexists 3
      iframe Herr
      isplitl
      · iexact Hfrag
      · ipureintro
        simp

/-- Rocq: `incr_counter_spec2`. -/
theorem incr_counter_spec2 (L : F.flipG GF) (N : Namespace) (E : CoPset) (c : val)
    (γ1 : GName) (Q : ℝ≥0∞ → (Fin 4 → ℝ≥0∞) → ℕ → ℕ → IProp GF) (Hsubset : ↑N ⊆ E) :
    {{ is_counter2 N c γ1 ∗
        |={E \ ↑N, ∅}=>
          (∃ (ε : ℝ≥0∞) (ε2 : Fin 4 → ℝ≥0∞),
            ↯ ε ∗ ⌜∑' n, 1 / 4 * ε2 n ≤ ε⌝ ∗
            (∀ n : Fin 4, ↯ (ε2 n) ={∅, E \ ↑N}=∗
              (∀ z : ℕ, counter_auth2 γ1 z ={E \ ↑N}=∗
                counter_auth2 γ1 (z + n) ∗ Q ε ε2 z n))) }}
      cpl(v(&incr_counter2) v(&c)) @ E
    {{ (z n : ℕ), RET cpl_val((#z, #n)); ∃ ε ε2, Q ε ε2 z n }} := by
  iintro %Φ ⟨#Hinv, Hvs⟩ HΦ
  unfold incr_counter2
  wp_pures
  wp_apply F.flip_allocate_tape_spec L E $$ [] with %α Htape
  · itrivial
  wp_pures
  ihave H : iprop(state_update E E iprop(∃ n : Fin 4,
      (F.flip_tapes L α (expander [(n : ℕ)]) ∗ ⌜∀ x ∈ [(n : ℕ)], x < 4⌝) ∗
      ∃ ε ε2, (∀ z : ℕ, counter_auth2 γ1 z ={E \ ↑N}=∗
        counter_auth2 γ1 (z + n) ∗ Q ε ε2 z n))) $$ [Hvs Htape]
  · iapply state_update_mono_fupd' (E \ ↑N) E _ LawfulSet.diff_subset_left
    imod Hvs with ⟨%ε, %ε2, Herr, %Hsum, Hvs⟩
    imod counter_tapes_presample2 L N ∅ γ1 c α ε ε2 Hsum $$ Hinv [Htape] Herr
      with ⟨%n, Herr, Htape, %Hf⟩
    · rw [show expander [] = [] from rfl]
      iframe Htape
      ipureintro
      simp
    imod Hvs $$ Herr with Hvs
    imodintro
    iexists n
    iframe Htape
    isplit
    · ipureintro
      exact Hf
    iexists ε, ε2
    iexact Hvs
  imod H with ⟨%n, ⟨Htape, %Hf⟩, %ε, %ε2, Hvs⟩
  rw [expander_singleton]
  wp_apply F.flip_tape_spec_some L E α _ _ $$ Htape with Hα
  wp_apply wp_bool_to_int (Nat.ble 2 n) E $$ [] with -
  · itrivial
  wp_pures
  wp_apply F.flip_tape_spec_some L E α _ _ $$ Hα with Hα
  wp_apply wp_bool_to_int (Nat.bodd n) E $$ [] with -
  · itrivial
  wp_pures
  have Hn : 2 * (Nat.ble 2 n).toInt + (Nat.bodd n).toInt = ((n : ℕ) : ℤ) :=
    (expander_eta n (Hf n List.mem_cons_self)).symm
  rw [Hn]
  wp_bind (FAA _ _)
  unfold is_counter2 counter_inv_pred2
  iinv Hinv with ⟨%l, %z, >%Hc, >H5, >H6⟩ Hclose
  subst Hc
  wp_faa
  imod Hvs $$ H6 with ⟨H6, HQ⟩
  imod Hclose $$ [H5 H6]
  · inext
    iexists l, z + n
    push_cast
    iframe
    ipureintro
    trivial
  imodintro
  wp_pures
  iapply HΦ
  iexists ε, ε2
  iexact HQ

/-- Rocq: `read_counter_spec2`. -/
theorem read_counter_spec2 (N : Namespace) (E : CoPset) (c : val) (γ1 : GName)
    (Q : ℕ → IProp GF) (Hsubset : ↑N ⊆ E) :
    {{ is_counter2 N c γ1 ∗
        (∀ z : ℕ, counter_auth2 γ1 z ={E \ ↑N}=∗ counter_auth2 γ1 z ∗ Q z) }}
      cpl(v(&read_counter2) v(&c)) @ E
    {{ (n' : ℕ), RET LitV (LitInt (n' : ℤ)); Q n' }} := by
  unfold is_counter2 counter_inv_pred2
  iintro %Φ ⟨#Hinv, Hvs⟩ HΦ
  unfold read_counter2
  wp_pure
  iinv Hinv with ⟨%l, %z, >%Hc, >Hloc, >Hcont⟩ Hclose
  subst Hc
  wp_load
  imod Hvs $$ Hcont with ⟨Hcont, HQ⟩
  imod Hclose $$ [Hloc Hcont]
  · inext
    iexists l, z
    iframe
    ipureintro
    trivial
  imodintro
  iapply HΦ $$ HQ

end impl2

/-! ## `random_counter2` -/

section random_counter2

variable {GF : BundledGFunctors} [conerisGS GF] [F : flip_spec GF]

/-- Rocq: `counterG2_to_flipG`. -/
def counterG2_to_flipG (L : counterG2 GF) : F.flipG GF := L.counterG2_flipG

/-- Rocq: first `Next Obligation` of `random_counter2`. -/
theorem random_counter2_counter_content_auth_exclusive (L : counterG2 GF) (γ : GName)
    (z1 z2 : ℕ) :
    ⊢ counter_auth2 (HE := L.counterG2_frac_authR) γ z1 -∗
      counter_auth2 (HE := L.counterG2_frac_authR) γ z2 -∗ False :=
  @frac_auth_nat_auth_exclusive GF L.counterG2_frac_authR γ z1 z2

/-- Rocq: second `Next Obligation` of `random_counter2`. -/
theorem random_counter2_counter_content_less_than (L : counterG2 GF) (γ : GName) (z z' : ℕ)
    (f : Qp) :
    ⊢ counter_auth2 (HE := L.counterG2_frac_authR) γ z -∗
      counter_frag2 (HE := L.counterG2_frac_authR) γ f z' -∗ ⌜z' ≤ z⌝ :=
  @frac_auth_nat_less_than GF L.counterG2_frac_authR γ z z' f

/-- Rocq: third `Next Obligation` of `random_counter2`. -/
theorem random_counter2_counter_content_frag_combine (L : counterG2 GF) (γ : GName)
    (f f' : Qp) (z z' : ℕ) :
    iprop(counter_frag2 (HE := L.counterG2_frac_authR) γ f z ∗
      counter_frag2 (HE := L.counterG2_frac_authR) γ f' z') ⊣⊢
      counter_frag2 (HE := L.counterG2_frac_authR) γ (f + f') (z + z') :=
  @frac_auth_nat_frag_combine GF L.counterG2_frac_authR γ f f' z z'

/-- Rocq: fourth `Next Obligation` of `random_counter2`. -/
theorem random_counter2_counter_content_agree (L : counterG2 GF) (γ : GName) (z z' : ℕ) :
    ⊢ counter_auth2 (HE := L.counterG2_frac_authR) γ z -∗
      counter_frag2 (HE := L.counterG2_frac_authR) γ 1 z' -∗ ⌜z' = z⌝ :=
  @frac_auth_nat_agree GF L.counterG2_frac_authR γ z z'

/-- Rocq: fifth `Next Obligation` of `random_counter2`. -/
theorem random_counter2_counter_content_update (L : counterG2 GF) (γ : GName) (f : Qp)
    (z1 z2 z3 : ℕ) :
    ⊢ counter_auth2 (HE := L.counterG2_frac_authR) γ z1 -∗
      counter_frag2 (HE := L.counterG2_frac_authR) γ f z2 ==∗
      counter_auth2 (HE := L.counterG2_frac_authR) γ (z1 + z3) ∗
      counter_frag2 (HE := L.counterG2_frac_authR) γ f (z2 + z3) :=
  @frac_auth_nat_update GF L.counterG2_frac_authR γ f z1 z2 z3

/-- Rocq: `random_counter2` (a `Program Definition`). -/
@[instance_reducible]
def random_counter2 : random_counter GF where
  new_counter := new_counter2
  incr_counter := incr_counter2
  read_counter := read_counter2
  counterG := counterG2
  counter_name := GName
  is_counter L N c γ1 := is_counter2 (HE := L.counterG2_frac_authR) N c γ1
  counter_content_auth L γ z := counter_auth2 (HE := L.counterG2_frac_authR) γ z
  counter_content_frag L γ f z := counter_frag2 (HE := L.counterG2_frac_authR) γ f z
  is_counter_persistent L N c γ1 := is_counter2_persistent (HE := L.counterG2_frac_authR) N c γ1
  counter_content_auth_timeless L _ _ := by let := L.counterG2_frac_authR; exact iOwn_timeless
  counter_content_frag_timeless L _ _ _ := by
    let := L.counterG2_frac_authR; exact iOwn_timeless
  counter_content_auth_exclusive := random_counter2_counter_content_auth_exclusive
  counter_content_less_than := random_counter2_counter_content_less_than
  counter_content_frag_combine := random_counter2_counter_content_frag_combine
  counter_content_agree := random_counter2_counter_content_agree
  counter_content_update := random_counter2_counter_content_update
  new_counter_spec L := new_counter_spec2 (HE := L.counterG2_frac_authR)
  incr_counter_spec L :=
    incr_counter_spec2 (HE := L.counterG2_frac_authR) (counterG2_to_flipG L)
  read_counter_spec L := read_counter_spec2 (HE := L.counterG2_frac_authR)

end random_counter2

end Coneris.Examples.RandomCounter3.Impl2
