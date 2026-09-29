module

public import Metrology.Coneris.Examples.RandomCounter.RandomCounter
public import Metrology.Coneris.Lib.HocapFlip
public import Metrology.Coneris.Lib.Conversion

/-!
# Random counter: second implementation (two flips per increment)

Ported from clutch/theories/coneris/examples/random_counter/impl2.v

## Rocq → Lean mapping
* The `Local` definitions and lemmas `expander`, `expander_eta`, `expander_inj`, `decoder`,
  `decoder_correct`, `decoder_inj`, `decoder_ineq`, `decoder_None`, `decoder_Some_length`
  keep their names (they are not `private`, so that they stay usable by other files).
  - `l ≫= f` is `l.flatMap f`; `2 <=? x` is `decide (2 ≤ x)`; `Nat.odd x` is `Nat.bodd x`;
    `Z.b2z b` is `b.toInt`; `bool_to_nat` is `Coneris.Lib.Flip.bool_to_nat`.
  - `res ← decoder ls; Some (...)` is `(decoder ls).bind (fun res => some (...))`.
  - `Forall (λ x, x<4) l` is `∀ x ∈ l, x < 4`.
* Section `impl2`: the context `F: flip_spec Σ` is `[F : flip_spec GF]`, and
  `L:!flipG Σ, !inG Σ (frac_authR natR)` is `(L : F.flipG GF) [ElemG GF frac_authF_nat]`
  (as in `Coneris.Lib.HocapFlip`, `L` is explicit).
* `new_counter2`, `allocate_tape2`, `incr_counter_tape2`, `read_counter2`: same names,
  transcribed with the `cpl` notation (`conversion.bool_to_int` is
  `Coneris.Lib.Conversion.bool_to_int`; `FAA "l" "x"` is `faa(l, x)`).
* `counterG2` (Rocq: `Class counterG2 Σ := CounterG2 { counterG2_frac_authR :: inG Σ
  (frac_authR natR); counterG2_flipG: flipG Σ }`) is the Lean `class counterG2 GF'` (over
  `[F : flip_spec GF]`). In `random_counter2` its field `counterG2_frac_authR` is a local
  instance.
* `own γ (●F z)` / `own γ (◯F{f} z)` are `own_auth_nat γ z` / `own_frag_nat γ f z` of
  `RandomCounter`.
* `counter_inv_pred2`, `is_counter2`, `new_counter_spec2`, `allocate_tape_spec2`,
  `incr_counter_tape_spec_some2`, `counter_tapes_presample2`, `read_counter_spec2`,
  `counterG2_to_flipG`: same names.
  - In `counter_tapes_presample2` the hypothesis `∀ x, 0 <= ε2 x` is dropped (`ℝ≥0∞`), and so
    are the nonnegativity side conditions of the two `flip_tapes_presample`s.
* `random_counter2` (Rocq: `Program Definition`) is a definition (not an instance) over
  `[F : flip_spec GF]`. Its `Next Obligation`s are the helper theorems
  `random_counter2_counter_tapes_exclusive`, `random_counter2_counter_tapes_valid`, and the
  shared `frac_auth_nat_*` lemmas of `RandomCounter`.

## Omitted
* The commented-out Rocq code (`is_flip`, `flip_inv_create_spec`, `fupd_mask_subseteq`,
  `counterG2_tapes`, `tape_name`, `counter_tapes_auth` and the commented-out
  `Next Obligation`).

## Added
* `expander_cons`, `expander_app_single` (unfolding lemmas for `expander`), `sum_fin4_halves`
  (the `SeriesC_finite_foldr ... lra` step), `counter_inv_pred2_timeless`,
  `is_counter2_persistent`.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.dupNamespace false
set_option linter.iris.dupNamespace false

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang
open Coneris Coneris.Lib.Conversion Coneris.Lib.Flip Coneris.Lib.HocapFlip
open Coneris.Examples.RandomCounter.RandomCounter

namespace Coneris.Examples.RandomCounter.Impl2

/-! ## Expander and decoder -/

/-- Rocq: `expander`. -/
def expander (l : List ℕ) : List Bool :=
  l.flatMap (fun x => [decide (2 ≤ x), Nat.bodd x])

/-- Helper: `expander` on a cons. -/
theorem expander_cons (x : ℕ) (l : List ℕ) :
    expander (x :: l) = decide (2 ≤ x) :: Nat.bodd x :: expander l := by
  simp [expander]

/-- Helper: `expander` on a snoc. -/
theorem expander_app_single (l : List ℕ) (x : ℕ) :
    expander (l ++ [x]) = expander l ++ [decide (2 ≤ x)] ++ [Nat.bodd x] := by
  simp [expander, List.flatMap_append]

/-- Rocq: `expander_eta`. -/
theorem expander_eta (x : ℕ) (h : x < 4) :
    (x : ℤ) = ((2 : ℕ) : ℤ) * (decide (2 ≤ x)).toInt + (Nat.bodd x).toInt := by
  rcases x with _ | _ | _ | _ | x <;> first | decide | omega

/-- Rocq: `expander_inj`. -/
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
      rw [expander_cons, expander_cons] at H
      simp only [List.cons.injEq] at H
      obtain ⟨Ha, Hb, Hc⟩ := H
      have hx := H1 x List.mem_cons_self
      have hy := H2 y List.mem_cons_self
      congr 1
      · have ex := expander_eta x hx
        have ey := expander_eta y hy
        rw [Ha, Hb] at ex
        omega
      · exact IH ys (fun z hz => H1 z (List.mem_cons_of_mem _ hz))
          (fun z hz => H2 z (List.mem_cons_of_mem _ hz)) Hc

/-- Rocq: `decoder`. -/
def decoder : List Bool → Option (List ℕ)
  | [] => some []
  | b :: b' :: ls =>
      (decoder ls).bind (fun res => some (((bool_to_nat b) * 2 + (bool_to_nat b')) :: res))
  | _ => none

/-- Rocq: `decoder_correct`. -/
theorem decoder_correct : ∀ (bs : List Bool) (ns : List ℕ), decoder bs = some ns →
    expander ns = bs
  | [], ns, H => by
    simp only [decoder, Option.some.injEq] at H
    subst H
    rfl
  | [_], _, H => by simp [decoder] at H
  | b :: b' :: ls, ns, H => by
    simp only [decoder, Option.bind_eq_some_iff, Option.some.injEq] at H
    obtain ⟨res, Hres, rfl⟩ := H
    rw [expander_cons, decoder_correct ls res Hres]
    cases b <;> cases b' <;> rfl

/-- Rocq: `decoder_inj`. -/
theorem decoder_inj (x y : List Bool) (z : List ℕ) (H1 : decoder x = some z)
    (H2 : decoder y = some z) : x = y := by
  rw [← decoder_correct x z H1, ← decoder_correct y z H2]

/-- Rocq: `decoder_ineq`. -/
theorem decoder_ineq : ∀ (bs : List Bool) (xs : List ℕ), decoder bs = some xs →
    ∀ x ∈ xs, x < 4
  | [], xs, H => by
    simp only [decoder, Option.some.injEq] at H
    subst H
    simp
  | [_], _, H => by simp [decoder] at H
  | b :: b' :: ls, xs, H => by
    simp only [decoder, Option.bind_eq_some_iff, Option.some.injEq] at H
    obtain ⟨res, Hres, rfl⟩ := H
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · cases b <;> cases b' <;> decide
    · exact decoder_ineq ls res Hres x hx

/-- Helper: `decoder_None` by recursion on `bs`. -/
theorem decoder_None_aux : ∀ bs : List Bool, decoder bs = none → ¬ ∃ num, bs.length = 2 * num
  | [], H, _ => by simp [decoder] at H
  | [_], _, ⟨num, h⟩ => by simp at h; omega
  | _ :: _ :: ls, H, ⟨num, h⟩ => by
    simp only [decoder, Option.bind_eq_none_iff, reduceCtorEq, imp_false] at H
    have H'' : decoder ls = none := by
      cases h' : decoder ls with
      | none => rfl
      | some r => exact (H r h').elim
    exact decoder_None_aux ls H'' ⟨num - 1, by simp only [List.length_cons] at h; omega⟩

/-- Rocq: `decoder_None`. -/
theorem decoder_None (p : ℕ) (bs : List Bool) (_Hlen : bs.length = p)
    (H' : decoder bs = none) : ¬ ∃ num, bs.length = 2 * num :=
  decoder_None_aux bs H'

/-- Rocq: `decoder_Some_length`. -/
theorem decoder_Some_length : ∀ (bs : List Bool) (xs : List ℕ), decoder bs = some xs →
    bs.length = 2 * xs.length
  | [], xs, H => by
    simp only [decoder, Option.some.injEq] at H
    subst H
    rfl
  | [_], _, H => by simp [decoder] at H
  | b :: b' :: ls, xs, H => by
    simp only [decoder, Option.bind_eq_some_iff, Option.some.injEq] at H
    obtain ⟨res, Hres, rfl⟩ := H
    simp only [List.length_cons, decoder_Some_length ls res Hres]
    omega

/-! ## The implementation -/

section impl2

variable {GF : BundledGFunctors} [conerisGS GF] [F : flip_spec GF]

/-- Rocq: `new_counter2`. -/
def new_counter2 : val := cpl_val(λ _, ref(#0))

/-- Rocq: `allocate_tape2`. -/
def allocate_tape2 : val := F.flip_allocate_tape

/-- Rocq: `incr_counter_tape2`. -/
def incr_counter_tape2 : val := cpl_val(
  λ l α,
    let n := &bool_to_int (v(&F.flip_tape) α) in
    let n' := &bool_to_int (v(&F.flip_tape) α) in
    let x := #2 * n + n' in
    (faa(l, x), x))

/-- Rocq: `read_counter2`. -/
def read_counter2 : val := cpl_val(λ l, !l)

/-- Rocq: `counterG2`. -/
class counterG2 (GF' : BundledGFunctors) where
  counterG2_frac_authR : ElemG GF' frac_authF_nat
  counterG2_flipG : F.flipG GF'

attribute [instance_reducible] counterG2.counterG2_frac_authR

variable (L : F.flipG GF) [ElemG GF frac_authF_nat]

/-- Rocq: `counter_inv_pred2`. -/
def counter_inv_pred2 (c : val) (γ : GName) : IProp GF :=
  iprop(∃ (l : Loc) (z : ℕ), ⌜c = LitV (LitLoc l)⌝ ∗ l ↦ LitV (LitInt (z : ℤ)) ∗
    own_auth_nat γ z)

instance counter_inv_pred2_timeless (c : val) (γ : GName) :
    Timeless (counter_inv_pred2 c γ) := by
  unfold counter_inv_pred2; infer_instance

/-- Rocq: `is_counter2`. -/
def is_counter2 (N : Namespace) (c : val) (γ1 : GName) : IProp GF :=
  inv N (counter_inv_pred2 c γ1)

instance is_counter2_persistent (N : Namespace) (c : val) (γ1 : GName) :
    Persistent (is_counter2 N c γ1) := by
  unfold is_counter2; infer_instance

/-- Rocq: `new_counter_spec2`. -/
theorem new_counter_spec2 (E : CoPset) (N : Namespace) :
    {{ True }} cpl(v(&new_counter2) #()) @ E
    {{ c, RET c; ∃ γ1, is_counter2 N c γ1 ∗ own_frag_nat γ1 1 0 }} := by
  unfold is_counter2
  iintro %Φ - HΦ
  unfold new_counter2
  wp_pures
  wp_alloc l as Hl
  imod frac_auth_nat_alloc with ⟨%γ1, H5, H6⟩
  imod inv_alloc N E (counter_inv_pred2 (LitV (LitLoc l)) γ1) $$ [Hl H5] with #Hinv'
  · inext
    unfold counter_inv_pred2
    iexists l, 0
    iframe
    ipureintro
    rfl
  iapply HΦ
  iexists γ1
  iframe Hinv' H6

/-- Rocq: `allocate_tape_spec2`. -/
theorem allocate_tape_spec2 (N : Namespace) (E : CoPset) (c : val) (γ1 : GName)
    (_Hsubset : ↑N ⊆ E) :
    {{ is_counter2 N c γ1 }} cpl(v(&allocate_tape2) #()) @ E
    {{ v, RET v; F.flip_tapes L v (expander []) ∗ ⌜∀ x ∈ ([] : List ℕ), x < 4⌝ }} := by
  simp only [show expander ([] : List ℕ) = [] from rfl]
  iintro %Φ #Hinv HΦ
  unfold allocate_tape2
  wp_apply F.flip_allocate_tape_spec L E $$ [] with %v Hv
  · itrivial
  iapply HΦ
  isplitl [Hv]
  · iexact Hv
  · ipureintro
    simp

/-- Rocq: `incr_counter_tape_spec_some2`. -/
theorem incr_counter_tape_spec_some2 (N : Namespace) (E : CoPset) (c : val) (γ1 : GName)
    (Q : ℕ → IProp GF) (α : val) (n : ℕ) (ns : List ℕ) (Hsubset : ↑N ⊆ E) :
    {{ is_counter2 N c γ1 ∗
        (F.flip_tapes L α (expander (n :: ns)) ∗ ⌜∀ x ∈ n :: ns, x < 4⌝) ∗
        (∀ z : ℕ, own_auth_nat γ1 z ={E \ ↑N}=∗ own_auth_nat γ1 (z + n) ∗ Q z) }}
      cpl(v(&incr_counter_tape2) v(&c) v(&α)) @ E
    {{ (z : ℕ), RET cpl_val((#z, #n));
        (F.flip_tapes L α (expander ns) ∗ ⌜∀ x ∈ ns, x < 4⌝) ∗ Q z }} := by
  unfold is_counter2 counter_inv_pred2
  rw [expander_cons]
  iintro %Φ ⟨#Hinv, ⟨Hα, %Hforall⟩, Hvs⟩ HΦ
  unfold incr_counter_tape2
  wp_pures
  wp_apply F.flip_tape_spec_some L E α _ _ $$ Hα with Hα
  wp_apply wp_bool_to_int _ E $$ [] with -
  · itrivial
  wp_pures
  wp_apply F.flip_tape_spec_some L E α _ _ $$ Hα with Hα
  wp_apply wp_bool_to_int _ E $$ [] with -
  · itrivial
  wp_pures
  wp_bind (FAA _ _)
  iinv Hinv with >⟨%l, %z, %Hc, Hl, Hauth⟩ Hclose
  subst Hc
  wp_faa
  imod Hvs $$ Hauth with ⟨H6, HQ⟩
  have hn := (expander_eta n (Hforall n List.mem_cons_self)).symm
  simp only [Nat.cast_ofNat] at hn
  rw [hn]
  imod Hclose $$ [Hl H6]
  · inext
    iexists l, z + n
    iframe H6
    isplitr
    · ipureintro; rfl
    rw [Nat.cast_add]
    iexact Hl
  imodintro
  wp_pures
  iapply HΦ
  iframe
  ipureintro
  exact fun x hx => Hforall x (List.mem_cons_of_mem _ hx)

/-- Helper (Rocq: `rewrite SeriesC_finite_foldr/=. lra.`). -/
theorem sum_fin4_halves (ε : ℝ≥0∞) (ε2 : Fin 4 → ℝ≥0∞) (Hineq : ∑' n, 1 / 4 * ε2 n ≤ ε) :
    ((1 / 2 * (ε2 2 + ε2 3)) + (1 / 2 * (ε2 0 + ε2 1))) / 2 ≤ ε := by
  rw [tsum_fintype, Fin.sum_univ_four] at Hineq
  refine le_trans (le_of_eq ?_) Hineq
  have h4 : (1 / 4 : ℝ≥0∞) = 1 / 2 * (1 / 2) := by
    simp only [one_div]
    rw [← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    norm_num
  rw [h4, ENNReal.div_eq_inv_mul, ← one_div]
  ring

/-- Rocq: `counter_tapes_presample2`. -/
theorem counter_tapes_presample2 (N : Namespace) (E : CoPset) (γ1 : GName) (c α : val)
    (ns : List ℕ) (ε : ℝ≥0∞) (ε2 : Fin 4 → ℝ≥0∞) (_Hsubset : ↑N ⊆ E)
    (Hineq : ∑' n, 1 / 4 * ε2 n ≤ ε) :
    ⊢ is_counter2 N c γ1 -∗ (F.flip_tapes L α (expander ns) ∗ ⌜∀ x ∈ ns, x < 4⌝) -∗ ↯ ε -∗
      state_update E E iprop(∃ n : Fin 4, ↯ (ε2 n) ∗
        (F.flip_tapes L α (expander (ns ++ [(n : ℕ)])) ∗
          ⌜∀ x ∈ ns ++ [(n : ℕ)], x < 4⌝)) := by
  iintro #Hinv' ⟨Hfrag, %Hforall⟩ Herr
  imod F.flip_tapes_presample L E α (expander ns) ε
    (fun b => 1 / 2 * if b then ε2 2 + ε2 3 else ε2 0 + ε2 1)
    (sum_fin4_halves ε ε2 Hineq) $$ Hfrag Herr with ⟨%b, Herr, Hfrag⟩
  have hforall : ∀ k : Fin 4, ∀ x ∈ ns ++ [(k : ℕ)], x < 4 := by
    intro k x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact Hforall x hx
    · rw [List.mem_singleton.1 hx]; exact k.isLt
  cases b
  · imod F.flip_tapes_presample L E α _ _ (fun b => if b then ε2 1 else ε2 0)
      (by simp only [Bool.false_eq_true, ↓reduceIte, ENNReal.div_eq_inv_mul, one_div,
        add_comm (ε2 1)]; exact le_refl _) $$ Hfrag Herr with ⟨%b, Herr, Hfrag⟩
    cases b
    · imodintro
      simp only [Bool.false_eq_true, ↓reduceIte]
      iexists 0
      iframe Herr
      rw [show expander (ns ++ [((0 : Fin 4) : ℕ)]) = expander ns ++ [false] ++ [false] from by
        rw [expander_app_single]; rfl]
      iframe Hfrag
      ipureintro
      exact hforall 0
    · imodintro
      simp only [↓reduceIte]
      iexists 1
      iframe Herr
      rw [show expander (ns ++ [((1 : Fin 4) : ℕ)]) = expander ns ++ [false] ++ [true] from by
        rw [expander_app_single]; rfl]
      iframe Hfrag
      ipureintro
      exact hforall 1
  · imod F.flip_tapes_presample L E α _ _ (fun b => if b then ε2 3 else ε2 2)
      (by simp only [↓reduceIte, ENNReal.div_eq_inv_mul, one_div,
        add_comm (ε2 3)]; exact le_refl _) $$ Hfrag Herr with ⟨%b, Herr, Hfrag⟩
    cases b
    · imodintro
      simp only [Bool.false_eq_true, ↓reduceIte]
      iexists 2
      iframe Herr
      rw [show expander (ns ++ [((2 : Fin 4) : ℕ)]) = expander ns ++ [true] ++ [false] from by
        rw [expander_app_single]; rfl]
      iframe Hfrag
      ipureintro
      exact hforall 2
    · imodintro
      simp only [↓reduceIte]
      iexists 3
      iframe Herr
      rw [show expander (ns ++ [((3 : Fin 4) : ℕ)]) = expander ns ++ [true] ++ [true] from by
        rw [expander_app_single]; rfl]
      iframe Hfrag
      ipureintro
      exact hforall 3

/-- Rocq: `read_counter_spec2`. -/
theorem read_counter_spec2 (N : Namespace) (E : CoPset) (c : val) (γ1 : GName)
    (Q : ℕ → IProp GF) (Hsubset : ↑N ⊆ E) :
    {{ is_counter2 N c γ1 ∗
        (∀ z : ℕ, own_auth_nat γ1 z ={E \ ↑N}=∗ own_auth_nat γ1 z ∗ Q z) }}
      cpl(v(&read_counter2) v(&c)) @ E
    {{ (n' : ℕ), RET LitV (LitInt (n' : ℤ)); Q n' }} := by
  unfold is_counter2 counter_inv_pred2
  iintro %Φ ⟨#Hinv, Hvs⟩ HΦ
  unfold read_counter2
  wp_pure
  iinv Hinv with >⟨%l, %z, %Hc, Hloc, Hcont⟩ Hclose
  subst Hc
  wp_load
  imod Hvs $$ Hcont with ⟨Hcont, HQ⟩
  imod Hclose $$ [Hloc Hcont]
  · inext
    iexists l, z
    iframe
    ipureintro; rfl
  imodintro
  iapply HΦ $$ HQ

end impl2

/-- Rocq: `counterG2_to_flipG` (a `Program Definition`). -/
def counterG2_to_flipG {GF : BundledGFunctors} [conerisGS GF] [F : flip_spec GF]
    [H : counterG2 (F := F) GF] : F.flipG GF :=
  H.counterG2_flipG

/-! ## `random_counter2` and its obligations -/

section obligations

variable {GF : BundledGFunctors} [conerisGS GF] [F : flip_spec GF]

attribute [local instance] counterG2.counterG2_frac_authR

/-- Rocq: first `Next Obligation` of `random_counter2` (`counter_tapes_exclusive`). -/
theorem random_counter2_counter_tapes_exclusive (K : counterG2 (F := F) GF) (α : val)
    (ns ns' : List ℕ) :
    ⊢ iprop(F.flip_tapes (counterG2_to_flipG (H := K)) α (expander ns) ∗ ⌜∀ x ∈ ns, x < 4⌝) -∗
      iprop(F.flip_tapes (counterG2_to_flipG (H := K)) α (expander ns') ∗
        ⌜∀ x ∈ ns', x < 4⌝) -∗ False := by
  iintro ⟨H1, -⟩ ⟨H2, -⟩
  iapply F.flip_tapes_exclusive $$ H1 H2

/-- Rocq: second `Next Obligation` of `random_counter2` (`counter_tapes_valid`). -/
theorem random_counter2_counter_tapes_valid (K : counterG2 (F := F) GF) (α : val)
    (ns : List ℕ) :
    ⊢ iprop(F.flip_tapes (counterG2_to_flipG (H := K)) α (expander ns) ∗ ⌜∀ x ∈ ns, x < 4⌝) -∗
      ⌜∀ n ∈ ns, n ≤ 3⌝ := by
  iintro ⟨-, %H⟩
  ipureintro
  exact fun n hn => Nat.le_of_lt_succ (H n hn)

/-- Rocq: `random_counter2` (a `Program Definition`). -/
@[instance_reducible]
def random_counter2 : random_counter GF where
  new_counter := new_counter2
  allocate_tape := allocate_tape2
  incr_counter_tape := incr_counter_tape2
  read_counter := read_counter2
  counterG := counterG2 (F := F)
  counter_name := GName
  is_counter _ N c γ1 := is_counter2 N c γ1
  counter_tapes K α ns :=
    iprop(F.flip_tapes (counterG2_to_flipG (H := K)) α (expander ns) ∗ ⌜∀ x ∈ ns, x < 4⌝)
  counter_content_auth _ γ z := own_auth_nat γ z
  counter_content_frag _ γ f z := own_frag_nat γ f z
  is_counter_persistent _ N c γ1 := is_counter2_persistent N c γ1
  counter_tapes_timeless _ _ _ := inferInstance
  counter_content_auth_timeless _ _ _ := inferInstance
  counter_content_frag_timeless _ _ _ _ := inferInstance
  counter_tapes_exclusive K := random_counter2_counter_tapes_exclusive K
  counter_tapes_valid K := random_counter2_counter_tapes_valid K
  counter_tapes_presample K := counter_tapes_presample2 (counterG2_to_flipG (H := K))
  counter_content_auth_exclusive _ := frac_auth_nat_auth_exclusive
  counter_content_less_than _ := frac_auth_nat_less_than
  counter_content_frag_combine _ := frac_auth_nat_frag_combine
  counter_content_agree _ := frac_auth_nat_agree
  counter_content_update _ := frac_auth_nat_update
  new_counter_spec _ := new_counter_spec2
  allocate_tape_spec K := allocate_tape_spec2 (counterG2_to_flipG (H := K))
  incr_counter_tape_spec_some K := incr_counter_tape_spec_some2 (counterG2_to_flipG (H := K))
  read_counter_spec _ := read_counter_spec2

end obligations

end Coneris.Examples.RandomCounter.Impl2
