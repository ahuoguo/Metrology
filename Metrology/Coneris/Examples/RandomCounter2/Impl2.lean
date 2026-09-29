module

public import Metrology.Coneris.Examples.RandomCounter2.RandomCounter
public import Metrology.Coneris.Examples.RandomCounter2.Impl1
public import Metrology.Coneris.Lib.HocapFlip
public import Metrology.Coneris.Lib.Conversion

/-!
# Random counter, implementation 2

Ported from clutch/theories/coneris/examples/random_counter2/impl2.v

The counter is incremented by `2 * b1 + b2` for two flips `b1`, `b2` of a freshly allocated hocap
flip tape (`Coneris.Lib.HocapFlip`). A counter tape holding `n` is a flip tape holding the two
bits of `n` (`expander`).

## Rocq → Lean mapping
* `Local Definition expander`, `Local Lemma expander_eta`, `expander_inj`,
  `Local Fixpoint decoder`, `decoder_correct`, `decoder_inj`, `decoder_ineq`, `decoder_None`,
  `decoder_Some_length`: same names, as ordinary (non-`private`) declarations of this
  namespace.
  - `l ≫= f` is `l.flatMap f`; `2 <=? x` is `Nat.ble 2 x`; `Nat.odd x` is `Nat.bodd x`;
    `Z.b2z` is `Bool.toInt`; `res ← decoder ls; Some ..` is `(decoder ls).bind ..`;
    `bool_to_nat` is `Coneris.Lib.Flip.bool_to_nat`.
  - `Forall (λ x, x < 4) l` is `∀ x ∈ l, x < 4` (also in the specs below).
  - The Rocq proofs by `lt_wf` induction / `naive_solver` are structural recursions.
* Section `impl2`: the context `F: flip_spec Σ`, `L:!flipG Σ`, `!inG Σ (frac_authR natR)` is
  `[F : flip_spec GF] (L : F.flipG GF) [Hfa : ElemG GF frac_authTF]` (`Impl1.frac_authTF`).
* `new_counter2`, `incr_counter2`, `read_counter2`, `counterG2`, `counter_inv_pred2`,
  `is_counter2`, `new_counter_spec2`, `incr_counter_spec2`, `counter_tapes_presample2`,
  `read_counter_spec2`, `counterG2_to_flipG`: same names. The programs are transcribed with
  the `cpl` notation; `conversion.bool_to_int` is `Coneris.Lib.Conversion.bool_to_int`.
* Errors are `ℝ≥0∞`: `∀ x, 0 <= ε2 x` is dropped; the first presampling function
  `λ b, 1/2 * if b then (ε2 2 + ε2 3) else (ε2 0 + ε2 1)` is kept literally.
* `counterG2_to_flipG` takes the `counterG2` as an instance argument `[H : counterG2 GF]`
  (Rocq: `!counterG2 Σ`); inside `random_counter2` the flip ghost-state argument is written
  directly as the projection `(L : counterG2 GF).counterG2_flipG` (definitionally the same).
* `random_counter2` (Rocq: `Program Definition`) is a definition (not an instance) over
  `[F : flip_spec GF]`, with `counterG := fun _ => counterG2 GF`; the field
  `incr_counter_spec` is given via `have`/`exact` (elaborating the term directly against the
  field type exceeds the heartbeat limit); its `Next Obligation`s are
  the (identical) obligation theorems of `Impl1` (`random_counter1_counter_content_*`), since
  the ghost state is the same.

## Added
* `is_counter2_persistent` (automatic obligation), `expander_cons` (helper: `expander` of a
  singleton), `presample2_sum` (the `lra` side condition of the first presampling).

## Omitted
* The commented-out Rocq code (`counterG2_tapes`, `is_flip`, `flip_inv_create_spec`,
  `fupd_mask_subseteq` steps, `tape_name`, `counter_tapes_auth`).
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang
open Coneris Coneris.Lib.Conversion Coneris.Lib.Flip Coneris.Lib.HocapFlip
open Coneris.Examples.RandomCounter2.RandomCounter Coneris.Examples.RandomCounter2.Impl1

namespace Coneris.Examples.RandomCounter2.Impl2

/-- Rocq: `expander`. -/
def expander (l : List ℕ) : List Bool :=
  l.flatMap (fun x => [Nat.ble 2 x, Nat.bodd x])

/-- Helper: `expander` of a cons. -/
theorem expander_cons (x : ℕ) (l : List ℕ) :
    expander (x :: l) = Nat.ble 2 x :: Nat.bodd x :: expander l := rfl

/-- Rocq: `expander_eta`. -/
theorem expander_eta (x : ℕ) (h : x < 4) :
    (x : ℤ) = (2 : ℕ) * (Nat.ble 2 x).toInt + (Nat.bodd x).toInt := by
  match x, h with
  | 0, _ | 1, _ | 2, _ | 3, _ => rfl

/-- Rocq: `expander_inj`. -/
theorem expander_inj : ∀ (l1 l2 : List ℕ), (∀ x ∈ l1, x < 4) → (∀ y ∈ l2, y < 4) →
    expander l1 = expander l2 → l1 = l2
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp [expander] at h
  | _ :: _, [], _, _, h => by simp [expander] at h
  | x :: xs, y :: ys, H1, H2, h => by
    rw [expander_cons, expander_cons] at h
    simp only [List.cons.injEq] at h
    obtain ⟨hb, ho, h⟩ := h
    have hx := H1 x List.mem_cons_self
    have hy := H2 y List.mem_cons_self
    congr 1
    · have ex := expander_eta x hx
      have ey := expander_eta y hy
      rw [hb, ho, ← ey] at ex
      exact_mod_cast ex
    · exact expander_inj xs ys (fun a ha => H1 a (List.mem_cons_of_mem _ ha))
        (fun a ha => H2 a (List.mem_cons_of_mem _ ha)) h

/-- Rocq: `decoder`. -/
def decoder : List Bool → Option (List ℕ)
  | [] => some []
  | b :: b' :: ls =>
      (decoder ls).bind (fun res => some ((bool_to_nat b * 2 + bool_to_nat b') :: res))
  | _ => none

/-- Rocq: `decoder_correct`. -/
theorem decoder_correct : ∀ (bs : List Bool) (ns : List ℕ), decoder bs = some ns →
    expander ns = bs
  | [], ns, h => by
    simp only [decoder, Option.some.injEq] at h
    subst h; rfl
  | [_], _, h => by simp [decoder] at h
  | b :: b' :: ls, ns, h => by
    simp only [decoder, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨a, ha, rfl⟩ := h
    rw [expander_cons, decoder_correct ls a ha]
    cases b <;> cases b' <;> rfl

/-- Rocq: `decoder_inj`. -/
theorem decoder_inj (x y : List Bool) (z : List ℕ) (H1 : decoder x = some z)
    (H2 : decoder y = some z) : x = y := by
  rw [← decoder_correct x z H1, ← decoder_correct y z H2]

/-- Rocq: `decoder_ineq`. -/
theorem decoder_ineq : ∀ (bs : List Bool) (xs : List ℕ), decoder bs = some xs →
    ∀ x ∈ xs, x < 4
  | [], xs, h => by
    simp only [decoder, Option.some.injEq] at h
    subst h; simp
  | [_], _, h => by simp [decoder] at h
  | b :: b' :: ls, xs, h => by
    simp only [decoder, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨a, ha, rfl⟩ := h
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · cases b <;> cases b' <;> decide
    · exact decoder_ineq ls a ha x hx

/-- Rocq: `decoder_None`. -/
theorem decoder_None : ∀ (p : ℕ) (bs : List Bool), bs.length = p → decoder bs = none →
    ¬ ∃ num, bs.length = 2 * num
  | _, [], _, h => by simp [decoder] at h
  | _, [_], _, _ => by
    rintro ⟨num, hnum⟩
    simp only [List.length_singleton] at hnum
    omega
  | _, b :: b' :: ls, _, h => by
    simp only [decoder, Option.bind_eq_none_iff, reduceCtorEq, imp_false] at h
    rintro ⟨num, hnum⟩
    have hls : decoder ls = none := by
      cases hd : decoder ls with
      | none => rfl
      | some a => exact absurd hd (h a)
    apply decoder_None ls.length ls rfl hls
    refine ⟨num - 1, ?_⟩
    simp only [List.length_cons] at hnum
    omega

/-- Rocq: `decoder_Some_length`. -/
theorem decoder_Some_length : ∀ (bs : List Bool) (xs : List ℕ), decoder bs = some xs →
    bs.length = 2 * xs.length
  | [], xs, h => by
    simp only [decoder, Option.some.injEq] at h
    subst h; rfl
  | [_], _, h => by simp [decoder] at h
  | b :: b' :: ls, xs, h => by
    simp only [decoder, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨a, ha, rfl⟩ := h
    simp only [List.length_cons, decoder_Some_length ls a ha]
    omega

/-- Helper (Rocq: the `lra` side condition of the first presampling). -/
theorem presample2_sum (ε : ℝ≥0∞) (ε2 : Fin 4 → ℝ≥0∞)
    (Hineq : ∑' n : Fin 4, 1 / 4 * ε2 n ≤ ε) :
    ((1 / 2 * (ε2 2 + ε2 3)) + (1 / 2 * (ε2 0 + ε2 1))) / 2 ≤ ε := by
  rw [tsum_fintype, Fin.sum_univ_four] at Hineq
  refine le_trans (le_of_eq ?_) Hineq
  rw [ENNReal.div_eq_inv_mul, ← mul_add, ← mul_add, ← mul_add, ← mul_add, ← mul_assoc]
  have h : (2 : ℝ≥0∞)⁻¹ * (1 / 2) = 1 / 4 := by
    rw [one_div, ← ENNReal.mul_inv (by norm_num) (by norm_num)]
    norm_num
  rw [h]
  congr 1
  ring

section impl2

variable {GF : BundledGFunctors} [conerisGS GF] [F : flip_spec GF]

/-- Rocq: `new_counter2`. -/
def new_counter2 : val := cpl_val(λ _, ref(#0))

/-- Rocq: `incr_counter2`. -/
def incr_counter2 : val := cpl_val(
  λ l, let α := (v(&F.flip_allocate_tape) #()) in
       let n := &bool_to_int (v(&F.flip_tape) α) in
       let n' := &bool_to_int (v(&F.flip_tape) α) in
       let x := #2 * n + n' in
       (faa(l, x), x))

/-- Rocq: `read_counter2`. -/
def read_counter2 : val := cpl_val(λ l, !l)

/-- Rocq: `counterG2`. -/
class counterG2 (GF : BundledGFunctors) [conerisGS GF] [F : flip_spec GF] : Type where
  counterG2_frac_authR : ElemG GF frac_authTF
  counterG2_flipG : F.flipG GF

variable (L : F.flipG GF) [Hfa : ElemG GF frac_authTF]

/-- Rocq: `counter_inv_pred2`. -/
def counter_inv_pred2 (c : val) (γ : GName) : IProp GF :=
  iprop(∃ (l : Loc) (z : ℕ), ⌜c = LitV (LitLoc l)⌝ ∗ l ↦ LitV (LitInt z) ∗
    iOwn (F := frac_authTF) γ (●F z))

/-- Rocq: `is_counter2`. -/
def is_counter2 (N : Namespace) (c : val) (γ1 : GName) : IProp GF :=
  inv N (counter_inv_pred2 c γ1)

instance is_counter2_persistent (N : Namespace) (c : val) (γ1 : GName) :
    Persistent (is_counter2 (GF := GF) N c γ1) := by
  unfold is_counter2; infer_instance

/-- Rocq: `new_counter_spec2`. -/
theorem new_counter_spec2 (E : CoPset) (N : Namespace) :
    {{ True }} cpl(v(&new_counter2) #()) @ E
    {{ (c : val), RET c; ∃ γ1, is_counter2 (GF := GF) N c γ1 ∗
        iOwn (F := frac_authTF) γ1 (◯F (0 : ℕ)) }} := by
  unfold new_counter2
  iintro %Φ - HΦ
  wp_pures
  wp_alloc l as Hl
  imod iOwn_alloc (F := frac_authTF) ((●F (0 : ℕ)) • (◯F (0 : ℕ))) (FracAuth.valid trivial)
    with ⟨%γ1, H5, H6⟩
  imod inv_alloc N E (counter_inv_pred2 (LitV (LitLoc l)) γ1) $$ [Hl H5] with #Hinv'
  · inext
    unfold counter_inv_pred2
    iexists l, 0
    iframe Hl H5
    ipureintro
    rfl
  iapply HΦ
  iexists γ1
  unfold is_counter2
  iframe Hinv' H6

/-- Rocq: `incr_counter_spec2`. -/
theorem incr_counter_spec2 (N : Namespace) (E : CoPset) (c : val) (γ1 : GName)
    (Q : ℕ → ℕ → IProp GF) (Hsubset : ↑N ⊆ E) :
    {{ is_counter2 N c γ1 ∗
        (∀ α, (F.flip_tapes L α (expander []) ∗ ⌜∀ x ∈ ([] : List ℕ), x < 4⌝) -∗
          state_update E E iprop(∃ n,
            (F.flip_tapes L α (expander [n]) ∗ ⌜∀ x ∈ [n], x < 4⌝) ∗
            (∀ z : ℕ, iOwn (F := frac_authTF) γ1 (●F z) ={E \ ↑N}=∗
              iOwn (F := frac_authTF) γ1 (●F (z + n)) ∗ Q z n))) }}
      cpl(v(&incr_counter2) v(&c)) @ E
    {{ (z n : ℕ), RET cpl_val((#z, #n)); Q z n }} := by
  iintro %Φ ⟨#Hinv, Hvs⟩ HΦ
  unfold incr_counter2
  wp_pures
  wp_apply F.flip_allocate_tape_spec L E $$ [] with %α Htape
  · itrivial
  wp_pures
  imod Hvs $$ [Htape] with ⟨%n, ⟨Htape, %H⟩, Hvs⟩
  · rw [show expander [] = [] from rfl]
    iframe Htape
    ipureintro
    simp
  rw [expander_cons]
  wp_apply F.flip_tape_spec_some L E α _ _ $$ Htape with Hα
  wp_apply wp_bool_to_int $$ [] with -
  · itrivial
  wp_pures
  wp_apply F.flip_tape_spec_some L E α _ _ $$ Hα with Hα
  wp_apply wp_bool_to_int $$ [] with -
  · itrivial
  wp_pures
  wp_bind (FAA _ _)
  unfold is_counter2 counter_inv_pred2
  iinv Hinv with ⟨%l, %z, >%Hc, >H5, >H6⟩ Hclose
  subst Hc
  wp_faa
  imod Hvs $$ H6 with ⟨H6, HQ⟩
  have Hn : (2 : ℤ) * (Nat.ble 2 n).toInt + (Nat.bodd n).toInt = (n : ℤ) := by
    have := expander_eta n (H n List.mem_cons_self)
    push_cast at this
    exact this.symm
  rw [Hn]
  imod Hclose $$ [H5 H6] with -
  · inext
    iexists l, z + n
    rw [Nat.cast_add]
    iframe H5 H6
    ipureintro
    rfl
  imodintro
  wp_pures
  iapply HΦ $$ HQ

/-- Rocq: `counter_tapes_presample2`. -/
theorem counter_tapes_presample2 (N : Namespace) (E : CoPset) (γ1 : GName) (c : val) (α : val)
    (ε : ℝ≥0∞) (ε2 : Fin 4 → ℝ≥0∞) (_Hsubset : ↑N ⊆ E)
    (Hineq : ∑' n : Fin 4, 1 / 4 * ε2 n ≤ ε) :
    ⊢ is_counter2 N c γ1 -∗
      (F.flip_tapes L α (expander []) ∗ ⌜∀ x ∈ ([] : List ℕ), x < 4⌝) -∗ ↯ ε -∗
      state_update E E iprop(∃ n : Fin 4, ↯ (ε2 n) ∗
        (F.flip_tapes L α (expander [(n : ℕ)]) ∗ ⌜∀ x ∈ [(n : ℕ)], x < 4⌝)) := by
  iintro #Hinv' ⟨Hfrag, %Hforall⟩ Herr
  imod F.flip_tapes_presample L E α _ ε
    (fun b => 1 / 2 * if b then (ε2 2 + ε2 3) else (ε2 0 + ε2 1))
    (presample2_sum ε ε2 Hineq) $$ Hfrag Herr with ⟨%b, Herr, Hfrag⟩
  cases b
  · imod F.flip_tapes_presample L E α _ _ (fun b => if b then ε2 1 else ε2 0) ?_
      $$ Hfrag Herr with ⟨%b, Herr, Hfrag⟩
    · simp only [Bool.false_eq_true, ↓reduceIte, ↓reduceIte]
      rw [ENNReal.div_eq_inv_mul, one_div, add_comm]
    cases b
    · imodintro
      iexists 0
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [show expander [((0 : Fin 4) : ℕ)] = expander [] ++ [false] ++ [false] from rfl]
      iframe Herr
      iframe Hfrag
      ipureintro
      intro x hx; simp at hx; omega
    · imodintro
      iexists 1
      simp only [↓reduceIte]
      rw [show expander [((1 : Fin 4) : ℕ)] = expander [] ++ [false] ++ [true] from rfl]
      iframe Herr
      iframe Hfrag
      ipureintro
      intro x hx; simp at hx; omega
  · imod F.flip_tapes_presample L E α _ _ (fun b => if b then ε2 3 else ε2 2) ?_
      $$ Hfrag Herr with ⟨%b, Herr, Hfrag⟩
    · simp only [Bool.false_eq_true, ↓reduceIte, ↓reduceIte]
      rw [ENNReal.div_eq_inv_mul, one_div, add_comm]
    cases b
    · imodintro
      iexists 2
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [show expander [((2 : Fin 4) : ℕ)] = expander [] ++ [true] ++ [false] from rfl]
      iframe Herr
      iframe Hfrag
      ipureintro
      intro x hx; simp at hx; omega
    · imodintro
      iexists 3
      simp only [↓reduceIte]
      rw [show expander [((3 : Fin 4) : ℕ)] = expander [] ++ [true] ++ [true] from rfl]
      iframe Herr
      iframe Hfrag
      ipureintro
      intro x hx; simp at hx; omega

/-- Rocq: `read_counter_spec2`. -/
theorem read_counter_spec2 (N : Namespace) (E : CoPset) (c : val) (γ1 : GName)
    (Q : ℕ → IProp GF) (Hsubset : ↑N ⊆ E) :
    {{ is_counter2 N c γ1 ∗
        (∀ z : ℕ, iOwn (F := frac_authTF) γ1 (●F z) ={E \ ↑N}=∗
          iOwn (F := frac_authTF) γ1 (●F z) ∗ Q z) }}
      cpl(v(&read_counter2) v(&c)) @ E
    {{ (n' : ℕ), RET LitV (LitInt n'); Q n' }} := by
  iintro %Φ ⟨#Hinv, Hvs⟩ HΦ
  unfold read_counter2
  wp_pure
  unfold is_counter2 counter_inv_pred2
  iinv Hinv with ⟨%l, %z, >%Hc, >Hloc, >Hcont⟩ Hclose
  subst Hc
  wp_load
  imod Hvs $$ Hcont with ⟨Hcont, HQ⟩
  imod Hclose $$ [Hloc Hcont] with -
  · inext
    iexists l, z
    iframe Hloc Hcont
    ipureintro
    rfl
  imodintro
  iapply HΦ $$ HQ

end impl2

/-- Rocq: `counterG2_to_flipG` (a `Program Definition`). -/
def counterG2_to_flipG {GF : BundledGFunctors} [conerisGS GF] [F : flip_spec GF]
    [H : counterG2 GF] : F.flipG GF :=
  H.counterG2_flipG

/-- Rocq: `random_counter2` (a `Program Definition`). -/
@[instance_reducible]
def random_counter2 {GF : BundledGFunctors} [conerisGS GF] [F : flip_spec GF] :
    random_counter GF where
  new_counter := new_counter2
  incr_counter := incr_counter2
  read_counter := read_counter2
  counterG := fun _ => counterG2 GF
  counter_name := GName
  is_counter L N c γ1 := is_counter2 (Hfa := (L : counterG2 GF).counterG2_frac_authR) N c γ1
  counter_tapes L α n :=
    iprop(F.flip_tapes ((L : counterG2 GF).counterG2_flipG) α
        (expander (match n with | some x => [x] | none => [])) ∗
      ⌜∀ x ∈ (match n with | some x => [x] | none => []), x < 4⌝)
  counter_content_auth L γ z :=
    iOwn (E := (L : counterG2 GF).counterG2_frac_authR) (F := frac_authTF) γ (●F z)
  counter_content_frag L γ f z :=
    iOwn (E := (L : counterG2 GF).counterG2_frac_authR) (F := frac_authTF) γ (◯F{f} z)
  is_counter_persistent L N c γ1 :=
    is_counter2_persistent (Hfa := (L : counterG2 GF).counterG2_frac_authR) N c γ1
  counter_tapes_timeless L α n := by infer_instance
  counter_content_auth_timeless L γ z :=
    letI := (L : counterG2 GF).counterG2_frac_authR; iOwn_timeless
  counter_content_frag_timeless L γ f z :=
    letI := (L : counterG2 GF).counterG2_frac_authR; iOwn_timeless
  counter_tapes_presample L :=
    counter_tapes_presample2 (Hfa := (L : counterG2 GF).counterG2_frac_authR)
      ((L : counterG2 GF).counterG2_flipG)
  counter_content_auth_exclusive L :=
    random_counter1_counter_content_auth_exclusive
      (Hfa := (L : counterG2 GF).counterG2_frac_authR)
  counter_content_less_than L :=
    random_counter1_counter_content_less_than (Hfa := (L : counterG2 GF).counterG2_frac_authR)
  counter_content_frag_combine L :=
    random_counter1_counter_content_frag_combine
      (Hfa := (L : counterG2 GF).counterG2_frac_authR)
  counter_content_agree L :=
    random_counter1_counter_content_agree (Hfa := (L : counterG2 GF).counterG2_frac_authR)
  counter_content_update L :=
    random_counter1_counter_content_update (Hfa := (L : counterG2 GF).counterG2_frac_authR)
  new_counter_spec L :=
    new_counter_spec2 (Hfa := (L : counterG2 GF).counterG2_frac_authR)
  -- (`have`/`exact`: elaborating the term directly against the field type times out)
  incr_counter_spec L N E c γ1 Q h := by
    have := incr_counter_spec2 (Hfa := (L : counterG2 GF).counterG2_frac_authR)
      ((L : counterG2 GF).counterG2_flipG) N E c γ1 Q h
    exact this
  read_counter_spec L :=
    read_counter_spec2 (Hfa := (L : counterG2 GF).counterG2_frac_authR)

end Coneris.Examples.RandomCounter2.Impl2
