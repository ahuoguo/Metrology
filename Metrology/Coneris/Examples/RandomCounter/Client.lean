module

public import Metrology.Coneris.Examples.RandomCounter.RandomCounter
public import Metrology.Coneris.Lib.Par
public import Metrology.Coneris.Lib.Flip
public import Iris.Algebra.Lib.ExclAuth
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# A concurrent client of the random counter

Ported from clutch/theories/coneris/examples/random_counter/client.v

Two threads each allocate a tape and increment a shared random counter; the final value is
positive with error `1/16`.

## Rocq → Lean mapping
* `T` (constructors `S0`, `S1`), `sampled`, `one_positive`, `TO`: same names.
  - `one_positive n1 n2 := bool_decide (∃ n, n > 0 ∧ (...))` is the (classical) `decide` of the
    same proposition; `one_positive_true_iff` is its characterisation.
  - `Canonical Structure TO := leibnizO T` is `TO := DiscreteO T`; `own γ (●E n)`/`own γ (◯E n)`
    are `own_auth γ n`/`own_frag γ n` for the functor `excl_authF_T := constOF (ExclAuthR TO)`
    (Rocq: `inG Σ (excl_authR TO)`).
* Section `lemmas`: `ghost_var_alloc`, `ghost_var_agree`, `ghost_var_update` (same names).
* Section `client`: the context `rc:random_counter`, `L: counterG Σ`, `!spawnG Σ`,
  `!inG Σ (excl_authR TO)` is `[rc : random_counter GF] (L : rc.counterG GF) [spawnG GF]
  [ElemG GF excl_authF_T]`.
  - `con_prog`, `counter_nroot`, `inv_nroot`, `con_prog_inv`, `Rpower_4_2`, `con_prog_spec`:
    same names. `e1 ||| e2` is `&par (λ <>, e1) (λ <>, e2)` (Rocq: `par (λ: <>, e1)%E
    (λ: <>, e2)%E`).
  - `Rpower 4 x` is `(4 : ℝ≥0∞) ^ x` (`x : ℝ`); `INR` is the cast `ℕ → ℝ`; `bool_to_nat` is
    `Coneris.Lib.Flip.bool_to_nat`; `(1/2)%Qp` is `(1 : Qp).half`.
  - The error functions of the two `counter_tapes_presample`s are
    `λ x, if 0 < x then 0 else 4 ^ (1 + (b - 2))` as in Rocq (`0 <? fin_to_nat x`), where `b` is
    the `bool_to_nat` of the other thread's sample being `0`; their nonnegativity side
    conditions are dropped (`ℝ≥0∞`).
  - `namespaces.coPset_subseteq_difference_r` + `ndot_ne_disjoint` is the helper
    `counter_nroot_subseteq`.

## Added
* `wp_par'` (`wp_par` with `par_V` unfolded), `ite_timeless`, `one_positive_true_iff`,
  `one_positive_S0_S0`, `four_rpow_mean`, `four_rpow_zero_sub_two`, `four_rpow_two_sub_two`,
  `counter_nroot_subseteq`, `con_prog_inv_timeless`, `excl_authF_T`, `own_auth`, `own_frag`.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang
open Coneris Coneris.Lib.Spawn Coneris.Lib.Par Coneris.Lib.Flip
open Coneris.Examples.RandomCounter.RandomCounter
open Iris.ExclAuth

namespace Coneris.Examples.RandomCounter.Client

/-- Rocq: `T`. -/
inductive T : Type where
  | S0 : T
  | S1 (n : ℕ) : T

open T

/-- Rocq: `sampled`. -/
def sampled (s : T) : Option ℕ :=
  match s with
  | S0 => none
  | S1 n => some n

open Classical in
/-- Rocq: `one_positive`. -/
def one_positive (n1 n2 : T) : Bool :=
  decide (∃ n : ℕ, n > 0 ∧ (sampled n1 = some n ∨ sampled n2 = some n))

open Classical in
/-- Helper: characterisation of `one_positive`. -/
theorem one_positive_true_iff (n1 n2 : T) :
    one_positive n1 n2 = true ↔ ∃ n : ℕ, n > 0 ∧ (sampled n1 = some n ∨ sampled n2 = some n) := by
  unfold one_positive
  exact decide_eq_true_iff

/-- Helper: `one_positive S0 S0 = false`. -/
theorem one_positive_S0_S0 : one_positive S0 S0 = false := by
  rw [Bool.eq_false_iff, ne_eq, one_positive_true_iff]
  rintro ⟨n, -, h | h⟩ <;> simp [sampled] at h

/-- Rocq: `TO` (`Canonical Structure TO := leibnizO T`). -/
abbrev TO : Type := DiscreteO T

/-- Rocq: the functor of `inG Σ (excl_authR TO)`. -/
abbrev excl_authF_T : COFE.OFunctorPre := constOF (ExclAuthR (A := TO))

/-- `own γ (●E a)`. -/
abbrev own_auth {GF : BundledGFunctors} [ElemG GF excl_authF_T] (γ : GName) (a : T) :
    IProp GF :=
  iOwn (F := excl_authF_T) γ (●E (⟨a⟩ : TO))

/-- `own γ (◯E a)`. -/
abbrev own_frag {GF : BundledGFunctors} [ElemG GF excl_authF_T] (γ : GName) (a : T) :
    IProp GF :=
  iOwn (F := excl_authF_T) γ (◯E (⟨a⟩ : TO))

section lemmas

variable {GF : BundledGFunctors} [ElemG GF excl_authF_T]

/-- Helper: `own γ (●E a)` is timeless (stated explicitly for instance search under binders). -/
instance own_auth_timeless (γ : GName) (a : T) : Timeless (own_auth (GF := GF) γ a) :=
  inferInstance

/-- Helper: `own γ (◯E a)` is timeless. -/
instance own_frag_timeless (γ : GName) (a : T) : Timeless (own_frag (GF := GF) γ a) :=
  inferInstance

/-- Rocq: `ghost_var_alloc`. -/
theorem ghost_var_alloc (b : T) :
    ⊢@{IProp GF} |==> ∃ γ, own_auth γ b ∗ own_frag γ b := by
  imod iOwn_alloc (F := excl_authF_T) ((●E (⟨b⟩ : TO)) • (◯E (⟨b⟩ : TO)))
    ExclAuth.valid with ⟨%γ, H1, H2⟩
  imodintro
  iexists γ
  iframe

/-- Rocq: `ghost_var_agree`. -/
theorem ghost_var_agree (γ : GName) (b c : T) :
    ⊢@{IProp GF} own_auth γ b -∗ own_frag γ c -∗ ⌜b = c⌝ := by
  iintro H1 H2
  icombine H1 H2 gives %H
  ipureintro
  exact DiscreteO.eqv_inj (ExclAuth.agree H)

/-- Rocq: `ghost_var_update`. -/
theorem ghost_var_update (γ : GName) (b' b c : T) :
    ⊢@{IProp GF} own_auth γ b -∗ own_frag γ c ==∗ own_auth γ b' ∗ own_frag γ b' := by
  iintro H1 H2
  ihave H := (iOwn_op (F := excl_authF_T)).2 $$ [H1 H2]
  · iframe
  imod iOwn_update ExclAuth.update $$ H with ⟨H1, H2⟩
  imodintro
  iframe

end lemmas

/-! ## Helpers -/

/-- Helper (not in Rocq): `wp_par` with `par_V` unfolded, so that `wp_apply` finds it. -/
theorem wp_par' {GF : BundledGFunctors} [conerisGS GF] [spawnG GF]
    (Ψ1 Ψ2 : val → IProp GF) (e1 e2 : expr) (Φ : val → IProp GF) :
    ⊢ WP e1 {{ Ψ1 }} -∗ WP e2 {{ Ψ2 }} -∗
      (∀ v1 v2, Ψ1 v1 ∗ Ψ2 v2 -∗ ▷ Φ (PairV v1 v2)) -∗
      WP cpl(&par v(λ <>, &e1) v(λ <>, &e2)) {{ Φ }} :=
  wp_par Ψ1 Ψ2 e1 e2 Φ

/-- Helper (Rocq infers it): an `if` of timeless propositions is timeless. -/
instance ite_timeless {GF : BundledGFunctors} (c : Prop) [Decidable c] (P Q : IProp GF)
    [Timeless P] [Timeless Q] : Timeless (if c then P else Q) := by
  split <;> infer_instance

/-- Helper: `Rpower 4 (t + 1) = Rpower 4 t * 4`. -/
theorem four_rpow_one_add (t : ℝ) : (4 : ℝ≥0∞) ^ (1 + t) = 4 * 4 ^ t := by
  rw [ENNReal.rpow_add 1 t (by norm_num) (by norm_num), ENNReal.rpow_one]

/-- Helper (Rocq: `rewrite SeriesC_finite_foldr/=. rewrite Rpower_plus Rpower_1; lra.`). -/
theorem four_rpow_mean (t : ℝ) :
    ∑' x : Fin 4, 1 / 4 * (if 0 < (x : ℕ) then 0 else (4 : ℝ≥0∞) ^ (1 + t)) ≤ 4 ^ t := by
  rw [tsum_fintype, Fin.sum_univ_four]
  simp only [Fin.val_zero, lt_irrefl, ↓reduceIte, Fin.val_one, Nat.lt_add_one, mul_zero,
    add_zero, Fin.val_two, Nat.ofNat_pos, four_rpow_one_add]
  have h3 : 0 < ((3 : Fin 4) : ℕ) := by decide
  simp only [h3, ↓reduceIte, mul_zero, add_zero]
  rw [← mul_assoc, one_div, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

/-- Helper: `Rpower 4 (INR 0 - 2) = 1/16` (Rocq: `Rpower_Ropp`, `Rpower_4_2`). -/
theorem four_rpow_zero_sub_two : (4 : ℝ≥0∞) ^ (((0 : ℕ) : ℝ) - 2) = 1 / 16 := by
  rw [Nat.cast_zero, zero_sub, ENNReal.rpow_neg, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
    ENNReal.rpow_natCast]
  norm_num

/-- Helper: `Rpower 4 (INR 2 - 2) = 1` (Rocq: `Rpower_O`). -/
theorem four_rpow_two_sub_two : (4 : ℝ≥0∞) ^ (((2 : ℕ) : ℝ) - 2) = 1 := by
  norm_num

/-- Rocq: `Rpower_4_2`. -/
theorem Rpower_4_2 : (4 : ℝ≥0∞) ^ (2 : ℝ) = 16 := by
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
  norm_num

/-! ## The client -/

section client

variable {GF : BundledGFunctors} [conerisGS GF] [rc : random_counter GF] (L : rc.counterG GF)

/-- Rocq: `con_prog`. -/
def con_prog : expr := cpl(
  let c := v(&rc.new_counter) #() in
  (&par (λ <>, let lbl := v(&rc.allocate_tape) #() in
                v(&rc.incr_counter_tape) c lbl)
        (λ <>, let lbl := v(&rc.allocate_tape) #() in
                v(&rc.incr_counter_tape) c lbl)) ;
  v(&rc.read_counter) c)

/-- Rocq: `counter_nroot`. -/
def counter_nroot : Namespace := ndot nroot "counter"

/-- Rocq: `inv_nroot`. -/
def inv_nroot : Namespace := ndot nroot "inv"

/-- Helper (Rocq: `namespaces.coPset_subseteq_difference_r` + `ndot_ne_disjoint`). -/
theorem counter_nroot_subseteq : (↑counter_nroot : CoPset) ⊆ ⊤ \ ↑inv_nroot := by
  intro p hp
  rw [LawfulSet.mem_diff]
  exact ⟨CoPset.subseteq_top p hp,
    fun hq => ndot_ne_disjoint nroot (by decide : "counter" ≠ "inv") p ⟨hp, hq⟩⟩

variable [spawnG GF] [ElemG GF excl_authF_T]

/-- Rocq: `con_prog_inv`. -/
def con_prog_inv (γ1 γ2 : GName) : IProp GF :=
  iprop(∃ (n1 n2 : T),
    own_auth γ1 n1 ∗ own_auth γ2 n2 ∗
    if one_positive n1 n2
    then ↯ 0
    else
      ∃ flip_num : ℕ,
        ↯ ((4 : ℝ≥0∞) ^ ((flip_num : ℝ) - 2)) ∗
        ⌜flip_num = bool_to_nat (decide (sampled n1 = some 0)) +
          bool_to_nat (decide (sampled n2 = some 0))⌝)

instance con_prog_inv_timeless (γ1 γ2 : GName) : Timeless (con_prog_inv (GF := GF) γ1 γ2) := by
  unfold con_prog_inv; infer_instance

include L in
/-- Rocq: `con_prog_spec`. -/
theorem con_prog_spec :
    {{ ↯ (1 / 16) }} (con_prog (rc := rc))
    {{ (n : ℕ), RET LitV (LitInt (n : ℤ)); (⌜0 < n⌝ : IProp GF) }} := by
  iintro %Φ Hε HΦ
  unfold con_prog
  wp_apply rc.new_counter_spec L ⊤ counter_nroot $$ [] with %c ⟨%γ, #Hcounter, Hfrag⟩
  · itrivial
  ihave ⟨Hc1, Hc2⟩ := (rc.counter_content_frag_combine L γ (1 : Qp).half (1 : Qp).half 0 0).2
    $$ [Hfrag]
  · rw [Qp.half_add_half]
    iexact Hfrag
  wp_pures
  imod ghost_var_alloc S0 with ⟨%γ1, Hauth1, Hfrag1⟩
  imod ghost_var_alloc S0 with ⟨%γ2, Hauth2, Hfrag2⟩
  imod inv_alloc inv_nroot ⊤ (con_prog_inv γ1 γ2) $$ [Hauth1 Hauth2 Hε] with #Hinv
  · inext
    unfold con_prog_inv
    iexists S0, S0
    iframe Hauth1 Hauth2
    rw [one_positive_S0_S0]
    simp only [Bool.false_eq_true, ↓reduceIte]
    iexists 0
    rw [four_rpow_zero_sub_two]
    iframe Hε
    ipureintro
    rfl
  wp_apply wp_par'
    (fun _ => iprop(∃ n : ℕ, own_frag γ1 (S1 n) ∗ rc.counter_content_frag L γ (1 : Qp).half n))
    (fun _ => iprop(∃ n : ℕ, own_frag γ2 (S1 n) ∗ rc.counter_content_frag L γ (1 : Qp).half n))
    $$ [Hfrag1 Hc1] [Hfrag2 Hc2]
  · -- thread 1
    wp_apply rc.allocate_tape_spec L counter_nroot ⊤ c γ CoPset.subseteq_top $$ Hcounter
      with %lbl Htape
    wp_pures
    ihave H : iprop(state_update ⊤ ⊤
        iprop(∃ n : ℕ, own_frag γ1 (S1 n) ∗ rc.counter_tapes L lbl [n])) $$ [Hfrag1 Htape]
    · iapply state_update_inv_acc _ ⊤ _ inv_nroot CoPset.subseteq_top $$ Hinv
      iintro >HI
      unfold con_prog_inv
      icases HI with ⟨%n1, %n2, Hauth1, Hauth2, Herr⟩
      ihave %Heq := ghost_var_agree $$ Hauth1 Hfrag1
      subst Heq
      cases H : one_positive S0 n2
      · -- `one_positive` is false
        simp only [Bool.false_eq_true, ↓reduceIte]
        icases Herr with ⟨%flip_num, Herr, %Hflip⟩
        rw [show bool_to_nat (decide (sampled S0 = some 0)) = 0 from rfl, zero_add] at Hflip
        subst Hflip
        imod rc.counter_tapes_presample L counter_nroot (⊤ \ ↑inv_nroot) γ c lbl [] _
          (fun x => if 0 < (x : ℕ) then 0 else
            (4 : ℝ≥0∞) ^ (1 + ((bool_to_nat (decide (sampled n2 = some 0)) : ℝ) - 2)))
          counter_nroot_subseteq (four_rpow_mean _) $$ Hcounter Htape Herr
          with ⟨%n, Herr, Htape⟩
        imod ghost_var_update γ1 (S1 (n : ℕ)) _ _ $$ Hauth1 Hfrag1 with ⟨Hauth1, Hfrag1⟩
        imodintro
        simp only [List.nil_append]
        isplitl [Hfrag1 Htape]
        · iexists (n : ℕ)
          iframe
        inext
        iexists S1 (n : ℕ), n2
        iframe Hauth1 Hauth2
        by_cases K : 0 < (n : ℕ)
        · have H' : one_positive (S1 n) n2 = true :=
            (one_positive_true_iff _ _).2 ⟨n, K, Or.inl rfl⟩
          simp only [H', K, ↓reduceIte]
          iexact Herr
        · have hn0 : (n : ℕ) = 0 := by omega
          have H' : one_positive (S1 n) n2 = false := by
            rw [Bool.eq_false_iff, ne_eq, one_positive_true_iff]
            rintro ⟨m, hm, h | h⟩
            · simp only [sampled, hn0, Option.some.injEq] at h
              omega
            · have := (one_positive_true_iff S0 _).2 ⟨m, hm, Or.inr h⟩
              rw [H] at this
              exact Bool.false_ne_true this
          simp only [H', K, Bool.false_eq_true, ↓reduceIte]
          iexists 1 + bool_to_nat (decide (sampled n2 = some 0))
          isplitl [Herr]
          · iapply ErrorCredit.ext _ $$ Herr
            push_cast
            ring_nf
          · ipureintro
            simp [sampled, hn0, bool_to_nat]
      · -- `one_positive` is true
        simp only [↓reduceIte]
        imod rc.counter_tapes_presample L counter_nroot (⊤ \ ↑inv_nroot) γ c lbl [] 0
          (fun _ => 0) counter_nroot_subseteq (by simp) $$ Hcounter Htape Herr
          with ⟨%n, Herr, Htape⟩
        imod ghost_var_update γ1 (S1 (n : ℕ)) _ _ $$ Hauth1 Hfrag1 with ⟨Hauth1, Hfrag1⟩
        imodintro
        simp only [List.nil_append]
        isplitl [Hfrag1 Htape]
        · iexists (n : ℕ)
          iframe
        inext
        iexists S1 (n : ℕ), n2
        have H' : one_positive (S1 n) n2 = true := by
          obtain ⟨m, hm, h | h⟩ := (one_positive_true_iff _ _).1 H
          · simp [sampled] at h
          · exact (one_positive_true_iff _ _).2 ⟨m, hm, Or.inr h⟩
        simp only [H', ↓reduceIte]
        iframe
    imod H with ⟨%n, Hfrag1, Htape⟩
    wp_apply rc.incr_counter_tape_spec_some L counter_nroot ⊤ c γ
      (fun _ => rc.counter_content_frag L γ (1 : Qp).half n) lbl n [] CoPset.subseteq_top
      $$ [Htape Hc1] with %z ⟨-, Hc1⟩
    · iframe Htape
      isplitr
      · iexact Hcounter
      iintro %z Hauth
      imod rc.counter_content_update L γ _ z 0 n $$ Hauth Hc1 with ⟨Hauth, Hc1⟩
      imodintro
      rw [zero_add]
      iframe
    iexists n
    iframe
  · -- thread 2
    wp_apply rc.allocate_tape_spec L counter_nroot ⊤ c γ CoPset.subseteq_top $$ Hcounter
      with %lbl Htape
    wp_pures
    ihave H : iprop(state_update ⊤ ⊤
        iprop(∃ n : ℕ, own_frag γ2 (S1 n) ∗ rc.counter_tapes L lbl [n])) $$ [Hfrag2 Htape]
    · iapply state_update_inv_acc _ ⊤ _ inv_nroot CoPset.subseteq_top $$ Hinv
      iintro >HI
      unfold con_prog_inv
      icases HI with ⟨%n1, %n2, Hauth1, Hauth2, Herr⟩
      ihave %Heq := ghost_var_agree $$ Hauth2 Hfrag2
      subst Heq
      cases H : one_positive n1 S0
      · -- `one_positive` is false
        simp only [Bool.false_eq_true, ↓reduceIte]
        icases Herr with ⟨%flip_num, Herr, %Hflip⟩
        rw [show bool_to_nat (decide (sampled S0 = some 0)) = 0 from rfl, add_zero] at Hflip
        subst Hflip
        imod rc.counter_tapes_presample L counter_nroot (⊤ \ ↑inv_nroot) γ c lbl [] _
          (fun x => if 0 < (x : ℕ) then 0 else
            (4 : ℝ≥0∞) ^ (1 + ((bool_to_nat (decide (sampled n1 = some 0)) : ℝ) - 2)))
          counter_nroot_subseteq (four_rpow_mean _) $$ Hcounter Htape Herr
          with ⟨%n, Herr, Htape⟩
        imod ghost_var_update γ2 (S1 (n : ℕ)) _ _ $$ Hauth2 Hfrag2 with ⟨Hauth2, Hfrag2⟩
        imodintro
        simp only [List.nil_append]
        isplitl [Hfrag2 Htape]
        · iexists (n : ℕ)
          iframe
        inext
        iexists n1, S1 (n : ℕ)
        iframe Hauth1 Hauth2
        by_cases K : 0 < (n : ℕ)
        · have H' : one_positive n1 (S1 n) = true :=
            (one_positive_true_iff _ _).2 ⟨n, K, Or.inr rfl⟩
          simp only [H', K, ↓reduceIte]
          iexact Herr
        · have hn0 : (n : ℕ) = 0 := by omega
          have H' : one_positive n1 (S1 n) = false := by
            rw [Bool.eq_false_iff, ne_eq, one_positive_true_iff]
            rintro ⟨m, hm, h | h⟩
            · have := (one_positive_true_iff _ S0).2 ⟨m, hm, Or.inl h⟩
              rw [H] at this
              exact Bool.false_ne_true this
            · simp only [sampled, hn0, Option.some.injEq] at h
              omega
          simp only [H', K, Bool.false_eq_true, ↓reduceIte]
          iexists bool_to_nat (decide (sampled n1 = some 0)) + 1
          isplitl [Herr]
          · iapply ErrorCredit.ext _ $$ Herr
            push_cast
            ring_nf
          · ipureintro
            simp [sampled, hn0, bool_to_nat]
      · -- `one_positive` is true
        simp only [↓reduceIte]
        imod rc.counter_tapes_presample L counter_nroot (⊤ \ ↑inv_nroot) γ c lbl [] 0
          (fun _ => 0) counter_nroot_subseteq (by simp) $$ Hcounter Htape Herr
          with ⟨%n, Herr, Htape⟩
        imod ghost_var_update γ2 (S1 (n : ℕ)) _ _ $$ Hauth2 Hfrag2 with ⟨Hauth2, Hfrag2⟩
        imodintro
        simp only [List.nil_append]
        isplitl [Hfrag2 Htape]
        · iexists (n : ℕ)
          iframe
        inext
        iexists n1, S1 (n : ℕ)
        have H' : one_positive n1 (S1 n) = true := by
          obtain ⟨m, hm, h | h⟩ := (one_positive_true_iff _ _).1 H
          · exact (one_positive_true_iff _ _).2 ⟨m, hm, Or.inl h⟩
          · simp [sampled] at h
        simp only [H', ↓reduceIte]
        iframe
    imod H with ⟨%n, Hfrag2, Htape⟩
    wp_apply rc.incr_counter_tape_spec_some L counter_nroot ⊤ c γ
      (fun _ => rc.counter_content_frag L γ (1 : Qp).half n) lbl n [] CoPset.subseteq_top
      $$ [Htape Hc2] with %z ⟨-, Hc2⟩
    · iframe Htape
      isplitr
      · iexact Hcounter
      iintro %z Hauth
      imod rc.counter_content_update L γ _ z 0 n $$ Hauth Hc2 with ⟨Hauth, Hc2⟩
      imodintro
      rw [zero_add]
      iframe
    iexists n
    iframe
  · iintro %v1 %v2 ⟨⟨%n1, Hfrag1, Hc1⟩, ⟨%n2, Hfrag2, Hc2⟩⟩
    inext
    wp_pures
    ihave Hc := (rc.counter_content_frag_combine L γ _ _ n1 n2).1 $$ [Hc1 Hc2]
    · iframe
    rw [Qp.half_add_half]
    ihave H : iprop(|={⊤}=> ⌜0 < n1 + n2⌝) $$ [Hfrag1 Hfrag2]
    · iinv Hinv with >HI Hclose
      unfold con_prog_inv
      icases HI with ⟨%m1, %m2, Hauth1, Hauth2, Herr⟩
      ihave %Heq1 := ghost_var_agree $$ Hauth1 Hfrag1
      ihave %Heq2 := ghost_var_agree $$ Hauth2 Hfrag2
      subst Heq1 Heq2
      by_cases hz : n1 = 0 ∧ n2 = 0
      · obtain ⟨rfl, rfl⟩ := hz
        have H' : one_positive (S1 0) (S1 0) = false := by
          rw [Bool.eq_false_iff, ne_eq, one_positive_true_iff]
          rintro ⟨m, hm, h | h⟩ <;> simp only [sampled, Option.some.injEq] at h <;> omega
        simp only [H', Bool.false_eq_true, ↓reduceIte]
        icases Herr with ⟨%fn, Herr, %Hfn⟩
        have hfn : fn = 2 := by simpa [sampled, bool_to_nat] using Hfn
        subst hfn
        iexfalso
        iapply ErrorCredit.contradict (le_of_eq four_rpow_two_sub_two.symm) $$ Herr
      · imod Hclose $$ [Hauth1 Hauth2 Herr]
        · inext
          iexists S1 n1, S1 n2
          iframe
        imodintro
        ipureintro
        omega
    imod H with %Hpos
    wp_apply rc.read_counter_spec L counter_nroot ⊤ c γ (fun n => iprop(⌜0 < n⌝))
      CoPset.subseteq_top $$ [Hc] with %n' %Hn'
    · iframe Hcounter
      iintro %z Hauth
      ihave %Heq := rc.counter_content_agree L γ z (n1 + n2) $$ Hauth Hc
      imodintro
      iframe Hauth
      ipureintro
      omega
    iapply HΦ
    ipureintro
    exact Hn'

end client

end Coneris.Examples.RandomCounter.Client
