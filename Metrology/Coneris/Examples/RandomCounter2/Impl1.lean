module

public import Metrology.Coneris.Examples.RandomCounter2.RandomCounter
public import Metrology.Coneris.Lib.HocapRand
public import Iris.Algebra.Lib.FracAuth
public import Iris.Algebra.Numbers

/-!
# Random counter, implementation 1

Ported from clutch/theories/coneris/examples/random_counter2/impl1.v

The counter is incremented by a sample of `rand #3`, drawn from a freshly allocated hocap tape
(`Coneris.Lib.HocapRand`).

## Rocq → Lean mapping
* Section `impl1`: the context `H:conerisGS Σ, r1:@rand_spec Σ H, L:randG Σ,
  !inG Σ (frac_authR natR)` is `[conerisGS GF] [r1 : rand_spec GF] (L : r1.randG GF)
  [ElemG GF frac_authTF]` with `frac_authTF := constOF (FracAuth (A := ℕ))` (iris-lean's
  `(ℕ, +)` camera; `natR`). As in `Coneris.Lib.HocapRand`, `L` is an explicit argument.
* `own γ (●F z)` / `own γ (◯F{f} z)` / `own γ (◯F z)` are `iOwn γ (●F z)` / `iOwn γ (◯F{f} z)`
  / `iOwn γ (◯F z)` (with `F := frac_authTF`).
* `new_counter1`, `incr_counter1`, `read_counter1`, `counter_inv_pred1`, `is_counter1`,
  `new_counter_spec1`, `incr_counter_spec1`, `counter_tapes_presample1`, `read_counter_spec1`:
  same names. The programs are transcribed with the `cpl` notation (`#3%nat` is `#3`).
* `Class counterG1 Σ := CounterG1 {counterG1_randG : randG Σ; counterG1_frac_authR :: inG ..}`
  is the Lean `class counterG1 GF` (over `[conerisGS GF] [rand_spec GF]`) with the same fields;
  the instance field `counterG1_frac_authR` is used explicitly (`haveI`) where needed.
* `counter_inv_pred1` takes `c : val` (Rocq: inferred).
* `c = #l` is `c = LitV (LitLoc l)`; `l ↦ #z` (`z : nat`) is `l ↦ LitV (LitInt z)`.
* Errors are `ℝ≥0∞`: the hypothesis `∀ x, 0 <= ε2 x` of `counter_tapes_presample1` is
  dropped; `SeriesC (λ n, 1 / 4 * ε2 n) <= ε` is `∑' n : Fin 4, 1 / 4 * ε2 n ≤ ε`.
* `random_counter1` (Rocq: `Program Definition`) is a definition (not an instance) over
  `[F : rand_spec GF]`. Its field `counterG` is `fun _ => counterG1 GF` (the Lean field is a
  function of the `BundledGFunctors`, only ever applied to `GF`). Its `Next Obligation`s are the
  helper theorems `random_counter1_counter_content_auth_exclusive`,
  `random_counter1_counter_content_less_than`, `random_counter1_counter_content_frag_combine`,
  `random_counter1_counter_content_agree`, `random_counter1_counter_content_update` (stated
  over a section instance `[ElemG GF frac_authTF]`); the automatically solved obligations
  (timelessness, persistence) are the instances `is_counter1_persistent`,
  `counter_inv_pred1_timeless`.

## Added
* `frac_authTF` (the functor of `inG Σ (frac_authR natR)`).

## Omitted
* The commented-out Rocq code (`rand_inv_create_spec`, `fupd_mask_subseteq` steps).
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang
open Coneris Coneris.Lib.HocapRand Coneris.Examples.RandomCounter2.RandomCounter

namespace Coneris.Examples.RandomCounter2.Impl1

/-- Rocq: the functor of `inG Σ (frac_authR natR)`. -/
abbrev frac_authTF : COFE.OFunctorPre := constOF (FracAuth (A := ℕ))

section impl1

variable {GF : BundledGFunctors} [conerisGS GF] [r1 : rand_spec GF] (L : r1.randG GF)
  [Hfa : ElemG GF frac_authTF]

/-- Rocq: `new_counter1`. -/
def new_counter1 : val := cpl_val(λ _, ref(#0))

/-- Rocq: `incr_counter1`. -/
def incr_counter1 : val := cpl_val(
  λ l, let n := v(&r1.rand_tape) (v(&r1.rand_allocate_tape) #3) #3 in (faa(l, n), n))

/-- Rocq: `read_counter1`. -/
def read_counter1 : val := cpl_val(λ l, !l)

/-- Rocq: `counterG1`. -/
class counterG1 (GF : BundledGFunctors) [conerisGS GF] [r1 : rand_spec GF] : Type where
  counterG1_randG : r1.randG GF
  counterG1_frac_authR : ElemG GF frac_authTF

/-- Rocq: `counter_inv_pred1`. -/
def counter_inv_pred1 (c : val) (γ2 : GName) : IProp GF :=
  iprop(∃ (l : Loc) (z : ℕ), ⌜c = LitV (LitLoc l)⌝ ∗ l ↦ LitV (LitInt z) ∗
    iOwn (F := frac_authTF) γ2 (●F z))

/-- Rocq: `is_counter1`. -/
def is_counter1 (N : Namespace) (c : val) (γ1 : GName) : IProp GF :=
  inv N (counter_inv_pred1 c γ1)

instance is_counter1_persistent (N : Namespace) (c : val) (γ1 : GName) :
    Persistent (is_counter1 (GF := GF) N c γ1) := by
  unfold is_counter1; infer_instance

/-- Rocq: `new_counter_spec1`. -/
theorem new_counter_spec1 (E : CoPset) (N : Namespace) :
    {{ True }} cpl(v(&new_counter1) #()) @ E
    {{ (c : val), RET c; ∃ γ1, is_counter1 (GF := GF) N c γ1 ∗
        iOwn (F := frac_authTF) γ1 (◯F (0 : ℕ)) }} := by
  unfold new_counter1
  iintro %Φ - HΦ
  wp_pures
  wp_alloc l as Hl
  imod iOwn_alloc (F := frac_authTF) ((●F (0 : ℕ)) • (◯F (0 : ℕ))) (FracAuth.valid trivial)
    with ⟨%γ1, H5, H6⟩
  imod inv_alloc N E (counter_inv_pred1 (LitV (LitLoc l)) γ1) $$ [Hl H5] with #Hinv'
  · inext
    unfold counter_inv_pred1
    iexists l, 0
    iframe Hl H5
    ipureintro
    rfl
  iapply HΦ
  iexists γ1
  unfold is_counter1
  iframe Hinv' H6

/-- Rocq: `incr_counter_spec1`. -/
theorem incr_counter_spec1 (N : Namespace) (E : CoPset) (c : val) (γ1 : GName)
    (Q : ℕ → ℕ → IProp GF) (Hineq : ↑N ⊆ E) :
    {{ is_counter1 N c γ1 ∗
        (∀ α, r1.rand_tapes L α (3, []) -∗
          state_update E E iprop(∃ n, r1.rand_tapes L α (3, [n]) ∗
            (∀ z : ℕ, iOwn (F := frac_authTF) γ1 (●F z) ={E \ ↑N}=∗
              iOwn (F := frac_authTF) γ1 (●F (z + n)) ∗ Q z n))) }}
      cpl(v(&incr_counter1) v(&c)) @ E
    {{ (z n : ℕ), RET cpl_val((#z, #n)); Q z n }} := by
  iintro %Φ ⟨#Hinv, Hvs⟩ HΦ
  unfold incr_counter1
  wp_pures
  wp_apply r1.rand_allocate_tape_spec L E 3 $$ [] with %α Htape
  · itrivial
  imod Hvs $$ Htape with ⟨%n, Htape, Hvs⟩
  wp_apply r1.rand_tape_spec_some L E α 3 n [] $$ Htape with Htape
  wp_pures
  wp_bind (FAA _ _)
  unfold is_counter1 counter_inv_pred1
  iinv Hinv with ⟨%l, %z, >%Hc, >H5, >H6⟩ Hclose
  subst Hc
  wp_faa
  imod Hvs $$ H6 with ⟨H6, HQ⟩
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

/-- Rocq: `counter_tapes_presample1`. -/
theorem counter_tapes_presample1 (N : Namespace) (E : CoPset) (γ1 : GName) (c : val) (α : val)
    (ε : ℝ≥0∞) (ε2 : Fin 4 → ℝ≥0∞) (_Hsubset : ↑N ⊆ E)
    (Hineq : ∑' n : Fin 4, 1 / 4 * ε2 n ≤ ε) :
    ⊢ is_counter1 N c γ1 -∗ r1.rand_tapes L α (3, []) -∗ ↯ ε -∗
      state_update E E iprop(∃ n : Fin 4, ↯ (ε2 n) ∗ r1.rand_tapes L α (3, [(n : ℕ)])) := by
  iintro #Hinv Hfrag Herr
  imod r1.rand_tapes_presample L E α 3 [] ε ε2 ?_ $$ Hfrag Herr with ⟨%n, Herr, Hfrag⟩
  · refine le_trans (le_of_eq ?_) Hineq
    norm_num
  imodintro
  iexists n
  simp only [List.nil_append]
  iframe Herr Hfrag

/-- Rocq: `read_counter_spec1`. -/
theorem read_counter_spec1 (N : Namespace) (E : CoPset) (c : val) (γ1 : GName)
    (Q : ℕ → IProp GF) (Hsubset : ↑N ⊆ E) :
    {{ is_counter1 N c γ1 ∗
        (∀ z : ℕ, iOwn (F := frac_authTF) γ1 (●F z) ={E \ ↑N}=∗
          iOwn (F := frac_authTF) γ1 (●F z) ∗ Q z) }}
      cpl(v(&read_counter1) v(&c)) @ E
    {{ (n' : ℕ), RET LitV (LitInt n'); Q n' }} := by
  iintro %Φ ⟨#Hinv, Hvs⟩ HΦ
  unfold read_counter1
  wp_pure
  unfold is_counter1 counter_inv_pred1
  iinv Hinv with ⟨%l, %z, >%Hc, >H5, >H6⟩ Hclose
  subst Hc
  wp_load
  imod Hvs $$ H6 with ⟨H6, HQ⟩
  imod Hclose $$ [H5 H6] with -
  · inext
    iexists l, z
    iframe H5 H6
    ipureintro
    rfl
  imodintro
  iapply HΦ $$ HQ

end impl1

/-! ### The `Next Obligation`s of `random_counter1` -/

section obligations

variable {GF : BundledGFunctors} [Hfa : ElemG GF frac_authTF]

/-- Rocq: first `Next Obligation` of `random_counter1`. -/
theorem random_counter1_counter_content_auth_exclusive (γ : GName) (z1 z2 : ℕ) :
    ⊢@{IProp GF} iOwn (F := frac_authTF) γ (●F z1) -∗ iOwn (F := frac_authTF) γ (●F z2) -∗
      False := by
  iintro H1 H2
  icombine H1 H2 gives %H
  exact (FracAuth.auth_op_valid H).elim

/-- Rocq: second `Next Obligation` of `random_counter1`. -/
theorem random_counter1_counter_content_less_than (γ : GName) (z z' : ℕ) (f : Qp) :
    ⊢@{IProp GF} iOwn (F := frac_authTF) γ (●F z) -∗ iOwn (F := frac_authTF) γ (◯F{f} z') -∗
      ⌜z' ≤ z⌝ := by
  iintro H1 H2
  icombine H1 H2 gives %H
  ipureintro
  have ⟨w, hw⟩ := CommMonoidLike.included_iff.mp (FracAuth.included_total H)
  change z = z' + w at hw
  omega

/-- Rocq: third `Next Obligation` of `random_counter1`. -/
theorem random_counter1_counter_content_frag_combine (γ : GName) (f f' : Qp) (z z' : ℕ) :
    (iOwn (F := frac_authTF) γ (◯F{f} z) ∗ iOwn (F := frac_authTF) γ (◯F{f'} z')) ⊣⊢@{IProp GF}
      iOwn (F := frac_authTF) γ (◯F{f + f'} (z + z')) := by
  rw [← iOwn_op.to_eq]
  exact (congrArg (iOwn (F := frac_authTF) γ) FracAuth.frag_op).symm.to_bi

/-- Rocq: fourth `Next Obligation` of `random_counter1`. -/
theorem random_counter1_counter_content_agree (γ : GName) (z z' : ℕ) :
    ⊢@{IProp GF} iOwn (F := frac_authTF) γ (●F z) -∗ iOwn (F := frac_authTF) γ (◯F{1} z') -∗
      ⌜z' = z⌝ := by
  iintro H1 H2
  icombine H1 H2 gives %H
  ipureintro
  exact (FracAuth.agree H).symm

/-- Rocq: fifth `Next Obligation` of `random_counter1`. -/
theorem random_counter1_counter_content_update (γ : GName) (f : Qp) (z1 z2 z3 : ℕ) :
    ⊢@{IProp GF} iOwn (F := frac_authTF) γ (●F z1) -∗ iOwn (F := frac_authTF) γ (◯F{f} z2) ==∗
      iOwn (F := frac_authTF) γ (●F (z1 + z3)) ∗ iOwn (F := frac_authTF) γ (◯F{f} (z2 + z3)) := by
  iintro H1 H2
  imod iOwn_update_op (a' := (●F (z1 + z3)) • (◯F{f} (z2 + z3))) $$ [$H1 $H2] with ⟨H1, H2⟩
  · exact FracAuth.update (CommMonoidLike.leftCancelAdd_local_update (by grind))
  imodintro
  iframe

end obligations

/-- Rocq: `random_counter1` (a `Program Definition`). -/
@[instance_reducible]
def random_counter1 {GF : BundledGFunctors} [conerisGS GF] [F : rand_spec GF] :
    random_counter GF where
  new_counter := new_counter1
  incr_counter := incr_counter1
  read_counter := read_counter1
  counterG := fun _ => counterG1 GF
  counter_name := GName
  is_counter L N c γ1 := is_counter1 (Hfa := (L : counterG1 GF).counterG1_frac_authR) N c γ1
  counter_tapes L α n :=
    F.rand_tapes (L : counterG1 GF).counterG1_randG α
      (3, match n with | some x => [x] | none => [])
  counter_content_auth L γ z :=
    iOwn (E := (L : counterG1 GF).counterG1_frac_authR) (F := frac_authTF) γ (●F z)
  counter_content_frag L γ f z :=
    iOwn (E := (L : counterG1 GF).counterG1_frac_authR) (F := frac_authTF) γ (◯F{f} z)
  is_counter_persistent L N c γ1 :=
    is_counter1_persistent (Hfa := (L : counterG1 GF).counterG1_frac_authR) N c γ1
  counter_tapes_timeless L α n := by infer_instance
  counter_content_auth_timeless L γ z :=
    letI := (L : counterG1 GF).counterG1_frac_authR; iOwn_timeless
  counter_content_frag_timeless L γ f z :=
    letI := (L : counterG1 GF).counterG1_frac_authR; iOwn_timeless
  counter_tapes_presample L :=
    counter_tapes_presample1 (Hfa := (L : counterG1 GF).counterG1_frac_authR)
      (L : counterG1 GF).counterG1_randG
  counter_content_auth_exclusive L :=
    random_counter1_counter_content_auth_exclusive
      (Hfa := (L : counterG1 GF).counterG1_frac_authR)
  counter_content_less_than L :=
    random_counter1_counter_content_less_than (Hfa := (L : counterG1 GF).counterG1_frac_authR)
  counter_content_frag_combine L :=
    random_counter1_counter_content_frag_combine
      (Hfa := (L : counterG1 GF).counterG1_frac_authR)
  counter_content_agree L :=
    random_counter1_counter_content_agree (Hfa := (L : counterG1 GF).counterG1_frac_authR)
  counter_content_update L :=
    random_counter1_counter_content_update (Hfa := (L : counterG1 GF).counterG1_frac_authR)
  new_counter_spec L :=
    new_counter_spec1 (Hfa := (L : counterG1 GF).counterG1_frac_authR)
  incr_counter_spec L :=
    incr_counter_spec1 (Hfa := (L : counterG1 GF).counterG1_frac_authR)
      (L : counterG1 GF).counterG1_randG
  read_counter_spec L :=
    read_counter_spec1 (Hfa := (L : counterG1 GF).counterG1_frac_authR)

end Coneris.Examples.RandomCounter2.Impl1
