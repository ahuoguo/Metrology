module

public import Metrology.Coneris.Examples.RandomCounter.RandomCounter
public import Metrology.Coneris.Lib.HocapRand

/-!
# Random counter: first implementation (a `rand_spec` tape with bound 3)

Ported from clutch/theories/coneris/examples/random_counter/impl1.v

## Rocq → Lean mapping
* Section `impl1`: the context `H:conerisGS Σ, r1:@rand_spec Σ H, L:randG Σ,
  !inG Σ (frac_authR natR)` is `[conerisGS GF] [r1 : rand_spec GF]` plus, for the proofs,
  `[L : counterG1 GF]` (the class bundling `randG` and `inG`; its `ElemG` field is a local
  instance, Rocq: `counterG1_frac_authR ::`). The rand tapes are `r1.rand_tapes
  L`.
* `new_counter1`, `allocate_tape1`, `incr_counter_tape1`, `read_counter1`: same names,
  transcribed with the `cpl` notation (`#3%nat` is `#3`, `FAA "l" "n"` is `faa(l, n)`).
* `counterG1` (Rocq: `Class counterG1 Σ := CounterG1 { counterG1_randG : randG Σ;
  counterG1_frac_authR :: inG Σ (frac_authR natR) }`) is the Lean `class counterG1 GF'`
  (over `[r1 : rand_spec GF]`, since `randG` is a field of `r1`). In `random_counter1` its
  field `counterG1_frac_authR` is a local instance (Rocq: `counterG1_frac_authR ::`) and
  `counterG1_randG` is passed as `L` (Rocq: `(L:=counterG1_randG)`).
* `own γ (●F z)` / `own γ (◯F{f} z)` are `own_auth_nat γ z` / `own_frag_nat γ f z` of
  `RandomCounter` (for the functor `frac_authF_nat`).
* `counter_inv_pred1`, `is_counter1`, `new_counter_spec1`, `allocate_tape_spec1`,
  `incr_counter_tape_spec_some1`, `counter_tapes_presample1`, `read_counter_spec1`: same names.
  - In `counter_tapes_presample1` the hypothesis `∀ x, 0 <= ε2 x` is dropped (`ℝ≥0∞`).
* `random_counter1` (Rocq: `Program Definition`) is a definition (not an instance) over
  `[r1 : rand_spec GF]`. Its `Next Obligation`s are the helper theorems
  `random_counter1_counter_tapes_exclusive`, `random_counter1_counter_tapes_valid`,
  `random_counter1_counter_content_auth_exclusive`, `random_counter1_counter_content_less_than`,
  `random_counter1_counter_content_frag_combine`, `random_counter1_counter_content_agree`,
  `random_counter1_counter_content_update` (the last five are the shared `frac_auth_nat_*`
  lemmas of `RandomCounter`). The persistence/timelessness obligations (solved automatically in
  Rocq) are instances.

## Omitted
* The commented-out Rocq code (`rand_inv_create_spec`, `fupd_mask_subseteq`, `tape_name`,
  `counter_tapes_auth` and the commented-out `Next Obligation`s).
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.dupNamespace false
set_option linter.iris.dupNamespace false

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang
open Coneris Coneris.Lib.HocapRand Coneris.Examples.RandomCounter.RandomCounter

namespace Coneris.Examples.RandomCounter.Impl1

section impl1

variable {GF : BundledGFunctors} [conerisGS GF] [r1 : rand_spec GF]

/-- Rocq: `new_counter1`. -/
def new_counter1 : val := cpl_val(λ _, ref(#0))

/-- Rocq: `allocate_tape1`. -/
def allocate_tape1 : val := cpl_val(λ _, v(&r1.rand_allocate_tape) #3)

/-- Rocq: `incr_counter_tape1`. -/
def incr_counter_tape1 : val := cpl_val(
  λ l α, let n := v(&r1.rand_tape) α #3 in (faa(l, n), n))

/-- Rocq: `read_counter1`. -/
def read_counter1 : val := cpl_val(λ l, !l)

/-- Rocq: `counterG1`. -/
class counterG1 (GF' : BundledGFunctors) where
  counterG1_randG : r1.randG GF'
  counterG1_frac_authR : ElemG GF' frac_authF_nat

attribute [instance_reducible] counterG1.counterG1_frac_authR

variable (L : r1.randG GF) [ElemG GF frac_authF_nat]

/-- Rocq: `counter_inv_pred1`. -/
def counter_inv_pred1 (c : val) (γ2 : GName) : IProp GF :=
  iprop(∃ (l : Loc) (z : ℕ), ⌜c = LitV (LitLoc l)⌝ ∗ l ↦ LitV (LitInt (z : ℤ)) ∗
    own_auth_nat γ2 z)

instance counter_inv_pred1_timeless (c : val) (γ2 : GName) :
    Timeless (counter_inv_pred1 c γ2) := by
  unfold counter_inv_pred1; infer_instance

/-- Rocq: `is_counter1`. -/
def is_counter1 (N : Namespace) (c : val) (γ1 : GName) : IProp GF :=
  inv N (counter_inv_pred1 c γ1)

instance is_counter1_persistent (N : Namespace) (c : val) (γ1 : GName) :
    Persistent (is_counter1 N c γ1) := by
  unfold is_counter1; infer_instance

/-- Rocq: `new_counter_spec1`. -/
theorem new_counter_spec1 (E : CoPset) (N : Namespace) :
    {{ True }} cpl(v(&new_counter1) #()) @ E
    {{ c, RET c; ∃ γ1, is_counter1 N c γ1 ∗ own_frag_nat γ1 1 0 }} := by
  unfold is_counter1
  iintro %Φ - HΦ
  unfold new_counter1
  wp_pures
  wp_alloc l as Hl
  imod frac_auth_nat_alloc with ⟨%γ1, H5, H6⟩
  imod inv_alloc N E (counter_inv_pred1 (LitV (LitLoc l)) γ1) $$ [Hl H5] with #Hinv'
  · inext
    unfold counter_inv_pred1
    iexists l, 0
    iframe
    ipureintro
    rfl
  iapply HΦ
  iexists γ1
  iframe Hinv' H6

/-- Rocq: `allocate_tape_spec1`. -/
theorem allocate_tape_spec1 (N : Namespace) (E : CoPset) (c : val) (γ1 : GName)
    (_Hsubset : ↑N ⊆ E) :
    {{ is_counter1 N c γ1 }} cpl(v(&allocate_tape1) #()) @ E
    {{ v, RET v; r1.rand_tapes L v (3, []) }} := by
  iintro %Φ #Hinv HΦ
  unfold allocate_tape1
  wp_pures
  wp_apply r1.rand_allocate_tape_spec L E 3 $$ [] with %v Hv
  · itrivial
  iapply HΦ $$ Hv

/-- Rocq: `incr_counter_tape_spec_some1`. -/
theorem incr_counter_tape_spec_some1 (N : Namespace) (E : CoPset) (c : val) (γ1 : GName)
    (Q : ℕ → IProp GF) (α : val) (n : ℕ) (ns : List ℕ) (Hsubset : ↑N ⊆ E) :
    {{ is_counter1 N c γ1 ∗ r1.rand_tapes L α (3, n :: ns) ∗
        (∀ z : ℕ, own_auth_nat γ1 z ={E \ ↑N}=∗ own_auth_nat γ1 (z + n) ∗ Q z) }}
      cpl(v(&incr_counter_tape1) v(&c) v(&α)) @ E
    {{ (z : ℕ), RET cpl_val((#z, #n)); r1.rand_tapes L α (3, ns) ∗ Q z }} := by
  unfold is_counter1 counter_inv_pred1
  iintro %Φ ⟨#Hinv, Hfrag, Hvs⟩ HΦ
  unfold incr_counter_tape1
  wp_pures
  wp_apply r1.rand_tape_spec_some L E α 3 n ns $$ Hfrag with Hfrag
  wp_pures
  wp_bind (FAA _ _)
  iinv Hinv with >⟨%l, %z, %Hc, Hl, Hauth⟩ Hclose
  subst Hc
  wp_faa
  imod Hvs $$ Hauth with ⟨Hauth, HQ⟩
  imod Hclose $$ [Hl Hauth]
  · inext
    iexists l, z + n
    iframe Hauth
    isplitr
    · ipureintro; rfl
    rw [Nat.cast_add]
    iexact Hl
  imodintro
  wp_pures
  iapply HΦ
  iframe

/-- Rocq: `counter_tapes_presample1`. -/
theorem counter_tapes_presample1 (N : Namespace) (E : CoPset) (γ1 : GName) (c α : val)
    (ns : List ℕ) (ε : ℝ≥0∞) (ε2 : Fin 4 → ℝ≥0∞) (_Hsubset : ↑N ⊆ E)
    (Hineq : ∑' n, 1 / 4 * ε2 n ≤ ε) :
    ⊢ is_counter1 N c γ1 -∗ r1.rand_tapes L α (3, ns) -∗ ↯ ε -∗
      state_update E E iprop(∃ n : Fin 4, ↯ (ε2 n) ∗
        r1.rand_tapes L α (3, ns ++ [(n : ℕ)])) := by
  iintro #Hinv Hfrag Herr
  imod r1.rand_tapes_presample L E α 3 ns ε ε2
    (by refine le_trans (le_of_eq ?_) Hineq; norm_num) $$ Hfrag Herr with ⟨%n, Herr, Hfrag⟩
  imodintro
  iexists n
  iframe

/-- Rocq: `read_counter_spec1`. -/
theorem read_counter_spec1 (N : Namespace) (E : CoPset) (c : val) (γ1 : GName)
    (Q : ℕ → IProp GF) (Hsubset : ↑N ⊆ E) :
    {{ is_counter1 N c γ1 ∗
        (∀ z : ℕ, own_auth_nat γ1 z ={E \ ↑N}=∗ own_auth_nat γ1 z ∗ Q z) }}
      cpl(v(&read_counter1) v(&c)) @ E
    {{ (n' : ℕ), RET LitV (LitInt (n' : ℤ)); Q n' }} := by
  unfold is_counter1 counter_inv_pred1
  iintro %Φ ⟨#Hinv, Hvs⟩ HΦ
  unfold read_counter1
  wp_pure
  iinv Hinv with >⟨%l, %z, %Hc, H5, H6⟩ Hclose
  subst Hc
  wp_load
  imod Hvs $$ H6 with ⟨H6, HQ⟩
  imod Hclose $$ [H5 H6]
  · inext
    iexists l, z
    iframe
    ipureintro; rfl
  imodintro
  iapply HΦ $$ HQ

end impl1

/-! ## `random_counter1` and its obligations -/

section obligations

variable {GF : BundledGFunctors} [conerisGS GF] [r1 : rand_spec GF]

attribute [local instance] counterG1.counterG1_frac_authR

/-- Rocq: first `Next Obligation` of `random_counter1` (`counter_tapes_exclusive`). -/
theorem random_counter1_counter_tapes_exclusive (L : counterG1 (r1 := r1) GF) (α : val)
    (ns ns' : List ℕ) :
    ⊢ r1.rand_tapes L.counterG1_randG α (3, ns) -∗
      r1.rand_tapes L.counterG1_randG α (3, ns') -∗ False := by
  iintro H1 H2
  iapply r1.rand_tapes_exclusive $$ H1 H2

/-- Rocq: second `Next Obligation` of `random_counter1` (`counter_tapes_valid`). -/
theorem random_counter1_counter_tapes_valid (L : counterG1 (r1 := r1) GF) (α : val)
    (ns : List ℕ) :
    ⊢ r1.rand_tapes L.counterG1_randG α (3, ns) -∗ ⌜∀ n ∈ ns, n ≤ 3⌝ := by
  iintro H
  iapply r1.rand_tapes_valid $$ H

/-- Rocq: `random_counter1` (a `Program Definition`). -/
@[instance_reducible]
def random_counter1 : random_counter GF where
  new_counter := new_counter1
  allocate_tape := allocate_tape1
  incr_counter_tape := incr_counter_tape1
  read_counter := read_counter1
  counterG := counterG1 (r1 := r1)
  counter_name := GName
  is_counter _ N c γ1 := is_counter1 N c γ1
  counter_tapes L α ns := r1.rand_tapes L.counterG1_randG α (3, ns)
  counter_content_auth _ γ z := own_auth_nat γ z
  counter_content_frag _ γ f z := own_frag_nat γ f z
  is_counter_persistent _ N c γ1 := is_counter1_persistent N c γ1
  counter_tapes_timeless _ _ _ := inferInstance
  counter_content_auth_timeless _ _ _ := inferInstance
  counter_content_frag_timeless _ _ _ _ := inferInstance
  counter_tapes_exclusive L := random_counter1_counter_tapes_exclusive L
  counter_tapes_valid L := random_counter1_counter_tapes_valid L
  counter_tapes_presample L := counter_tapes_presample1 L.counterG1_randG
  counter_content_auth_exclusive _ := frac_auth_nat_auth_exclusive
  counter_content_less_than _ := frac_auth_nat_less_than
  counter_content_frag_combine _ := frac_auth_nat_frag_combine
  counter_content_agree _ := frac_auth_nat_agree
  counter_content_update _ := frac_auth_nat_update
  new_counter_spec _ := new_counter_spec1
  allocate_tape_spec L := allocate_tape_spec1 L.counterG1_randG
  incr_counter_tape_spec_some L := incr_counter_tape_spec_some1 L.counterG1_randG
  read_counter_spec _ := read_counter_spec1

end obligations

end Coneris.Examples.RandomCounter.Impl1
