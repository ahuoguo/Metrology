module

public import Metrology.Coneris.Examples.RandomCounter3.RandomCounter
public import Metrology.Coneris.Lib.HocapRand

/-!
# Random counter, implementation 1 (a direct `rand #3`)

Ported from clutch/theories/coneris/examples/random_counter3/impl1.v

## Rocq → Lean mapping
* Section `impl1`: the context `H:conerisGS Σ, r1:@rand_spec Σ H, L:randG Σ,
  !inG Σ (frac_authR natR)` is `[conerisGS GF] [r1 : rand_spec GF]
  [ElemG GF frac_auth_natF]`. The section variable `L : randG Σ` is used by no statement or
  proof of the section (the programs call `rand` directly), so the Lean lemmas do not take it;
  in `random_counter1` the Rocq `(L:=counterG1_randG)` arguments are accordingly dropped.
* `new_counter1`, `incr_counter1`, `read_counter1`: transcribed with the `cpl` notation
  (`λ: "_"` is the string binder `λ "_"`, `#3%nat` is `#3`, `FAA` is `faa(..)`).
* `counterG1` (a Rocq `Class` with the fields `counterG1_randG : randG Σ` and the instance
  field `counterG1_frac_authR :: inG Σ (frac_authR natR)`) is a Lean class with the same
  fields, `counterG1_frac_authR : ElemG Σ frac_auth_natF`.
* `counter_inv_pred1`, `is_counter1`, `new_counter_spec1`, `incr_counter_spec1`,
  `read_counter_spec1`: same names. `own γ (●F z)` is `iOwn (F := frac_auth_natF) γ (●F z)`,
  `#l` is `LitV (LitLoc l)`, `#z` (`z : nat`) is `LitV (LitInt z)`.
  Errors are `ℝ≥0∞` (see `RandomCounter`): the hypothesis `⌜∀ x, 0 <= ε2 x⌝` is dropped.
* `random_counter1` (a `Program Definition`) is a definition (not an instance). The own
  instances for the fields are taken from the `counterG1` argument (Rocq: found through the
  `::` instance field). Its `Next Obligation`s are the helper theorems
  `random_counter1_counter_content_*`, proved by the shared helpers `frac_auth_nat_*` of
  `RandomCounter`; the timeless/persistent obligations (automatic in Rocq) are the instances
  `is_counter1_persistent`, `counter_auth1_timeless`, `counter_frag1_timeless`.

## Proofs that differ from Rocq
* `replace (_+_+_+_)%R with 4%R` is the conversion `1 / 4 = 1 / ((3 : ℕ) + 1)` in the call of
  `wp_couple_rand_adv_comp1'`.
* `rewrite -Nat2Z.inj_add` is `push_cast` on the value stored by `FAA`.

## Added
* `counter_auth1`, `counter_frag1` (the `own` assertions, with the `ElemG` instance explicit).
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE CMRA Prob ConProbLang ConProbLang.con_prob_lang
open Coneris Coneris.Lib.HocapRand Coneris.Examples.RandomCounter3.RandomCounter

namespace Coneris.Examples.RandomCounter3.Impl1

section impl1

variable {GF : BundledGFunctors} [conerisGS GF]

/-- Rocq: `new_counter1`. -/
def new_counter1 : val := cpl_val(λ "_", ref(#0))

/-- Rocq: `incr_counter1`. -/
def incr_counter1 : val := cpl_val(λ "l", let "n" := rand(#3) in (faa("l", "n"), "n"))

/-- Rocq: `read_counter1`. -/
def read_counter1 : val := cpl_val(λ "l", !"l")

section counterG1

variable [r1 : rand_spec GF]

/-- Rocq: `counterG1`. -/
class counterG1 (GF' : BundledGFunctors) : Type where
  counterG1_randG : r1.randG GF'
  counterG1_frac_authR : ElemG GF' frac_auth_natF

end counterG1

variable [ElemG GF frac_auth_natF]

/-- `own γ (●F z)`. -/
abbrev counter_auth1 (γ : GName) (z : ℕ) : IProp GF := iOwn (F := frac_auth_natF) γ (●F z)

/-- `own γ (◯F{f} z)`. -/
abbrev counter_frag1 (γ : GName) (f : Qp) (z : ℕ) : IProp GF :=
  iOwn (F := frac_auth_natF) γ (◯F{f} z)

/-- Rocq: `counter_inv_pred1`. -/
def counter_inv_pred1 (c : val) (γ2 : GName) : IProp GF :=
  iprop(∃ (l : Loc) (z : ℕ), ⌜c = LitV (LitLoc l)⌝ ∗ l ↦ LitV (LitInt (z : ℤ)) ∗
    counter_auth1 γ2 z)

/-- Rocq: `is_counter1`. -/
def is_counter1 (N : Namespace) (c : val) (γ1 : GName) : IProp GF :=
  inv N (counter_inv_pred1 c γ1)

instance is_counter1_persistent (N : Namespace) (c : val) (γ1 : GName) :
    Persistent (is_counter1 (GF := GF) N c γ1) := by
  unfold is_counter1; infer_instance

/-- Rocq: `new_counter_spec1`. -/
theorem new_counter_spec1 (E : CoPset) (N : Namespace) :
    {{ True }} cpl(v(&new_counter1) #()) @ E
    {{ c, RET c; ∃ γ1, is_counter1 (GF := GF) N c γ1 ∗ counter_frag1 γ1 1 0 }} := by
  iintro %Φ - HΦ
  unfold new_counter1
  wp_pures
  wp_alloc l as Hl
  imod iOwn_alloc (F := frac_auth_natF) (CMRA.op (●F (0 : ℕ)) (◯F (0 : ℕ))) with ⟨%γ1, H5, H6⟩
  · exact FracAuth.valid trivial
  imod inv_alloc N E (counter_inv_pred1 (LitV (LitLoc l)) γ1) $$ [Hl H5] with #Hinv'
  · inext
    unfold counter_inv_pred1
    iexists l, 0
    iframe
    ipureintro
    rfl
  imodintro
  iapply HΦ
  iexists γ1
  unfold is_counter1
  iframe
  iexact Hinv'

/-- Rocq: `incr_counter_spec1`. -/
theorem incr_counter_spec1 (N : Namespace) (E : CoPset) (c : val) (γ1 : GName)
    (Q : ℝ≥0∞ → (Fin 4 → ℝ≥0∞) → ℕ → ℕ → IProp GF) (Hineq : ↑N ⊆ E) :
    {{ is_counter1 N c γ1 ∗
        |={E \ ↑N, ∅}=>
          (∃ (ε : ℝ≥0∞) (ε2 : Fin 4 → ℝ≥0∞),
            ↯ ε ∗ ⌜∑' n, 1 / 4 * ε2 n ≤ ε⌝ ∗
            (∀ n : Fin 4, ↯ (ε2 n) ={∅, E \ ↑N}=∗
              (∀ z : ℕ, counter_auth1 γ1 z ={E \ ↑N}=∗
                counter_auth1 γ1 (z + n) ∗ Q ε ε2 z n))) }}
      cpl(v(&incr_counter1) v(&c)) @ E
    {{ (z n : ℕ), RET cpl_val((#z, #n)); ∃ ε ε2, Q ε ε2 z n }} := by
  unfold is_counter1 counter_inv_pred1
  iintro %Φ ⟨#Hinv, Hvs⟩ HΦ
  unfold incr_counter1
  wp_pures
  wp_bind (Rand _ _)
  iapply pgl_wp_mask_mono (E1 := E \ ↑N) LawfulSet.diff_subset_left
  imod Hvs with ⟨%ε, %ε2, Herr, %Hsum, Hvs⟩
  wp_apply wp_couple_rand_adv_comp1' 3 3 ε ε2 rfl (by convert Hsum using 3; norm_num) $$ Herr
    with %n Herr
  imod Hvs $$ Herr with Hvs
  imodintro
  wp_pures
  wp_bind (FAA _ _)
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

/-- Rocq: `read_counter_spec1`. -/
theorem read_counter_spec1 (N : Namespace) (E : CoPset) (c : val) (γ1 : GName)
    (Q : ℕ → IProp GF) (Hsubset : ↑N ⊆ E) :
    {{ is_counter1 N c γ1 ∗
        (∀ z : ℕ, counter_auth1 γ1 z ={E \ ↑N}=∗ counter_auth1 γ1 z ∗ Q z) }}
      cpl(v(&read_counter1) v(&c)) @ E
    {{ (n' : ℕ), RET LitV (LitInt (n' : ℤ)); Q n' }} := by
  unfold is_counter1 counter_inv_pred1
  iintro %Φ ⟨#Hinv, Hvs⟩ HΦ
  unfold read_counter1
  wp_pure
  iinv Hinv with ⟨%l, %z, >%Hc, >H5, >H6⟩ Hclose
  subst Hc
  wp_load
  imod Hvs $$ H6 with ⟨H6, HQ⟩
  imod Hclose $$ [H5 H6]
  · inext
    iexists l, z
    iframe
    ipureintro
    trivial
  imodintro
  iapply HΦ $$ HQ

end impl1

/-! ## `random_counter1` -/

section random_counter1

variable {GF : BundledGFunctors} [conerisGS GF] [r1 : rand_spec GF]

/-- Rocq: first `Next Obligation` of `random_counter1`. -/
theorem random_counter1_counter_content_auth_exclusive (L : counterG1 GF) (γ : GName)
    (z1 z2 : ℕ) :
    ⊢ @counter_auth1 GF L.counterG1_frac_authR γ z1 -∗
      @counter_auth1 GF L.counterG1_frac_authR γ z2 -∗ False :=
  @frac_auth_nat_auth_exclusive GF L.counterG1_frac_authR γ z1 z2

/-- Rocq: second `Next Obligation` of `random_counter1`. -/
theorem random_counter1_counter_content_less_than (L : counterG1 GF) (γ : GName) (z z' : ℕ)
    (f : Qp) :
    ⊢ @counter_auth1 GF L.counterG1_frac_authR γ z -∗
      @counter_frag1 GF L.counterG1_frac_authR γ f z' -∗ ⌜z' ≤ z⌝ :=
  @frac_auth_nat_less_than GF L.counterG1_frac_authR γ z z' f

/-- Rocq: third `Next Obligation` of `random_counter1`. -/
theorem random_counter1_counter_content_frag_combine (L : counterG1 GF) (γ : GName)
    (f f' : Qp) (z z' : ℕ) :
    iprop(@counter_frag1 GF L.counterG1_frac_authR γ f z ∗
      @counter_frag1 GF L.counterG1_frac_authR γ f' z') ⊣⊢
      @counter_frag1 GF L.counterG1_frac_authR γ (f + f') (z + z') :=
  @frac_auth_nat_frag_combine GF L.counterG1_frac_authR γ f f' z z'

/-- Rocq: fourth `Next Obligation` of `random_counter1`. -/
theorem random_counter1_counter_content_agree (L : counterG1 GF) (γ : GName) (z z' : ℕ) :
    ⊢ @counter_auth1 GF L.counterG1_frac_authR γ z -∗
      @counter_frag1 GF L.counterG1_frac_authR γ 1 z' -∗ ⌜z' = z⌝ :=
  @frac_auth_nat_agree GF L.counterG1_frac_authR γ z z'

/-- Rocq: fifth `Next Obligation` of `random_counter1`. -/
theorem random_counter1_counter_content_update (L : counterG1 GF) (γ : GName) (f : Qp)
    (z1 z2 z3 : ℕ) :
    ⊢ @counter_auth1 GF L.counterG1_frac_authR γ z1 -∗
      @counter_frag1 GF L.counterG1_frac_authR γ f z2 ==∗
      @counter_auth1 GF L.counterG1_frac_authR γ (z1 + z3) ∗
      @counter_frag1 GF L.counterG1_frac_authR γ f (z2 + z3) :=
  @frac_auth_nat_update GF L.counterG1_frac_authR γ f z1 z2 z3

/-- Rocq: `random_counter1` (a `Program Definition`). -/
@[instance_reducible]
def random_counter1 : random_counter GF where
  new_counter := new_counter1
  incr_counter := incr_counter1
  read_counter := read_counter1
  counterG := counterG1
  counter_name := GName
  is_counter L N c γ1 := @is_counter1 GF _ L.counterG1_frac_authR N c γ1
  counter_content_auth L γ z := @counter_auth1 GF L.counterG1_frac_authR γ z
  counter_content_frag L γ f z := @counter_frag1 GF L.counterG1_frac_authR γ f z
  is_counter_persistent L N c γ1 := @is_counter1_persistent GF _ L.counterG1_frac_authR N c γ1
  counter_content_auth_timeless L _ _ := by let := L.counterG1_frac_authR; exact iOwn_timeless
  counter_content_frag_timeless L _ _ _ := by
    let := L.counterG1_frac_authR; exact iOwn_timeless
  counter_content_auth_exclusive := random_counter1_counter_content_auth_exclusive
  counter_content_less_than := random_counter1_counter_content_less_than
  counter_content_frag_combine := random_counter1_counter_content_frag_combine
  counter_content_agree := random_counter1_counter_content_agree
  counter_content_update := random_counter1_counter_content_update
  new_counter_spec L := @new_counter_spec1 GF _ L.counterG1_frac_authR
  incr_counter_spec L := @incr_counter_spec1 GF _ L.counterG1_frac_authR
  read_counter_spec L := @read_counter_spec1 GF _ L.counterG1_frac_authR

end random_counter1

end Coneris.Examples.RandomCounter3.Impl1
