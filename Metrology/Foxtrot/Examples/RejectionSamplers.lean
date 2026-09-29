module

public import Metrology.Foxtrot.CouplingRulesMisc
public import Metrology.Foxtrot.BinaryRel.BinarySoundness
public import Metrology.Foxtrot.BinaryRel.BinaryRelTactics
public import Metrology.Foxtrot.AdequacyInstance

/-!
# Rejection samplers

Ported from clutch/theories/foxtrot/examples/rejection_samplers.v

For `M < N`, the rejection sampler that samples `x ≤ N` until `x ≤ M` is contextually
equivalent to directly sampling a number `≤ M`.

## Rocq → Lean map
* `NM1`, `NMpos`, `rejection_sampler_prog`, `rand_prog`, `rand_prog'`,
  `wp_rejection_sampler_prog_rand_prog`, `wp_rand_prog_rand_prog'`,
  `wp_rand_prog'_rejection_sampler_prog`, `rejection_sampler_prog_refines_rand_prog`,
  `rand_prog_refines_rejection_sampler_prog`, `rejection_sampler_prog_eq_rand_prog`: same names
  (namespace `Foxtrot.Examples.RejectionSamplers`).
* The section variables `N M : nat` and the hypothesis `Hineq : M < N` are explicit arguments
  (with Rocq's `Default Proof Using "Type*"`, `Hineq` is abstracted over by every lemma of the
  section; the programs only take `N M`).
* `foxtrotRΣ` / `#[foxtrotRΣ]` is `foxtrotSigma` (of `Metrology.Foxtrot.AdequacyInstance`),
  with the instance `foxtrotRGpreS_foxtrotSigma`.
* `ec_ind_simpl` is iris-lean's `ErrorCredit.Induction.simple`, whose amplification factor
  is an `ℝ≥0`; Rocq's real `S N / (S N - S M)` is `rs_k N M : ℝ≥0` (below), and `rs_k_coe`
  identifies its `ℝ≥0∞` cast with the factor `(N+1)/((N+1) - (M+1))` produced by
  `pupd_couple_fragmented_tape_rand_inj_rev'`.

## Deviations
* Reals are replaced by `ℝ≥0∞` (errors) / `ℝ≥0` (the amplification factor). `NM1` / `NMpos`
  are stated for the `ℝ≥0∞` factor `((N+1 : ℕ) : ℝ≥0∞) / ((N+1 : ℕ) - (M+1 : ℕ))` (whose
  subtraction is truncated, but `M < N` makes it positive, so neither the truncation nor
  `x / 0 = ∞` applies).
* Texan triples are at mask `⊤` (Rocq: no mask). `lrel_nat v v'` is
  `(lrel_nat : lrel GF) v v'`. The programs are `val`s; the refinements are stated for
  `Val rejection_sampler_prog` etc. `TUnit → TNat` is `TArrow TUnit TNat`.
* Rocq's `iRevert "Hspec HΦ Hα"; iApply (ec_ind_simpl _ k with "[][$]")` applies
  `ErrorCredit.Induction.simple` with the proposition `P` (the reverted goal) given
  explicitly.
* The couplings take the injection / bijection `id` explicitly (Rocq: `id` / inferred).
* `bool_decide_eq_true_2` / `bool_decide_eq_false_2` are `decide_eq_true` / `decide_eq_false`.
* `Local Hint Resolve NM1 NMpos` has no counterpart (the lemmas are applied explicitly).

## Added
* `rs_k`, `rs_k_coe`, `rs_k_one_lt` (the `ℝ≥0` amplification factor, see above);
  `foxtrotRGpreS_foxtrotSigma` (Rocq: `subG_foxtrotRGPreS`).

## Omitted
None.
-/

@[expose] public section

noncomputable section

open scoped ENNReal NNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE ConProbLang ConProbLang.con_prob_lang
open Foxtrot Foxtrot.BinaryRel

namespace Foxtrot.Examples.RejectionSamplers

/-- Rocq: `subG_foxtrotRGPreS` (at `foxtrotSigma`, Rocq's `foxtrotRΣ`). -/
instance foxtrotRGpreS_foxtrotSigma : foxtrotRGpreS foxtrotSigma := ⟨inferInstance⟩

section rejection_sampler

variable (N M : ℕ)

/-- Rocq: `NM1`. -/
theorem NM1 (Hineq : M < N) :
    1 < ((N + 1 : ℕ) : ℝ≥0∞) / (((N + 1 : ℕ) : ℝ≥0∞) - ((M + 1 : ℕ) : ℝ≥0∞)) := by
  have hsub : ((N + 1 : ℕ) : ℝ≥0∞) - ((M + 1 : ℕ) : ℝ≥0∞) = ((N - M : ℕ) : ℝ≥0∞) := by
    rw [← ENNReal.natCast_sub]; congr 1; omega
  rw [hsub, ENNReal.lt_div_iff_mul_lt (by simp) (by simp), one_mul]
  exact_mod_cast (by omega : N - M < N + 1)

/-- Rocq: `NMpos`. -/
theorem NMpos (Hineq : M < N) :
    0 < ((N + 1 : ℕ) : ℝ≥0∞) / (((N + 1 : ℕ) : ℝ≥0∞) - ((M + 1 : ℕ) : ℝ≥0∞)) :=
  lt_trans zero_lt_one (NM1 N M Hineq)

/-- Added: Rocq's real `S N / (S N - S M)` as an `ℝ≥0` (the factor of `ec_ind_simpl`). -/
def rs_k : ℝ≥0 := ((N + 1 : ℕ) : ℝ≥0) / ((N - M : ℕ) : ℝ≥0)

/-- Added: the `ℝ≥0∞` cast of `rs_k` is the factor of
`pupd_couple_fragmented_tape_rand_inj_rev'`. -/
theorem rs_k_coe (Hineq : M < N) :
    ((rs_k N M : ℝ≥0) : ℝ≥0∞) =
      ((N + 1 : ℕ) : ℝ≥0∞) / (((N + 1 : ℕ) : ℝ≥0∞) - ((M + 1 : ℕ) : ℝ≥0∞)) := by
  have hsub : ((N + 1 : ℕ) : ℝ≥0∞) - ((M + 1 : ℕ) : ℝ≥0∞) = ((N - M : ℕ) : ℝ≥0∞) := by
    rw [← ENNReal.natCast_sub]; congr 1; omega
  rw [hsub, rs_k, ENNReal.coe_div (Nat.cast_ne_zero.mpr (by omega))]
  simp

/-- Added: `1 < rs_k` (Rocq: `NM1`, for the `ℝ≥0` factor). -/
theorem rs_k_one_lt (Hineq : M < N) : 1 < rs_k N M := by
  have h := NM1 N M Hineq
  rw [← rs_k_coe N M Hineq] at h
  exact_mod_cast h

/-- Rocq: `rejection_sampler_prog`. -/
def rejection_sampler_prog : val := cpl_val(
  rec "f" "_" :=
    let "x" := rand(#N) in
    if ("x" ≤ #M) then "x"
    else "f" #())

/-- Rocq: `rand_prog`. -/
def rand_prog : val := cpl_val(
  λ "_", rand(#M))

/-- Rocq: `rand_prog'`. -/
def rand_prog' : val := cpl_val(
  λ "_", let "x" := alloc(#M) in rand("x") #M)

section proof

variable {GF : BundledGFunctors} [foxtrotRGS GF]

/-- Rocq: `wp_rejection_sampler_prog_rand_prog`. -/
theorem wp_rejection_sampler_prog_rand_prog (Hineq : M < N) (K : List ectx_item) (j : ℕ) :
    {{ j ⤇ fill K cpl(&(rand_prog M) #()) }}
      (cpl(&(rejection_sampler_prog N M) #()))
    {{ v, RET v; ∃ v' : val, j ⤇ fill K (Val v') ∗ (lrel_nat : lrel GF) v v' }} := by
  iintro %Φ Hspec HΦ
  unfold rand_prog
  tp_pures j
  unfold rejection_sampler_prog
  iloeb as IH generalizing Hspec HΦ
  wp_pures
  wp_bind (Rand _ _)
  wp_apply wp_couple_fragmented_rand_rand_inj id Function.injective_id j K (le_of_lt Hineq)
      (fun n hn => by simp only [id]; omega) $$ Hspec
    with %n ⟨%Hn, (⟨%m, %Hm, %Hfm, Hspec⟩ | ⟨%Hfalse, Hspec⟩)⟩
  · simp only [id] at Hfm
    subst Hfm
    wp_pures
    rw [decide_eq_true (by exact_mod_cast Hm)]
    wp_pures
    iapply HΦ
    iexists _
    iframe Hspec
    dsimp only [lrel_nat]
    iexists m
    ipureintro
    exact ⟨rfl, rfl⟩
  · wp_pures
    rw [decide_eq_false (by
      intro H'
      exact Hfalse ⟨n, by exact_mod_cast H', rfl⟩)]
    wp_pure
    iapply IH $$ Hspec [HΦ]
    inext
    iexact HΦ

end proof

section proof'

variable {GF : BundledGFunctors} [foxtrotRGS GF]

/-- Rocq: `wp_rand_prog_rand_prog'`. -/
theorem wp_rand_prog_rand_prog' (_Hineq : M < N) (K : List ectx_item) (j : ℕ) :
    {{ j ⤇ fill K cpl(&(rand_prog' M) #()) }}
      (cpl(&(rand_prog M) #()))
    {{ v, RET v; ∃ v' : val, j ⤇ fill K (Val v') ∗ (lrel_nat : lrel GF) v v' }} := by
  iintro %Φ Hspec HΦ
  unfold rand_prog rand_prog'
  tp_pures j
  wp_pures
  tp_allocnattape j α as Hα
  tp_pures j
  wp_apply wp_couple_rand_rand_lbl M id Function.bijective_id (M : ℤ) K α j (by simp)
    (fun n hn => hn) $$ [Hα Hspec] with %n ⟨-, Hspec, %Hn⟩
  · iframe Hα Hspec
  iapply HΦ
  iexists _
  iframe Hspec
  dsimp only [lrel_nat]
  iexists n
  ipureintro
  exact ⟨rfl, rfl⟩

/-- Rocq: `wp_rand_prog'_rejection_sampler_prog`. -/
theorem wp_rand_prog'_rejection_sampler_prog (Hineq : M < N) (K : List ectx_item) (j : ℕ) :
    {{ j ⤇ fill K cpl(&(rejection_sampler_prog N M) #()) }}
      (cpl(&(rand_prog' M) #()))
    {{ v, RET v; ∃ v' : val, j ⤇ fill K (Val v') ∗ (lrel_nat : lrel GF) v v' }} := by
  iintro %Φ Hspec HΦ
  unfold rand_prog'
  wp_pures
  wp_alloctape α as Hα
  wp_pures
  imod pupd_epsilon_err ⊤ with ⟨%ε, %Hε, Herr⟩
  ihave Hind := ErrorCredit.Induction.simple (k := rs_k N M)
      (P := iprop(j ⤇ fill K cpl(&(rejection_sampler_prog N M) #()) -∗
        (∀ v, (∃ v' : val, j ⤇ fill K (Val v') ∗ (lrel_nat : lrel GF) v v') -∗ Φ v) -∗
        α ↪N (M; []) -∗ WP cpl(rand(#lbl(α)) #M) {{ Φ }})) Hε (rs_k_one_lt N M Hineq)
      $$ [] Herr
  · imodintro
    iintro ⟨Hind, Herr⟩ Hspec HΦ Hα
    unfold rejection_sampler_prog
    tp_pures j
    tp_bind j (Rand _ _)
    imod pupd_couple_fragmented_tape_rand_inj_rev' (M := N) (N := M) id Function.injective_id
        [] α j _ ⊤ ε Hineq (fun n hn => by simp only [id]; omega) $$ [Hα] Herr Hspec
      with ⟨%m, %Hm, Hspec, (⟨%n, %Hn, %Hfn, Hα⟩ | ⟨%Hfalse, Hα, Herr⟩)⟩
    · inext
      iexact Hα
    · simp only [id] at Hfn
      subst Hfn
      tp_pures j
      rw [decide_eq_true (by exact_mod_cast Hn)]
      tp_pures j
      wp_randtape
      iapply HΦ
      iexists _
      iframe Hspec
      dsimp only [lrel_nat]
      iexists n
      ipureintro
      exact ⟨rfl, rfl⟩
    · tp_pures j
      rw [decide_eq_false (by
        intro H'
        exact Hfalse ⟨m, by exact_mod_cast H', rfl⟩)]
      tp_pure j
      iapply Hind $$ [Herr] Hspec HΦ Hα
      iapply ErrorCredit.ext (by rw [rs_k_coe N M Hineq]) $$ Herr
  iapply Hind $$ Hspec HΦ Hα

end proof'

/-- Rocq: `rejection_sampler_prog_refines_rand_prog`. -/
theorem rejection_sampler_prog_refines_rand_prog (Hineq : M < N) :
    (∅ : varmap type) ⊨ Val (rejection_sampler_prog N M) ≤ctx≤ Val (rand_prog M) :
      TArrow TUnit TNat := by
  refine refines_sound foxtrotSigma _ _ _ fun Δ => ?_
  unfold_rel
  iintro %K %j Hspec
  wp_pures
  iexists _
  iframe Hspec
  imodintro
  dsimp only [interp, lrel_arr, lrel_unit]
  imodintro
  iintro %v1 %v2 %⟨h1, h2⟩
  subst h1 h2
  unfold_rel
  iintro %K' %j' Hspec
  wp_apply wp_rejection_sampler_prog_rand_prog N M Hineq K' j' $$ Hspec with %v ⟨%v', Hspec, Hv⟩
  iexists v'
  iframe Hspec Hv

/-- Rocq: `rand_prog_refines_rejection_sampler_prog`. -/
theorem rand_prog_refines_rejection_sampler_prog (Hineq : M < N) :
    (∅ : varmap type) ⊨ Val (rand_prog M) ≤ctx≤ Val (rejection_sampler_prog N M) :
      TArrow TUnit TNat := by
  refine ctx_refines_transitive _ _ _ (Val (rand_prog' M)) _ ?_ ?_ <;>
    refine refines_sound foxtrotSigma _ _ _ fun Δ => ?_
  · unfold_rel
    iintro %K %j Hspec
    wp_pures
    iexists _
    iframe Hspec
    imodintro
    dsimp only [interp, lrel_arr, lrel_unit]
    imodintro
    iintro %v1 %v2 %⟨h1, h2⟩
    subst h1 h2
    unfold_rel
    iintro %K' %j' Hspec
    wp_apply wp_rand_prog_rand_prog' N M Hineq K' j' $$ Hspec with %v ⟨%v', Hspec, Hv⟩
    iexists v'
    iframe Hspec Hv
  · unfold_rel
    iintro %K %j Hspec
    wp_pures
    iexists _
    iframe Hspec
    imodintro
    dsimp only [interp, lrel_arr, lrel_unit]
    imodintro
    iintro %v1 %v2 %⟨h1, h2⟩
    subst h1 h2
    unfold_rel
    iintro %K' %j' Hspec
    wp_apply wp_rand_prog'_rejection_sampler_prog N M Hineq K' j' $$ Hspec with %v ⟨%v', Hspec, Hv⟩
    iexists v'
    iframe Hspec Hv

/-- Rocq: `rejection_sampler_prog_eq_rand_prog`. -/
theorem rejection_sampler_prog_eq_rand_prog (Hineq : M < N) :
    (∅ : varmap type) ⊨ Val (rejection_sampler_prog N M) =ctx= Val (rand_prog M) :
      TArrow TUnit TNat :=
  ⟨rejection_sampler_prog_refines_rand_prog N M Hineq,
    rand_prog_refines_rejection_sampler_prog N M Hineq⟩

end rejection_sampler

end Foxtrot.Examples.RejectionSamplers
