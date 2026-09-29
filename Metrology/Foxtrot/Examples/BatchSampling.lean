module

public import Metrology.Foxtrot.Lib.Par
public import Metrology.Foxtrot.CouplingRulesMisc
public import Metrology.Foxtrot.BinaryRel.BinarySoundness
public import Metrology.Foxtrot.BinaryRel.BinaryRelTactics
public import Metrology.Foxtrot.AdequacyInstance

/-!
# Batch sampling

Ported from clutch/theories/foxtrot/examples/batch_sampling.v

Sampling two numbers `x ≤ N`, `y ≤ M` in parallel and returning `x * (M + 1) + y` is
contextually equivalent to sampling one number `≤ (N + 1) * (M + 1) - 1`.

## Rocq → Lean map
* `batch_prog`, `batch_prog'`, `rand_prog`, `coupling_f`, `coupling_f_cond1`,
  `coupling_f_cond2`, `coupling_f_cond3`, `wp_batch_prog_batch_prog'`,
  `wp_batch_prog'_rand_prog`, `wp_rand_prog_batch_prog`, `batch_prog_refines_rand_prog`,
  `rand_prog_refines_batch_prog`, `batch_prog_eq_rand_prog`: same names (namespace
  `Foxtrot.Examples.BatchSampling`).
* The section variables `N M : nat` are explicit arguments. As in Rocq (where a section
  variable is only abstracted over when used), `coupling_f` only takes `M`.
* Rocq's `(e1 ||| e2)` is `e1 ‖ e2` (scoped notation of `Foxtrot.Lib.Par`); `let, ("x", "y")`
  is the destructuring `let ("x", "y") := ..; ..`; `#(M+1)` for `M : nat` is `#((M + 1 : ℕ))`
  and `#((S N) * (S M) - 1)` is `#(((N + 1) * (M + 1) - 1 : ℕ))` (truncated subtraction on `ℕ`,
  as in Rocq).
* `#[spawnΣ; foxtrotRΣ]` is the concrete functor list `batchSigma` (with the instances
  `foxtrotRGpreS_batchSigma`, `spawnG_batchSigma`), `foxtrotRΣ` is `foxtrotSigma` (of
  `Metrology.Foxtrot.AdequacyInstance`, with the local instance `foxtrotRGpreS_foxtrotSigma`).

## Deviations
* Texan triples are at mask `⊤` (Rocq: no mask). `lrel_nat v v'` is written
  `(lrel_nat : lrel GF) v v'`.
* The programs are `val`s; the contextual refinements are stated for `Val batch_prog` etc.
  (Rocq's coercion). `TUnit → TNat` is `TArrow TUnit TNat`.
* `wp_couple_rand_rand_lbl` takes the bijection explicitly
  (Rocq: `f` inferred, here `id`), so the returned spec value is `#(id n)`, simplified with
  `simp only [id]`.
* Rocq's `rewrite /interp/=` is `dsimp only [interp, lrel_arr, lrel_unit]`; Rocq's `iIntros
  (??[->->])` is `iintro %v1 %v2 %⟨h1, h2⟩; subst h1 h2`.
* The final `lia` goals (`#(n * (M + 1) + m) = #(n * (M + 1) + m)` after the `ℕ → ℤ` cast) are
  closed by `push_cast; rfl`.

## Added
* `batchSigma`, `foxtrotRGpreS_batchSigma`, `spawnG_batchSigma`,
  `foxtrotRGpreS_foxtrotSigma` (the Rocq functor lists `#[spawnΣ; foxtrotRΣ]` / `foxtrotRΣ`
  with their `subG` instances; iris-lean has no `gFunctors` lists).

## Omitted
None.
-/

@[expose] public section

noncomputable section

open Iris Iris.BI Iris.Std Iris.ProofMode OFE ConProbLang ConProbLang.con_prob_lang
open Foxtrot Foxtrot.BinaryRel Foxtrot.Lib.Spawn Foxtrot.Lib.Par

namespace Foxtrot.Examples.BatchSampling

/-- The functor list of Rocq's `#[spawnΣ; foxtrotRΣ]`: `foxtrotSigma` (Rocq: `foxtrotRΣ`
is `foxtrotΣ`) extended with the token functor of `spawnΣ` at index 8 (defined by delegation
to `foxtrotSigma`, whose indices 0-7 are in use). -/
def batchSigma : BundledGFunctors
  | 8 => ⟨TokenF, by infer_instance⟩
  | n => foxtrotSigma n

/-- Rocq: `subG_foxtrotRGPreS` (at `batchSigma`). -/
instance foxtrotRGpreS_batchSigma : foxtrotRGpreS batchSigma where
  foxtrotRGpreS_foxtrot := {
    foxtrotGpreS_iris := {
      toWsatGpreS := ⟨⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩⟩
      toLcGpreS := ⟨⟨3, rfl⟩⟩ }
    foxtrotGpreS_heap := ⟨⟨4, rfl⟩⟩
    foxtrotGpreS_tapes := ⟨⟨5, rfl⟩⟩
    foxtrotGpreS_spec := ⟨⟨⟨6, rfl⟩⟩, ⟨⟨4, rfl⟩⟩, ⟨⟨5, rfl⟩⟩⟩
    foxtrotGpreS_err := ⟨⟨7, rfl⟩⟩ }

/-- Rocq: `subG_foxtrotRGPreS` (at `foxtrotSigma`, Rocq's `foxtrotRΣ`). -/
local instance foxtrotRGpreS_foxtrotSigma : foxtrotRGpreS foxtrotSigma := ⟨inferInstance⟩

/-- Rocq: `subG_spawnΣ` (at `batchSigma`). -/
instance spawnG_batchSigma : spawnG batchSigma where
  spawn_tokG := ⟨8, rfl⟩

section batch

variable (N M : ℕ)

/-- Rocq: `batch_prog`. -/
def batch_prog : val := cpl_val(
  λ "_",
    let ("x", "y") := ((rand(#N)) ‖ rand(#M));
    "x" * #((M + 1 : ℕ)) + "y")

/-- Rocq: `batch_prog'`. -/
def batch_prog' : val := cpl_val(
  λ "_",
    let "α" := alloc(#N) in
    let "α'" := alloc(#M) in
    let ("x", "y") := ((rand("α") #N) ‖ rand("α'") #M);
    "x" * #((M + 1 : ℕ)) + "y")

/-- Rocq: `rand_prog`. -/
def rand_prog : val := cpl_val(λ "_", rand(#(((N + 1) * (M + 1) - 1 : ℕ))))

/-- Rocq: `coupling_f`. -/
def coupling_f (n m : ℕ) : ℕ := n * (M + 1) + m

/-- Rocq: `coupling_f_cond1`. -/
theorem coupling_f_cond1 (n m : ℕ) (hn : n < N + 1) (hm : m < M + 1) :
    coupling_f M n m < (N + 1) * (M + 1) := by
  unfold coupling_f
  have : n * (M + 1) ≤ N * (M + 1) := Nat.mul_le_mul_right _ (by omega)
  rw [Nat.succ_mul]
  omega

/-- Rocq: `coupling_f_cond2`. -/
theorem coupling_f_cond2 (n n' m m' : ℕ) (_hn : n < N + 1) (_hn' : n' < N + 1)
    (hm : m < M + 1) (hm' : m' < M + 1) (h : coupling_f M n m = coupling_f M n' m') :
    n = n' ∧ m = m' := by
  unfold coupling_f at h
  have h1 : (n * (M + 1) + m) / (M + 1) = n := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hm, Nat.zero_add]
  have h2 : (n' * (M + 1) + m') / (M + 1) = n' := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hm', Nat.zero_add]
  have hnn : n = n' := by rw [← h1, ← h2, h]
  subst hnn
  exact ⟨rfl, by omega⟩

/-- Rocq: `coupling_f_cond3`. -/
theorem coupling_f_cond3 (x : ℕ) (hx : x < (N + 1) * (M + 1)) :
    ∃ n m : ℕ, n < N + 1 ∧ m < M + 1 ∧ coupling_f M n m = x := by
  refine ⟨x / (M + 1), x % (M + 1), ?_, Nat.mod_lt _ (by omega), ?_⟩
  · exact Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hx)
  · unfold coupling_f
    rw [Nat.mul_comm]
    exact Nat.div_add_mod x (M + 1)

section proof

variable {GF : BundledGFunctors} [foxtrotRGS GF] [spawnG GF]

/-- Rocq: `wp_batch_prog_batch_prog'`. -/
theorem wp_batch_prog_batch_prog' (K : List ectx_item) (j : ℕ) :
    {{ j ⤇ fill K cpl(&(batch_prog' N M) #()) }}
      (cpl(&(batch_prog N M) #()))
    {{ v, RET v; ∃ v' : val, j ⤇ fill K (Val v') ∗ (lrel_nat : lrel GF) v v' }} := by
  iintro %Φ Hspec HΦ
  unfold batch_prog' batch_prog
  wp_pures
  tp_pures j
  tp_allocnattape j α as Hα
  tp_pures j
  tp_allocnattape j α' as Hα'
  tp_pure j
  tp_pure j
  tp_bind j cpl(v(&par) _ _)
  imod tp_par $$ Hspec with ⟨%j1, %j2, %K1, %K2, Hspec1, Hspec2, Hcont⟩
  wp_apply wp_par (fun x => iprop(∃ n : ℕ, ⌜x = LitV (LitInt (n : ℤ))⌝ ∗ j1 ⤇ fill K1 (Val (LitV (LitInt (n : ℤ))))))
    (fun x => iprop(∃ m : ℕ, ⌜x = LitV (LitInt (m : ℤ))⌝ ∗ j2 ⤇ fill K2 (Val (LitV (LitInt (m : ℤ))))))
    $$ [Hα Hspec1] [Hα' Hspec2]
  · wp_apply wp_couple_rand_rand_lbl N id Function.bijective_id (N : ℤ) K1 α j1 (by simp)
      (fun n hn => hn) $$ [Hα Hspec1] with %n ⟨-, Hspec1, -⟩
    · iframe Hα Hspec1
    simp only [id]
    iexists n
    iframe Hspec1
    ipureintro
    rfl
  · wp_apply wp_couple_rand_rand_lbl M id Function.bijective_id (M : ℤ) K2 α' j2 (by simp)
      (fun n hn => hn) $$ [Hα' Hspec2] with %m ⟨-, Hspec2, -⟩
    · iframe Hα' Hspec2
    simp only [id]
    iexists m
    iframe Hspec2
    ipureintro
    rfl
  · iintro %v1 %v2 ⟨⟨%n, %Hn, Hspec1⟩, ⟨%m, %Hm, Hspec2⟩⟩
    subst Hn Hm
    inext
    imod Hcont $$ %_ %_ %⊤ [Hspec1 Hspec2] with Hspec
    · iframe Hspec1 Hspec2
    tp_pures j
    wp_pures
    iapply HΦ
    iexists _
    iframe Hspec
    imodintro
    dsimp only [lrel_nat]
    iexists n * (M + 1) + m
    ipureintro
    constructor <;> push_cast <;> rfl

/-- Rocq: `wp_batch_prog'_rand_prog`. -/
theorem wp_batch_prog'_rand_prog (K : List ectx_item) (j : ℕ) :
    {{ j ⤇ fill K cpl(&(rand_prog N M) #()) }}
      (cpl(&(batch_prog' N M) #()))
    {{ v, RET v; ∃ v' : val, j ⤇ fill K (Val v') ∗ (lrel_nat : lrel GF) v v' }} := by
  iintro %Φ Hspec HΦ
  unfold batch_prog' rand_prog
  wp_pures
  wp_alloctape α as Hα
  wp_pures
  wp_alloctape α' as Hα'
  wp_pures
  tp_pures j
  imod pupd_couple_two_tapes_rand N M (coupling_f M) K ⊤ α α' N M _ [] [] j (by simp) (by simp)
    rfl (coupling_f_cond1 N M) (coupling_f_cond2 N M) (coupling_f_cond3 N M)
    $$ [Hα] [Hα'] [Hspec] with ⟨%n, %m, Hα, Hα', Hspec, %Hn, %Hm⟩
  · inext; iexact Hα
  · inext; iexact Hα'
  · iexact Hspec
  simp only [List.nil_append]
  unfold coupling_f
  wp_apply wp_par (fun x => iprop(⌜x = LitV (LitInt (n : ℤ))⌝))
    (fun x => iprop(⌜x = LitV (LitInt (m : ℤ))⌝)) $$ [Hα] [Hα']
  · wp_randtape as %H
    imodintro
    ipureintro
    rfl
  · wp_randtape as %H
    imodintro
    ipureintro
    rfl
  · iintro %v1 %v2 ⟨%H1, %H2⟩
    subst H1 H2
    inext
    wp_pures
    iapply HΦ
    iexists _
    iframe Hspec
    dsimp only [lrel_nat]
    iexists n * (M + 1) + m
    ipureintro
    constructor <;> push_cast <;> rfl

end proof

section proof'

variable {GF : BundledGFunctors} [foxtrotRGS GF]

/-- Rocq: `wp_rand_prog_batch_prog`. -/
theorem wp_rand_prog_batch_prog (K : List ectx_item) (j : ℕ) :
    {{ j ⤇ fill K cpl(&(batch_prog N M) #()) }}
      (cpl(&(rand_prog N M) #()))
    {{ v, RET v; ∃ v' : val, j ⤇ fill K (Val v') ∗ (lrel_nat : lrel GF) v v' }} := by
  iintro %Φ Hspec HΦ
  unfold batch_prog rand_prog
  wp_pures
  tp_pure j
  iapply wp_pupd
  tp_bind j cpl(v(&par) _ _)
  imod tp_par $$ Hspec with ⟨%j1, %j2, %K1, %K2, Hspec1, Hspec2, Hcont⟩
  wp_apply wp_couple_rand_two_rands N M (coupling_f M) K1 K2 N M _ j1 j2 (by simp) (by simp)
    rfl (coupling_f_cond1 N M) (coupling_f_cond2 N M) (coupling_f_cond3 N M)
    $$ [Hspec1 Hspec2] with %x ⟨%n, %m, %Hn, %Hm, %Hx, Hspec1, Hspec2⟩
  · iframe Hspec1 Hspec2
  subst Hx
  imod Hcont $$ %_ %_ %⊤ [Hspec1 Hspec2] with Hspec
  · iframe Hspec1 Hspec2
  tp_pures j
  unfold coupling_f
  iapply HΦ
  iexists _
  iframe Hspec
  dsimp only [lrel_nat]
  iexists n * (M + 1) + m
  ipureintro
  constructor <;> push_cast <;> rfl

end proof'

/-- Rocq: `batch_prog_refines_rand_prog`. -/
theorem batch_prog_refines_rand_prog :
    (∅ : varmap type) ⊨ Val (batch_prog N M) ≤ctx≤ Val (rand_prog N M) : TArrow TUnit TNat := by
  refine ctx_refines_transitive _ _ _ (Val (batch_prog' N M)) _ ?_ ?_ <;>
    refine refines_sound batchSigma _ _ _ fun Δ => ?_
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
    wp_apply wp_batch_prog_batch_prog' N M K' j' $$ Hspec with %v ⟨%v', Hspec, Hv⟩
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
    wp_apply wp_batch_prog'_rand_prog N M K' j' $$ Hspec with %v ⟨%v', Hspec, Hv⟩
    iexists v'
    iframe Hspec Hv

/-- Rocq: `rand_prog_refines_batch_prog`. -/
theorem rand_prog_refines_batch_prog :
    (∅ : varmap type) ⊨ Val (rand_prog N M) ≤ctx≤ Val (batch_prog N M) : TArrow TUnit TNat := by
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
  wp_apply wp_rand_prog_batch_prog N M K' j' $$ Hspec with %v ⟨%v', Hspec, Hv⟩
  iexists v'
  iframe Hspec Hv

/-- Rocq: `batch_prog_eq_rand_prog`. -/
theorem batch_prog_eq_rand_prog :
    (∅ : varmap type) ⊨ Val (batch_prog N M) =ctx= Val (rand_prog N M) : TArrow TUnit TNat :=
  ⟨batch_prog_refines_rand_prog N M, rand_prog_refines_batch_prog N M⟩

end batch

end Foxtrot.Examples.BatchSampling
