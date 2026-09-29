module

public import Metrology.Coneris.ErrorRules
public import Metrology.Coneris.Atomic

/-!
# Hocap atomic rand specs

Ported from clutch/theories/coneris/lib/hocap_rand_atomic.v

The sampling operation is atomic. This allows tapes to be placed within invariants.
Note that this spec does not support compressing multiple rands,
e.g. simulating a rand 3 with two rand 1s.

## Rocq → Lean mapping
* `Class rand_atomic_spec (tb:nat) `{!conerisGS Σ}` is `class rand_atomic_spec (tb : ℕ) GF`
  (over `[conerisGS GF]`) with the same field names. As in `Coneris.Lib.HocapRand`:
  errors are `ℝ≥0∞` (the hypothesis `∀ x, 0 <= ε2 x` is dropped), `Forall` is `∀ n ∈ ns, ..`,
  magic wands are stated as `⊢ P -∗ Q`, the `Timeless` instance field is re-exported as the
  instance `rand_atomic_spec_rand_tapes_timeless`.
* The logically atomic triple `<<{∀∀ n ns, rand_tapes α (n::ns) }>> rand_tape α @ E
  <<{ rand_tapes α ns | RET #n }>>` is written with iris-lean's notation, which elaborates to
  `Coneris.atomic_wp` (`Metrology.Coneris.Atomic`).
* Section `impl`: `rand_tapes1` and `rand_atomic_spec1` (Rocq: `#[local] Program Definition`, a
  definition here); the `Next Obligation`s are the helper theorems `rand_atomic_spec1_*`.
* Section `impl3` (the rejection sampler): `rand_tapes3` and `rand_atomic_spec3`, with
  obligations `rand_atomic_spec3_*` (in `Coneris.Lib.HocapRandAtomicPart2`).
  `filter (λ x, x <= tb) ns'` is `ns'.filter (fun x => decide (x ≤ tb))`.

## Proofs that differ from Rocq
* `wp_atomic_rand_tape_1` and the atomic obligations reduce the concrete telescopes of the
  atomic triples with the helper tactic `tele_simp` (Rocq's `iAaccIntro`/`simpl` do this
  implicitly); `iMod "AU" as "(%&%&H&[AU _])"` is `imod AU with ⟨%⟨n, ns, ⟨⟩⟩, H, AU, -⟩`.

## Added
* `tele_simp` (tactic), `rand_tapes1_timeless` (Rocq infers it).

## Omitted
* `Local Opaque INR`: Rocq-specific.
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang

namespace Coneris.Lib.HocapRandAtomic

/-- Helper (not in Rocq, whose `iAaccIntro`/`simpl` reduce telescopes): simplify the telescope
applications and quantifiers of an atomic triple for concrete telescopes. -/
macro "tele_simp" : tactic =>
  `(tactic| simp only [Tele.app, Tele.lam, Tele.bind, Tele.app_bind, BI.tforall_nil,
    BI.tforall_cons, BI.texist_nil, BI.texist_cons, BIBase.wandM])

/-- Rocq: `rand_atomic_spec`. -/
class rand_atomic_spec (tb : ℕ) (GF : BundledGFunctors) [conerisGS GF] where
  -- * Operations
  rand_allocate_tape : val
  rand_tape : val
  -- * Predicates
  rand_tapes (α : val) (ns : List ℕ) : IProp GF
  -- * General properties of the predicates
  rand_tapes_timeless (α : val) (ns : List ℕ) : Timeless (rand_tapes α ns)
  rand_tapes_exclusive (α : val) (ns ns' : List ℕ) :
    ⊢ rand_tapes α ns -∗ rand_tapes α ns' -∗ False
  rand_tapes_valid (α : val) (ns : List ℕ) : ⊢ rand_tapes α ns -∗ ⌜∀ n ∈ ns, n ≤ tb⌝
  rand_tapes_presample (E : CoPset) (α : val) (ns : List ℕ) (ε : ℝ≥0∞)
    (ε2 : Fin (tb + 1) → ℝ≥0∞) (Hsum : ∑' n, 1 / ((tb : ℝ≥0∞) + 1) * ε2 n ≤ ε) :
    ⊢ rand_tapes α ns -∗ ↯ ε -∗
      state_update E E iprop(∃ n : Fin (tb + 1), ↯ (ε2 n) ∗ rand_tapes α (ns ++ [(n : ℕ)]))
  -- * Program specs
  rand_allocate_tape_spec (E : CoPset) :
    {{ True }} cpl(v(&rand_allocate_tape) #()) @ E {{ v, RET v; rand_tapes v [] }}
  rand_tape_spec_some (E : CoPset) (α : val) :
    ⊢ iprop(<<{ ∀∀ (n : ℕ) (ns : List ℕ), rand_tapes α (n :: ns) }>>
      cpl(v(&rand_tape) v(&α)) @ E
      <<{ rand_tapes α ns | RET LitV (LitInt (n : ℤ)) }>>)

/-- Rocq: `#[global] rand_tapes_timeless` (the instance). -/
instance rand_atomic_spec_rand_tapes_timeless {tb : ℕ} {GF : BundledGFunctors} [conerisGS GF]
    [r : rand_atomic_spec tb GF] (α : val) (ns : List ℕ) : Timeless (r.rand_tapes α ns) :=
  r.rand_tapes_timeless α ns

/-! ## Checks -/

section checks

variable {GF : BundledGFunctors} [conerisGS GF] {tb : ℕ} [r1 : rand_atomic_spec tb GF]

/-- Rocq: `wp_atomic_rand_tape_1`. -/
theorem wp_atomic_rand_tape_1 (n : ℕ) (ns : List ℕ) (α : val) :
    {{ ▷ r1.rand_tapes α (n :: ns) }} cpl(v(&r1.rand_tape) v(&α))
    {{ RET LitV (LitInt (n : ℤ)); r1.rand_tapes α ns ∗ ⌜n ≤ tb⌝ }} := by
  iintro %Φ >Hfrag HΦ
  iapply pgl_wp_step_fupd rfl LawfulSet.subset_refl $$ [HΦ]
  · imodintro; inext; imodintro; iexact HΦ
  ihave %H' := r1.rand_tapes_valid α (n :: ns) $$ Hfrag
  awp_apply r1.rand_tape_spec_some ∅ α
  iaaccintro %⟨n, ns, ⟨⟩⟩ [Hfrag]
  · tele_simp
    iexact Hfrag
  · tele_simp
    iintro H; imodintro; iexact H
  · tele_simp
    iintro H
    imodintro
    iintro HΦ
    iapply HΦ
    imodintro
    iframe H
    ipureintro
    exact H' n List.mem_cons_self

end checks

/-! ## Implementation 1 -/

section impl

variable (tb : ℕ) {GF : BundledGFunctors} [conerisGS GF]

/-- Rocq: `rand_tapes1`. -/
def rand_tapes1 (α : val) (ns : List ℕ) : IProp GF :=
  iprop(∃ α' : Loc, ⌜α = LitV (LitLbl α')⌝ ∗ α' ↪N (tb; ns))

instance rand_tapes1_timeless (α : val) (ns : List ℕ) :
    Timeless (rand_tapes1 (GF := GF) tb α ns) := by
  unfold rand_tapes1; infer_instance

/-- Rocq: `rand_allocate_tape` of `rand_atomic_spec1`. -/
def rand_allocate_tape1 : val := cpl_val(λ <>, alloc(#tb))

/-- Rocq: `rand_tape` of `rand_atomic_spec1`. -/
def rand_tape1 : val := cpl_val(λ α, rand(α) #tb)

/-- Rocq: first `Next Obligation` of `rand_atomic_spec1`. -/
theorem rand_atomic_spec1_rand_tapes_exclusive (α : val) (ns ns' : List ℕ) :
    ⊢@{IProp GF} rand_tapes1 tb α ns -∗ rand_tapes1 tb α ns' -∗ False := by
  unfold rand_tapes1
  iintro ⟨%a1, %h1, H1⟩ ⟨%a2, %h2, H2⟩
  rw [h1] at h2
  cases h2
  iapply tapeN_tapeN_contradict $$ H1 H2

/-- Rocq: second `Next Obligation` of `rand_atomic_spec1`. -/
theorem rand_atomic_spec1_rand_tapes_valid (α : val) (ns : List ℕ) :
    ⊢@{IProp GF} rand_tapes1 tb α ns -∗ ⌜∀ n ∈ ns, n ≤ tb⌝ := by
  unfold rand_tapes1
  iintro ⟨%a, -, H⟩
  iapply tapeN_ineq $$ H

/-- Rocq: third `Next Obligation` of `rand_atomic_spec1`. -/
theorem rand_atomic_spec1_rand_tapes_presample (E : CoPset) (α : val) (ns : List ℕ)
    (ε : ℝ≥0∞) (ε2 : Fin (tb + 1) → ℝ≥0∞) (Hsum : ∑' n, 1 / ((tb : ℝ≥0∞) + 1) * ε2 n ≤ ε) :
    ⊢@{IProp GF} rand_tapes1 tb α ns -∗ ↯ ε -∗
      state_update E E iprop(∃ n : Fin (tb + 1), ↯ (ε2 n) ∗ rand_tapes1 tb α (ns ++ [(n : ℕ)])) := by
  unfold rand_tapes1
  iintro ⟨%a, %h, H⟩ Herr
  imod state_update_presample_exp E a tb ns ε ε2 Hsum $$ H Herr with ⟨%n, H, Herr⟩
  imodintro
  iexists n
  iframe Herr
  iexists a
  iframe H
  ipureintro
  exact h

/-- Rocq: fourth `Next Obligation` of `rand_atomic_spec1`. -/
theorem rand_atomic_spec1_rand_allocate_tape_spec (E : CoPset) :
    {{ True }} cpl(v(&(rand_allocate_tape1 tb)) #()) @ E
    {{ v, RET v; rand_tapes1 (GF := GF) tb v [] }} := by
  iintro %Φ - HΦ
  wp_lam
  wp_alloctape α as Hα
  iapply HΦ
  unfold rand_tapes1
  iexists α
  iframe Hα
  ipureintro
  rfl

/-- Rocq: fifth `Next Obligation` of `rand_atomic_spec1`. -/
theorem rand_atomic_spec1_rand_tape_spec_some (E : CoPset) (α : val) :
    ⊢@{IProp GF} iprop(<<{ ∀∀ (n : ℕ) (ns : List ℕ), rand_tapes1 tb α (n :: ns) }>>
      cpl(v(&(rand_tape1 tb)) v(&α)) @ E
      <<{ rand_tapes1 tb α ns | RET LitV (LitInt (n : ℤ)) }>>) := by
  iunfold atomic_wp
  iintro %Φ AU
  wp_lam
  iapply fupd_pgl_wp
  imod AU with ⟨%⟨n, ns, ⟨⟩⟩, Ht, Habort, -⟩
  tele_simp
  iunfold rand_tapes1 at Ht
  icases Ht with ⟨%a, %h, Ht⟩
  subst h
  imod Habort $$ [Ht] with AU
  · iunfold rand_tapes1
    iexists a
    iframe Ht
    ipureintro
    rfl
  imodintro
  imod AU with ⟨%⟨n', ns', ⟨⟩⟩, Ht, -, Hcommit⟩
  tele_simp
  iunfold rand_tapes1 at Ht
  icases Ht with ⟨%a', %h, Ht⟩
  cases h
  wp_randtape as %_
  imod Hcommit $$ [Ht] with HΦ
  · iunfold rand_tapes1
    iexists a
    iframe Ht
    ipureintro
    rfl
  imodintro
  iexact HΦ

/-- Rocq: `rand_atomic_spec1` (a `#[local] Program Definition`). -/
@[instance_reducible]
def rand_atomic_spec1 : rand_atomic_spec tb GF where
  rand_allocate_tape := rand_allocate_tape1 tb
  rand_tape := rand_tape1 tb
  rand_tapes := rand_tapes1 tb
  rand_tapes_timeless := rand_tapes1_timeless tb
  rand_tapes_exclusive := rand_atomic_spec1_rand_tapes_exclusive tb
  rand_tapes_valid := rand_atomic_spec1_rand_tapes_valid tb
  rand_tapes_presample := rand_atomic_spec1_rand_tapes_presample tb
  rand_allocate_tape_spec := rand_atomic_spec1_rand_allocate_tape_spec tb
  rand_tape_spec_some := rand_atomic_spec1_rand_tape_spec_some tb

end impl

end Coneris.Lib.HocapRandAtomic
