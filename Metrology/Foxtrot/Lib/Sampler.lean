module

public import Metrology.Foxtrot.SpecProofMode
public import Metrology.Foxtrot.CouplingRulesMisc

/-!
# An abstract spec for samplers

Ported from clutch/theories/foxtrot/lib/sampler.v

An abstract spec (`sample_spec tb sample_without_tape`) for a module that samples a number from
`0` to `tb`, with an unknown distribution, with (`sample_with_tape`) or without
(`sample_without_tape`) a tape, and two implementations: `sample_spec1` (uniform sampling with
`rand`) and `sample_spec2` (always `0`).

## Rocq → Lean map
* `sample_spec` (constructor `SampleSpec`) with the fields `sample_allocate_tape`,
  `sample_with_tape`, `sample_tape`, `sample_tape'`, `sample_tape_timeless`,
  `sample_tape_timeless'`, `sample_tape_exclusive`, `sample_tape_exclusive'`,
  `sample_tape_valid`, `sample_tape_presample`, `sample_allocate_tape_spec`,
  `sample_allocate_tape_spec'`, `sample_tape_spec_some`, `sample_tape_spec_couple'`,
  `sample_without_tape_spec'`: same names.
* `sample_spec1`, `sample_spec2`: same names. The Rocq `Program Definition` obligations are the
  lemmas `sample_spec1_<field>` / `sample_spec2_<field>`, and the predicates are the defs
  `sample_spec1_tape`, `sample_spec1_tape'`, `sample_spec2_tape`, `sample_spec2_tape'`.

## Deviations
* The fields quantifying over `` `{!foxtrotGS Σ} `` quantify over `{GF : BundledGFunctors}
  [foxtrotGS GF]` (placed first, before the other arguments); the fields that are WP specs also
  quantify over the (ignored) stuckness `{s : Stuckness}` of the Foxtrot WP.
* `#[global] sample_tape_timeless ::` are made global instances with `attribute [instance]`.
* `fin (S tb)` is `Fin (tb + 1)`, and `#n` for `n : Fin (tb + 1)` is
  `LitV (LitInt ((n : ℕ) : ℤ))`; `fin_to_nat n` is `(n : ℕ)`, `nat_to_fin K` is `⟨n, K⟩`.
* `Forall (λ n, n ≤ tb) ns` is `∀ n ∈ ns, n ≤ tb`, `Forall (λ x, x = 0) ns` is
  `∀ x ∈ ns, x = 0` (as `tapeN_ineq` in `Foxtrot.PrimitiveLaws`).
* Rocq's `P -∗ Q -∗ False` fields are `⊢ P -∗ Q -∗ False`, Rocq's `P -∗ pupd E E Q` fields are
  entailments `P ⊢ pupd E E Q`, Rocq's `{{{ P }}} e @ E {{{ .. }}}` are iris-lean Texan triples.
* `#[local] Program Definition sample_spec1 (tb : nat) `{!foxtrotGS Σ}` is a plain `def` (not an
  instance) without the unused `foxtrotGS` argument.
* `sample_spec1`, `sample_tape_spec_couple'`: Rocq applies `wp_couple_rand_rand_lbl` with the
  bijection found by instance search (`id`); here `f := id` explicitly.

## Omitted
* The commented-out fields (`sample_f`, the error-credit variant of `sample_tape_presample`,
  `sample_tape_spec_couple`, `sample_tape_spec_some'` and its error-credit variant) and the
  commented-out obligations of `sample_spec1`/`sample_spec2`.

## Added
* `nat_spec_tape_timeless` (the spec tape `α ↪ₛN (N; ns)` is timeless; Rocq infers it by
  unfolding, and the Lean core files lack the instance).
-/

@[expose] public section

open Iris Iris.BI Iris.Std Iris.ProofMode OFE ConProbLang ConProbLang.con_prob_lang

namespace Foxtrot.Lib.Sampler

/-- Added helper: the spec tape `α ↪ₛN (N; ns)` is timeless. -/
instance nat_spec_tape_timeless {GF : BundledGFunctors} [specG_con_prob_lang GF] (l : Loc)
    (N : ℕ) (ns : List ℕ) : Timeless (l ↪ₛN (N; ns) : IProp GF) := by
  unfold nat_spec_tape spec_tapes_frag
  infer_instance

/-- Rocq: `sample_spec`. An abstract spec for a module that samples a number from `0` to `tb`,
but with an unknown distribution. -/
class sample_spec (tb : ℕ) (sample_without_tape : val) where
  SampleSpec ::
  -- Operations
  sample_allocate_tape : val
  sample_with_tape : val
  -- Predicates
  sample_tape {GF : BundledGFunctors} [foxtrotGS GF] (α : val) (ns : List ℕ) : IProp GF
  sample_tape' {GF : BundledGFunctors} [foxtrotGS GF] (α : val) : IProp GF
  -- General properties of the predicates
  sample_tape_timeless {GF : BundledGFunctors} [foxtrotGS GF] (α : val) (ns : List ℕ) :
    Timeless (sample_tape (GF := GF) α ns)
  sample_tape_timeless' {GF : BundledGFunctors} [foxtrotGS GF] (α : val) :
    Timeless (sample_tape' (GF := GF) α)
  sample_tape_exclusive {GF : BundledGFunctors} [foxtrotGS GF] (α : val) (ns ns' : List ℕ) :
    ⊢@{IProp GF} sample_tape α ns -∗ sample_tape α ns' -∗ False
  sample_tape_exclusive' {GF : BundledGFunctors} [foxtrotGS GF] (α : val) :
    ⊢@{IProp GF} sample_tape' α -∗ sample_tape' α -∗ False
  sample_tape_valid {GF : BundledGFunctors} [foxtrotGS GF] (α : val) (ns : List ℕ) :
    sample_tape α ns ⊢@{IProp GF} ⌜∀ n ∈ ns, n ≤ tb⌝
  sample_tape_presample {GF : BundledGFunctors} [foxtrotGS GF] (E : CoPset) (α : val)
      (ns : List ℕ) :
    sample_tape α ns ⊢@{IProp GF}
      pupd E E iprop(∃ n : Fin (tb + 1), sample_tape α (ns ++ [(n : ℕ)]))
  -- Program specs
  sample_allocate_tape_spec {GF : BundledGFunctors} [foxtrotGS GF] {s : Stuckness}
      (E : CoPset) :
    {{ True }} (cpl(&sample_allocate_tape #())) @ s; E
    {{ (v : val), RET v; (sample_tape v [] : IProp GF) }}
  sample_allocate_tape_spec' {GF : BundledGFunctors} [foxtrotGS GF] (E : CoPset) (j : ℕ)
      (K : List ectx_item) :
    j ⤇ fill K cpl(&sample_allocate_tape #()) ⊢@{IProp GF}
      pupd E E iprop(∃ v, sample_tape' v ∗ j ⤇ fill K (Val v))
  sample_tape_spec_some {GF : BundledGFunctors} [foxtrotGS GF] {s : Stuckness} (E : CoPset)
      (α : val) (n : ℕ) (ns : List ℕ) :
    {{ sample_tape α (n :: ns) }} (cpl(&sample_with_tape &α)) @ s; E
    {{ RET LitV (LitInt (n : ℤ)); (sample_tape α ns : IProp GF) }}
  sample_tape_spec_couple' {GF : BundledGFunctors} [foxtrotGS GF] {s : Stuckness} (E : CoPset)
      (α : val) (j : ℕ) (K : List ectx_item) :
    {{ sample_tape' α ∗ j ⤇ fill K cpl(&sample_with_tape &α) }}
      (cpl(&sample_without_tape #())) @ s; E
    {{ (n : Fin (tb + 1)), RET LitV (LitInt ((n : ℕ) : ℤ));
      (iprop(sample_tape' α ∗ j ⤇ fill K (Val (LitV (LitInt ((n : ℕ) : ℤ))))) : IProp GF) }}
  sample_without_tape_spec' {GF : BundledGFunctors} [foxtrotGS GF] (E : CoPset) (j : ℕ)
      (K : List ectx_item) :
    j ⤇ fill K cpl(&sample_without_tape #()) ⊢@{IProp GF}
      pupd E E iprop(∃ n : Fin (tb + 1), j ⤇ fill K (Val (LitV (LitInt ((n : ℕ) : ℤ)))))

attribute [instance] sample_spec.sample_tape_timeless sample_spec.sample_tape_timeless'

/-! ## Implementations -/

section impl

variable {GF : BundledGFunctors} [foxtrotGS GF]
variable {s : Stuckness}

/-! ### `sample_spec1`: uniform sampling -/

/-- The tape predicate of `sample_spec1` (Rocq: inline in `sample_spec1`). -/
def sample_spec1_tape (tb : ℕ) (α : val) (ns : List ℕ) : IProp GF :=
  iprop(∃ α', ⌜α = LitV (LitLbl α')⌝ ∗ α' ↪N (tb; ns))

/-- The spec tape predicate of `sample_spec1` (Rocq: inline in `sample_spec1`). -/
def sample_spec1_tape' (tb : ℕ) (α : val) : IProp GF :=
  iprop(∃ α', ⌜α = LitV (LitLbl α')⌝ ∗ α' ↪ₛN (tb; []))

instance sample_spec1_tape_timeless (tb : ℕ) (α : val) (ns : List ℕ) :
    Timeless (sample_spec1_tape (GF := GF) tb α ns) := by
  unfold sample_spec1_tape
  infer_instance

instance sample_spec1_tape_timeless' (tb : ℕ) (α : val) :
    Timeless (sample_spec1_tape' (GF := GF) tb α) := by
  unfold sample_spec1_tape'
  infer_instance

theorem sample_spec1_tape_exclusive (tb : ℕ) (α : val) (ns ns' : List ℕ) :
    ⊢@{IProp GF} sample_spec1_tape tb α ns -∗ sample_spec1_tape tb α ns' -∗ False := by
  unfold sample_spec1_tape
  iintro ⟨%α1, %H1, H1⟩ ⟨%α2, %H2, H2⟩
  subst H1
  cases H2
  iapply tapeN_tapeN_contradict $$ H1 H2

theorem sample_spec1_tape_exclusive' (tb : ℕ) (α : val) :
    ⊢@{IProp GF} sample_spec1_tape' tb α -∗ sample_spec1_tape' tb α -∗ False := by
  unfold sample_spec1_tape'
  iintro ⟨%α1, %H1, H1⟩ ⟨%α2, %H2, H2⟩
  subst H1
  cases H2
  iapply spec_tapeN_tapeN_contradict $$ H1 H2

theorem sample_spec1_tape_valid (tb : ℕ) (α : val) (ns : List ℕ) :
    sample_spec1_tape tb α ns ⊢@{IProp GF} ⌜∀ n ∈ ns, n ≤ tb⌝ := by
  unfold sample_spec1_tape
  iintro ⟨%α', -, H⟩
  iapply tapeN_ineq $$ H

theorem sample_spec1_tape_presample (tb : ℕ) (E : CoPset) (α : val) (ns : List ℕ) :
    sample_spec1_tape tb α ns ⊢@{IProp GF}
      pupd E E iprop(∃ n : Fin (tb + 1), sample_spec1_tape tb α (ns ++ [(n : ℕ)])) := by
  unfold sample_spec1_tape
  iintro ⟨%α', %Hα, H⟩
  subst Hα
  imod pupd_presample tb E ns α' $$ H with ⟨%n, H, %Hn⟩
  imodintro
  iexists ⟨n, Nat.lt_succ_of_le Hn⟩
  iexists α'
  iframe H
  ipureintro
  rfl

theorem sample_spec1_allocate_tape_spec (tb : ℕ) (E : CoPset) :
    {{ True }} (cpl(v(λ _, alloc(#tb)) #())) @ s; E
    {{ (v : val), RET v; (sample_spec1_tape tb v [] : IProp GF) }} := by
  iintro %Φ - HΦ
  wp_pures
  wp_alloctape α as Hα
  iapply HΦ
  unfold sample_spec1_tape
  iexists α
  iframe Hα
  ipureintro
  rfl

theorem sample_spec1_allocate_tape_spec' (tb : ℕ) (E : CoPset) (j : ℕ) (K : List ectx_item) :
    j ⤇ fill K cpl(v(λ _, alloc(#tb)) #()) ⊢@{IProp GF}
      pupd E E iprop(∃ v, sample_spec1_tape' tb v ∗ j ⤇ fill K (Val v)) := by
  iintro Hspec
  tp_pure j
  tp_allocnattape j α as Hα
  imodintro
  iexists LitV (LitLbl α)
  iframe Hspec
  unfold sample_spec1_tape'
  iexists α
  iframe Hα
  ipureintro
  rfl

theorem sample_spec1_tape_spec_some (tb : ℕ) (E : CoPset) (α : val) (n : ℕ) (ns : List ℕ) :
    {{ sample_spec1_tape tb α (n :: ns) }} (cpl(v(λ α, rand(α) #tb) &α)) @ s; E
    {{ RET LitV (LitInt (n : ℤ)); (sample_spec1_tape tb α ns : IProp GF) }} := by
  unfold sample_spec1_tape
  iintro %Φ ⟨%α', %Hα, Hα⟩ HΦ
  subst Hα
  wp_pures
  wp_randtape as %Hn
  iapply HΦ
  iexists α'
  iframe Hα
  ipureintro
  rfl

theorem sample_spec1_tape_spec_couple' (tb : ℕ) (E : CoPset) (α : val) (j : ℕ)
    (K : List ectx_item) :
    {{ sample_spec1_tape' tb α ∗ j ⤇ fill K cpl(v(λ α, rand(α) #tb) &α) }}
      (cpl(v(λ _, rand(#tb)) #())) @ s; E
    {{ (n : Fin (tb + 1)), RET LitV (LitInt ((n : ℕ) : ℤ));
      (iprop(sample_spec1_tape' tb α ∗ j ⤇ fill K (Val (LitV (LitInt ((n : ℕ) : ℤ))))) :
        IProp GF) }} := by
  unfold sample_spec1_tape'
  iintro %Φ ⟨⟨%α', %Hα, Hα⟩, Hspec⟩ HΦ
  subst Hα
  wp_pures
  tp_pures j
  wp_apply (wp_couple_rand_rand_lbl tb id Function.bijective_id (tb : ℤ) K α' j (by simp)
    (fun n hn => hn)) $$ [Hα Hspec] with %n ⟨Hα, Hspec, %Hn⟩
  · iframe Hα Hspec
  iapply HΦ $$ %⟨n, Nat.lt_succ_of_le Hn⟩
  simp only [id_eq]
  iframe Hspec
  iexists α'
  iframe Hα
  ipureintro
  rfl

theorem sample_spec1_without_tape_spec' (tb : ℕ) (E : CoPset) (j : ℕ) (K : List ectx_item) :
    j ⤇ fill K cpl(v(λ _, rand(#tb)) #()) ⊢@{IProp GF}
      pupd E E iprop(∃ n : Fin (tb + 1), j ⤇ fill K (Val (LitV (LitInt ((n : ℕ) : ℤ))))) := by
  iintro Hspec
  tp_pures j
  imod pupd_rand j K tb (tb : ℤ) E (by simp) $$ Hspec with ⟨%n, Hspec, %Hn⟩
  imodintro
  iexists ⟨n, Nat.lt_succ_of_le Hn⟩
  iexact Hspec

end impl

/-- Rocq: `sample_spec1`. Uniform sampling with `rand`. -/
@[instance_reducible]
def sample_spec1 (tb : ℕ) : sample_spec tb cpl_val(λ _, rand(#tb)) where
  sample_allocate_tape := cpl_val(λ _, alloc(#tb))
  sample_with_tape := cpl_val(λ α, rand(α) #tb)
  sample_tape α ns := sample_spec1_tape tb α ns
  sample_tape' α := sample_spec1_tape' tb α
  sample_tape_timeless α ns := sample_spec1_tape_timeless tb α ns
  sample_tape_timeless' α := sample_spec1_tape_timeless' tb α
  sample_tape_exclusive α ns ns' := sample_spec1_tape_exclusive tb α ns ns'
  sample_tape_exclusive' α := sample_spec1_tape_exclusive' tb α
  sample_tape_valid α ns := sample_spec1_tape_valid tb α ns
  sample_tape_presample E α ns := sample_spec1_tape_presample tb E α ns
  sample_allocate_tape_spec E := sample_spec1_allocate_tape_spec tb E
  sample_allocate_tape_spec' E j K := sample_spec1_allocate_tape_spec' tb E j K
  sample_tape_spec_some E α n ns := sample_spec1_tape_spec_some tb E α n ns
  sample_tape_spec_couple' E α j K := sample_spec1_tape_spec_couple' tb E α j K
  sample_without_tape_spec' E j K := sample_spec1_without_tape_spec' tb E j K

section impl2

variable {GF : BundledGFunctors} [foxtrotGS GF]
variable {s : Stuckness}

/-! ### `sample_spec2`: always `0` -/

/-- The tape predicate of `sample_spec2` (Rocq: inline in `sample_spec2`). -/
def sample_spec2_tape (tb : ℕ) (α : val) (ns : List ℕ) : IProp GF :=
  iprop(∃ α', ⌜α = LitV (LitLbl α')⌝ ∗ (α' ↪N (tb; []) ∗ ⌜∀ x ∈ ns, x = 0⌝))

/-- The spec tape predicate of `sample_spec2` (Rocq: inline in `sample_spec2`). -/
def sample_spec2_tape' (tb : ℕ) (α : val) : IProp GF :=
  iprop(∃ α', ⌜α = LitV (LitLbl α')⌝ ∗ α' ↪ₛN (tb; []))

instance sample_spec2_tape_timeless (tb : ℕ) (α : val) (ns : List ℕ) :
    Timeless (sample_spec2_tape (GF := GF) tb α ns) := by
  unfold sample_spec2_tape
  infer_instance

instance sample_spec2_tape_timeless' (tb : ℕ) (α : val) :
    Timeless (sample_spec2_tape' (GF := GF) tb α) := by
  unfold sample_spec2_tape'
  infer_instance

theorem sample_spec2_tape_exclusive (tb : ℕ) (α : val) (ns ns' : List ℕ) :
    ⊢@{IProp GF} sample_spec2_tape tb α ns -∗ sample_spec2_tape tb α ns' -∗ False := by
  unfold sample_spec2_tape
  iintro ⟨%α1, %H1, H1, -⟩ ⟨%α2, %H2, H2, -⟩
  subst H1
  cases H2
  iapply tapeN_tapeN_contradict $$ H1 H2

theorem sample_spec2_tape_exclusive' (tb : ℕ) (α : val) :
    ⊢@{IProp GF} sample_spec2_tape' tb α -∗ sample_spec2_tape' tb α -∗ False := by
  unfold sample_spec2_tape'
  iintro ⟨%α1, %H1, H1⟩ ⟨%α2, %H2, H2⟩
  subst H1
  cases H2
  iapply spec_tapeN_tapeN_contradict $$ H1 H2

theorem sample_spec2_tape_valid (tb : ℕ) (α : val) (ns : List ℕ) :
    sample_spec2_tape tb α ns ⊢@{IProp GF} ⌜∀ n ∈ ns, n ≤ tb⌝ := by
  unfold sample_spec2_tape
  iintro ⟨%α', -, -, %H⟩
  ipureintro
  intro n hn
  rw [H n hn]
  exact Nat.zero_le _

theorem sample_spec2_tape_presample (tb : ℕ) (E : CoPset) (α : val) (ns : List ℕ) :
    sample_spec2_tape tb α ns ⊢@{IProp GF}
      pupd E E iprop(∃ n : Fin (tb + 1), sample_spec2_tape tb α (ns ++ [(n : ℕ)])) := by
  unfold sample_spec2_tape
  iintro ⟨%α', %Hα, H, %Hns⟩
  imodintro
  iexists ⟨0, Nat.succ_pos tb⟩
  iexists α'
  iframe H
  isplitr
  · ipureintro
    exact Hα
  · ipureintro
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact Hns x hx
    · exact List.mem_singleton.1 hx

theorem sample_spec2_allocate_tape_spec (tb : ℕ) (E : CoPset) :
    {{ True }} (cpl(v(λ _, alloc(#tb)) #())) @ s; E
    {{ (v : val), RET v; (sample_spec2_tape tb v [] : IProp GF) }} := by
  iintro %Φ - HΦ
  wp_pures
  wp_alloctape α as Hα
  iapply HΦ
  unfold sample_spec2_tape
  iexists α
  iframe Hα
  isplitr
  · ipureintro
    rfl
  · ipureintro
    intro x hx
    cases hx

theorem sample_spec2_allocate_tape_spec' (tb : ℕ) (E : CoPset) (j : ℕ) (K : List ectx_item) :
    j ⤇ fill K cpl(v(λ _, alloc(#tb)) #()) ⊢@{IProp GF}
      pupd E E iprop(∃ v, sample_spec2_tape' tb v ∗ j ⤇ fill K (Val v)) := by
  iintro Hspec
  tp_pure j
  tp_allocnattape j α as Hα
  imodintro
  iexists LitV (LitLbl α)
  iframe Hspec
  unfold sample_spec2_tape'
  iexists α
  iframe Hα
  ipureintro
  rfl

theorem sample_spec2_tape_spec_some (tb : ℕ) (E : CoPset) (α : val) (n : ℕ) (ns : List ℕ) :
    {{ sample_spec2_tape tb α (n :: ns) }} (cpl(v(λ α, #0) &α)) @ s; E
    {{ RET LitV (LitInt (n : ℤ)); (sample_spec2_tape tb α ns : IProp GF) }} := by
  unfold sample_spec2_tape
  iintro %Φ ⟨%α', %Hα, Hα, %H⟩ HΦ
  wp_pures
  have Hn : n = 0 := H n List.mem_cons_self
  subst Hn
  iapply HΦ
  iexists α'
  iframe Hα
  isplitr
  · ipureintro
    exact Hα
  · ipureintro
    intro x hx
    exact H x (List.mem_cons_of_mem _ hx)

theorem sample_spec2_tape_spec_couple' (tb : ℕ) (E : CoPset) (α : val) (j : ℕ)
    (K : List ectx_item) :
    {{ sample_spec2_tape' tb α ∗ j ⤇ fill K cpl(v(λ α, #0) &α) }}
      (cpl(v(λ _, #0) #())) @ s; E
    {{ (n : Fin (tb + 1)), RET LitV (LitInt ((n : ℕ) : ℤ));
      (iprop(sample_spec2_tape' tb α ∗ j ⤇ fill K (Val (LitV (LitInt ((n : ℕ) : ℤ))))) :
        IProp GF) }} := by
  iintro %Φ ⟨Hα, Hspec⟩ HΦ
  tp_pures j
  wp_pures
  iapply HΦ $$ %⟨0, Nat.succ_pos tb⟩
  iframe Hα Hspec

theorem sample_spec2_without_tape_spec' (tb : ℕ) (E : CoPset) (j : ℕ) (K : List ectx_item) :
    j ⤇ fill K cpl(v(λ _, #0) #()) ⊢@{IProp GF}
      pupd E E iprop(∃ n : Fin (tb + 1), j ⤇ fill K (Val (LitV (LitInt ((n : ℕ) : ℤ))))) := by
  iintro Hspec
  tp_pures j
  imodintro
  iexists ⟨0, Nat.succ_pos tb⟩
  iexact Hspec

end impl2

/-- Rocq: `sample_spec2`. The sampler that always returns `0`. -/
@[instance_reducible]
def sample_spec2 (tb : ℕ) : sample_spec tb cpl_val(λ _, #0) where
  sample_allocate_tape := cpl_val(λ _, alloc(#tb))
  sample_with_tape := cpl_val(λ α, #0)
  sample_tape α ns := sample_spec2_tape tb α ns
  sample_tape' α := sample_spec2_tape' tb α
  sample_tape_timeless α ns := sample_spec2_tape_timeless tb α ns
  sample_tape_timeless' α := sample_spec2_tape_timeless' tb α
  sample_tape_exclusive α ns ns' := sample_spec2_tape_exclusive tb α ns ns'
  sample_tape_exclusive' α := sample_spec2_tape_exclusive' tb α
  sample_tape_valid α ns := sample_spec2_tape_valid tb α ns
  sample_tape_presample E α ns := sample_spec2_tape_presample tb E α ns
  sample_allocate_tape_spec E := sample_spec2_allocate_tape_spec tb E
  sample_allocate_tape_spec' E j K := sample_spec2_allocate_tape_spec' tb E j K
  sample_tape_spec_some E α n ns := sample_spec2_tape_spec_some tb E α n ns
  sample_tape_spec_couple' E α j K := sample_spec2_tape_spec_couple' tb E α j K
  sample_without_tape_spec' E j K := sample_spec2_without_tape_spec' tb E j K

end Foxtrot.Lib.Sampler
