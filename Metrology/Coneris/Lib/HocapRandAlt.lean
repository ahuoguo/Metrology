module

public import Metrology.Coneris.Lib.AbstractTape
public import Metrology.Coneris.ErrorRules
public import Iris.Instances.Lib.Invariants

/-!
# An alternative hocap rand spec (with exclusive tokens)

Ported from clutch/theories/coneris/lib/hocap_rand_alt.v

This file is an experimental attempt in deriving a different spec for the abstract rand module.
This is not described in the paper.

Hocap rand spec that generates an exclusive token as well.
In most examples, the exclusive token is not needed since the data structure need not need to
create an auth view of all the tapes.
Useful for building more complex data structures when we need to know all the tapes generated.
We also fix the tape bound.

This module contains the spec, the checks and the implementation `rand_spec1` (section
`impl1`); `impl2` (a rand 3 simulated with two flips) is in `Coneris.Lib.HocapRandAltPart2`,
and `impl3` (the rejection sampler) in `Coneris.Lib.HocapRandAltPart3`.

## Rocq → Lean mapping
* `Class rand_spec' (tb:nat) `{!conerisGS Σ}` is `class rand_spec' (tb : ℕ) GF` (over
  `[conerisGS GF]`) with the same field names. As in `Coneris.Lib.HocapRand`: errors are
  `ℝ≥0∞` (the hypothesis `∀ x, 0 <= ε2 x` is dropped), `Forall` is `∀ n ∈ ns, ..`, magic
  wands are stated as `⊢ P -∗ Q`, the `#[global] ... ::` instance fields are re-exported as the
  instances `rand_spec'_is_rand_persistent`, `rand_spec'_rand_tapes_timeless`,
  `rand_spec'_rand_token_timeless`.
* Context `ghost_mapG Σ val ()`, `abstract_tapesGS Σ` is
  `[GhostMapG GF val Unit val_map] [abstract_tapesGS GF]`, where `val_map` is the finite map
  type keyed by values of `Coneris.Lib.AbstractTape` (Rocq: `gmap val`).
* `gmap` operations: `f <$> m` is `m.map (fun _ x => f x)` (`Std.ExtTreeMap.map`), `m !! k` is
  `m[k]?`, `<[k:=v]>m` is `m.insert k v`, bridged to iris-lean's `Iris.Std.insert` by
  `val_map_insert_eq`. The needed `gmap` lemmas (`fmap_insert`, `fmap_empty`, `insert_id`,
  `lookup_fmap`) are the helpers `val_map_map_insert`, `val_map_map_empty`,
  `val_map_insert_id`, `val_map_getElem?_map`.
* `ghost_map_auth γ 1 m` is `ghost_map_auth (H := val_map) γ (DFrac.own 1) m` and
  `α ↪[γ] ()` is `ghost_map_elem (H := val_map) γ (DFrac.own 1) α ()`.
* `rand_tape_name` is `GName × GName`, as in Rocq.

## Proofs that differ from Rocq
The three Rocq invariants `rand_inv_pred1/2/3` are the same predicate at the tape bounds `tb`,
`1` and `S tb`, and the corresponding obligations repeat the same invariant reasoning. Here the
predicate is the helper `rand_inv_pred_gen M γ` (`rand_inv_pred1 γ := rand_inv_pred_gen tb γ`,
etc.), and the shared reasoning is stated once for all `M`:
* `rand_inv_gen_create` (the `rand_inv_create_spec` obligations),
* `rand_inv_gen_alloc` (the `alloc #M` step of the `rand_allocate_tape_spec` obligations),
* `rand_inv_gen_presample` (the `state_update_presample_exp` step, with the invariant opened,
  of the `rand_tapes_presample` obligations),
* `rand_inv_gen_rand` (the `rand(α) #M` step, with the invariant opened twice, of the
  `rand_tape_spec_some` obligations).

## Omitted
* `Local Opaque INR`, `Local Opaque enum_uniform_fin_list`: Rocq-specific.
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang
open Coneris.Lib.AbstractTape

namespace Coneris.Lib.HocapRandAlt

/-- Rocq: `rand_spec'`. -/
class rand_spec' (tb : ℕ) (GF : BundledGFunctors) [conerisGS GF] where
  -- * Operations
  rand_allocate_tape : val
  rand_tape : val
  -- * Ghost state
  rand_tape_name : Type
  -- * Predicates
  is_rand (N : Namespace) (γ1 : rand_tape_name) : IProp GF
  rand_tapes (α : val) (ns : List ℕ) (γ1 : rand_tape_name) : IProp GF
  rand_token (α : val) (γ : rand_tape_name) : IProp GF
  -- * General properties of the predicates
  is_rand_persistent (N : Namespace) (γ1 : rand_tape_name) : Persistent (is_rand N γ1)
  rand_tapes_timeless (α : val) (ns : List ℕ) (γ : rand_tape_name) :
    Timeless (rand_tapes α ns γ)
  rand_token_timeless (α : val) (γ : rand_tape_name) : Timeless (rand_token α γ)
  rand_tapes_exclusive (α : val) (ns ns' : List ℕ) (γ : rand_tape_name) :
    ⊢ rand_tapes α ns γ -∗ rand_tapes α ns' γ -∗ False
  rand_token_exclusive (α : val) (γ : rand_tape_name) :
    ⊢ rand_token α γ -∗ rand_token α γ -∗ False
  rand_tapes_valid (α : val) (ns : List ℕ) (γ : rand_tape_name) :
    ⊢ rand_tapes α ns γ -∗ ⌜∀ n ∈ ns, n ≤ tb⌝
  rand_tapes_presample (N : Namespace) (E : CoPset) (α : val) (ns : List ℕ) (ε : ℝ≥0∞)
    (ε2 : Fin (tb + 1) → ℝ≥0∞) (γ : rand_tape_name) (HN : ↑N ⊆ E)
    (Hsum : ∑' n, 1 / ((tb : ℝ≥0∞) + 1) * ε2 n ≤ ε) :
    ⊢ is_rand N γ -∗ rand_tapes α ns γ -∗ ↯ ε -∗
      state_update E E iprop(∃ n : Fin (tb + 1), ↯ (ε2 n) ∗ rand_tapes α (ns ++ [(n : ℕ)]) γ)
  -- * Program specs
  rand_inv_create_spec (N : Namespace) (E : CoPset) (HN : ↑N ⊆ E) :
    ⊢ |={E}=> ∃ γ1, is_rand N γ1
  rand_allocate_tape_spec (N : Namespace) (γ : rand_tape_name) (E : CoPset) (HN : ↑N ⊆ E) :
    {{ is_rand N γ }} cpl(v(&rand_allocate_tape) #()) @ E
    {{ v, RET v; rand_token v γ ∗ rand_tapes v [] γ }}
  rand_tape_spec_some (N : Namespace) (γ : rand_tape_name) (E : CoPset) (α : val) (n : ℕ)
    (ns : List ℕ) (HN : ↑N ⊆ E) :
    {{ is_rand N γ ∗ rand_tapes α (n :: ns) γ }} cpl(v(&rand_tape) v(&α)) @ E
    {{ RET LitV (LitInt (n : ℤ)); rand_tapes α ns γ }}

section instances

variable {tb : ℕ} {GF : BundledGFunctors} [conerisGS GF] [r : rand_spec' tb GF]

/-- Rocq: `#[global] is_rand_persistent` (the instance). -/
instance rand_spec'_is_rand_persistent (N : Namespace) (γ1 : r.rand_tape_name) :
    Persistent (r.is_rand N γ1) := r.is_rand_persistent N γ1

/-- Rocq: `#[global] rand_tapes_timeless` (the instance). -/
instance rand_spec'_rand_tapes_timeless (α : val) (ns : List ℕ) (γ : r.rand_tape_name) :
    Timeless (r.rand_tapes α ns γ) := r.rand_tapes_timeless α ns γ

/-- Rocq: `#[global] rand_token_timeless` (the instance). -/
instance rand_spec'_rand_token_timeless (α : val) (γ : r.rand_tape_name) :
    Timeless (r.rand_token α γ) := r.rand_token_timeless α γ

end instances

/-! ## Checks -/

section checks

variable {GF : BundledGFunctors} [conerisGS GF] {tb : ℕ} [r1 : rand_spec' tb GF]

/-- Rocq: `wp_rand_tape_1`. -/
theorem wp_rand_tape_1 (N : Namespace) (n : ℕ) (ns : List ℕ) (α : val)
    (γ : r1.rand_tape_name) :
    {{ r1.is_rand N γ ∗ ▷ r1.rand_tapes α (n :: ns) γ }} cpl(v(&r1.rand_tape) v(&α))
    {{ RET LitV (LitInt (n : ℤ)); r1.rand_tapes α ns γ ∗ ⌜n ≤ tb⌝ }} := by
  iintro %Φ ⟨#Hinv, >Hfrag⟩ HΦ
  ihave %H' := r1.rand_tapes_valid α (n :: ns) γ $$ Hfrag
  wp_apply r1.rand_tape_spec_some N γ ⊤ α n ns CoPset.subseteq_top $$ [Hfrag] with H
  · iframe Hinv Hfrag
  iapply HΦ
  iframe H
  ipureintro
  exact H' n List.mem_cons_self

/-- Rocq: `wp_presample_adv_comp_rand_tape`. -/
theorem wp_presample_adv_comp_rand_tape (N : Namespace) (E : CoPset) (α : val) (ns : List ℕ)
    (ε1 : ℝ≥0∞) (ε2 : Fin (tb + 1) → ℝ≥0∞) (γ : r1.rand_tape_name) (Hsubset : ↑N ⊆ E)
    (Hsum : ∑' n, 1 / ((tb : ℝ≥0∞) + 1) * ε2 n ≤ ε1) :
    ⊢ r1.is_rand N γ -∗ ▷ r1.rand_tapes α ns γ -∗ ↯ ε1 -∗
      wp_update E iprop(∃ n : Fin (tb + 1), ↯ (ε2 n) ∗ r1.rand_tapes α (ns ++ [(n : ℕ)]) γ) := by
  iintro #Hinv >Htape Herr
  iapply wp_update_state_update
  iapply r1.rand_tapes_presample N E α ns ε1 ε2 γ Hsubset Hsum $$ Hinv Htape Herr

end checks

/-! ## Finite maps keyed by values (helpers) -/

section val_map_lemmas

/-- Helper (Rocq: `lookup_fmap`). -/
theorem val_map_getElem?_map {V W : Type} (m : val_map V) (f : val → V → W) (k : val) :
    (m.map f)[k]? = m[k]?.map (f k) :=
  Std.ExtTreeMap.getElem?_map

/-- Helper (Rocq: `fmap_insert`). -/
theorem val_map_map_insert {V W : Type} (m : val_map V) (f : val → V → W) (k : val) (v : V) :
    (m.insert k v).map f = (m.map f).insert k (f k v) :=
  Std.ExtTreeMap.ext_getElem? fun k' => by
    rw [val_map_getElem?_map, Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getElem?_insert,
      val_map_getElem?_map]
    split
    · rename_i h
      obtain rfl := compare_eq_iff_eq.1 h
      rfl
    · rfl

/-- Helper (Rocq: `fmap_empty`). -/
theorem val_map_map_empty {V W : Type} (f : val → V → W) :
    (∅ : val_map V).map f = ∅ :=
  Std.ExtTreeMap.ext_getElem? fun k' => by
    rw [val_map_getElem?_map]
    simp

/-- Helper (Rocq: `insert_id`). -/
theorem val_map_insert_id {V : Type} (m : val_map V) (k : val) (v : V) (h : m[k]? = some v) :
    m.insert k v = m :=
  Std.ExtTreeMap.ext_getElem? fun k' => by
    rw [Std.ExtTreeMap.getElem?_insert]
    split
    · rename_i h'
      obtain rfl := compare_eq_iff_eq.1 h'
      exact h.symm
    · rfl

end val_map_lemmas

/-! ## The invariant shared by the implementations (helpers) -/

section inv_gen

variable {GF : BundledGFunctors} [conerisGS GF] [GhostMapG GF val Unit val_map]
  [abstract_tapesGS GF]

/-- Helper (not in `Coneris.Lib.AbstractTape`; Rocq infers it by unfolding). -/
instance abstract_tapes_auth_timeless (γ : GName) (m : val_map (ℕ × List ℕ)) :
    Timeless (abstract_tapes_auth (GF := GF) γ m) := by
  unfold abstract_tapes_auth; infer_instance

/-- Helper (not in `Coneris.Lib.AbstractTape`; Rocq infers it by unfolding). -/
instance abstract_tapes_frag_timeless (γ : GName) (α : val) (M : ℕ) (ns : List ℕ) :
    Timeless (abstract_tapes_frag (GF := GF) γ α M ns) := by
  unfold abstract_tapes_frag; infer_instance

/-- Helper: the Rocq invariants `rand_inv_pred1`/`rand_inv_pred2`/`rand_inv_pred3`, for the
tape bound `M` (`tb`, `1` and `S tb` respectively). -/
def rand_inv_pred_gen (M : ℕ) (γ : GName × GName) : IProp GF :=
  iprop(∃ m : val_map (List ℕ),
    ghost_map_auth (H := val_map) γ.1 (DFrac.own 1) (m.map fun _ _ => ()) ∗
    (●ₐ (m.map fun _ x => (M, x)) @ γ.2) ∗
    [∗map] α ↦ ns ∈ (m : val_map (List ℕ)), ∃ α' : Loc, ⌜α = LitV (LitLbl α')⌝ ∗ α' ↪N (M; ns))

instance rand_inv_pred_gen_timeless (M : ℕ) (γ : GName × GName) :
    Timeless (rand_inv_pred_gen (GF := GF) M γ) := by
  unfold rand_inv_pred_gen; infer_instance

/-- Helper: the `rand_inv_create_spec` obligations. -/
theorem rand_inv_gen_create (M : ℕ) (N : Namespace) (E : CoPset) :
    ⊢@{IProp GF} |={E}=> ∃ γ, inv N (rand_inv_pred_gen M γ) := by
  imod abstract_tapes_alloc (GF := GF) ∅ with ⟨%γ2, H1, -⟩
  imod ghost_map_alloc_empty (GF := GF) (K := val) (V := Unit) (H := val_map) with ⟨%γ1, H2⟩
  imod inv_alloc N E (rand_inv_pred_gen M (γ1, γ2)) $$ [H1 H2] with #Hinv
  · inext
    unfold rand_inv_pred_gen
    iexists ∅
    rw [val_map_map_empty, val_map_map_empty]
    iframe H1 H2
    iapply (BigSepM.bigSepM_empty (PROP := IProp GF) (M := val_map)).2
    iempintro
  imodintro
  iexists (γ1, γ2)
  iexact Hinv

omit [GhostMapG GF val Unit val_map] [abstract_tapesGS GF] in
/-- Helper: the tape points-to of a new tape is not in the invariant's map. -/
theorem rand_inv_gen_notin (M : ℕ) (m : val_map (List ℕ)) (α : Loc) (ns : List ℕ) :
    ⊢@{IProp GF} α ↪N (M; ns) -∗
      ([∗map] α ↦ ns ∈ (m : val_map (List ℕ)), ∃ α' : Loc, ⌜α = LitV (LitLbl α')⌝ ∗ α' ↪N (M; ns)) -∗
      ⌜m[LitV (LitLbl α)]? = none⌝ := by
  cases Heqn : m[LitV (LitLbl α)]? with
  | none =>
    iintro - -
    ipureintro
    rfl
  | some t =>
    iintro Hα Hmap
    ihave ⟨%α', %Heq, Ht⟩ := BigSepM.bigSepM_lookup (M := val_map) (i := LitV (LitLbl α)) Heqn $$ Hmap
    cases Heq
    iexfalso
    iapply tapeN_tapeN_contradict $$ Hα Ht

/-- Helper: the `alloc #M` step of the `rand_allocate_tape_spec` obligations. -/
theorem rand_inv_gen_alloc (M : ℕ) (N : Namespace) (γ : GName × GName) (E : CoPset)
    (HN : ↑N ⊆ E) :
    {{ inv N (rand_inv_pred_gen (GF := GF) M γ) }} cpl(alloc(#M)) @ E
    {{ v, RET v; ghost_map_elem (H := val_map) γ.1 (DFrac.own 1) v () ∗ (v ◯↪N (M; []) @ γ.2) }} := by
  iintro %Φ #Hinv HΦ
  iinv Hinv with >HI
  iunfold rand_inv_pred_gen at HI
  icases HI with ⟨%m, Hs, Hm, Hts⟩
  wp_alloctape α as Ht
  ihave %Hnone := rand_inv_gen_notin M m α [] $$ Ht Hts
  have Hnone1 : get? (show val_map Unit from m.map fun _ _ => ()) (LitV (LitLbl α)) = none := by
    show (m.map _)[_]? = none
    rw [val_map_getElem?_map, Hnone]; rfl
  have Hnone2 : (m.map fun _ x => (M, x))[LitV (LitLbl α)]? = none := by
    rw [val_map_getElem?_map, Hnone]; rfl
  imod ghost_map_insert (LitV (LitLbl α)) () Hnone1 $$ Hs with ⟨Hs, Htoken⟩
  imod abstract_tapes_new γ.2 _ (LitV (LitLbl α)) M [] Hnone2 $$ Hm with ⟨Hm, Hfrag⟩
  imodintro
  isplitl [Hs Hm Hts Ht]
  · inext
    unfold rand_inv_pred_gen
    iexists m.insert (LitV (LitLbl α)) []
    rw [val_map_insert_eq, ← val_map_map_insert, ← val_map_map_insert]
    iframe Hs Hm
    rw [← val_map_insert_eq]
    iapply (BigSepM.bigSepM_insert (PROP := IProp GF) (M := val_map) Hnone).2
    iframe Hts
    iexists α
    iframe Ht
    ipureintro
    rfl
  · iapply HΦ
    iframe

omit [conerisGS GF] [GhostMapG GF val Unit val_map] in
/-- Helper: the invariant's map contains the tapes of the fragments. -/
theorem rand_inv_gen_agree (M : ℕ) (m : val_map (List ℕ)) (γ : GName) (α : val)
    (ns : List ℕ) :
    ⊢@{IProp GF} (●ₐ (m.map fun _ x => (M, x)) @ γ) -∗ (α ◯↪N (M; ns) @ γ) -∗ ⌜m[α]? = some ns⌝ := by
  iintro Hm H1
  ihave %Hsome := abstract_tapes_agree _ γ α M ns $$ Hm H1
  ipureintro
  rw [val_map_getElem?_map] at Hsome
  obtain ⟨x, hx, hx'⟩ := Option.map_eq_some_iff.1 Hsome
  cases hx'
  exact hx

/-- Helper: the `state_update_presample_exp` step of the `rand_tapes_presample` obligations. -/
theorem rand_inv_gen_presample (M : ℕ) (N : Namespace) (E : CoPset) (α : val) (ns : List ℕ)
    (ε : ℝ≥0∞) (ε2 : Fin (M + 1) → ℝ≥0∞) (γ : GName × GName) (HN : ↑N ⊆ E)
    (Hsum : ∑' n, 1 / ((M : ℝ≥0∞) + 1) * ε2 n ≤ ε) :
    ⊢@{IProp GF} inv N (rand_inv_pred_gen M γ) -∗ (α ◯↪N (M; ns) @ γ.2) -∗ ↯ ε -∗
      state_update E E iprop(∃ n : Fin (M + 1), ↯ (ε2 n) ∗ (α ◯↪N (M; ns ++ [(n : ℕ)]) @ γ.2)) := by
  iintro #Hinv H1 Herr
  imod inv_acc HN $$ Hinv with ⟨>HI, Hclose⟩
  iunfold rand_inv_pred_gen at HI
  icases HI with ⟨%m, Hs, Hm, Ht⟩
  ihave %Hsome := rand_inv_gen_agree M m γ.2 α ns $$ Hm H1
  ihave ⟨⟨%α', %Heq, Ht⟩, Hclose'⟩ :=
    BigSepM.bigSepM_insert_acc (PROP := IProp GF) (M := val_map) (i := α) Hsome $$ Ht
  subst Heq
  imod state_update_presample_exp _ α' M ns ε ε2 Hsum $$ Ht Herr with ⟨%n, Ht, Herr⟩
  imod abstract_tapes_presample γ.2 _ _ M ns n $$ Hm H1 with ⟨Hm, H1⟩
  ihave Ht := Hclose' $$ %(ns ++ [(n : ℕ)]) [Ht]
  · iexists α'
    iframe Ht
    ipureintro
    rfl
  imod Hclose $$ [Hs Hm Ht] with -
  · inext
    unfold rand_inv_pred_gen
    iexists Iris.Std.insert m (LitV (LitLbl α')) (ns ++ [(n : ℕ)])
    rw [val_map_insert_eq, val_map_map_insert, val_map_map_insert,
      val_map_insert_id (m.map fun _ _ => ()) _ ()
        (by rw [val_map_getElem?_map, Hsome]; rfl)]
    iframe
  imodintro
  iexists n
  iframe

/-- Helper: the `rand(α) #M` step of the `rand_tape_spec_some` obligations. -/
theorem rand_inv_gen_rand (M : ℕ) (N : Namespace) (γ : GName × GName) (E : CoPset) (α : val)
    (n : ℕ) (ns : List ℕ) (HN : ↑N ⊆ E) :
    {{ inv N (rand_inv_pred_gen (GF := GF) M γ) ∗ (α ◯↪N (M; n :: ns) @ γ.2) }}
      cpl(rand(v(&α)) #M) @ E
    {{ RET LitV (LitInt (n : ℤ)); α ◯↪N (M; ns) @ γ.2 }} := by
  iintro %Φ ⟨#Hinv, Hfrag⟩ HΦ
  iapply fupd_pgl_wp
  imod inv_acc HN $$ Hinv with ⟨>HI, Hclose⟩
  iunfold rand_inv_pred_gen at HI
  icases HI with ⟨%m, Hs, Hm, Hts⟩
  ihave %Hsome := rand_inv_gen_agree M m γ.2 α (n :: ns) $$ Hm Hfrag
  ihave ⟨⟨%α', %Heq, Ht⟩, Hclose'⟩ :=
    (BigSepM.bigSepM_lookup_acc (PROP := IProp GF) (M := val_map) (i := α) Hsome).1 $$ Hts
  subst Heq
  imod Hclose $$ [Hs Hm Ht Hclose'] with -
  · inext
    unfold rand_inv_pred_gen
    iexists m
    iframe Hs Hm
    iapply Hclose'
    iexists α'
    iframe Ht
    ipureintro
    rfl
  imodintro
  iinv Hinv with >HI
  iunfold rand_inv_pred_gen at HI
  icases HI with ⟨%m', Hs, Hm, Hts⟩
  ihave %Hsome' := rand_inv_gen_agree M m' γ.2 _ (n :: ns) $$ Hm Hfrag
  ihave ⟨⟨%α'', %Heq, Ht⟩, Hclose'⟩ :=
    BigSepM.bigSepM_insert_acc (PROP := IProp GF) (M := val_map) (i := LitV (LitLbl α')) Hsome' $$ Hts
  cases Heq
  wp_randtape as %_
  imod abstract_tapes_pop γ.2 _ _ M ns n $$ Hm Hfrag with ⟨Hm, Hfrag⟩
  ihave Hts := Hclose' $$ %ns [Ht]
  · iexists α'
    iframe Ht
    ipureintro
    rfl
  imodintro
  isplitl [Hs Hm Hts]
  · inext
    unfold rand_inv_pred_gen
    iexists Iris.Std.insert m' (LitV (LitLbl α')) ns
    rw [val_map_insert_eq, val_map_map_insert, val_map_map_insert,
      val_map_insert_id (m'.map fun _ _ => ()) _ ()
        (by rw [val_map_getElem?_map, Hsome']; rfl)]
    iframe
  · iapply HΦ
    iexact Hfrag

omit [conerisGS GF] [abstract_tapesGS GF] in
/-- Helper: the `rand_token_exclusive` obligations. -/
theorem rand_token_gen_exclusive (α : val) (γ : GName) :
    ⊢@{IProp GF} ghost_map_elem (H := val_map) γ (DFrac.own 1) α () -∗
      ghost_map_elem (H := val_map) γ (DFrac.own 1) α () -∗ False := by
  iintro H1 H2
  ihave ⟨%H, -⟩ := ghost_map_elem_valid_2 (H := val_map) γ α _ _ () () $$ [H1 H2]
  · iframe
  exact absurd (DFrac.valid_own_op H) (by simp)

end inv_gen

/-! ## Implementation 1 -/

section impl1

variable {GF : BundledGFunctors} [conerisGS GF] [GhostMapG GF val Unit val_map]
  [abstract_tapesGS GF] (tb : ℕ)

/-- Rocq: `rand_inv_pred1`. -/
def rand_inv_pred1 (γ : GName × GName) : IProp GF := rand_inv_pred_gen tb γ

/-- Rocq: `is_rand1`. -/
def is_rand1 (N : Namespace) (γ : GName × GName) : IProp GF := inv N (rand_inv_pred1 tb γ)

/-- Rocq: `rand_tapes1`. -/
def rand_tapes1 (α : val) (ns : List ℕ) (γ : GName × GName) : IProp GF :=
  iprop((α ◯↪N (tb; ns) @ γ.2) ∗ ⌜∀ x ∈ ns, x ≤ tb⌝)

/-- Rocq: `rand_token1`. -/
def rand_token1 (α : val) (γ : GName × GName) : IProp GF :=
  ghost_map_elem (H := val_map) γ.1 (DFrac.own 1) α ()

/-- Rocq: `rand_allocate_tape` of `rand_spec1`. -/
def rand_allocate_tape1 : val := cpl_val(λ <>, alloc(#tb))

/-- Rocq: `rand_tape` of `rand_spec1`. -/
def rand_tape1 : val := cpl_val(λ α, rand(α) #tb)

instance is_rand1_persistent (N : Namespace) (γ : GName × GName) :
    Persistent (is_rand1 (GF := GF) tb N γ) := by
  unfold is_rand1; infer_instance

instance rand_tapes1_timeless (α : val) (ns : List ℕ) (γ : GName × GName) :
    Timeless (rand_tapes1 (GF := GF) tb α ns γ) := by
  unfold rand_tapes1; infer_instance

instance rand_token1_timeless (α : val) (γ : GName × GName) :
    Timeless (rand_token1 (GF := GF) α γ) := by
  unfold rand_token1; infer_instance

omit [conerisGS GF] [GhostMapG GF val Unit val_map] in
/-- Rocq: first `Next Obligation` of `rand_spec1`. -/
theorem rand_spec1_rand_tapes_exclusive (α : val) (ns ns' : List ℕ) (γ : GName × GName) :
    ⊢@{IProp GF} rand_tapes1 tb α ns γ -∗ rand_tapes1 tb α ns' γ -∗ False := by
  unfold rand_tapes1
  iintro ⟨H1, -⟩ ⟨H2, -⟩
  iapply abstract_tapes_frag_exclusive $$ H1 H2

omit [conerisGS GF] [abstract_tapesGS GF] in
/-- Rocq: second `Next Obligation` of `rand_spec1`. -/
theorem rand_spec1_rand_token_exclusive (α : val) (γ : GName × GName) :
    ⊢@{IProp GF} rand_token1 α γ -∗ rand_token1 α γ -∗ False :=
  rand_token_gen_exclusive α γ.1

omit [conerisGS GF] [GhostMapG GF val Unit val_map] in
/-- Rocq: third `Next Obligation` of `rand_spec1`. -/
theorem rand_spec1_rand_tapes_valid (α : val) (ns : List ℕ) (γ : GName × GName) :
    ⊢@{IProp GF} rand_tapes1 tb α ns γ -∗ ⌜∀ n ∈ ns, n ≤ tb⌝ := by
  unfold rand_tapes1
  iintro ⟨-, %H⟩
  ipureintro
  exact H

/-- Rocq: fourth `Next Obligation` of `rand_spec1`. -/
theorem rand_spec1_rand_tapes_presample (N : Namespace) (E : CoPset) (α : val) (ns : List ℕ)
    (ε : ℝ≥0∞) (ε2 : Fin (tb + 1) → ℝ≥0∞) (γ : GName × GName) (HN : ↑N ⊆ E)
    (Hsum : ∑' n, 1 / ((tb : ℝ≥0∞) + 1) * ε2 n ≤ ε) :
    ⊢@{IProp GF} is_rand1 tb N γ -∗ rand_tapes1 tb α ns γ -∗ ↯ ε -∗
      state_update E E iprop(∃ n : Fin (tb + 1), ↯ (ε2 n) ∗ rand_tapes1 tb α (ns ++ [(n : ℕ)]) γ) := by
  unfold is_rand1 rand_inv_pred1 rand_tapes1
  iintro #Hinv ⟨H1, %Hf⟩ Herr
  imod rand_inv_gen_presample tb N E α ns ε ε2 γ HN Hsum $$ Hinv H1 Herr with ⟨%n, Herr, H1⟩
  imodintro
  iexists n
  iframe Herr H1
  ipureintro
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · exact Hf x hx
  · rw [List.mem_singleton.1 hx]
    exact Nat.lt_succ_iff.1 n.isLt

/-- Rocq: fifth `Next Obligation` of `rand_spec1`. -/
theorem rand_spec1_rand_inv_create_spec (N : Namespace) (E : CoPset) (_HN : ↑N ⊆ E) :
    ⊢@{IProp GF} |={E}=> ∃ γ1, is_rand1 tb N γ1 :=
  rand_inv_gen_create tb N E

/-- Rocq: sixth `Next Obligation` of `rand_spec1`. -/
theorem rand_spec1_rand_allocate_tape_spec (N : Namespace) (γ : GName × GName) (E : CoPset)
    (HN : ↑N ⊆ E) :
    {{ is_rand1 (GF := GF) tb N γ }} cpl(v(&(rand_allocate_tape1 tb)) #()) @ E
    {{ v, RET v; rand_token1 v γ ∗ rand_tapes1 tb v [] γ }} := by
  unfold is_rand1 rand_inv_pred1
  iintro %Φ #Hinv HΦ
  wp_lam
  wp_apply rand_inv_gen_alloc tb N γ E HN $$ Hinv with %v ⟨Htok, Hfrag⟩
  iapply HΦ
  unfold rand_token1 rand_tapes1
  iframe Htok Hfrag
  ipureintro
  simp

/-- Rocq: seventh `Next Obligation` of `rand_spec1`. -/
theorem rand_spec1_rand_tape_spec_some (N : Namespace) (γ : GName × GName) (E : CoPset)
    (α : val) (n : ℕ) (ns : List ℕ) (HN : ↑N ⊆ E) :
    {{ is_rand1 (GF := GF) tb N γ ∗ rand_tapes1 tb α (n :: ns) γ }} cpl(v(&(rand_tape1 tb)) v(&α)) @ E
    {{ RET LitV (LitInt (n : ℤ)); rand_tapes1 tb α ns γ }} := by
  unfold is_rand1 rand_inv_pred1 rand_tapes1
  iintro %Φ ⟨#Hinv, Hfrag, %H⟩ HΦ
  wp_lam
  wp_apply rand_inv_gen_rand tb N γ E α n ns HN $$ [Hfrag] with Hfrag
  · iframe Hinv Hfrag
  iapply HΦ
  iframe Hfrag
  ipureintro
  exact fun x hx => H x (List.mem_cons_of_mem n hx)

/-- Rocq: `rand_spec1` (a `#[local] Program Definition`). -/
@[instance_reducible]
def rand_spec1 : rand_spec' tb GF where
  rand_allocate_tape := rand_allocate_tape1 tb
  rand_tape := rand_tape1 tb
  rand_tape_name := GName × GName
  is_rand := is_rand1 tb
  rand_tapes := rand_tapes1 tb
  rand_token := rand_token1
  is_rand_persistent := is_rand1_persistent tb
  rand_tapes_timeless := rand_tapes1_timeless tb
  rand_token_timeless := rand_token1_timeless
  rand_tapes_exclusive := rand_spec1_rand_tapes_exclusive tb
  rand_token_exclusive := rand_spec1_rand_token_exclusive
  rand_tapes_valid := rand_spec1_rand_tapes_valid tb
  rand_tapes_presample := rand_spec1_rand_tapes_presample tb
  rand_inv_create_spec := rand_spec1_rand_inv_create_spec tb
  rand_allocate_tape_spec := rand_spec1_rand_allocate_tape_spec tb
  rand_tape_spec_some := rand_spec1_rand_tape_spec_some tb

end impl1

end Coneris.Lib.HocapRandAlt
