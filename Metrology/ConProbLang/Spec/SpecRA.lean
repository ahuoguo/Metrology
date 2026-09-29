module

public import Metrology.ConProbLang.Lang
public import Iris.Instances.Lib.GhostMap
public import Iris.ProofMode

/-!
# Spec resources for `con_prob_lang`

Ported from clutch/theories/con_prob_lang/spec/spec_ra.v

Ghost state tracking a (right-hand side, "specification") `con_prob_lang` configuration: a
ghost map `ℕ → expr` for the thread pool, and ghost maps `Loc → val` / `Loc → tape` for the heap
and tapes. Built on iris-lean's `Iris.Instances.Lib.GhostMap`.

## Design (and Rocq → Lean mapping)

* Maps: the thread-pool map is `Std.ExtTreeMap ℕ expr compare`, heaps/tapes are
  `Std.ExtTreeMap Loc _ compare` (as in `Lang.lean`); the ghost maps use iris-lean's
  `LawfulFiniteMap (Std.ExtTreeMap K · compare) K` instance.
* `ghost_mapG Σ K V` is iris-lean's `GhostMapG GF K V H` (with `H` the `ExtTreeMap` functor).
* `specG_con_prob_lang` is a class over `GF : BundledGFunctors` with constructor `SpecGS` and
  the Rocq field names. As in Rocq, where they are `#[local]`, the three `GhostMapG` fields are
  *not* global instances; they are registered as `local instance`s in this file only
  (downstream code works through the definitions and lemmas below).
* `specGpreS` has the Rocq fields (global instances, as in Rocq).
* `specΣ` / `subG_clutchGPreS`: `gFunctors` lists are subsumed by `BundledGFunctors` typeclass
  synthesis; `subG_clutchGPreS` is replaced by an instance building `specGpreS GF` from three
  `GhostMapG` instances.
* `to_tpool tp := FiniteMap.map_seq (M := tpoolF) 0 tp`. Rocq's map insert `<[j:=e]> m` is `m.insert j e`
  (Std's `insert`), list insert `<[j:=e]> tp` is `tp.set j e`. iris-lean's ghost-map lemmas
  produce `Iris.Std.insert m k v` (= `m.alter k (fun _ => some v)`); the helper
  `ext_insert_eq` rewrites it to `m.insert k v`.
* Notations (`scoped` in `ConProbLang`, to avoid clashing with `Metrology.Iris.SpecProgram`):
  `j ⤇ e`, `l ↦ₛ{dq} v`, `l ↦ₛ□ v`, `l ↦ₛ{#q} v`, `l ↦ₛ v`, and the same with `↪ₛ` for tapes,
  and `l ↪ₛN ( M ; ns )`. `DfracOwn q` is `DFrac.own q`, `DfracDiscarded` is `DFrac.discard`.
* `spec_auth (ρ : cfg)` takes a `con_prob_lang.cfg` (= `List expr × state`).
* `spec_ra_init` takes `[specGpreS GF]` and produces `∃ _ : specG_con_prob_lang GF, ...`, with
  the resources referring to that existential instance.
* `nat_spec_tape l N ns`: `fin_to_nat <$> fs` is `fs.map (·.val)`.

## Added helpers
* `ext_insert_eq` (iris-lean `PartialMap.insert` on `ExtTreeMap` is `ExtTreeMap.insert`).
* `ext_get?_eq` (iris-lean `PartialMap.get?` on `ExtTreeMap` is `m[k]?`).
-/

@[expose] public section

namespace ConProbLang

open Iris Iris.Std Iris.BI con_prob_lang

/-! ## Helpers relating iris-lean's `PartialMap` operations to `Std.ExtTreeMap` ones -/

section helpers

variable {K V : Type _} [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K]

omit [Std.LawfulEqOrd K] in
theorem ext_get?_eq (m : Std.ExtTreeMap K V compare) (k : K) :
    Iris.Std.get? (M := (Std.ExtTreeMap K · compare)) m k = m[k]? := rfl

theorem ext_insert_eq (m : Std.ExtTreeMap K V compare) (k : K) (v : V) :
    Iris.Std.insert (M := (Std.ExtTreeMap K · compare)) m k v = m.insert k v := by
  apply Std.ExtTreeMap.ext_getElem?
  intro a
  change (m.alter k (fun _ => some v))[a]? = _
  rw [Std.ExtTreeMap.getElem?_alter, Std.ExtTreeMap.getElem?_insert]

end helpers

/-- The thread-pool ghost map functor (`gmap nat`). -/
abbrev tpoolF := (Std.ExtTreeMap ℕ · compare)
/-- The heap/tapes ghost map functor (`gmap loc`). -/
abbrev locF := (Std.ExtTreeMap Loc · compare)

/-- Rocq: `specG_con_prob_lang`. The CMRA for the spec `cfg`. -/
class specG_con_prob_lang (GF : BundledGFunctors) where
  SpecGS ::
  specG_con_prob_lang_prog : GhostMapG GF ℕ expr tpoolF
  specG_con_prob_lang_prog_name : GName
  specG_con_prob_lang_heap : GhostMapG GF Loc val locF
  specG_con_prob_lang_tapes : GhostMapG GF Loc tape locF
  specG_con_prob_lang_heap_name : GName
  specG_con_prob_lang_tapes_name : GName

attribute [reducible] specG_con_prob_lang.specG_con_prob_lang_prog
  specG_con_prob_lang.specG_con_prob_lang_heap specG_con_prob_lang.specG_con_prob_lang_tapes

/-- Rocq: `specGpreS`. -/
class specGpreS (GF : BundledGFunctors) where
  SpecGPreS ::
  specGpreS_prog_inG : GhostMapG GF ℕ expr tpoolF
  specGpreS_heap : GhostMapG GF Loc val locF
  specGpreS_tapes : GhostMapG GF Loc tape locF

attribute [reducible, instance] specGpreS.specGpreS_prog_inG specGpreS.specGpreS_heap
  specGpreS.specGpreS_tapes

/-- Rocq: `subG_clutchGPreS` (`subG specΣ Σ → specGpreS Σ`). -/
instance subG_clutchGPreS {GF : BundledGFunctors} [GhostMapG GF ℕ expr tpoolF]
    [GhostMapG GF Loc val locF] [GhostMapG GF Loc tape locF] : specGpreS GF :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- Rocq: `to_tpool`. -/
def to_tpool (tp : List expr) : Std.ExtTreeMap ℕ expr compare := FiniteMap.map_seq (M := tpoolF) 0 tp

/-- Rocq: `tpool_lookup`. -/
theorem tpool_lookup (tp : List expr) (j : ℕ) : (to_tpool tp)[j]? = tp[j]? := by
  rw [← ext_get?_eq, to_tpool, LawfulFiniteMap.get?_map_seq]
  simp

/-- Rocq: `to_tpool_insert`. -/
theorem to_tpool_insert (tp : List expr) (j : ℕ) (e : expr) (_h : j < tp.length) :
    to_tpool (tp.set j e) = (to_tpool tp).insert j e := by
  apply Std.ExtTreeMap.ext_getElem?
  intro i
  rw [tpool_lookup, Std.ExtTreeMap.getElem?_insert, List.getElem?_set]
  by_cases hij : j = i
  · subst hij; simp [_h]
  · have : compare j i ≠ .eq := by simpa [compare_eq_iff_eq] using hij
    simp [hij, this, tpool_lookup]

/-- Rocq: `to_tpool_app`. -/
theorem to_tpool_app (tp : List expr) (e : expr) :
    (to_tpool tp).insert tp.length e = to_tpool (tp ++ [e]) := by
  apply Std.ExtTreeMap.ext_getElem?
  intro i
  rw [tpool_lookup, Std.ExtTreeMap.getElem?_insert]
  by_cases hi : tp.length = i
  · subst hi; simp
  · have : compare tp.length i ≠ .eq := by simpa [compare_eq_iff_eq] using hi
    rw [ite_eq_right_iff.2 (fun h => absurd h this), tpool_lookup]
    rcases Nat.lt_or_ge i tp.length with h | h
    · rw [List.getElem?_append_left h]
    · rw [List.getElem?_eq_none h, List.getElem?_eq_none (by simp; omega)]

section resources

variable {GF : BundledGFunctors} [S : specG_con_prob_lang GF]

attribute [local instance] specG_con_prob_lang.specG_con_prob_lang_prog
  specG_con_prob_lang.specG_con_prob_lang_heap specG_con_prob_lang.specG_con_prob_lang_tapes

/-- Rocq: `spec_prog_auth`. -/
def spec_prog_auth (m : Std.ExtTreeMap ℕ expr compare) : IProp GF :=
  ghost_map_auth (H := tpoolF) S.specG_con_prob_lang_prog_name (DFrac.own 1) m

/-- Rocq: `spec_heap_auth`. -/
def spec_heap_auth (m : Std.ExtTreeMap Loc val compare) : IProp GF :=
  ghost_map_auth (H := locF) S.specG_con_prob_lang_heap_name (DFrac.own 1) m

/-- Rocq: `spec_tapes_auth`. -/
def spec_tapes_auth (m : Std.ExtTreeMap Loc tape compare) : IProp GF :=
  ghost_map_auth (H := locF) S.specG_con_prob_lang_tapes_name (DFrac.own 1) m

/-- Rocq: `spec_auth`. -/
def spec_auth (ρ : con_prob_lang.cfg) : IProp GF :=
  iprop(spec_prog_auth (to_tpool ρ.1) ∗ spec_heap_auth ρ.2.heap ∗ spec_tapes_auth ρ.2.tapes)

/-- Rocq: `spec_prog_frag`. -/
def spec_prog_frag (j : ℕ) (e : expr) : IProp GF :=
  ghost_map_elem S.specG_con_prob_lang_prog_name (DFrac.own 1) j e

/-- Rocq: `spec_heap_frag`. -/
def spec_heap_frag (l : Loc) (v : val) (dq : DFrac) : IProp GF :=
  ghost_map_elem S.specG_con_prob_lang_heap_name dq l v

/-- Rocq: `spec_tapes_frag`. -/
def spec_tapes_frag (l : Loc) (v : tape) (dq : DFrac) : IProp GF :=
  ghost_map_elem S.specG_con_prob_lang_tapes_name dq l v

end resources

/-! Spec program -/
scoped notation:50 j:50 " ⤇ " e:50 => spec_prog_frag j e

/-! Spec heap -/
scoped notation:50 l:50 " ↦ₛ{" dq "} " v:50 => spec_heap_frag l v dq
scoped notation:50 l:50 " ↦ₛ□ " v:50 => spec_heap_frag l v DFrac.discard
scoped notation:50 l:50 " ↦ₛ{#" q "} " v:50 => spec_heap_frag l v (DFrac.own q)
scoped notation:50 l:50 " ↦ₛ " v:50 => spec_heap_frag l v (DFrac.own 1)

/-! Spec tapes -/
scoped notation:50 l:50 " ↪ₛ{" dq "} " v:50 => spec_tapes_frag l v dq
scoped notation:50 l:50 " ↪ₛ□ " v:50 => spec_tapes_frag l v DFrac.discard
scoped notation:50 l:50 " ↪ₛ{#" q "} " v:50 => spec_tapes_frag l v (DFrac.own q)
scoped notation:50 l:50 " ↪ₛ " v:50 => spec_tapes_frag l v (DFrac.own 1)

section theory

variable {GF : BundledGFunctors} [S : specG_con_prob_lang GF]

attribute [local instance] specG_con_prob_lang.specG_con_prob_lang_prog
  specG_con_prob_lang.specG_con_prob_lang_heap specG_con_prob_lang.specG_con_prob_lang_tapes

/-- Rocq: `spec_auth_prog_agree`. -/
theorem spec_auth_prog_agree (es : List expr) (σ : state) (j : ℕ) (e : expr) :
    ⊢@{IProp GF} spec_auth (es, σ) -∗ j ⤇ e -∗ ⌜es[j]? = some e⌝ := by
  unfold spec_auth spec_prog_auth spec_prog_frag
  iintro ⟨Ha, -, -⟩ Hf
  ihave %H := ghost_map_lookup $$ Ha Hf
  ipureintro
  rw [ext_get?_eq, tpool_lookup] at H
  exact H

/-- Rocq: `spec_auth_prog_length`. -/
theorem spec_auth_prog_length (es : List expr) (σ : state) (j : ℕ) (e : expr) :
    ⊢@{IProp GF} spec_auth (es, σ) -∗ j ⤇ e -∗ ⌜j < es.length⌝ := by
  iintro Ha Hf
  ihave %H := spec_auth_prog_agree es σ j e $$ Ha Hf
  ipureintro
  exact (List.getElem?_eq_some_iff.1 H).1

/-- Rocq: `spec_update_prog`. -/
theorem spec_update_prog (es : List expr) (σ : state) (j : ℕ) (e e' : expr) :
    ⊢@{IProp GF} spec_auth (es, σ) -∗ j ⤇ e ==∗ spec_auth (es.set j e', σ) ∗ j ⤇ e' := by
  iintro Ha Hf
  ihave %Hlen := spec_auth_prog_length es σ j e $$ Ha Hf
  unfold spec_auth spec_prog_auth spec_prog_frag
  icases Ha with ⟨Ha, Hh, Ht⟩
  imod ghost_map_update e' $$ Ha Hf with ⟨Ha, Hf⟩
  imodintro
  rw [ext_insert_eq, ← to_tpool_insert es j e' Hlen]
  iframe

/-- Rocq: `spec_fork_prog`. -/
theorem spec_fork_prog (es : List expr) (σ : state) (e : expr) :
    ⊢@{IProp GF} spec_auth (es, σ) ==∗ spec_auth (es ++ [e], σ) ∗ ∃ j, j ⤇ e := by
  iintro Ha
  unfold spec_auth spec_prog_auth spec_prog_frag
  icases Ha with ⟨Ha, Hh, Ht⟩
  imod ghost_map_insert es.length e (by
    rw [ext_get?_eq, tpool_lookup]; exact List.getElem?_eq_none (le_refl _)) $$ Ha with ⟨Ha, Hf⟩
  imodintro
  rw [ext_insert_eq, to_tpool_app]
  iframe

/-! Heap -/

/-- Rocq: `spec_auth_lookup_heap`. -/
theorem spec_auth_lookup_heap (e1 : List expr) (σ1 : state) (l : Loc) (v : val) (dq : DFrac) :
    ⊢@{IProp GF} spec_auth (e1, σ1) -∗ l ↦ₛ{dq} v -∗ ⌜σ1.heap[l]? = some v⌝ := by
  unfold spec_auth spec_heap_auth spec_heap_frag
  iintro ⟨-, Hh, -⟩ Hf
  iapply ghost_map_lookup $$ Hh Hf

/-- Rocq: `spec_auth_heap_alloc`. -/
theorem spec_auth_heap_alloc (e : List expr) (σ : state) (v : val) :
    ⊢@{IProp GF} spec_auth (e, σ) ==∗
      spec_auth (e, state_upd_heap (·.insert (fresh_loc σ.heap) v) σ) ∗
        fresh_loc σ.heap ↦ₛ v := by
  iintro Ha
  unfold spec_auth spec_heap_auth spec_heap_frag
  icases Ha with ⟨Hp, Hh, Ht⟩
  imod ghost_map_insert (fresh_loc σ.heap) v (by
    rw [ext_get?_eq]
    exact Std.ExtTreeMap.getElem?_eq_none (fresh_loc_is_fresh σ.heap)) $$ Hh with ⟨Hh, Hl⟩
  imodintro
  rw [ext_insert_eq]
  simp only [state_upd_heap_heap, state_upd_heap_tapes]
  iframe

/-- Rocq: `spec_auth_update_heap`. -/
theorem spec_auth_update_heap (w : val) (e1 : List expr) (σ1 : state) (l : Loc) (v : val) :
    ⊢@{IProp GF} spec_auth (e1, σ1) -∗ l ↦ₛ{#1} v ==∗
      spec_auth (e1, state_upd_heap (·.insert l w) σ1) ∗ l ↦ₛ{#1} w := by
  unfold spec_auth spec_heap_auth spec_heap_frag
  iintro ⟨Hp, Hh, Ht⟩ Hf
  imod ghost_map_update w $$ Hh Hf with ⟨Hh, Hf⟩
  imodintro
  rw [ext_insert_eq]
  simp only [state_upd_heap_heap, state_upd_heap_tapes]
  iframe

/-! Tapes -/

/-- Rocq: `spec_auth_lookup_tape`. -/
theorem spec_auth_lookup_tape (e1 : List expr) (σ1 : state) (l : Loc) (v : tape) (dq : DFrac) :
    ⊢@{IProp GF} spec_auth (e1, σ1) -∗ l ↪ₛ{dq} v -∗ ⌜σ1.tapes[l]? = some v⌝ := by
  unfold spec_auth spec_tapes_auth spec_tapes_frag
  iintro ⟨-, -, Ht⟩ Hf
  iapply ghost_map_lookup $$ Ht Hf

/-- Rocq: `spec_auth_update_tape`. -/
theorem spec_auth_update_tape (w : tape) (e1 : List expr) (σ1 : state) (l : Loc) (v : tape) :
    ⊢@{IProp GF} spec_auth (e1, σ1) -∗ l ↪ₛ{#1} v ==∗
      spec_auth (e1, state_upd_tapes (·.insert l w) σ1) ∗ l ↪ₛ{#1} w := by
  unfold spec_auth spec_tapes_auth spec_tapes_frag
  iintro ⟨Hp, Hh, Ht⟩ Hf
  imod ghost_map_update w $$ Ht Hf with ⟨Ht, Hf⟩
  imodintro
  rw [ext_insert_eq]
  simp only [state_upd_tapes_heap', state_upd_tapes_tapes]
  iframe

/-- Rocq: `spec_auth_tape_alloc`. -/
theorem spec_auth_tape_alloc (e : List expr) (σ : state) (N : ℕ) :
    ⊢@{IProp GF} spec_auth (e, σ) ==∗
      spec_auth (e, state_upd_tapes (·.insert (fresh_loc σ.tapes) ⟨N, []⟩) σ) ∗
        fresh_loc σ.tapes ↪ₛ ⟨N, []⟩ := by
  iintro Ha
  unfold spec_auth spec_tapes_auth spec_tapes_frag
  icases Ha with ⟨Hp, Hh, Ht⟩
  imod ghost_map_insert (fresh_loc σ.tapes) (⟨N, []⟩ : tape) (by
    rw [ext_get?_eq]
    exact Std.ExtTreeMap.getElem?_eq_none (fresh_loc_is_fresh σ.tapes)) $$ Ht with ⟨Ht, Hl⟩
  imodintro
  rw [ext_insert_eq]
  simp only [state_upd_tapes_heap', state_upd_tapes_tapes]
  iframe

end theory

/-- Rocq: `spec_ra_init`. -/
theorem spec_ra_init {GF : BundledGFunctors} (es : List expr) (σ : state) [specGpreS GF] :
    ⊢@{IProp GF} |==> ∃ _ : specG_con_prob_lang GF,
      spec_auth (es, σ) ∗ bigSepM (M := tpoolF) (fun n e => n ⤇ e) (to_tpool es) ∗
        bigSepM (M := locF) (fun l v => l ↦ₛ v) σ.heap ∗
        bigSepM (M := locF) (fun α t => α ↪ₛ t) σ.tapes := by
  imod ghost_map_alloc (H := tpoolF) (to_tpool es) with ⟨%γE, He, Hes⟩
  imod ghost_map_alloc (H := locF) σ.heap with ⟨%γH, Hh, Hls⟩
  imod ghost_map_alloc (H := locF) σ.tapes with ⟨%γT, Ht, Hαs⟩
  imodintro
  iexists (specG_con_prob_lang.SpecGS inferInstance γE inferInstance inferInstance γH γT)
  unfold spec_auth spec_prog_auth spec_heap_auth spec_tapes_auth spec_prog_frag spec_heap_frag
    spec_tapes_frag
  iframe

/-! Tapes containing natural numbers defined as a wrapper over backend tapes -/

/-- Rocq: `nat_spec_tape`. -/
def nat_spec_tape {GF : BundledGFunctors} [specG_con_prob_lang GF] (l : Loc) (N : ℕ)
    (ns : List ℕ) : IProp GF :=
  iprop(∃ fs : List (Fin (N + 1)), ⌜fs.map (·.val) = ns⌝ ∗ l ↪ₛ ⟨N, fs⟩)

scoped notation:50 l:50 " ↪ₛN " "(" M "; " ns ")" => nat_spec_tape l M ns

section spec_tape_interface

variable {GF : BundledGFunctors} [S : specG_con_prob_lang GF]

attribute [local instance] specG_con_prob_lang.specG_con_prob_lang_prog
  specG_con_prob_lang.specG_con_prob_lang_heap specG_con_prob_lang.specG_con_prob_lang_tapes

/-- Rocq: `spec_tapeN_to_empty`. -/
theorem spec_tapeN_to_empty (l : Loc) (M : ℕ) :
    ⊢@{IProp GF} l ↪ₛN ( M ; [] ) -∗ l ↪ₛ ⟨M, []⟩ := by
  unfold nat_spec_tape
  iintro ⟨%fs, %Hmap, Hl⟩
  have : fs = [] := List.map_eq_nil_iff.mp Hmap
  subst this
  iexact Hl

/-- Rocq: `empty_to_spec_tapeN`. -/
theorem empty_to_spec_tapeN (l : Loc) (M : ℕ) :
    ⊢@{IProp GF} l ↪ₛ ⟨M, []⟩ -∗ l ↪ₛN ( M ; [] ) := by
  iintro Hl
  unfold nat_spec_tape
  iexists []
  isplitr
  · ipureintro; rfl
  · iexact Hl

/-- Rocq: `read_spec_tape_head`. -/
theorem read_spec_tape_head (l : Loc) (M n : ℕ) (ns : List ℕ) :
    ⊢@{IProp GF} l ↪ₛN ( M ; n :: ns ) -∗
      ∃ (x : Fin (M + 1)) (xs : List (Fin (M + 1))), l ↪ₛ ⟨M, x :: xs⟩ ∗ ⌜x.val = n⌝ ∗
        (l ↪ₛ ⟨M, xs⟩ -∗ l ↪ₛN ( M ; ns )) := by
  unfold nat_spec_tape
  iintro ⟨%fs, %Hmap, Hl⟩
  obtain ⟨x, xs, rfl, hx, hxs⟩ := List.map_eq_cons_iff.mp Hmap
  iexists x, xs
  isplitl [Hl]
  · iexact Hl
  isplitr
  · ipureintro; exact hx
  iintro Hl'
  iexists xs
  isplitr
  · ipureintro; exact hxs
  · iexact Hl'

/-- Rocq: `spec_tapeN_tapeN_contradict`. -/
theorem spec_tapeN_tapeN_contradict (l : Loc) (N M : ℕ) (ns ms : List ℕ) :
    ⊢@{IProp GF} l ↪ₛN ( N ; ns ) -∗ l ↪ₛN ( M ; ms ) -∗ False := by
  unfold nat_spec_tape spec_tapes_frag
  iintro ⟨%fs1, -, H1⟩ ⟨%fs2, -, H2⟩
  ihave %H := ghost_map_elem_ne $$ H1 H2
  exact absurd rfl H

end spec_tape_interface

end ConProbLang
