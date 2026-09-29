module

public import Metrology.Coneris.EctxLifting
public import Metrology.ConProbLang.ClassInstances
public import Metrology.ConProbLang.Notation
public import Metrology.Iris.ErrorCredits
public import Iris.Instances.Lib.GhostMap
public import Iris.Std.HeapInstances

/-!
# Primitive laws of Coneris

Ported from clutch/theories/coneris/primitive_laws.v

This file proves the basic laws of the `con_prob_lang` weakest precondition by applying the
lifting lemmas.

## Design choices (Rocq → Lean)

* `conerisGS GF` bundles the invariant ghost state (`InvGS_gen .hasNoLC GF`, Rocq:
  `invGS_gen HasNoLc Σ`), the ghost maps of the heap (`Loc ↦ val`) and of the tapes
  (`Loc ↦ tape`) with their ghost names, and the error-credit ghost state `ECGS GF` of
  `Metrology.Iris.ErrorCredits` (Rocq: `ecGS Σ`). As in iris-lean's `HeapLangGS`, the invariant
  field is not an instance itself (it is found through `conerisGS_conerisWpGS`), to avoid
  instance diamonds; the other fields are instances. `GF` is an `outParam` of `conerisGS` (as
  in iris-lean's `genHeapGS`), so that the points-to notations, whose ghost names do not
  mention `GF`, determine `GF` by instance search (Rocq finds `Σ` by unification).
* The ghost maps are iris-lean's `GhostMapG GF Loc V (Std.ExtTreeMap Loc · compare)`
  (`loc_map`), matching the representation `Std.ExtTreeMap Loc V` of `state.heap`/`state.tapes`.
  `ghost_map_insert`/`ghost_map_update` produce `Iris.Std.insert m k v`, which is bridged to
  `m.insert k v` by `loc_map_insert_eq`.
* `ec_supply ε` (Rocq) is `ecAuth ε` (`●↯ ε`), and `↯ ε` is `ec ε`.
* `heap_auth q m`/`tapes_auth q m` take `q : Qp` as the Rocq `ghost_map_auth γ q m`.
* Points-to notations: `l ↦{dq} v`, `l ↦□ v`, `l ↦{#q} v`, `l ↦ v` (heap) and
  `l ↪{dq} t`, `l ↪□ t`, `l ↪{#q} t`, `l ↪ t` (tapes), with `t : tape`; Rocq's `(N; fs)` is
  `⟨N, fs⟩`. They unfold to the reducible helpers `heap_elem`/`tapes_elem` (a
  `ghost_map_elem`). The user-level tape `l ↪N ( M ; ns )` is `nat_tape l M ns`, written
  `l ↪N (M; ns)`.
* Mathlib's `α ↪ β` (`Function.Embedding`, `infixr:25`) shares the token `↪`; since Lean
  prefers the longest parse, a tape points-to followed by `∗`/`-∗` must be parenthesised,
  `(l ↪ t) ∗ P`.
* Texan triples are iris-lean's, written with double braces:
  `{{ P }} (e) @ s; E {{ x, RET v; Q }}` (Rocq `{{{ P }}} e @ s; E {{{ x, RET v; Q }}}`) unfolds to
  `⊢ ∀ Φ, P -∗ ▷ (∀ x, Q -∗ Φ v) -∗ WP e @ s; E {{ Φ }}` (without the Rocq `□`, which is
  irrelevant for a closed statement). The Rocq side conditions `TCEq N (Z.to_nat z)` are plain
  equalities `(hN : N = z.toNat)`. In `wp_rand` the postcondition `True` is annotated
  `(iprop(True) : IProp GF)`, since nothing else in that triple fixes `GF`.
* Rocq `#n` for `n : fin (S N)` / `n : nat` is `LitV (LitInt ((n : ℕ) : ℤ))`; `rand #z` is
  `Rand (Val (LitV (LitInt z))) (Val (LitV LitUnit))`, `rand(#lbl:α) #z` is
  `Rand (Val (LitV (LitInt z))) (Val (LitV (LitLbl α)))`.
* `tapeN_ineq` states `Forall (λ n, n ≤ N) ns` as `∀ n ∈ ns, n ≤ N`.
* `hocap_tapes_notin` takes `m : Std.ExtTreeMap Loc (ℕ × List ℕ)` (Rocq: `gmap loc (nat * list nat)`).
* `fin_to_nat <$> fs` is `fs.map (↑)` (i.e. `List.map Fin.val fs`).
* `wp_allocN_seq` produces `[∗list] i ∈ List.range N, (l +ₗ ((i : ℕ) : ℤ)) ↦ v` (Rocq:
  `seq 0 N`), and is proved by induction on `N` with `ghost_map_insert` (Rocq: one
  `ghost_map_insert_big` followed by an induction on the big map); see `heap_auth_alloc_N`.

## Omitted
* `Global Hint Extern 0 (TCEq _ (Z.to_nat _ )) => rewrite Nat2Z.id`: the side conditions are
  plain equalities here.
* The commented-out `spec_tapeN_*` lemmas of the Rocq file.

## Added
* Helpers (not in Rocq): `loc_map`, `loc_map_insert_eq`, `loc_map_get?_eq`,
  `heap_elem`, `tapes_elem`, `nat_tape_timeless` (Rocq infers it by unfolding),
  `conerisGS_state_interp_eq`, `conerisGS_err_interp_eq`, `conerisGS_fork_post_eq`,
  `heap_auth_alloc_N`.
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang

namespace Coneris

/-- Helper: the finite-map type of heaps and tapes, as a type constructor. -/
abbrev loc_map : Type → Type := (Std.ExtTreeMap Loc · compare)

/-- Helper: iris-lean's `PartialMap.insert` on `Std.ExtTreeMap` is `Std.ExtTreeMap.insert`. -/
theorem loc_map_insert_eq {V : Type} (m : loc_map V) (l : Loc) (v : V) :
    Iris.Std.insert m l v = m.insert l v :=
  Std.ExtTreeMap.ext_getElem? fun k => by
    show (m.alter l (fun _ => some v))[k]? = (m.insert l v)[k]?
    simp [Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getElem?_alter]

/-- Helper: iris-lean's `PartialMap.get?` on `Std.ExtTreeMap` is `[·]?`. -/
theorem loc_map_get?_eq {V : Type} (m : loc_map V) (l : Loc) : Iris.Std.get? m l = m[l]? := rfl

/-- Rocq: `conerisGS`. -/
class conerisGS (GF : outParam BundledGFunctors) where
  conerisGS_invG : InvGS_gen .hasNoLC GF
  /-- CMRA for the state -/
  conerisGS_heap : GhostMapG GF Loc val loc_map
  conerisGS_tapes : GhostMapG GF Loc tape loc_map
  /-- ghost names for the state -/
  conerisGS_heap_name : GName
  conerisGS_tapes_name : GName
  /-- CMRA and ghost name for the error -/
  conerisGS_error : ECGS GF

attribute [reducible, instance] conerisGS.conerisGS_heap conerisGS.conerisGS_tapes
  conerisGS.conerisGS_error

export conerisGS (conerisGS_heap_name conerisGS_tapes_name)

/-- Rocq: `progUR`. -/
abbrev progUR : Type := Option (Excl (DiscreteO expr))

/-- Rocq: `partial_cfgO`. -/
abbrev partial_cfgO : Type := DiscreteO (expr × state)

/-- Rocq: `partial_cfgUR`. -/
abbrev partial_cfgUR : Type := Option (Excl partial_cfgO)

section auth

variable {GF : BundledGFunctors} [conerisGS GF]

/-- Rocq: `heap_auth`. -/
def heap_auth (q : Qp) (m : Std.ExtTreeMap Loc val) : IProp GF :=
  ghost_map_auth (H := loc_map) conerisGS_heap_name (DFrac.own q) m

/-- Rocq: `tapes_auth`. -/
def tapes_auth (q : Qp) (m : Std.ExtTreeMap Loc tape) : IProp GF :=
  ghost_map_auth (H := loc_map) conerisGS_tapes_name (DFrac.own q) m

/-- Helper: the heap points-to `l ↦{dq} v` (Rocq: a notation for `ghost_map_elem`). -/
abbrev heap_elem (l : Loc) (dq : DFrac) (v : val) : IProp GF :=
  ghost_map_elem (H := loc_map) conerisGS_heap_name dq l v

/-- Helper: the tape points-to `l ↪{dq} t` (Rocq: a notation for `ghost_map_elem`). -/
abbrev tapes_elem (l : Loc) (dq : DFrac) (t : tape) : IProp GF :=
  ghost_map_elem (H := loc_map) conerisGS_tapes_name dq l t

end auth

/-- Rocq: `conerisGS_conerisWpGS`. -/
@[reducible]
instance conerisGS_conerisWpGS {GF : BundledGFunctors} [conerisGS GF] :
    conerisWpGS con_prob_lang GF where
  conerisWpGS_invGS := conerisGS.conerisGS_invG
  state_interp σ := iprop(heap_auth 1 σ.heap ∗ tapes_auth 1 σ.tapes)
  fork_post _ := iprop(True)
  err_interp ε := ecAuth ε

section interp

variable {GF : BundledGFunctors} [conerisGS GF]

theorem conerisGS_state_interp_eq (σ : state) :
    state_interp σ = iprop(heap_auth (GF := GF) 1 σ.heap ∗ tapes_auth 1 σ.tapes) := rfl

theorem conerisGS_err_interp_eq (ε : ℝ≥0∞) : err_interp ε = ecAuth (GF := GF) ε := rfl

theorem conerisGS_fork_post_eq (v : val) :
    fork_post (Λ := con_prob_lang) v = iprop(True : IProp GF) := rfl

end interp

/-! ## Heap -/

/-- Rocq: `l ↦{dq} v`. -/
notation:50 l:50 " ↦{" dq "} " v:50 => heap_elem l dq v
/-- Rocq: `l ↦□ v`. -/
notation:50 l:50 " ↦□ " v:50 => heap_elem l DFrac.discard v
/-- Rocq: `l ↦{# q} v`. -/
notation:50 l:50 " ↦{#" q "} " v:50 => heap_elem l (DFrac.own q) v
/-- Rocq: `l ↦ v`. -/
notation:50 l:50 " ↦ " v:50 => heap_elem l (DFrac.own 1) v

/-! ## Tapes -/

/-- Rocq: `l ↪{dq} v`. -/
notation:50 l:50 " ↪{" dq "} " v:50 => tapes_elem l dq v
/-- Rocq: `l ↪□ v`. -/
notation:50 l:50 " ↪□ " v:50 => tapes_elem l DFrac.discard v
/-- Rocq: `l ↪{# q} v`. -/
notation:50 l:50 " ↪{#" q "} " v:50 => tapes_elem l (DFrac.own q) v
/-- Rocq: `l ↪ v`. -/
notation:50 l:50 " ↪ " v:50 => tapes_elem l (DFrac.own 1) v

/-! ## User-level tapes -/

/-- Rocq: `nat_tape`. -/
def nat_tape {GF : BundledGFunctors} [conerisGS GF] (l : Loc) (N : ℕ) (ns : List ℕ) :
    IProp GF :=
  iprop(∃ fs : List (Fin (N + 1)), ⌜fs.map (↑) = ns⌝ ∗ (l ↪ ⟨N, fs⟩))

/-- Rocq: `l ↪N ( M ; ns )`. -/
notation:50 l:50 " ↪N " "(" M "; " ns ")" => nat_tape l M ns

/-- Helper (Rocq infers it by unfolding `nat_tape`). -/
instance nat_tape_timeless {GF : BundledGFunctors} [conerisGS GF] (l : Loc) (N : ℕ)
    (ns : List ℕ) : Timeless (l ↪N (N; ns)) := by
  unfold nat_tape
  infer_instance

section tape_interface

variable {GF : BundledGFunctors} [conerisGS GF]

/-! Helper lemmas to go back and forth between the user-level representation of tapes (using
`ℕ`) and the backend (using `Fin`). -/

/-- Rocq: `tapeN_to_empty`. -/
theorem tapeN_to_empty (l : Loc) (M : ℕ) :
    ⊢@{IProp GF} l ↪N (M; []) -∗ (l ↪ ⟨M, []⟩) := by
  unfold nat_tape
  iintro ⟨%fs, %Hmap, Hl'⟩
  obtain rfl := List.map_eq_nil_iff.1 Hmap
  iexact Hl'

/-- Rocq: `empty_to_tapeN`. -/
theorem empty_to_tapeN (l : Loc) (M : ℕ) :
    ⊢@{IProp GF} (l ↪ ⟨M, []⟩) -∗ l ↪N (M; []) := by
  unfold nat_tape
  iintro Hl
  iexists []
  iframe Hl
  ipureintro
  rfl

/-- Rocq: `tapeN_tapeN_contradict`. -/
theorem tapeN_tapeN_contradict (l : Loc) (N M : ℕ) (ns ms : List ℕ) :
    ⊢@{IProp GF} l ↪N (N; ns) -∗ l ↪N (M; ms) -∗ False := by
  unfold nat_tape
  iintro ⟨%fs1, -, H1⟩ ⟨%fs2, -, H2⟩
  icases ghost_map_elem_ne _ _ _ _ _ _ $$ H1 H2 with %H
  exact absurd rfl H

/-- Rocq: `read_tape_head`. -/
theorem read_tape_head (l : Loc) (M n : ℕ) (ns : List ℕ) :
    ⊢@{IProp GF} l ↪N (M; n :: ns) -∗
      ∃ (x : Fin (M + 1)) (xs : List (Fin (M + 1))), (l ↪ ⟨M, x :: xs⟩) ∗ ⌜(x : ℕ) = n⌝ ∗
        ((l ↪ ⟨M, xs⟩) -∗ l ↪N (M; ns)) := by
  unfold nat_tape
  iintro ⟨%xss, %Hmap, Hl'⟩
  obtain ⟨x, xs, rfl, rfl, rfl⟩ := List.map_eq_cons_iff.1 Hmap
  iexists x, xs
  iframe Hl'
  isplitr
  · ipureintro; rfl
  iintro Hl
  iexists xs
  iframe Hl
  ipureintro
  rfl

/-- Rocq: `tapeN_lookup`. -/
theorem tapeN_lookup (α : Loc) (N : ℕ) (ns : List ℕ) (m : Std.ExtTreeMap Loc tape) :
    ⊢@{IProp GF} tapes_auth 1 m -∗ α ↪N (N; ns) -∗
      ⌜∃ ns' : List (Fin (N + 1)), m[α]? = some (⟨N, ns'⟩ : tape) ∧ ns'.map (↑) = ns⌝ := by
  unfold nat_tape
  iintro Hm Hα
  icases Hα with ⟨%fs, %Hmap, Hα⟩
  unfold tapes_auth
  icases ghost_map_lookup $$ Hm Hα with %H
  ipureintro
  exact ⟨fs, H, Hmap⟩

/-- Rocq: `tapeN_update_append`. -/
theorem tapeN_update_append (α : Loc) (N : ℕ) (ns : List (Fin (N + 1)))
    (m : Std.ExtTreeMap Loc tape) (x : Fin (N + 1)) :
    ⊢@{IProp GF} tapes_auth 1 m -∗ α ↪N (N; ns.map (↑)) ==∗
      tapes_auth 1 (m.insert α ⟨N, ns ++ [x]⟩) ∗
        α ↪N (N; ns.map (↑) ++ [(x : ℕ)]) := by
  unfold nat_tape
  iintro Hm Hα
  icases Hα with ⟨%fs, %Hmap, Hα⟩
  have hfs : ns = fs := (List.map_injective_iff.2 Fin.val_injective Hmap).symm
  subst hfs
  unfold tapes_auth
  imod ghost_map_update ⟨N, ns ++ [x]⟩ $$ Hm Hα with ⟨Hm, Hα⟩
  rw [loc_map_insert_eq]
  iframe Hm
  imodintro
  iexists ns ++ [x]
  iframe Hα
  ipureintro
  simp

/-- Rocq: `tapeN_update_append'`. -/
theorem tapeN_update_append' (α : Loc) (N : ℕ) (m : Std.ExtTreeMap Loc tape)
    (ns ns' : List (Fin (N + 1))) :
    ⊢@{IProp GF} tapes_auth 1 m -∗ α ↪N (N; ns.map (↑)) ==∗
      tapes_auth 1 (m.insert α ⟨N, ns ++ ns'⟩) ∗
        α ↪N (N; ns.map (↑) ++ ns'.map (↑)) := by
  unfold nat_tape
  iintro Hm Hα
  icases Hα with ⟨%fs, %Hmap, Hα⟩
  have hfs : ns = fs := (List.map_injective_iff.2 Fin.val_injective Hmap).symm
  subst hfs
  unfold tapes_auth
  imod ghost_map_update ⟨N, ns ++ ns'⟩ $$ Hm Hα with ⟨Hm, Hα⟩
  rw [loc_map_insert_eq]
  iframe Hm
  imodintro
  iexists ns ++ ns'
  iframe Hα
  ipureintro
  simp

/-- Rocq: `tapeN_ineq`. -/
theorem tapeN_ineq (α : Loc) (N : ℕ) (ns : List ℕ) :
    ⊢@{IProp GF} α ↪N (N; ns) -∗ ⌜∀ n ∈ ns, n ≤ N⌝ := by
  unfold nat_tape
  iintro Hα
  icases Hα with ⟨%fs, %Hmap, -⟩
  ipureintro
  subst Hmap
  intro n hn
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hn
  exact Nat.lt_succ_iff.1 x.2

/-- Rocq: `hocap_tapes_notin`. -/
theorem hocap_tapes_notin (α : Loc) (N : ℕ) (ns : List ℕ) (m : Std.ExtTreeMap Loc (ℕ × List ℕ))
    (f : ℕ × List ℕ → ℕ) (g : ℕ × List ℕ → List ℕ) :
    ⊢@{IProp GF} α ↪N (N; ns) -∗ ([∗map] α0 ↦ t ∈ (m : loc_map (ℕ × List ℕ)),
      α0 ↪N (f t; g t)) -∗ ⌜m[α]? = none⌝ := by
  cases Heqn : m[α]? with
  | none =>
    iintro - -
    ipureintro
    rfl
  | some t =>
    iintro Hα Hmap
    ihave Ht := BigSepM.bigSepM_lookup (M := loc_map) (i := α) Heqn $$ Hmap
    iexfalso
    iapply tapeN_tapeN_contradict $$ Hα Ht

end tape_interface

section lifting

variable {GF : BundledGFunctors} [conerisGS GF]
variable {s : Stuckness} {E : CoPset}

/-- Rocq: `wp_rec_löb`. Recursive functions: we do not use this lemma as it is easier to use
Löb induction directly, but this demonstrates that we can state the expected reasoning
principle for recursive functions, without any visible `▷`. -/
theorem wp_rec_löb (f x : binder) (e : expr) (Φ Ψ : val → IProp GF) :
    ⊢ □ (□ (∀ v, Ψ v -∗ WP (App (Val (RecV f x e)) (Val v)) @ s; E {{ Φ }}) -∗
        ∀ v, Ψ v -∗ WP (subst' x v (subst' f (RecV f x e) e)) @ s; E {{ Φ }}) -∗
      ∀ v, Ψ v -∗ WP (App (Val (RecV f x e)) (Val v)) @ s; E {{ Φ }} := by
  iintro #Hrec
  iloeb as IH
  iintro %v HΨ
  iapply wp_pure_step_later (Hφ := True.intro)
  inext
  iapply Hrec $$ [] HΨ
  iintro !> %w HΨ
  iapply IH $$ HΨ

/-! ### Heap -/

/-- Rocq: `wp_alloc`. -/
theorem wp_alloc (v : val) :
    {{ True }} (Alloc (Val v)) @ s; E {{ l, RET LitV (LitLoc l); l ↦ v }} := by
  iintro %Φ - HΦ
  iapply wp_lift_atomic_head_step rfl
  simp only [conerisGS_state_interp_eq]
  iintro %σ1 ⟨Hh, Ht⟩ !>
  isplitr
  · ipureintro
    solve_red
  iintro !> %e2 %σ2 %efs %Hs
  inv_head_step
  rename_i N l _ hN hl
  subst hN hl
  rw [show Int.toNat 1 = 1 from rfl, state_upd_heap_singleton]
  simp only [state_upd_heap_heap, state_upd_heap_tapes, to_val_Val, Option.elim]
  unfold heap_auth
  imod ghost_map_insert (fresh_loc σ1.heap) v
    (Std.ExtTreeMap.getElem?_eq_none (fresh_loc_is_fresh σ1.heap)) $$ Hh with ⟨Hh, Hl⟩
  rw [loc_map_insert_eq]
  imodintro
  iframe Hh Ht
  isplitl
  · iapply HΦ $$ Hl
  · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    iempintro

/-- Helper: allocating a block of `n` fresh heap cells in the ghost heap. -/
theorem heap_auth_alloc_N (m : Std.ExtTreeMap Loc val) (l : Loc) (v : val) (n : ℕ)
    (Hfresh : ∀ i : ℤ, 0 ≤ i → m[l +ₗ i]? = none) :
    ⊢@{IProp GF} heap_auth 1 m ==∗ heap_auth 1 (m ∪ heap_array l (List.replicate n v)) ∗
      [∗list] i ∈ List.range n, (l +ₗ ((i : ℕ) : ℤ)) ↦ v := by
  induction n with
  | zero =>
    have heq : m ∪ heap_array l (List.replicate 0 v) = m := by
      ext k : 1
      simp [map_getElem?_union]
    rw [heq, List.range_zero]
    iintro Hm
    imodintro
    iframe Hm
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    iempintro
  | succ n IH =>
    have hnone : (m ∪ heap_array l (List.replicate n v))[l +ₗ (n : ℤ)]? = none := by
      rw [map_getElem?_union]
      rcases h : (heap_array l (List.replicate n v))[l +ₗ (n : ℤ)]? with _ | w
      · simpa using Hfresh n (by omega)
      · obtain ⟨j, hj, hjl, hjv⟩ := (heap_array_lookup _ _ _ _).1 h
        have hj' := congrArg Loc.loc_car hjl
        simp only [loc_add_loc_car, add_right_inj] at hj'
        subst hj'
        simp at hjv
    have heq : m ∪ heap_array l (List.replicate (n + 1) v) =
        (m ∪ heap_array l (List.replicate n v)).insert (l +ₗ (n : ℤ)) v := by
      rw [heap_array_replicate_S_end]
      ext k : 1
      rw [map_getElem?_union, map_getElem?_insert, map_getElem?_insert, map_getElem?_union]
      split <;> simp
    rw [heq, List.range_succ]
    iintro Hm
    imod IH $$ Hm with ⟨Hm, Hl⟩
    unfold heap_auth
    imod ghost_map_insert (l +ₗ (n : ℤ)) v hnone $$ Hm with ⟨Hm, Hn⟩
    rw [loc_map_insert_eq]
    imodintro
    iframe Hm
    iapply BigSepL.bigSepL_snoc.2
    iframe Hl Hn

/-- Rocq: `wp_allocN_seq`. -/
theorem wp_allocN_seq (N : ℕ) (z : ℤ) (v : val) (hN : N = z.toNat) (hpos : 0 < N) :
    {{ True }} (AllocN (Val (LitV (LitInt z))) (Val v)) @ s; E
    {{ l, RET LitV (LitLoc l); [∗list] i ∈ List.range N, (l +ₗ ((i : ℕ) : ℤ)) ↦ v }} := by
  iintro %Φ - HΦ
  iapply wp_lift_atomic_head_step rfl
  simp only [conerisGS_state_interp_eq]
  iintro %σ1 ⟨Hh, Ht⟩ !>
  isplitr
  · ipureintro
    exact head_reducible_of_rel (AllocNS z N v σ1 _ rfl hN hpos)
  iintro !> %e2 %σ2 %efs %Hs
  inv_head_step
  rename_i N' l _ hN' hl
  subst hN hN' hl
  simp only [state_upd_heap_N, state_upd_heap_heap, state_upd_heap_tapes, to_val_Val,
    Option.elim]
  imod heap_auth_alloc_N σ1.heap (fresh_loc σ1.heap) v z.toNat
    (fun i hi => Std.ExtTreeMap.getElem?_eq_none (fresh_loc_offset_is_fresh σ1.heap i hi))
    $$ Hh with ⟨Hh, Hl⟩
  imodintro
  iframe Hh Ht
  isplitl
  · iapply HΦ $$ Hl
  · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    iempintro

/-- Rocq: `wp_load`. -/
theorem wp_load (l : Loc) (dq : DFrac) (v : val) :
    {{ ▷ l ↦{dq} v }} (Load (Val (LitV (LitLoc l)))) @ s; E {{ RET v; l ↦{dq} v }} := by
  iintro %Φ >Hl HΦ
  iapply wp_lift_atomic_head_step rfl
  simp only [conerisGS_state_interp_eq]
  iintro %σ1 ⟨Hh, Ht⟩
  unfold heap_auth
  icombine Hh Hl gives %H
  rw [loc_map_get?_eq] at H
  imodintro
  isplitr
  · ipureintro
    exact head_reducible_of_rel (LoadS l v σ1 H)
  iintro !> %e2 %σ2 %efs %Hs
  inv_head_step
  rename_i v' H'
  rw [H] at H'
  cases H'
  simp only [to_val_Val, Option.elim]
  imodintro
  iframe Hh Ht
  isplitl
  · iapply HΦ $$ Hl
  · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    iempintro

/-- Rocq: `wp_store`. -/
theorem wp_store (l : Loc) (v' v : val) :
    {{ ▷ l ↦ v' }} (Store (Val (LitV (LitLoc l))) (Val v)) @ s; E
    {{ RET LitV LitUnit; l ↦ v }} := by
  iintro %Φ >Hl HΦ
  iapply wp_lift_atomic_head_step rfl
  simp only [conerisGS_state_interp_eq]
  iintro %σ1 ⟨Hh, Ht⟩
  unfold heap_auth
  icombine Hh Hl gives %H
  rw [loc_map_get?_eq] at H
  imodintro
  isplitr
  · ipureintro
    exact head_reducible_of_rel (StoreS l v' v σ1 H)
  iintro !> %e2 %σ2 %efs %Hs
  inv_head_step
  imod ghost_map_update v $$ Hh Hl with ⟨Hh, Hl⟩
  rw [loc_map_insert_eq]
  simp only [state_upd_heap_heap, state_upd_heap_tapes, to_val_Val, Option.elim]
  imodintro
  iframe Hh Ht
  isplitl
  · iapply HΦ $$ Hl
  · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    iempintro

/-- Rocq: `wp_rand`. -/
theorem wp_rand (N : ℕ) (z : ℤ) (hN : N = z.toNat) :
    {{ True }} (Rand (Val (LitV (LitInt z))) (Val (LitV LitUnit))) @ s; E
    {{ (n : Fin (N + 1)), RET LitV (LitInt ((n : ℕ) : ℤ)); (iprop(True) : IProp GF) }} := by
  subst hN
  iintro %Φ - HΦ
  iapply wp_lift_atomic_head_step rfl
  iintro %σ1 Hσ !>
  isplitr
  · ipureintro
    exact head_reducible_of_rel (RandNoTapeS z z.toNat 0 σ1 rfl)
  iintro !> %e2 %σ2 %efs %Hs
  inv_head_step
  rename_i N' n hN'
  subst hN'
  simp only [to_val_Val, Option.elim]
  imodintro
  iframe Hσ
  isplitl
  · iapply HΦ $$ %n
    itrivial
  · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    iempintro

/-! ### Tapes -/

/-- Rocq: `wp_alloc_tape`. -/
theorem wp_alloc_tape (N : ℕ) (z : ℤ) (hN : N = z.toNat) :
    {{ True }} (alloc (Val (LitV (LitInt z)))) @ s; E
    {{ α, RET LitV (LitLbl α); α ↪N (N; []) }} := by
  subst hN
  iintro %Φ - HΦ
  iapply wp_lift_atomic_head_step rfl
  simp only [conerisGS_state_interp_eq]
  iintro %σ1 ⟨Hh, Ht⟩ !>
  isplitr
  · ipureintro
    exact head_reducible_of_rel (AllocTapeS z z.toNat σ1 _ rfl rfl)
  iintro !> %e2 %σ2 %efs %Hs
  inv_head_step
  rename_i N' l hl hN'
  subst hl hN'
  unfold tapes_auth
  imod ghost_map_insert (fresh_loc σ1.tapes) (⟨z.toNat, []⟩ : tape)
    (Std.ExtTreeMap.getElem?_eq_none (fresh_loc_is_fresh σ1.tapes)) $$ Ht with ⟨Ht, Hl⟩
  rw [loc_map_insert_eq]
  simp only [state_upd_tapes_heap', state_upd_tapes_tapes, to_val_Val, Option.elim]
  imodintro
  iframe Hh Ht
  isplitl
  · iapply HΦ
    iapply empty_to_tapeN $$ Hl
  · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    iempintro

/-- Rocq: `wp_rand_tape`. -/
theorem wp_rand_tape (N : ℕ) (α : Loc) (n : ℕ) (ns : List ℕ) (z : ℤ) (hN : N = z.toNat) :
    {{ ▷ α ↪N (N; n :: ns) }} (Rand (Val (LitV (LitInt z))) (Val (LitV (LitLbl α)))) @ s; E
    {{ RET LitV (LitInt (n : ℤ)); α ↪N (N; ns) ∗ ⌜n ≤ N⌝ }} := by
  subst hN
  iintro %Φ >Hl HΦ
  iapply wp_lift_atomic_head_step rfl
  simp only [conerisGS_state_interp_eq]
  iintro %σ1 ⟨Hh, Ht⟩
  icases read_tape_head α z.toNat n ns $$ Hl with ⟨%x, %xs, Hl, %Hx, Hret⟩
  subst Hx
  unfold tapes_auth
  icombine Ht Hl gives %H
  rw [loc_map_get?_eq] at H
  imodintro
  isplitr
  · ipureintro
    exact head_reducible_of_rel (RandTapeS α z z.toNat x xs σ1 rfl H)
  iintro !> %e2 %σ2 %efs %Hs
  inv_head_step
  case RandTapeS =>
    rename_i N' n' ns' hN' h
    subst hN'
    rw [H] at h
    cases h
    imod ghost_map_update (⟨z.toNat, xs⟩ : tape) $$ Ht Hl with ⟨Ht, Hl⟩
    rw [loc_map_insert_eq]
    simp only [state_upd_tapes_heap', state_upd_tapes_tapes, to_val_Val, Option.elim]
    imodintro
    iframe Hh Ht
    isplitl
    · iapply HΦ
      isplitl
      · iapply Hret $$ Hl
      · ipureintro
        omega
    · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
      iempintro
  all_goals
    rename_i h
    rw [H] at h
    cases h
    try simp_all

/-- Rocq: `wp_rand_tape_empty`. -/
theorem wp_rand_tape_empty (N : ℕ) (z : ℤ) (α : Loc) (hN : N = z.toNat) :
    {{ ▷ α ↪N (N; []) }} (Rand (Val (LitV (LitInt z))) (Val (LitV (LitLbl α)))) @ s; E
    {{ (n : ℕ), RET LitV (LitInt (n : ℤ)); α ↪N (N; []) ∗ ⌜n ≤ N⌝ }} := by
  subst hN
  iintro %Φ >Hl HΦ
  ihave Hl := tapeN_to_empty α z.toNat $$ Hl
  iapply wp_lift_atomic_head_step rfl
  simp only [conerisGS_state_interp_eq]
  iintro %σ1 ⟨Hh, Ht⟩
  unfold tapes_auth
  icombine Ht Hl gives %H
  rw [loc_map_get?_eq] at H
  imodintro
  isplitr
  · ipureintro
    exact head_reducible_of_rel (RandTapeEmptyS α z z.toNat 0 σ1 rfl H)
  iintro !> %e2 %σ2 %efs %Hs
  inv_head_step
  case RandTapeEmptyS =>
    rename_i N' n hN' _
    subst hN'
    simp only [to_val_Val, Option.elim]
    imodintro
    iframe Hh Ht
    isplitl
    · iapply HΦ $$ %n
      isplitl
      · iapply empty_to_tapeN $$ Hl
      · ipureintro
        omega
    · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
      iempintro
  all_goals
    rename_i h
    rw [H] at h
    cases h
    try simp_all

/-- Rocq: `wp_rand_tape_wrong_bound`. -/
theorem wp_rand_tape_wrong_bound (N M : ℕ) (z : ℤ) (α : Loc) (ns : List ℕ) (hN : N = z.toNat)
    (hNM : N ≠ M) :
    {{ ▷ α ↪N (M; ns) }} (Rand (Val (LitV (LitInt z))) (Val (LitV (LitLbl α)))) @ s; E
    {{ (n : ℕ), RET LitV (LitInt (n : ℤ)); α ↪N (M; ns) ∗ ⌜n ≤ N⌝ }} := by
  subst hN
  iintro %Φ >Hl HΦ
  iapply wp_lift_atomic_head_step rfl
  simp only [conerisGS_state_interp_eq]
  iintro %σ1 ⟨Hh, Ht⟩
  iunfold nat_tape at Hl
  icases Hl with ⟨%fs, %Hfs, Hl⟩
  unfold tapes_auth
  icombine Ht Hl gives %H
  rw [loc_map_get?_eq] at H
  imodintro
  isplitr
  · ipureintro
    exact head_reducible_of_rel (RandTapeOtherS α z M z.toNat fs 0 σ1 rfl H hNM)
  iintro !> %e2 %σ2 %efs %Hs
  inv_head_step
  case RandTapeOtherS =>
    rename_i n _ _ _
    simp only [to_val_Val, Option.elim]
    imodintro
    iframe Hh Ht
    isplitl
    · iapply HΦ $$ %n
      isplitl
      · iunfold nat_tape
        iexists fs
        iframe Hl
        ipureintro
        exact Hfs
      · ipureintro
        omega
    · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
      iempintro
  all_goals
    rename_i h
    rw [H] at h
    cases h
    try simp_all

/-- Rocq: `wp_fork`. -/
theorem wp_fork (e : expr) (Φ : val → IProp GF) :
    ⊢ ▷ WP e @ s; ⊤ {{ _v, True }} -∗ ▷ Φ (LitV LitUnit) -∗ WP (Fork e) @ s; E {{ Φ }} := by
  iintro He HΦ
  iapply wp_lift_atomic_head_step rfl
  iintro %σ1 Hσ !>
  isplitr
  · ipureintro
    exact head_reducible_of_rel (ForkS e σ1)
  iintro !> %e2 %σ2 %efs %Hs
  inv_head_step
  simp only [to_val_Val, Option.elim]
  imodintro
  iframe Hσ HΦ
  iapply BigSepL.bigSepL_singleton.2
  iexact He

/-! ### Concurrency -/

/-- Rocq: `wp_cmpxchg_fail`. -/
theorem wp_cmpxchg_fail (v v1 v2 : val) (l : Loc) (dq : DFrac) (Hsafe : vals_compare_safe v v1)
    (Hne : v ≠ v1) :
    {{ ▷ l ↦{dq} v }} (CmpXchg (Val (LitV (LitLoc l))) (Val v1) (Val v2)) @ s; E
    {{ RET PairV v (LitV (LitBool false)); l ↦{dq} v }} := by
  iintro %Φ >Hl HΦ
  iapply wp_lift_atomic_head_step rfl
  simp only [conerisGS_state_interp_eq]
  iintro %σ1 ⟨Hh, Ht⟩
  unfold heap_auth
  icombine Hh Hl gives %H
  rw [loc_map_get?_eq] at H
  imodintro
  isplitr
  · ipureintro
    exact head_reducible_of_rel (CmpXchgS σ1 l v v1 v2 _ H Hsafe rfl)
  iintro !> %e2 %σ2 %efs %Hs
  inv_head_step
  rename_i vl b _ hb H'
  rw [H] at H'
  cases H'
  subst hb
  simp only [Hne, decide_false, Bool.false_eq_true, ↓reduceIte, to_val_Val, Option.elim]
  imodintro
  iframe Hh Ht
  isplitl
  · iapply HΦ $$ Hl
  · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    iempintro

/-- Rocq: `wp_cmpxchg_suc`. -/
theorem wp_cmpxchg_suc (v v1 v2 : val) (l : Loc) (Hsafe : vals_compare_safe v v1)
    (Heq : v = v1) :
    {{ ▷ l ↦ v }} (CmpXchg (Val (LitV (LitLoc l))) (Val v1) (Val v2)) @ s; E
    {{ RET PairV v (LitV (LitBool true)); l ↦ v2 }} := by
  iintro %Φ >Hl HΦ
  iapply wp_lift_atomic_head_step rfl
  simp only [conerisGS_state_interp_eq]
  iintro %σ1 ⟨Hh, Ht⟩
  unfold heap_auth
  icombine Hh Hl gives %H
  rw [loc_map_get?_eq] at H
  imodintro
  isplitr
  · ipureintro
    exact head_reducible_of_rel (CmpXchgS σ1 l v v1 v2 _ H Hsafe rfl)
  iintro !> %e2 %σ2 %efs %Hs
  inv_head_step
  rename_i vl b _ hb H'
  rw [H] at H'
  cases H'
  subst hb
  subst Heq
  imod ghost_map_update v2 $$ Hh Hl with ⟨Hh, Hl⟩
  rw [loc_map_insert_eq]
  simp only [decide_true, ↓reduceIte, state_upd_heap_heap, state_upd_heap_tapes, to_val_Val,
    Option.elim]
  imodintro
  iframe Hh Ht
  isplitl
  · iapply HΦ $$ Hl
  · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    iempintro

/-- Rocq: `wp_xchg`. -/
theorem wp_xchg (v1 v2 : val) (l : Loc) :
    {{ ▷ l ↦ v1 }} (Xchg (Val (LitV (LitLoc l))) (Val v2)) @ s; E {{ RET v1; l ↦ v2 }} := by
  iintro %Φ >Hl HΦ
  iapply wp_lift_atomic_head_step rfl
  simp only [conerisGS_state_interp_eq]
  iintro %σ1 ⟨Hh, Ht⟩
  unfold heap_auth
  icombine Hh Hl gives %H
  rw [loc_map_get?_eq] at H
  imodintro
  isplitr
  · ipureintro
    exact head_reducible_of_rel (XchgS σ1 l v1 v2 H)
  iintro !> %e2 %σ2 %efs %Hs
  inv_head_step
  rename_i v1' H'
  rw [H] at H'
  cases H'
  imod ghost_map_update v2 $$ Hh Hl with ⟨Hh, Hl⟩
  rw [loc_map_insert_eq]
  simp only [state_upd_heap_heap, state_upd_heap_tapes, to_val_Val, Option.elim]
  imodintro
  iframe Hh Ht
  isplitl
  · iapply HΦ $$ Hl
  · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    iempintro

/-- Rocq: `wp_faa`. -/
theorem wp_faa (i1 i2 : ℤ) (l : Loc) :
    {{ ▷ l ↦ LitV (LitInt i1) }} (FAA (Val (LitV (LitLoc l))) (Val (LitV (LitInt i2)))) @ s; E
    {{ RET LitV (LitInt i1); l ↦ LitV (LitInt (i1 + i2)) }} := by
  iintro %Φ >Hl HΦ
  iapply wp_lift_atomic_head_step rfl
  simp only [conerisGS_state_interp_eq]
  iintro %σ1 ⟨Hh, Ht⟩
  unfold heap_auth
  icombine Hh Hl gives %H
  rw [loc_map_get?_eq] at H
  imodintro
  isplitr
  · ipureintro
    exact head_reducible_of_rel (FAAS σ1 l i1 i2 H)
  iintro !> %e2 %σ2 %efs %Hs
  inv_head_step
  rename_i i1' H'
  rw [H] at H'
  cases H'
  imod ghost_map_update (LitV (LitInt (i1 + i2))) $$ Hh Hl with ⟨Hh, Hl⟩
  rw [loc_map_insert_eq]
  simp only [state_upd_heap_heap, state_upd_heap_tapes, to_val_Val, Option.elim]
  imodintro
  iframe Hh Ht
  isplitl
  · iapply HΦ $$ Hl
  · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    iempintro

end lifting

end Coneris
