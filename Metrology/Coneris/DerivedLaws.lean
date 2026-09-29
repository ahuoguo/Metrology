module

public import Metrology.Coneris.PrimitiveLaws

/-!
# Derived laws of Coneris

Ported from clutch/theories/coneris/derived_laws.v

This file extends the Coneris program logic with some derived laws (not using the lifting
lemmas) about arrays. Most of these are taken from the Clutch program logic.

## Design choices (Rocq → Lean)

* `array l dq vs` is `[∗list] i ↦ v ∈ vs, (l +ₗ ((i : ℕ) : ℤ)) ↦{dq} v`, with notations
  `l ↦∗{dq} vs` and `l ↦∗ vs` (as in iris-lean's `HeapLang/DerivedLaws.lean`).
* `is_Some o` is `∃ w, o = some w`; `<[off:=v]> vs` is `vs.set off v`, `vs !! off` is `vs[off]?`, `seq 0 n` is `List.range n`.
* `vec val sz` is core `Vector val sz`; `vreplicate n v` is `Vector.replicate n v`,
  `vs !!! off` is `ws[off]`, `vinsert off v vs` is `ws.set off v`, and the coercion
  `vec_to_list` is `Vector.toList`. `off : fin sz` is `off : Fin sz`.
* Texan triples follow `PrimitiveLaws.lean`: `{{ P }} (e) @ s; E {{ x, RET v; Q }}`.
  Rocq `#(l +ₗ off)` with `off : nat` is `Val (LitV (LitLoc (l +ₗ ((off : ℕ) : ℤ))))`.
* `update_array` is stated as an entailment `l ↦∗{dq} vs ⊢ ...` (Rocq: `⊢ _ -∗ _`), and is
  proved directly by `BigSepL.bigSepL_insert_acc`.
* Instance costs: Rocq's `array_cons_frame ... | 2` (low cost = tried early) is ported as
  `instance (priority := high)`.

## Omitted
* `Global Typeclasses Opaque array`: `array` is a `def`, hence already opaque to instance search.

## Added
* `array_timeless`, `array_fractional`, `array_as_fractional`: commented out in the Rocq file,
  ported here since they are free (as in iris-lean).
* Helper `update_array_read` (not in Rocq): `update_array` specialised to a read, where the
  array is restored unchanged (Rocq inlines `list_insert_id`).
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang

namespace Coneris

/-- Rocq: `array`. The `array` connective is a version of `pointsto` that works with lists of
values. -/
def array {GF : BundledGFunctors} [conerisGS GF] (l : Loc) (dq : DFrac) (vs : List val) :
    IProp GF :=
  iprop([∗list] i ↦ v ∈ vs, (l +ₗ ((i : ℕ) : ℤ)) ↦{dq} v)

/-- Rocq: `l ↦∗{dq} vs`. -/
notation:50 l:50 " ↦∗{" dq "} " vs:50 => array l dq vs
/-- Rocq: `l ↦∗ vs`. -/
notation:50 l:50 " ↦∗ " vs:50 => array l (DFrac.own 1) vs

section lifting

variable {GF : BundledGFunctors} [conerisGS GF]
variable {s : Stuckness} {E : CoPset}

/-- Rocq: `array_timeless` (commented out in Rocq). -/
instance array_timeless (l : Loc) (dq : DFrac) (vs : List val) :
    Timeless (l ↦∗{dq} vs : IProp GF) := by
  unfold array; infer_instance

/-- Rocq: `array_fractional` (commented out in Rocq). -/
instance array_fractional (l : Loc) (vs : List val) :
    Fractional (fun q => (l ↦∗{DFrac.own q} vs : IProp GF)) := by
  unfold array; infer_instance

/-- Rocq: `array_as_fractional` (commented out in Rocq). -/
instance array_as_fractional (l : Loc) (q : Qp) (vs : List val) :
    AsFractional (l ↦∗{DFrac.own q} vs : IProp GF) ioΦ (fun q => l ↦∗{DFrac.own q} vs) ioq q where
  as_fractional := .rfl
  as_fractional_fractional := array_fractional l vs

/-- Rocq: `array_nil`. -/
theorem array_nil (l : Loc) (dq : DFrac) : (l ↦∗{dq} [] : IProp GF) ⊣⊢ emp := .rfl

/-- Rocq: `array_singleton`. -/
theorem array_singleton (l : Loc) (dq : DFrac) (v : val) :
    (l ↦∗{dq} [v] : IProp GF) ⊣⊢ l ↦{dq} v := by
  unfold array
  refine BigSepL.bigSepL_singleton.trans (.of_eq ?_)
  simp

/-- Rocq: `array_app`. -/
theorem array_app (l : Loc) (dq : DFrac) (vs ws : List val) :
    (l ↦∗{dq} (vs ++ ws) : IProp GF) ⊣⊢
      l ↦∗{dq} vs ∗ (l +ₗ ((vs.length : ℕ) : ℤ)) ↦∗{dq} ws := by
  unfold array
  refine BigSepL.bigSepL_append.trans ?_
  refine sep_congr_right (.of_eq ?_)
  refine BigSepL.bigSepL_eq_of_forall_eq <| @fun k x => ?_
  rw [loc_add_assoc]
  congr 3
  omega

/-- Rocq: `array_cons`. -/
theorem array_cons (l : Loc) (dq : DFrac) (v : val) (vs : List val) :
    (l ↦∗{dq} (v :: vs) : IProp GF) ⊣⊢ l ↦{dq} v ∗ (l +ₗ 1) ↦∗{dq} vs := by
  unfold array
  refine BigSepL.bigSepL_cons.trans ?_
  refine sep_congr (.of_eq ?_) (.of_eq (BigSepL.bigSepL_eq_of_forall_eq @fun k x => ?_))
  · simp
  · rw [loc_add_assoc]
    congr 3
    push_cast; omega

/-- Rocq: `array_cons_frame`. -/
instance (priority := high) array_cons_frame (l : Loc) (dq : DFrac) (v : val) (vs : List val)
    {R Q : IProp GF}
    [h : Frame false R iprop(l ↦{dq} v ∗ (l +ₗ 1) ↦∗{dq} vs) Q] :
    Frame false R (l ↦∗{dq} (v :: vs)) Q where
  frame := h.frame.trans (array_cons l dq v vs).2

/-- Rocq: `update_array`. -/
theorem update_array (l : Loc) (dq : DFrac) (vs : List val) (off : ℕ) (v : val)
    (h : vs[off]? = some v) :
    (l ↦∗{dq} vs : IProp GF) ⊢ (l +ₗ ((off : ℕ) : ℤ)) ↦{dq} v ∗
      ∀ v', (l +ₗ ((off : ℕ) : ℤ)) ↦{dq} v' -∗ l ↦∗{dq} vs.set off v' :=
  BigSepL.bigSepL_insert_acc h

/-- Helper (not in Rocq): `update_array` specialised to a read; the array is restored
unchanged (Rocq: `list_insert_id`). -/
theorem update_array_read (l : Loc) (dq : DFrac) (vs : List val) (off : ℕ) (v : val)
    (h : vs[off]? = some v) :
    (l ↦∗{dq} vs : IProp GF) ⊢ (l +ₗ ((off : ℕ) : ℤ)) ↦{dq} v ∗
      ((l +ₗ ((off : ℕ) : ℤ)) ↦{dq} v -∗ l ↦∗{dq} vs) := by
  refine (update_array l dq vs off v h).trans (sep_mono_right ?_)
  refine (forall_elim v).trans (wand_mono .rfl ?_)
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp h
  rw [List.set_getElem_self hlt]

/-! ## Rules for allocation -/

/-- Rocq: `pointsto_seq_array`. -/
theorem pointsto_seq_array (l : Loc) (dq : DFrac) (v : val) (n : ℕ) :
    ([∗list] i ∈ List.range n, (l +ₗ ((i : ℕ) : ℤ)) ↦{dq} v) ⊢
      (l ↦∗{dq} List.replicate n v : IProp GF) := by
  unfold array
  induction n with
  | zero => exact .rfl
  | succ n ih =>
    rw [List.range_succ, List.replicate_succ']
    refine BigSepL.bigSepL_snoc.1.trans (.trans ?_ BigSepL.bigSepL_snoc.2)
    simp only [List.length_replicate]
    exact sep_mono ih .rfl

/-- Rocq: `wp_allocN`. -/
theorem wp_allocN (v : val) (n : ℤ) (hn : 0 < n) :
    {{ True }} (AllocN (Val (LitV (LitInt n))) (Val v)) @ s; E
    {{ l, RET LitV (LitLoc l); (l ↦∗ List.replicate n.toNat v : IProp GF) }} := by
  iintro %Φ - HΦ
  iapply wp_allocN_seq n.toNat n v rfl (by omega)
  · itrivial
  iintro !> %l Hlm
  iapply HΦ
  iapply pointsto_seq_array $$ Hlm

/-- Rocq: `wp_allocN_vec`. -/
theorem wp_allocN_vec (v : val) (n : ℤ) (hn : 0 < n) :
    {{ True }} (AllocN (Val (LitV (LitInt n))) (Val v)) @ s; E
    {{ l, RET LitV (LitLoc l); (l ↦∗ (Vector.replicate n.toNat v).toList : IProp GF) }} :=
  Vector.toList_replicate ▸ wp_allocN v n hn

/-! ## Rules for accessing array elements -/

/-- Rocq: `wp_load_offset`. -/
theorem wp_load_offset (l : Loc) (dq : DFrac) (off : ℕ) (vs : List val) (v : val)
    (Hlookup : vs[off]? = some v) :
    {{ ▷ l ↦∗{dq} vs }} (Load (Val (LitV (LitLoc (l +ₗ ((off : ℕ) : ℤ)))))) @ s; E
    {{ RET v; (l ↦∗{dq} vs : IProp GF) }} := by
  iintro %Φ >Hl HΦ
  icases update_array_read l dq vs off v Hlookup $$ Hl with ⟨Hl1, Hl2⟩
  iapply wp_load $$ Hl1
  iintro !> Hl1
  iapply HΦ
  iapply Hl2 $$ Hl1

/-- Rocq: `wp_load_offset_vec`. -/
theorem wp_load_offset_vec (l : Loc) (dq : DFrac) (sz : ℕ) (off : Fin sz) (vs : Vector val sz) :
    {{ ▷ l ↦∗{dq} vs.toList }} (Load (Val (LitV (LitLoc (l +ₗ ((off : ℕ) : ℤ)))))) @ s; E
    {{ RET vs[off]; (l ↦∗{dq} vs.toList : IProp GF) }} :=
  wp_load_offset l dq off vs.toList vs[off] (by simp)

/-- Rocq: `wp_store_offset`. -/
theorem wp_store_offset (l : Loc) (off : ℕ) (vs : List val) (v : val)
    (Hsome : ∃ w, vs[off]? = some w) :
    {{ ▷ l ↦∗ vs }} (Store (Val (LitV (LitLoc (l +ₗ ((off : ℕ) : ℤ))))) (Val v)) @ s; E
    {{ RET LitV LitUnit; (l ↦∗ vs.set off v : IProp GF) }} := by
  obtain ⟨w, Hlookup⟩ := Hsome
  iintro %Φ >Hl HΦ
  icases update_array l (DFrac.own 1) vs off w Hlookup $$ Hl with ⟨Hl1, Hl2⟩
  iapply wp_store $$ Hl1
  iintro !> Hl1
  iapply HΦ
  iapply Hl2 $$ %v Hl1

/-- Rocq: `wp_store_offset_vec`. -/
theorem wp_store_offset_vec (l : Loc) (sz : ℕ) (off : Fin sz) (vs : Vector val sz) (v : val) :
    {{ ▷ l ↦∗ vs.toList }} (Store (Val (LitV (LitLoc (l +ₗ ((off : ℕ) : ℤ))))) (Val v)) @ s; E
    {{ RET LitV LitUnit; (l ↦∗ (vs.set off v).toList : IProp GF) }} := by
  rw [Vector.toList_set]
  exact wp_store_offset l off vs.toList v (by simp)

end lifting

end Coneris
