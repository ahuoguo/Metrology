module

public import Metrology.Coneris.Examples.HashDir.ConHashImpl4

/-!
# A concurrent hash with per-key presampling tapes (part 2: predicates, `wp_init_hash_state`)

Ported from clutch/theories/coneris/examples/hash/con_hash_impl4.v (from `hashkey` up to and
including `wp_init_hash_state`; see `ConHashImpl4` for the general mapping).

## Rocq → Lean mapping
* `γs : gname * gname * gname` is `γs : GName × GName × GName` (the type fixed by
  `ConHashInterface4`). Lean's `×` nests to the right, Rocq's `*` to the left, so Rocq's
  `γs.1.1`, `γs.1.2`, `γs.2` (the key, tape and value ghost maps) are `γs.1`, `γs.2.1`, `γs.2.2`,
  and Rocq's `(γk, γt, γv)` is `(γk, γt, γv)` (the same components in the same order). `ghost_map_auth γ 1 m` is `γ ↪●MAP m`, `k ↪[γ] v` is `γ ↪◯MAP[k] v`, `k ↪[γ]□ v` is
  `γ ↪◯MAP[k]{.discard} v`.
* Predicates (same names): `hashkey`, `hashfunI`, `hashfunInv`, `hashfun`; the instance
  `haskey_persistent` (same name, Rocq's typo kept) and the helper instances
  `hashkey_timeless`, `hashfunI_timeless`, `hashfun_timeless`, `hashfunInv_persistent`
  (found by `apply _` in Rocq).
  - `gmap nat (option nat)`, `gmap nat loc`, `gmap nat nat` are `nat_map (Option ℕ)`,
    `nat_map Loc`, `nat_map ℕ` (`= hmap`); `i ∈ dom tm` is `i ∈ tm`;
    `(λ n, LitV (LitInt n)) <$> vm` is `vm.map (fun _ n => LitV (LitInt n))`.
  - `if o is Some n then P n else Q` is a Lean `match`.
* `wp_init_hash_state`: `gset_to_gmap None (dom tm)` is `tm.map (fun _ _ => none)`
  (the same map); `rewrite !gset_to_gmap_dom !big_sepM_fmap` is `bigSepM_nat_map_map`.
  `i < S max` is `i < max + 1`. The binders `γs tm hash` are kept.

## Omitted
Nothing.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang
open Coneris Coneris.Lib.Map Coneris.Lib.Lock
open Coneris.Examples.HashDir.HashViewInterface (hmap nat_map nat_map_insert_eq)

namespace Coneris.Examples.HashDir.ConHashImpl4

section con_hash_impl

variable {GF : BundledGFunctors} [conerisGS GF] [H : con_hashG GF]

/-- Rocq: `hashkey`. -/
def hashkey (γs : GName × GName × GName) (k : ℕ) (v : Option ℕ) : IProp GF :=
  match v with
  | some n => iprop(∃ α : Loc, (γs.2.1 ↪◯MAP[k]{.discard} α) ∗
      (γs.1 ↪◯MAP[k]{.discard} (some n : Option ℕ)))
  | none => γs.1 ↪◯MAP[k] (none : Option ℕ)

/-- Rocq: `haskey_persistent`. -/
instance haskey_persistent (γs : GName × GName × GName) (k n : ℕ) :
    Persistent (hashkey (GF := GF) γs k (some n)) := by
  unfold hashkey; infer_instance

instance hashkey_timeless (γs : GName × GName × GName) (k : ℕ) (v : Option ℕ) :
    Timeless (hashkey (GF := GF) γs k v) := by
  unfold hashkey; cases v <;> infer_instance

/-- Helper: the per-key resource of `hashfunI` (Rocq: inline
`if o is Some n then α ↪N (val_size; [n]) ∨ k ↪[γs.2.2]□ n else α ↪N (val_size; [])`). -/
def hashfunI_tape (γs : GName × GName × GName) (val_size k : ℕ) (α : Loc) (o : Option ℕ) :
    IProp GF :=
  match o with
  | some n => iprop((α ↪N (val_size; [n])) ∨ (γs.2.2 ↪◯MAP[k]{.discard} n))
  | none => iprop(α ↪N (val_size; []))

instance hashfunI_tape_timeless (γs : GName × GName × GName) (val_size k : ℕ) (α : Loc)
    (o : Option ℕ) : Timeless (hashfunI_tape (GF := GF) γs val_size k α o) := by
  unfold hashfunI_tape; cases o <;> infer_instance

/-- Rocq: `hashfunI`. -/
def hashfunI (γs : GName × GName × GName) (val_size : ℕ) : IProp GF :=
  iprop(∃ m : nat_map (Option ℕ),
    (γs.1 ↪●MAP m) ∗
    [∗map] k ↦ o ∈ m,
      ∃ α : Loc, (γs.2.1 ↪◯MAP[k]{.discard} α) ∗ hashfunI_tape γs val_size k α o)

instance hashfunI_timeless (γs : GName × GName × GName) (val_size : ℕ) :
    Timeless (hashfunI (GF := GF) γs val_size) := by
  unfold hashfunI; infer_instance

/-- Rocq: `hashfunInv`. -/
def hashfunInv (N : Namespace) (γs : GName × GName × GName) (val_size : ℕ) : IProp GF :=
  inv N (hashfunI γs val_size)

instance hashfunInv_persistent (N : Namespace) (γs : GName × GName × GName) (val_size : ℕ) :
    Persistent (hashfunInv (GF := GF) N γs val_size) := by
  unfold hashfunInv; infer_instance

/-- Rocq: `hashfun`. (Sequential) hash function. -/
def hashfun (γs : GName × GName × GName) (val_size max : ℕ) (f : val) : IProp GF :=
  iprop(∃ (lvm ltm : Loc) (vm : hmap) (tm : nat_map Loc),
    ⌜∀ i : ℕ, i ≤ max ↔ i ∈ tm⌝ ∗
    ⌜f = compute_hash_specialized (LitV (LitInt (val_size : ℤ))) (LitV (LitLoc lvm))
      (LitV (LitLoc ltm))⌝ ∗
    map_list lvm (vm.map fun _ (n : ℕ) => LitV (LitInt (n : ℤ))) ∗
    map_list ltm (tm.map fun _ (α : Loc) => LitV (LitLbl α)) ∗
    (γs.2.1 ↪●MAP tm) ∗
    (γs.2.2 ↪●MAP vm) ∗
    [∗map] k ↦ n ∈ vm, γs.1 ↪◯MAP[k]{.discard} (some n : Option ℕ))

instance hashfun_timeless (γs : GName × GName × GName) (val_size max : ℕ) (f : val) :
    Timeless (hashfun (GF := GF) γs val_size max f) := by
  unfold hashfun; infer_instance

/-- Rocq: `wp_init_hash_state`. -/
theorem wp_init_hash_state (N : Namespace) (val_size max : ℕ) :
    {{ True }} cpl(&init_hash_state #val_size #max)
    {{ (γs : GName × GName × GName) (tm : nat_map Loc) hash, RET hash;
        (hashfun γs val_size max hash ∗
        hashfunInv N γs val_size ∗
        ⌜∀ i : ℕ, i < max + 1 ↔ i ∈ tm⌝ ∗
        ([∗map] k ↦ _v ∈ tm, hashkey γs k none) : IProp GF) }} := by
  iintro %Φ - HΦ
  unfold init_hash_state
  wp_pures
  wp_apply wp_init_map $$ [] with %lvm Hvm
  · itrivial
  wp_pures
  wp_apply wp_init_map $$ [] with %ltm Htm
  · itrivial
  wp_pures
  rw [show ((max : ℤ) + 1) = ((max + 1 : ℕ) : ℤ) by push_cast; rfl]
  wp_apply wp_alloc_tapes ⊤ val_size ltm (max + 1) $$ Htm with ⟨%tm, Htm, %Hdom, Htapes⟩
  unfold compute_hash
  wp_pures
  imod ghost_map_alloc (GF := GF) (H := nat_map) (tm.map fun _ _ => (none : Option ℕ))
    with ⟨%γk, HkeyA, Hkeys⟩
  imod ghost_map_alloc_empty (GF := GF) (K := ℕ) (V := Loc) (H := nat_map) with ⟨%γt, HtapesA⟩
  imod ghost_map_insert_persist_big (H := nat_map) tm
    (LawfulPartialMap.disjoint_empty_right tm) $$ HtapesA with ⟨HtapesA, #Htapes'⟩
  imod ghost_map_alloc_empty (GF := GF) (K := ℕ) (V := ℕ) (H := nat_map) with ⟨%γv, HvalsA⟩
  rw [LawfulPartialMap.union_empty_right, bigSepM_nat_map_map]
  have hmono : ([∗map] k ↦ α ∈ tm, iprop((γt ↪◯MAP[k]{.discard} α) ∗ α ↪N (val_size; []))) ⊢
      [∗map] k ↦ o ∈ tm, iprop(∃ α : Loc, (γt ↪◯MAP[k]{.discard} α) ∗
        hashfunI_tape (GF := GF) (γk, γt, γv) val_size k α none) :=
    BigSepM.bigSepM_mono fun _ => by
      iintro ⟨H1, H2⟩
      iexists _
      unfold hashfunI_tape
      iframe
  imod inv_alloc N ⊤ (hashfunI (γk, γt, γv) val_size) $$ [HkeyA Htapes] with #HI
  · inext
    unfold hashfunI
    iexists (tm.map fun _ _ => (none : Option ℕ))
    iframe HkeyA
    rw [bigSepM_nat_map_map]
    iapply hmono
    rw [BigSepM.bigSepM_sep_eq]
    iframe
    iexact Htapes'
  imodintro
  iapply HΦ $$ %(γk, γt, γv) %tm
  unfold hashfun hashfunInv
  iframe HI
  isplitl [Hvm Htm HtapesA HvalsA]
  · iexists lvm, ltm, ∅, tm
    rw [Std.ExtTreeMap.map_eq_empty_iff.mpr rfl]
    iframe
    isplitr
    · ipureintro
      intro i
      rw [← Hdom i]
      omega
    isplitr
    · ipureintro
      rfl
    iapply (BigSepM.bigSepM_empty (M := nat_map)).2
    itrivial
  isplitr
  · ipureintro
    exact Hdom
  unfold hashkey
  iexact Hkeys

end con_hash_impl

end Coneris.Examples.HashDir.ConHashImpl4
