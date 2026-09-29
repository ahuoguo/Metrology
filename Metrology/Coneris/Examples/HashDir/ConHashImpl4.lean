module

public import Metrology.Coneris.Examples.HashDir.ConHashInterface4
public import Metrology.Coneris.Examples.HashDir.HashViewInterface
public import Metrology.Coneris.Lib.Map
public import Metrology.Coneris.Lib.Lock
public import Iris.Instances.Lib.GhostMap

/-!
# A concurrent hash with per-key presampling tapes (part 1: programs and `alloc_tapes`)

Ported from clutch/theories/coneris/examples/hash/con_hash_impl4.v (up to and including
`wp_alloc_tapes`; the predicates and `wp_init_hash_state` are in `ConHashImpl4Part2`,
`wp_hashfun_prev` and `hashkey_presample` in `ConHashImpl4Part3`, the concurrent hash and the
interface instance in `ConHashImpl4Part4`).

## Rocq → Lean mapping
* `Class con_hashG Σ `{conerisGS Σ}` (fields `con_hash_lock :: lock.lock`,
  `con_hash_lockG : lockG Σ`, `con_hash_ghost_mapG1 :: ghost_mapG Σ nat (option nat)`,
  `con_hash_ghost_mapG2 :: ghost_mapG Σ nat loc`, `con_hash_ghost_mapG3 :: ghost_mapG Σ nat nat`)
  is the Lean class `con_hashG GF` with the same field names. The ghost maps are
  `GhostMapG GF ℕ V nat_map` (iris-lean's ghost maps over `nat_map = gmap nat`), declared as
  instances. The lock field `con_hash_lock : Lock.lock` is *not* an instance (Lean's `lock`
  class has no `GF` argument, so the instance could never be found); it is always passed
  explicitly, as Rocq does in `compute_con_hash_specialized` (`acquire (lock0 := con_hash_lock)`).
  `con_hash_lockG : con_hash_lock.lockG GF` is passed explicitly to the lock predicates (see
  `Coneris.Lib.Lock`).
* Programs (same names): `alloc_tapes`, `compute_hash`, `compute_hash_specialized`,
  `init_hash_state` (this file), `compute_con_hash`, `compute_con_hash_specialized`,
  `init_con_hash` (`ConHashImpl4Part4`), transcribed with the `cpl` notation.
  `map.set`/`map.get`/`init_map` are `Coneris.Lib.Map.set`/`get`/`init_map`
  (antiquoted `&set`, `&get`, `&init_map`); `alloc "val_size"` is `alloc(val_size)`,
  `rand("α") "val_size"` is `rand(α) val_size`. `compute_hash_specialized val_size vm tm`
  takes the three `val`s (Rocq: `val_size vm tm : val`, antiquoted `&val_size` ...). Rocq's
  `match: .. with SOME "b" => .. | NONE => .. end` nested inside a `NONE` arm is written with
  parentheses (the Rocq `end` delimits it).
* `wp_alloc_tapes`: `gmap nat loc` is `nat_map Loc`, `(λ v, LitV (LitLbl v)) <$> tm` is
  `tm.map (fun _ α => LitV (LitLbl α))`, `i ∈ dom tm` is `i ∈ tm`. The Rocq `iInduction` is
  the Lean induction of the helper `wp_alloc_tapes_aux`.

## Added
* `nat_map_map_insert` (stdpp's `fmap_insert`), `bigSepM_nat_map_map` (stdpp's
  `big_sepM_fmap`), `wp_alloc_tapes_aux` (the `iInduction` of `wp_alloc_tapes`).

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

/-! ## Map helpers -/

/-- Helper (stdpp: `fmap_insert`). -/
theorem nat_map_map_insert {V W : Type} (m : nat_map V) (f : ℕ → V → W) (n : ℕ) (x : V) :
    (m.insert n x).map f = (m.map f).insert n (f n x) := by
  apply Std.ExtTreeMap.ext_getElem?
  intro k
  rw [Std.ExtTreeMap.getElem?_map, Std.ExtTreeMap.getElem?_insert,
    Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getElem?_map]
  split
  · next h => have := compare_eq_iff_eq.mp h; subst this; simp
  · rfl

/-- Helper (stdpp: `big_sepM_fmap`). -/
theorem bigSepM_nat_map_map {PROP : Type _} [BI PROP] {V W : Type} (m : nat_map V)
    (f : ℕ → V → W) (Φ : ℕ → W → PROP) :
    bigSepM (M := nat_map) (fun k w => Φ k w) (m.map f) =
      bigSepM (M := nat_map) (fun k v => Φ k (f k v)) m := by
  show ([∗list] kv ∈ (m.map f).toList, Φ kv.1 kv.2) =
    [∗list] kv ∈ m.toList, Φ kv.1 (f kv.1 kv.2)
  rw [Std.ExtTreeMap.toList_map, BigSepL.bigSepL_map]

/-! ## The ghost state -/

/-- Rocq: `con_hashG`. -/
class con_hashG (GF : BundledGFunctors) [conerisGS GF] where
  con_hash_lock : lock
  con_hash_lockG : con_hash_lock.lockG GF
  con_hash_ghost_mapG1 : GhostMapG GF ℕ (Option ℕ) nat_map
  con_hash_ghost_mapG2 : GhostMapG GF ℕ Loc nat_map
  con_hash_ghost_mapG3 : GhostMapG GF ℕ ℕ nat_map

attribute [reducible, instance] con_hashG.con_hash_ghost_mapG1 con_hashG.con_hash_ghost_mapG2
  con_hashG.con_hash_ghost_mapG3

/-! ## Programs -/

/-- Rocq: `alloc_tapes`. -/
def alloc_tapes : val :=
  cpl_val(rec alloc_tapes val_size tm n :=
    if (n - #1) < #0 then
      #()
    else
      let α := alloc(val_size) in
      &set tm (n - #1) α;
      alloc_tapes val_size tm (n - #1))

/-- Rocq: `compute_hash`. -/
def compute_hash : val :=
  cpl_val(λ val_size vm tm v,
    match &get vm v with
    | some(b) => b
    | none() =>
        (match &get tm v with
         | some(α) =>
             let b := rand(α) val_size in
             &set vm v b;
             b
         | none() => #0))

/-- Rocq: `compute_hash_specialized`. -/
def compute_hash_specialized (val_size vm tm : val) : val :=
  cpl_val(λ v,
    match &get &vm v with
    | some(b) => b
    | none() =>
        (match &get &tm v with
         | some(α) =>
             let b := rand(α) &val_size in
             &set &vm v b;
             b
         | none() => #0))

/-- Rocq: `init_hash_state`. -/
def init_hash_state : val :=
  cpl_val(λ val_size max_val,
    let val_map := &init_map #() in
    let tape_map := &init_map #() in
    &alloc_tapes val_size tape_map (max_val + #1);
    &compute_hash val_size val_map tape_map)

/-- Sanity check: the transcription of `compute_hash_specialized` is the intended AST. -/
example (val_size vm tm : val) : compute_hash_specialized val_size vm tm =
    val.RecV .BAnon (.BNamed "v")
      (Match (App (App (Val get) (Val vm)) (Var "v"))
        .BAnon
          (Match (App (App (Val get) (Val tm)) (Var "v"))
            .BAnon (Val (LitV (LitInt 0)))
            (.BNamed "α")
              (Let (.BNamed "b") (Rand (Val val_size) (Var "α"))
                (Seq (App (App (App (Val set) (Val vm)) (Var "v")) (Var "b")) (Var "b"))))
        (.BNamed "b") (Var "b")) :=
  rfl

section con_hash_impl

variable {GF : BundledGFunctors} [conerisGS GF] [H : con_hashG GF]

/-- The `iInduction` of Rocq's `wp_alloc_tapes`. -/
theorem wp_alloc_tapes_aux (E : CoPset) (val_size : ℕ) (ltm : Loc) (max : ℕ)
    (Φ : val → IProp GF) (k : ℕ) (Hk : k ≤ max) :
    ⊢ ▷ ((∃ tm : nat_map Loc, map_list ltm (tm.map fun _ α => LitV (LitLbl α)) ∗
          ⌜∀ i : ℕ, i < max ↔ i ∈ tm⌝ ∗ [∗map] _i ↦ α ∈ tm, α ↪N (val_size; [])) -∗
          Φ (LitV LitUnit)) -∗
      ∀ tm : nat_map Loc, ⌜∀ i : ℕ, (k ≤ i ∧ i < max) ↔ i ∈ tm⌝ -∗
        map_list ltm (tm.map fun _ α => LitV (LitLbl α)) -∗
        ([∗map] _i ↦ α ∈ tm, α ↪N (val_size; [])) -∗
        WP cpl(&alloc_tapes #val_size #ltm #k) @ E {{ Φ }} := by
  induction k with
  | zero =>
    iintro HΦ %tm %Hdom Hm Htapes
    unfold alloc_tapes
    wp_pures
    imodintro
    iapply HΦ
    iexists tm
    iframe
    ipureintro
    intro i
    rw [← Hdom i]
    omega
  | succ k IH =>
    iintro HΦ
    ihave IH' := IH (by omega) $$ HΦ
    iintro %tm %Hdom Hm Htapes
    unfold alloc_tapes
    wp_pures
    rw [decide_eq_false (by omega : ¬ ((k : ℤ) < 0))]
    wp_pures
    wp_apply wp_alloc_tape val_size (val_size : ℤ) (by simp) $$ [] with %α Hα
    · itrivial
    wp_pures
    wp_apply wp_set ltm _ k (LitV (LitLbl α)) $$ Hm with Hm
    wp_pure
    wp_pure
    wp_pure
    have Hk' : tm[k]? = none := by
      rw [Std.ExtTreeMap.getElem?_eq_none]
      intro h
      have := (Hdom k).2 h
      omega
    iapply IH' $$ %(tm.insert k α) [] [Hm] [Htapes Hα]
    · ipureintro
      intro i
      rw [Std.ExtTreeMap.mem_insert, ← Hdom i]
      constructor
      · intro ⟨h1, h2⟩
        by_cases hi : i = k
        · left; subst hi; exact compare_eq_iff_eq.mpr rfl
        · right; omega
      · rintro (h | ⟨h1, h2⟩)
        · have := compare_eq_iff_eq.mp h; subst this; omega
        · omega
    · rw [nat_map_map_insert]
      iexact Hm
    · rw [← nat_map_insert_eq]
      iapply (BigSepM.bigSepM_insert (M := nat_map)
        (Φ := fun _ α => iprop(α ↪N (val_size; []))) Hk').2
      iframe

/-- Rocq: `wp_alloc_tapes`. -/
theorem wp_alloc_tapes (E : CoPset) (val_size : ℕ) (ltm : Loc) (max : ℕ) :
    {{ map_list ltm ∅ }} cpl(&alloc_tapes #val_size #ltm #max) @ E
    {{ RET LitV LitUnit; (∃ tm : nat_map Loc,
        map_list ltm (tm.map fun _ α => LitV (LitLbl α)) ∗
        ⌜∀ i : ℕ, i < max ↔ i ∈ tm⌝ ∗ [∗map] _i ↦ α ∈ tm, α ↪N (val_size; []) : IProp GF) }} := by
  iintro %Φ Hm HΦ
  iapply wp_alloc_tapes_aux E val_size ltm max Φ max le_rfl $$ HΦ %∅ [] [Hm] []
  · ipureintro
    intro i
    simp
  · rw [Std.ExtTreeMap.map_eq_empty_iff.mpr rfl]
    iexact Hm
  · iapply (BigSepM.bigSepM_empty (M := nat_map)).2
    itrivial

end con_hash_impl

end Coneris.Examples.HashDir.ConHashImpl4
