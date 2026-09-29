module

public import Metrology.Coneris.Examples.HashDir.ConHashInterface0
public import Metrology.Coneris.Examples.HashDir.ConHashInterface1
public import Metrology.Coneris.Examples.HashDir.HashViewInterface
public import Iris.Instances.Lib.GhostMap

/-!
# A concurrent hash implementation (version 1), on top of version 0

Ported from clutch/theories/coneris/examples/hash/con_hash_impl1.v

## Rocq → Lean mapping
* Section `con_hash_impl1`: the section variable `val_size` is explicit; the context
  `Hc: conerisGS Σ, Hs: !ghost_mapG Σ nat (), h : @hash_view Σ Hc, Hhv: hvG Σ,
  hash0: !con_hash0 val_size` is `[conerisGS GF] [Hs : GhostMapG GF ℕ Unit nat_map]
  [h : hash_view GF] (Hhv : h.hvG GF) [hash0 : con_hash0 GF val_size]`, where `hash_view` is
  the (non collision-free) `HashViewInterface.hash_view` and, as in that file, the hash view's
  ghost-state assumption is an explicit argument `Hhv`.
* Programs (same names): `init_hash := init_hash0`, `compute_hash := compute_hash0`,
  `allocate_tape := allocate_tape0`.
* Predicates (same names): `hash_set_frag`, `hash_set`, `hash_auth`, `hash_tape`, `hash_frag`,
  `con_hash_inv`.
  - `v ↪[γ]□ ()` is `γ ↪◯MAP[v]{.discard} ()` and `ghost_map_auth γ 1 m` is `γ ↪●MAP m`
    (iris-lean's ghost maps over `nat_map = gmap nat`).
  - `gset nat` is `Finset ℕ`; `gset_to_gmap () s` is the helper `gset_to_gmap s`;
    `[∗ set] x ∈ s, P x` is `[∗list] x ∈ s.toList, P x` (stdpp's `big_sepS_elements`: a big
    separating conjunction over a set is one over its list of elements); `s ∪ {[x]}` is
    `s ∪ {x}`.
  - `[∗ map] v ∈ m, P v` (the key unused) is `[∗map] _k ↦ v ∈ m, P v`.
  - Rocq defines `con_hash_inv N f l hm R γ1 γ2 γ_lock := con_hash_inv0 N f l hm (..) γ_lock`,
    so that its last argument is `con_hash_inv0`'s lock name, and the Rocq `γ_lock` is really
    the tape name. The Lean definition takes both explicitly
    (`con_hash_inv N f l hm R γ1 γ2 γ_tape γ_lock`), which is the eta-expanded Rocq definition.
* Lemmas (same names): `hash_set_frag_in_set`, `hash_frag_in_hash_set`, `tape_in_hash_set`,
  `hash_tape_presample`, `con_hash_init`, `con_hash_alloc_tape`, `con_hash_spec`.
  - `Forall (λ x, x ∈ s) ns` is `∀ x ∈ ns, x ∈ s`.
  - `hash_tape_presample`: `ε εI εO : nonnegreal` are `ℝ≥0∞`; the real subtraction
    `val_size + 1 - size bad` is the truncated `ℝ≥0∞` one, which does not truncate since every
    element of `bad` is `< val_size + 1` (as in `ConHashInterface1`). The Rocq `SeriesC`
    computation ("copied from error rules") is `Coneris.SeriesC_in_out_le`.
* `Program Definition con_hash_impl1 : con_hash1 val_size` is the definition `con_hash_impl1`
  (not an instance, as in Rocq), taking `Hhv` explicitly. Its `Next Obligation`s are the
  lemmas `con_hash_impl1_hash_auth_exclusive`, `con_hash_impl1_hash_auth_frag_agree`,
  `con_hash_impl1_hash_auth_duplicate`, `con_hash_impl1_hash_frag_frag_agree`,
  `con_hash_impl1_hash_frag_in_hash_set`, `con_hash_impl1_hash_tape_in_hash_set`,
  `con_hash_impl1_hash_set_duplicate`, `con_hash_impl1_hash_set_frag_in_set`,
  `con_hash_impl1_hash_auth_insert`, `con_hash_impl1_hash_set_valid`,
  `con_hash_impl1_hash_tape_valid`, `con_hash_impl1_hash_tape_exclusive` (in this order); the
  timeless/persistent obligations (solved automatically in Rocq) are the instances
  `hash_tape_timeless`, `hash_auth_timeless`, etc.

## Added
* `gset_to_gmap` (stdpp's `gset_to_gmap ()` on `gset nat`), with `gset_to_gmap_getElem?`
  (stdpp's `lookup_gset_to_gmap`), `gset_to_gmap_empty`, `gset_to_gmap_union_singleton`,
  `finset_union_singleton_toList_perm` (stdpp's `big_sepS_insert` via `elements`).

## Omitted
Nothing.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang
open Coneris
open Coneris.Examples.HashDir.HashViewInterface
open Coneris.Examples.HashDir.ConHashInterface0 Coneris.Examples.HashDir.ConHashInterface1

namespace Coneris.Examples.HashDir.ConHashImpl1

/-! ## Finite sets as finite maps (helpers) -/

/-- Helper (stdpp: `gset_to_gmap ()`, on `gset nat`). -/
def gset_to_gmap (s : Finset ℕ) : nat_map Unit :=
  s.toList.foldr (fun x m => m.insert x ()) ∅

theorem list_foldr_insert_getElem? (l : List ℕ) (k : ℕ) :
    (l.foldr (fun x (m : nat_map Unit) => m.insert x ()) ∅)[k]? =
      if k ∈ l then some () else none := by
  induction l with
  | nil => simp
  | cons x l IH =>
    rw [List.foldr_cons, Std.ExtTreeMap.getElem?_insert, IH]
    by_cases hx : x = k
    · subst hx; simp
    · have : compare x k ≠ .eq := by simpa using hx
      simp [this, Ne.symm hx]

/-- Helper (stdpp: `lookup_gset_to_gmap`). -/
theorem gset_to_gmap_getElem? (s : Finset ℕ) (k : ℕ) :
    (gset_to_gmap s)[k]? = if k ∈ s then some () else none := by
  unfold gset_to_gmap
  rw [list_foldr_insert_getElem?]
  simp

/-- Helper (stdpp: `gset_to_gmap_empty`). -/
theorem gset_to_gmap_empty : gset_to_gmap ∅ = ∅ :=
  Std.ExtTreeMap.ext_getElem? fun k => by rw [gset_to_gmap_getElem?]; simp

/-- Helper (stdpp: `gset_to_gmap_union_singleton`), with iris-lean's `insert`. -/
theorem gset_to_gmap_union_singleton (s : Finset ℕ) (n : ℕ) :
    Iris.Std.insert (gset_to_gmap s) n () = gset_to_gmap (s ∪ {n}) := by
  rw [nat_map_insert_eq]
  apply Std.ExtTreeMap.ext_getElem?
  intro k
  rw [Std.ExtTreeMap.getElem?_insert, gset_to_gmap_getElem?, gset_to_gmap_getElem?]
  by_cases hk : n = k
  · subst hk; simp
  · have : compare n k ≠ .eq := by simpa using hk
    simp [this, Ne.symm hk]

/-- Helper: the elements of `s ∪ {n}`, for `n ∉ s` (stdpp: `big_sepS_insert`). -/
theorem finset_union_singleton_toList_perm (s : Finset ℕ) (n : ℕ) (h : n ∉ s) :
    (s ∪ {n}).toList.Perm (n :: s.toList) := by
  rw [show s ∪ {n} = insert n s by rw [Finset.union_comm]; rfl]
  exact Finset.toList_insert h

section con_hash_impl1

variable (val_size : ℕ)
variable {GF : BundledGFunctors} [Hc : conerisGS GF] [Hs : GhostMapG GF ℕ Unit nat_map]
  [h : hash_view GF] (Hhv : h.hvG GF) [hash0 : con_hash0 GF val_size]

/-! ## Code -/

/-- Rocq: `init_hash`. -/
def init_hash : val := hash0.init_hash0
/-- Rocq: `compute_hash`. -/
def compute_hash : val := hash0.compute_hash0
/-- Rocq: `allocate_tape`. -/
def allocate_tape : val := hash0.allocate_tape0

/-! ## Predicates -/

/-- Rocq: `hash_set_frag`. -/
def hash_set_frag (v : ℕ) (γ : GName) : IProp GF := γ ↪◯MAP[v]{.discard} ()

/-- Rocq: `hash_set`. -/
def hash_set (s : Finset ℕ) (γ : GName) : IProp GF :=
  iprop((γ ↪●MAP gset_to_gmap s) ∗ ⌜∀ x, x ∈ s → x < val_size + 1⌝ ∗
    [∗list] x ∈ s.toList, hash_set_frag x γ)

/-- Rocq: `hash_auth`. -/
def hash_auth (m : hmap) (γ1 : h.hv_name) (γ2 : GName) : IProp GF :=
  iprop(h.hv_auth Hhv m γ1 ∗ [∗map] _k ↦ v ∈ m, hash_set_frag v γ2)

/-- Rocq: `hash_tape`. -/
def hash_tape (α : val) (ns : List ℕ) (γ2 : GName) (γ_tape : hash0.hash_tape_gname) :
    IProp GF :=
  iprop(hash0.hash_tape0 α ns γ_tape ∗ [∗list] n ∈ ns, hash_set_frag n γ2)

/-- Rocq: `hash_frag`. -/
def hash_frag (k v : ℕ) (γ1 : h.hv_name) (γ2 : GName) : IProp GF :=
  iprop(h.hv_frag Hhv k v γ1 ∗ hash_set_frag v γ2)

instance hash_set_frag_timeless (v : ℕ) (γ : GName) :
    Timeless (hash_set_frag v γ : IProp GF) := by
  unfold hash_set_frag; infer_instance

instance hash_set_frag_persistent (v : ℕ) (γ : GName) :
    Persistent (hash_set_frag v γ : IProp GF) := by
  unfold hash_set_frag; infer_instance

instance hash_set_timeless (s : Finset ℕ) (γ : GName) :
    Timeless (hash_set val_size s γ : IProp GF) := by
  unfold hash_set; infer_instance

instance hash_auth_timeless (m : hmap) (γ1 : h.hv_name) (γ2 : GName) :
    Timeless (hash_auth Hhv m γ1 γ2) := by
  unfold hash_auth; infer_instance

instance hash_tape_timeless (α : val) (ns : List ℕ) (γ2 : GName)
    (γ_tape : hash0.hash_tape_gname) : Timeless (hash_tape val_size α ns γ2 γ_tape) := by
  unfold hash_tape; infer_instance

instance hash_frag_timeless (k v : ℕ) (γ1 : h.hv_name) (γ2 : GName) :
    Timeless (hash_frag Hhv k v γ1 γ2) := by
  unfold hash_frag; infer_instance

instance hash_frag_persistent (k v : ℕ) (γ1 : h.hv_name) (γ2 : GName) :
    Persistent (hash_frag Hhv k v γ1 γ2) := by
  unfold hash_frag; infer_instance

/-- Rocq: `con_hash_inv`. -/
def con_hash_inv (N : Namespace) (f l hm : val) (R : hmap → IProp GF)
    [HR : ∀ m, Timeless (R m)] (γ1 : h.hv_name) (γ2 : GName) (γ_tape : hash0.hash_tape_gname)
    (γ_lock : hash0.hash_lock_gname) : IProp GF :=
  hash0.con_hash_inv0 N f l hm (fun m => iprop(hash_auth Hhv m γ1 γ2 ∗ R m)) γ_tape γ_lock

instance con_hash_inv_persistent (N : Namespace) (f l hm : val) (R : hmap → IProp GF)
    [HR : ∀ m, Timeless (R m)] (γ1 : h.hv_name) (γ2 : GName) (γ_tape : hash0.hash_tape_gname)
    (γ_lock : hash0.hash_lock_gname) :
    Persistent (con_hash_inv val_size Hhv N f l hm R γ1 γ2 γ_tape γ_lock) := by
  unfold con_hash_inv; infer_instance

/-! ## Lemmas -/

/-- Rocq: `hash_set_frag_in_set`. -/
theorem hash_set_frag_in_set (s : Finset ℕ) (n : ℕ) (γ : GName) :
    ⊢@{IProp GF} hash_set val_size s γ -∗ hash_set_frag n γ -∗ ⌜n ∈ s⌝ := by
  unfold hash_set hash_set_frag
  iintro ⟨H1, -⟩ H2
  ihave %H := ghost_map_lookup (H := nat_map) $$ H1 H2
  ipureintro
  change (gset_to_gmap s)[n]? = some () at H
  rw [gset_to_gmap_getElem?] at H
  by_contra hn
  simp [hn] at H

/-- Rocq: `hash_frag_in_hash_set`. -/
theorem hash_frag_in_hash_set (γ1 : h.hv_name) (γ3 : GName) (s : Finset ℕ) (v res : ℕ) :
    ⊢ hash_frag Hhv v res γ1 γ3 -∗ hash_set val_size s γ3 -∗ ⌜res ∈ s⌝ := by
  unfold hash_frag
  iintro ⟨-, #H1⟩ H2
  iapply hash_set_frag_in_set val_size s res γ3 $$ H2 H1

/-- Rocq: `tape_in_hash_set`. -/
theorem tape_in_hash_set (α : val) (ns : List ℕ) (γ : GName) (γ_tape : hash0.hash_tape_gname)
    (s : Finset ℕ) :
    ⊢ hash_tape val_size α ns γ γ_tape -∗ hash_set val_size s γ -∗ ⌜∀ x ∈ ns, x ∈ s⌝ := by
  unfold hash_tape
  iintro ⟨-, #H1⟩ H2
  iintro %x %Hx
  ihave H := (BigSepL.bigSepL_mem (Φ := fun n => hash_set_frag n γ) Hx) $$ H1
  iapply hash_set_frag_in_set val_size s x γ $$ H2 H

/-- Rocq: `hash_tape_presample`. -/
theorem hash_tape_presample (N : Namespace) (f l hm : val) (R : hmap → IProp GF)
    [HR : ∀ m, Timeless (R m)] (γ_hv : h.hv_name) (γ_set : GName)
    (γ : hash0.hash_tape_gname) (γ_lock : hash0.hash_lock_gname) (α : val) (ns : List ℕ)
    (s bad : Finset ℕ) (ε εI εO : ℝ≥0∞) (E : CoPset) (Hsubset : ↑N ⊆ E)
    (Hbound : ∀ x : ℕ, x ∈ bad → x < val_size + 1)
    (Hineq : εI * bad.card + εO * ((val_size : ℝ≥0∞) + 1 - bad.card) ≤
      ε * ((val_size : ℝ≥0∞) + 1)) :
    ⊢ con_hash_inv val_size Hhv N f l hm R γ_hv γ_set γ γ_lock -∗
      hash_tape val_size α ns γ_set γ -∗ ↯ ε -∗
      hash_set val_size s γ_set -∗
      state_update E E iprop(∃ n : Fin (val_size + 1),
        ((⌜(n : ℕ) ∈ bad⌝ ∗ ↯ εI) ∨ (⌜(n : ℕ) ∉ bad⌝ ∗ ↯ εO)) ∗
        hash_set val_size (s ∪ {(n : ℕ)}) γ_set ∗
        hash_tape val_size α (ns ++ [(n : ℕ)]) γ_set γ) := by
  classical
  unfold con_hash_inv hash_tape hash_set
  iintro #Hinv ⟨Ht, #Hts⟩ Herr ⟨Hs, %Hsb, #Hsfrags⟩
  have Hsum := SeriesC_in_out_le val_size bad ε εI εO Hbound Hineq
  imod hash0.hash_tape_presample N γ γ_lock f l hm _ α ns ε
    (fun x => if (x : ℕ) ∈ bad then εI else εO) E Hsubset Hsum $$ Hinv Ht Herr
    with ⟨%n, Herr, Ht⟩
  -- the error credits
  ihave Herr : iprop((⌜(n : ℕ) ∈ bad⌝ ∗ ↯ εI) ∨ (⌜(n : ℕ) ∉ bad⌝ ∗ ↯ εO)) $$ [Herr]
  · by_cases hb : (n : ℕ) ∈ bad
    · rw [show (if (n : ℕ) ∈ bad then εI else εO) = εI by simp [hb]]
      ileft
      iframe Herr
      ipureintro
      exact hb
    · rw [show (if (n : ℕ) ∈ bad then εI else εO) = εO by simp [hb]]
      iright
      iframe Herr
      ipureintro
      exact hb
  by_cases hns : (n : ℕ) ∈ s
  · have hs : s ∪ {(n : ℕ)} = s := Finset.union_eq_left.2 (Finset.singleton_subset_iff.2 hns)
    ihave #Hn := (BigSepL.bigSepL_mem (Φ := fun x => hash_set_frag x γ_set)
      (Finset.mem_toList.2 hns)) $$ Hsfrags
    imodintro
    iexists n
    rw [hs]
    isplitl [Herr]
    · iexact Herr
    isplitl [Hs]
    · iframe Hs Hsfrags
      ipureintro
      exact Hsb
    isplitl [Ht]
    · iexact Ht
    iapply (BigSepL.bigSepL_snoc (Φ := fun _ x => hash_set_frag x γ_set)).2
    isplitl
    · iexact Hts
    iexact Hn
  · imod ghost_map_insert_persist (H := nat_map) (n : ℕ) ()
      (by show (gset_to_gmap s)[(n : ℕ)]? = none; rw [gset_to_gmap_getElem?]; simp [hns])
      $$ Hs with ⟨Hs, #Hn⟩
    ihave #Hn : hash_set_frag (GF := GF) (n : ℕ) γ_set $$ [Hn]
    · unfold hash_set_frag
      iexact Hn
    rw [gset_to_gmap_union_singleton]
    imodintro
    iexists n
    isplitl [Herr]
    · iexact Herr
    isplitl [Hs]
    · iframe Hs
      isplitr
      · ipureintro
        intro x hx
        rcases Finset.mem_union.1 hx with hx | hx
        · exact Hsb x hx
        · rw [Finset.mem_singleton.1 hx]; exact n.2
      iapply (BigSepL.bigSepL_perm (Φ := fun x => hash_set_frag x γ_set)
        (finset_union_singleton_toList_perm s n hns)).2
      iapply BigSepL.bigSepL_cons.2
      isplitl
      · iexact Hn
      iexact Hsfrags
    isplitl [Ht]
    · iexact Ht
    iapply (BigSepL.bigSepL_snoc (Φ := fun _ x => hash_set_frag x γ_set)).2
    isplitl
    · iexact Hts
    iexact Hn

/-- Rocq: `con_hash_init`. -/
theorem con_hash_init (N : Namespace) (R : hmap → IProp GF) [HR : ∀ m, Timeless (R m)] :
    {{ R ∅ }} cpl(&(init_hash val_size) #())
    {{ (f : val), RET f; ∃ l hm γ1 γ2 γ3 γ_lock,
        con_hash_inv val_size Hhv N f l hm R γ1 γ2 γ3 γ_lock ∗ hash_set val_size ∅ γ2 }} := by
  iintro %Φ HR HΦ
  unfold init_hash
  iapply fupd_pgl_wp
  imod h.hv_auth_init Hhv with ⟨%γ1, H⟩
  imod ghost_map_alloc_empty (GF := GF) (K := ℕ) (V := Unit) (H := nat_map) with ⟨%γ2, H'⟩
  imodintro
  wp_apply hash0.con_hash_init0 N (fun m => iprop(hash_auth Hhv m γ1 γ2 ∗ R m)) $$ [HR H]
    with %f ⟨%l, %hm, %γ3, %γ_lock, #Hinv⟩
  · unfold hash_auth
    iframe HR H
    iapply (BigSepM.bigSepM_empty (M := nat_map)).2
    iempintro
  iapply HΦ
  unfold con_hash_inv hash_set
  iexists l, hm, γ1, γ2, γ3, γ_lock
  rw [gset_to_gmap_empty, Finset.toList_empty]
  iframe Hinv H'
  isplitr
  · ipureintro
    simp
  iapply BigSepL.bigSepL_nil.2
  iempintro

/-- Rocq: `con_hash_alloc_tape`. -/
theorem con_hash_alloc_tape (N : Namespace) (f l hm : val) (R : hmap → IProp GF)
    [HR : ∀ m, Timeless (R m)] (γ1 : h.hv_name) (γ2 : GName) (γ3 : hash0.hash_tape_gname)
    (γ_lock : hash0.hash_lock_gname) :
    {{ con_hash_inv val_size Hhv N f l hm R γ1 γ2 γ3 γ_lock }} cpl(&(allocate_tape val_size) #())
    {{ (α : val), RET α; hash_tape val_size α [] γ2 γ3 }} := by
  iintro %Φ #Hinv HΦ
  unfold allocate_tape
  unfold con_hash_inv
  wp_apply hash0.con_hash_alloc_tape0 N f l hm _ γ3 γ_lock $$ Hinv with %α H
  iapply HΦ
  unfold hash_tape
  iframe H
  iapply BigSepL.bigSepL_nil.2
  iempintro

/-- Rocq: `con_hash_spec`. -/
theorem con_hash_spec (N : Namespace) (f l hm : val) (R : hmap → IProp GF)
    [HR : ∀ m, Timeless (R m)] (γ1 : h.hv_name) (γ2 : GName) (γ3 : hash0.hash_tape_gname)
    (γ_lock : hash0.hash_lock_gname) (Q1 : ℕ → IProp GF) (Q2 : ℕ → List ℕ → IProp GF)
    (α : val) (v : ℕ) :
    {{ con_hash_inv val_size Hhv N f l hm R γ1 γ2 γ3 γ_lock ∗
        (∀ m, R m -∗ hash_auth Hhv m γ1 γ2 -∗ state_update ⊤ ⊤
          (match m[v]? with
           | some res => iprop(R m ∗ hash_auth Hhv m γ1 γ2 ∗ Q1 res)
           | none => iprop(∃ n ns, hash_tape val_size α (n :: ns) γ2 γ3 ∗
                (hash_tape val_size α ns γ2 γ3 ={⊤}=∗ R (m.insert v n) ∗
                  hash_auth Hhv (m.insert v n) γ1 γ2 ∗ Q2 n ns)))) }}
      cpl(&f #v &α)
    {{ (res : ℕ), RET LitV (LitInt (res : ℤ)); Q1 res ∨ ∃ ns, Q2 res ns }} := by
  iintro %Φ ⟨#Hinv, Hvs⟩ HΦ
  unfold con_hash_inv
  iapply hash0.con_hash_spec0 N f l hm _ γ3 γ_lock Q1
    (fun n ns => iprop(Q2 n ns ∗ [∗list] n ∈ ns, hash_set_frag n γ2)) α v $$ [Hvs]
  · iframe Hinv
    iintro %m ⟨Hauth, HR⟩
    imod Hvs $$ HR Hauth with Hcont
    cases hm' : m[v]? with
    | some res =>
      rw [hm'] at *
      dsimp only
      icases Hcont with ⟨HR, Hauth, HQ⟩
      imodintro
      iframe
    | none =>
      rw [hm'] at *
      dsimp only
      unfold hash_tape
      icases Hcont with ⟨%n, %ns, ⟨Ht, #Hfrag⟩, Hcont⟩
      imodintro
      iexists n, ns
      iframe Ht
      iintro Ht
      ihave ⟨-, #Hfrag'⟩ := BigSepL.bigSepL_cons.1 $$ Hfrag
      imod Hcont $$ [Ht] with ⟨HR, Hauth, HQ⟩
      · iframe Ht Hfrag'
      imodintro
      iframe HR Hauth HQ Hfrag'
  iintro !> %res H
  iapply HΦ
  icases H with (HQ | ⟨%ns, HQ, -⟩)
  · ileft
    iexact HQ
  · iright
    iexists ns
    iexact HQ

/-! ## The obligations of `con_hash_impl1` -/

/-- Rocq: `Next Obligation` 1 of `con_hash_impl1` (`hash_auth_exclusive`). -/
theorem con_hash_impl1_hash_auth_exclusive (m m' : hmap) (γ : h.hv_name) (γ2 : GName) :
    ⊢ hash_auth Hhv m γ γ2 -∗ hash_auth Hhv m' γ γ2 -∗ False := by
  unfold hash_auth
  iintro ⟨H1, -⟩ ⟨H2, -⟩
  iapply h.hv_auth_exclusive Hhv m m' γ $$ H1 H2

/-- Rocq: `Next Obligation` 2 of `con_hash_impl1` (`hash_auth_frag_agree`). -/
theorem con_hash_impl1_hash_auth_frag_agree (m : hmap) (k v : ℕ) (γ : h.hv_name) (γ2 : GName) :
    ⊢ hash_auth Hhv m γ γ2 -∗ hash_frag Hhv k v γ γ2 -∗ ⌜m[k]? = some v⌝ := by
  unfold hash_auth hash_frag
  iintro ⟨H1, -⟩ ⟨H2, -⟩
  iapply h.hv_auth_frag_agree Hhv m γ k v $$ [H1 H2]
  iframe

/-- Rocq: `Next Obligation` 3 of `con_hash_impl1` (`hash_auth_duplicate`). -/
theorem con_hash_impl1_hash_auth_duplicate (m : hmap) (k v : ℕ) (γ : h.hv_name) (γ2 : GName)
    (Hlk : m[k]? = some v) :
    ⊢ hash_auth Hhv m γ γ2 -∗ hash_frag Hhv k v γ γ2 := by
  unfold hash_auth hash_frag
  iintro ⟨H1, #H2⟩
  ihave ⟨-, H⟩ := h.hv_auth_duplicate_frag Hhv m k v γ Hlk $$ H1
  iframe H
  iapply (BigSepM.bigSepM_lookup (M := nat_map) (Φ := fun _ v => hash_set_frag v γ2)
    (i := k) (x := v) Hlk) $$ H2

/-- Rocq: `Next Obligation` 4 of `con_hash_impl1` (`hash_frag_frag_agree`). -/
theorem con_hash_impl1_hash_frag_frag_agree (k v1 v2 : ℕ) (γ : h.hv_name) (γ2 : GName) :
    ⊢ hash_frag Hhv k v1 γ γ2 -∗ hash_frag Hhv k v2 γ γ2 -∗ ⌜v1 = v2⌝ := by
  unfold hash_frag
  iintro ⟨H1, -⟩ ⟨H2, -⟩
  iapply h.hv_frag_frag_agree Hhv γ k v1 v2 $$ H1 H2

/-- Rocq: `Next Obligation` 5 of `con_hash_impl1` (`hash_frag_in_hash_set`). -/
theorem con_hash_impl1_hash_frag_in_hash_set (γ1 : h.hv_name) (γ2 : GName) (v res : ℕ) :
    ⊢ hash_frag Hhv v res γ1 γ2 -∗ hash_set_frag res γ2 := by
  unfold hash_frag
  iintro ⟨-, H⟩
  iexact H

/-- Rocq: `Next Obligation` 6 of `con_hash_impl1` (`hash_tape_in_hash_set`). -/
theorem con_hash_impl1_hash_tape_in_hash_set (α : val) (ns : List ℕ) (γ : GName)
    (γ' : hash0.hash_tape_gname) :
    ⊢ hash_tape val_size α ns γ γ' -∗ [∗list] n ∈ ns, hash_set_frag n γ := by
  unfold hash_tape
  iintro ⟨-, #H⟩
  iexact H

/-- Rocq: `Next Obligation` 7 of `con_hash_impl1` (`hash_set_duplicate`). -/
theorem con_hash_impl1_hash_set_duplicate (x : ℕ) (s : Finset ℕ) (γ : GName) (Hx : x ∈ s) :
    ⊢@{IProp GF} hash_set val_size s γ -∗ hash_set_frag x γ := by
  unfold hash_set
  iintro ⟨-, -, #H⟩
  iapply (BigSepL.bigSepL_mem (Φ := fun x => hash_set_frag x γ) (Finset.mem_toList.2 Hx)) $$ H

/-- Rocq: `Next Obligation` 8 of `con_hash_impl1` (`hash_set_frag_in_set`). -/
theorem con_hash_impl1_hash_set_frag_in_set (s : Finset ℕ) (n : ℕ) (γ : GName) :
    ⊢@{IProp GF} hash_set val_size s γ -∗ hash_set_frag n γ -∗ ⌜n ∈ s⌝ :=
  hash_set_frag_in_set val_size s n γ

/-- Rocq: `Next Obligation` 9 of `con_hash_impl1` (`hash_auth_insert`). -/
theorem con_hash_impl1_hash_auth_insert (m : hmap) (k v : ℕ) (γ1 : h.hv_name) (γ2 : GName)
    (Hlk : m[k]? = none) :
    ⊢ hash_set_frag v γ2 -∗ hash_auth Hhv m γ1 γ2 ==∗ hash_auth Hhv (m.insert k v) γ1 γ2 := by
  unfold hash_auth
  iintro #Hv ⟨Ha, Hm⟩
  imod h.hv_auth_insert Hhv m k v γ1 Hlk $$ Ha with ⟨Ha, -⟩
  imodintro
  iframe Ha
  rw [← nat_map_insert_eq]
  iapply (BigSepM.bigSepM_insert (M := nat_map) (Φ := fun _ v => hash_set_frag v γ2) Hlk).2
  iframe Hv Hm

/-- Rocq: `Next Obligation` 10 of `con_hash_impl1` (`hash_set_valid`). -/
theorem con_hash_impl1_hash_set_valid (s : Finset ℕ) (γ : GName) :
    ⊢@{IProp GF} hash_set val_size s γ -∗ ⌜∀ n, n ∈ s → n ≤ val_size⌝ := by
  unfold hash_set
  iintro ⟨-, %H, -⟩
  ipureintro
  intro n hn
  have := H n hn
  omega

/-- Rocq: `Next Obligation` 11 of `con_hash_impl1` (`hash_tape_valid`). -/
theorem con_hash_impl1_hash_tape_valid (α : val) (ns : List ℕ) (γ2 : GName)
    (γ3 : hash0.hash_tape_gname) :
    ⊢ hash_tape val_size α ns γ2 γ3 -∗ ⌜∀ x ∈ ns, x ≤ val_size⌝ := by
  unfold hash_tape
  iintro ⟨H, -⟩
  iapply hash0.hash_tape_valid α ns γ3 $$ H

/-- Rocq: `Next Obligation` 12 of `con_hash_impl1` (`hash_tape_exclusive`). -/
theorem con_hash_impl1_hash_tape_exclusive (α : val) (ns ns' : List ℕ) (γ2 : GName)
    (γ3 : hash0.hash_tape_gname) :
    ⊢ hash_tape val_size α ns γ2 γ3 -∗ hash_tape val_size α ns' γ2 γ3 -∗ False := by
  unfold hash_tape
  iintro ⟨H1, -⟩ ⟨H2, -⟩
  iapply hash0.hash_tape_exclusive α ns ns' γ3 $$ H1 H2

/-- Rocq: `con_hash_impl1` (a `Program Definition`). -/
@[instance_reducible]
def con_hash_impl1 : con_hash1 GF val_size where
  init_hash1 := init_hash val_size
  allocate_tape1 := allocate_tape val_size
  compute_hash1 := compute_hash val_size
  hash_view_gname := h.hv_name
  hash_set_gname := GName
  hash_tape_gname := hash0.hash_tape_gname
  hash_lock_gname := hash0.hash_lock_gname
  con_hash_inv1 N f l hm R _ γ1 γ2 γ3 γ_lock := con_hash_inv val_size Hhv N f l hm R γ1 γ2 γ3 γ_lock
  hash_tape1 := hash_tape val_size
  hash_auth1 := hash_auth Hhv
  hash_frag1 := hash_frag Hhv
  hash_set1 := hash_set val_size
  hash_set_frag1 := hash_set_frag
  hash_tape_timeless := hash_tape_timeless val_size
  hash_auth_timeless := hash_auth_timeless Hhv
  hash_frag_timeless := hash_frag_timeless Hhv
  hash_set_timeless := hash_set_timeless val_size
  hash_set_frag_timeless := hash_set_frag_timeless
  con_hash_inv_persistent N f l hm γ1 γ2 γ3 R _ γ_lock :=
    con_hash_inv_persistent val_size Hhv N f l hm R γ1 γ2 γ3 γ_lock
  hash_frag_persistent := hash_frag_persistent Hhv
  hash_set_frag_persistent := hash_set_frag_persistent
  hash_auth_exclusive := con_hash_impl1_hash_auth_exclusive Hhv
  hash_auth_frag_agree := con_hash_impl1_hash_auth_frag_agree Hhv
  hash_auth_duplicate := con_hash_impl1_hash_auth_duplicate Hhv
  hash_frag_frag_agree := con_hash_impl1_hash_frag_frag_agree Hhv
  hash_frag_in_hash_set := con_hash_impl1_hash_frag_in_hash_set Hhv
  hash_tape_in_hash_set := con_hash_impl1_hash_tape_in_hash_set val_size
  hash_set_duplicate := con_hash_impl1_hash_set_duplicate val_size
  hash_set_frag_in_set := con_hash_impl1_hash_set_frag_in_set val_size
  hash_auth_insert := con_hash_impl1_hash_auth_insert Hhv
  hash_set_valid := con_hash_impl1_hash_set_valid val_size
  hash_tape_valid := con_hash_impl1_hash_tape_valid val_size
  hash_tape_exclusive := con_hash_impl1_hash_tape_exclusive val_size
  hash_tape_presample N f l hm R _ γ_hv γ_set γ γ_lock α ns s bad ε εI εO E HN Hbound Hineq :=
    hash_tape_presample val_size Hhv N f l hm R γ_hv γ_set γ γ_lock α ns s bad ε εI εO E HN
      Hbound Hineq
  con_hash_init1 N R _ := con_hash_init val_size Hhv N R
  con_hash_alloc_tape1 N f l hm R _ γ1 γ2 γ3 γ_lock :=
    con_hash_alloc_tape val_size Hhv N f l hm R γ1 γ2 γ3 γ_lock
  con_hash_spec1 N f l hm R _ γ1 γ2 γ3 γ_lock Q1 Q2 α v :=
    con_hash_spec val_size Hhv N f l hm R γ1 γ2 γ3 γ_lock Q1 Q2 α v

end con_hash_impl1

end Coneris.Examples.HashDir.ConHashImpl1
