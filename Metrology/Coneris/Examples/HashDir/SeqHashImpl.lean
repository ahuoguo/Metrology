module

public import Metrology.Coneris.Examples.HashDir.SeqHashInterface
public import Metrology.Coneris.Lib.Map
public import Metrology.Coneris.Lib.HocapRand

/-!
# A sequential hash implementation against the collision-free hash view interface
(part 1: programs, predicates and simple specs)

Ported from clutch/theories/coneris/examples/hash/seq_hash_impl.v (up to and including
`wp_hash_allocate_tape`; `coll_free_hash_presample` is in `SeqHashImplPart2`,
`wp_insert_no_coll` and `seq_hashG_impl` in `SeqHashImplPart3`).

(Rocq: "test: a sequential hash implementation that the coll-free hash view interface. Not
finished and should be deleted".)

## Rocq → Lean mapping
* The section context `conerisGS Σ, r1 : rand_spec, L : randG Σ, hv1 : hash_view, L' : hvG Σ,
  HinG' : abstract_tapesGS Σ` is `[conerisGS GF] [r1 : rand_spec GF] (L : r1.randG GF)
  [hv1 : hash_view GF] (L' : hv1.hvG GF) [HinG' : abstract_tapesGS GF]`, where `hash_view` is
  the collision-free `CollFreeHashViewInterface.hash_view` and `rand_spec` is
  `Coneris.Lib.HocapRand.rand_spec`. The explicit `L`, `L'` and the section variable
  `val_size` are explicit arguments (in this order) of the definitions/lemmas using them.
* Programs (same names): `init_hash_state`, `compute_hash_specialized`, `compute_hash`,
  `init_hash`, `allocate_tape`, transcribed with the `cpl` notation; `rand_tape` and
  `rand_allocate_tape` are the `rand_spec` operations `r1.rand_tape`, `r1.rand_allocate_tape`.
  Rocq's binder `"_"` is the named binder `"_"`.
* Predicates (same names): `hashfun`, `hash_tape`, `coll_free_hashfun`.
  - `gmap nat nat` is `hmap`, `(λ b, #b) <$> m` is `m.map (fun _ b => #b)`, `map_Forall P m` is
    `∀ k x, m[k]? = some x → P k x`.
  - `gmap val (list nat)` is `val_map (List ℕ)` (`Coneris.Lib.AbstractTape`),
    `(λ x, (val_size, x)) <$> tape_m` is `tape_m.map (fun _ x => (val_size, x))`.
  - `NoDup l` is `l.Nodup`; `(map_to_list m).*2` is `m.toList.map (fun p => p.2)`.
* Lemmas (same names): `coll_free_hashfun_implies_hashfun`, `timeless_hashfun`,
  `timeless_hashfun_amortized`, `coll_free_hashfun_implies_coll_free`,
  `hashfun_implies_bounded_range`, `coll_free_hashfun_implies_bounded_range`, `wp_init_hash`,
  `coll_free_insert`, `wp_hashfun_prev`, `wp_coll_free_hashfun_prev`,
  `wp_coll_free_hashfun_frag_prev`, `wp_hash_allocate_tape`.
  `P -∗ Q` lemmas are stated as `⊢ P -∗ Q` (or `P ⊢ Q`); Texan triples are iris-lean's
  `{{ P }} e @ E {{ x, RET v; Q }}`; `RET #b` (`b : nat`) is `RET LitV (LitInt (b : ℤ))`.
* In `coll_free_insert`, `Forall (λ x, z ≠ snd x) (map_to_list m)` is
  `∀ x ∈ m.toList, z ≠ x.2`.

## Added
* `hmap_map_insert` (stdpp's `fmap_insert` for the value map), `tapes_map_insert` (the same
  for the tape map), `toList_insert_perm_nat`, `toList_insert_perm_val` (stdpp's
  `map_to_list_insert`), `tape_m_elements_insert_none`, `tape_m_elements_insert`,
  `tape_m_elements_lookup` (the permutation reasoning of Rocq's `map_to_list_insert` /
  `insert_delete` rewrites), `tapes_lookup_of_map`.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang
open Coneris Coneris.Lib.Map Coneris.Lib.HocapRand Coneris.Lib.AbstractTape
open Coneris.Examples.HashDir.CollFreeHashViewInterface
open Coneris.Examples.HashDir.SeqHashInterface
open Coneris.Examples.HashDir.HashViewInterface (hmap nat_map nat_map_insert_eq)

namespace Coneris.Examples.HashDir.SeqHashImpl

/-! ## Map helpers -/

/-- Helper (stdpp: `fmap_insert`), for the value map of `hashfun`. -/
theorem hmap_map_insert (m : hmap) (n x : ℕ) :
    (m.insert n x).map (fun _ (b : ℕ) => LitV (LitInt (b : ℤ))) =
      (m.map (fun _ (b : ℕ) => LitV (LitInt (b : ℤ)))).insert n (LitV (LitInt (x : ℤ))) := by
  apply Std.ExtTreeMap.ext_getElem?
  intro k
  rw [Std.ExtTreeMap.getElem?_map, Std.ExtTreeMap.getElem?_insert,
    Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getElem?_map]
  split <;> simp

/-- Helper (stdpp: `fmap_insert`), for the tape map of `hashfun`. -/
theorem tapes_map_insert (tape_m : val_map (List ℕ)) (α : val) (ns : List ℕ) (N : ℕ) :
    (tape_m.insert α ns).map (fun _ x => (N, x)) =
      (tape_m.map (fun _ x => (N, x))).insert α (N, ns) := by
  apply Std.ExtTreeMap.ext_getElem?
  intro k
  rw [Std.ExtTreeMap.getElem?_map, Std.ExtTreeMap.getElem?_insert,
    Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getElem?_map]
  split <;> simp

/-- Helper: a lookup in the mapped tape map. -/
theorem tapes_lookup_of_map (tape_m : val_map (List ℕ)) (α : val) (N N' : ℕ) (ns : List ℕ)
    (h : (tape_m.map (fun _ x => (N, x)))[α]? = some (N', ns)) : tape_m[α]? = some ns := by
  rw [Std.ExtTreeMap.getElem?_map] at h
  cases h' : tape_m[α]? with
  | none => simp [h'] at h
  | some t => simp only [h', Option.map_some, Option.some.injEq, Prod.mk.injEq] at h; rw [h.2]

/-- Helper (stdpp: `map_to_list_insert`), for `hmap`. -/
theorem toList_insert_perm_nat (m : hmap) (k v : ℕ) (h : m[k]? = none) :
    (m.insert k v).toList.Perm ((k, v) :: m.toList) := by
  have := LawfulFiniteMap.toList_insert (M := nat_map) (m := m) (k := k) (v := v) h
  rwa [nat_map_insert_eq] at this

/-- Helper (stdpp: `map_to_list_insert`), for `val_map`. -/
theorem toList_insert_perm_val {V : Type} (m : val_map V) (k : val) (v : V) (h : m[k]? = none) :
    (m.insert k v).toList.Perm ((k, v) :: m.toList) := by
  have := LawfulFiniteMap.toList_insert (M := val_map) (m := m) (k := k) (v := v) h
  rwa [val_map_insert_eq] at this

/-- Helper: `tape_m_elements` of a fresh insertion. -/
theorem tape_m_elements_insert_none (tape_m : val_map (List ℕ)) (α : val) (t : List ℕ)
    (h : tape_m[α]? = none) :
    (tape_m_elements (tape_m.insert α t)).Perm (t ++ tape_m_elements tape_m) := by
  unfold tape_m_elements
  have := ((toList_insert_perm_val tape_m α t h).map (fun p => p.2)).flatten
  simpa using this

/-- Helper: `tape_m_elements` of an insertion, in terms of the erased map. -/
theorem tape_m_elements_insert (tape_m : val_map (List ℕ)) (α : val) (t : List ℕ) :
    (tape_m_elements (tape_m.insert α t)).Perm (t ++ tape_m_elements (tape_m.erase α)) := by
  have heq : tape_m.insert α t = (tape_m.erase α).insert α t := by
    apply Std.ExtTreeMap.ext_getElem?
    intro k
    simp only [Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getElem?_erase]
    split <;> rfl
  rw [heq]
  exact tape_m_elements_insert_none _ α t (by simp)

/-- Helper: `tape_m_elements` of a map with a known entry. -/
theorem tape_m_elements_lookup (tape_m : val_map (List ℕ)) (α : val) (t : List ℕ)
    (h : tape_m[α]? = some t) :
    (tape_m_elements tape_m).Perm (t ++ tape_m_elements (tape_m.erase α)) := by
  have heq : tape_m = tape_m.insert α t := by
    apply Std.ExtTreeMap.ext_getElem?
    intro k
    rw [Std.ExtTreeMap.getElem?_insert]
    split
    · next hk => rw [← h]; congr 1; exact (compare_eq_iff_eq.mp hk).symm
    · rfl
  conv => lhs; rw [heq]
  exact tape_m_elements_insert tape_m α t

section seq_hash_impl

variable {GF : BundledGFunctors} [conerisGS GF] [r1 : rand_spec GF] (L : r1.randG GF)
variable [hv1 : hash_view GF] (L' : hv1.hvG GF) [HinG' : abstract_tapesGS GF]
variable (val_size : ℕ)

/-! ## Programs -/

/-- Rocq: `init_hash_state`. A hash function's internal state is a map from previously queried
keys to their hash value. -/
def init_hash_state : val := init_map

/-- Rocq: `compute_hash_specialized`. To hash a value `v`, we check whether it is in the map
(i.e. it has been previously hashed). If it has we return the saved hash value, otherwise we
draw a hash value and save it in the map. -/
def compute_hash_specialized (hm : val) : val :=
  cpl_val(λ v α,
    match &get &hm v with
    | some(b) => b
    | none() =>
        let b := &(r1.rand_tape) α #val_size in
        &set &hm v b;
        b)

/-- Sanity check: the transcription of `compute_hash_specialized` is the intended AST. -/
example (hm : val) : compute_hash_specialized val_size hm =
    val.RecV .BAnon (.BNamed "v") (expr.Rec .BAnon (.BNamed "α")
      (Match (App (App (Val get) (Val hm)) (Var "v"))
        .BAnon (Let (.BNamed "b")
          (App (App (Val r1.rand_tape) (Var "α")) (Val (LitV (LitInt (val_size : ℤ)))))
          (Seq (App (App (App (Val set) (Val hm)) (Var "v")) (Var "b")) (Var "b")))
        (.BNamed "b") (Var "b"))) :=
  rfl

/-- Rocq: `compute_hash`. -/
def compute_hash : val :=
  cpl_val(λ hm v α,
    match &get hm v with
    | some(b) => b
    | none() =>
        let b := &(r1.rand_tape) α #val_size in
        &set hm v b;
        b)

/-- Rocq: `init_hash`. `init_hash` returns a hash as a function, basically wrapping the
internal state in the returned function. -/
def init_hash : val :=
  cpl_val(λ "_",
    let hm := &init_hash_state #() in
    &(compute_hash val_size) hm)

/-- Rocq: `allocate_tape`. -/
def allocate_tape : val :=
  cpl_val(λ "_", &(r1.rand_allocate_tape) #val_size)

/-! ## Predicates -/

/-- Rocq: `hashfun`. -/
def hashfun (f : val) (m : hmap) (tape_m : val_map (List ℕ)) (γ : GName) : IProp GF :=
  iprop(∃ hm : Loc, ⌜f = compute_hash_specialized val_size (LitV (LitLoc hm))⌝ ∗
    map_list hm (m.map (fun _ (b : ℕ) => LitV (LitInt (b : ℤ)))) ∗
    ⌜∀ ind i : ℕ, m[ind]? = some i → 0 ≤ i ∧ i ≤ val_size⌝ ∗
    -- the tapes
    (●ₐ (tape_m.map (fun _ x => (val_size, x))) @ γ) ∗
    [∗map] α ↦ t ∈ tape_m, r1.rand_tapes L α (val_size, t))

/-- Rocq: `hash_tape`. -/
def hash_tape (α : val) (ns : List ℕ) (γ : GName) : IProp GF :=
  α ◯↪N (val_size; ns) @ γ

/-- Rocq: `coll_free_hashfun`. -/
def coll_free_hashfun (f : val) (m : hmap) (tape_m : val_map (List ℕ)) (γ1 : GName)
    (γ2 : hv1.hv_name) : IProp GF :=
  iprop(hashfun L val_size f m tape_m γ1 ∗ hv1.hv_auth L' m γ2 ∗
    ⌜(tape_m_elements tape_m ++ m.toList.map (fun p => p.2)).Nodup⌝)

/-- Rocq: `coll_free_hashfun_implies_hashfun`. -/
theorem coll_free_hashfun_implies_hashfun (f : val) (m : hmap) (γ1 : GName) (γ2 : hv1.hv_name)
    (tape_m : val_map (List ℕ)) :
    coll_free_hashfun L L' val_size f m tape_m γ1 γ2 ⊢ hashfun L val_size f m tape_m γ1 := by
  unfold coll_free_hashfun
  iintro ⟨H, -⟩
  iexact H

/-- Rocq: `timeless_hashfun`. -/
instance timeless_hashfun (f : val) (m : hmap) (tape_m : val_map (List ℕ)) (γ : GName) :
    Timeless (hashfun L val_size f m tape_m γ) := by
  unfold hashfun abstract_tapes_auth; infer_instance

/-- Rocq: `timeless_hashfun_amortized`. -/
instance timeless_hashfun_amortized (f : val) (m : hmap) (tape_m : val_map (List ℕ))
    (γ1 : GName) (γ2 : hv1.hv_name) :
    Timeless (coll_free_hashfun L L' val_size f m tape_m γ1 γ2) := by
  unfold coll_free_hashfun; infer_instance

/-- Rocq: `coll_free_hashfun_implies_coll_free`. -/
theorem coll_free_hashfun_implies_coll_free (f : val) (m : hmap) (tape_m : val_map (List ℕ))
    (γ1 : GName) (γ2 : hv1.hv_name) :
    ⊢ coll_free_hashfun L L' val_size f m tape_m γ1 γ2 -∗ ⌜coll_free m⌝ := by
  unfold coll_free_hashfun
  iintro ⟨-, H, -⟩
  iapply hv1.hv_auth_coll_free L' m γ2 $$ H

/-- Rocq: `hashfun_implies_bounded_range`. -/
theorem hashfun_implies_bounded_range (f : val) (m : hmap) (tape_m : val_map (List ℕ))
    (γ : GName) (idx x : ℕ) :
    ⊢ hashfun L val_size f m tape_m γ -∗ ⌜m[idx]? = some x⌝ -∗ ⌜0 ≤ x ∧ x ≤ val_size⌝ := by
  unfold hashfun
  iintro ⟨%hm, %_, _H, %K, -⟩ %Hx
  ipureintro
  exact K idx x Hx

/-- Rocq: `coll_free_hashfun_implies_bounded_range`. -/
theorem coll_free_hashfun_implies_bounded_range (f : val) (m : hmap) (tape_m : val_map (List ℕ))
    (idx x : ℕ) (γ1 : GName) (γ2 : hv1.hv_name) :
    ⊢ coll_free_hashfun L L' val_size f m tape_m γ1 γ2 -∗ ⌜m[idx]? = some x⌝ -∗
      ⌜0 ≤ x ∧ x ≤ val_size⌝ := by
  unfold coll_free_hashfun
  iintro ⟨H, -⟩ %Hx
  iapply hashfun_implies_bounded_range L val_size f m tape_m γ1 idx x $$ H
  ipureintro
  exact Hx

/-- Rocq: `wp_init_hash`. -/
theorem wp_init_hash (E : CoPset) :
    {{ True }} cpl(&(init_hash val_size) #()) @ E
    {{ f, RET f; ∃ γ1 γ2, |={E}=> coll_free_hashfun L L' val_size f ∅ ∅ γ1 γ2 }} := by
  iintro %Φ - HΦ
  unfold init_hash
  wp_pures
  unfold init_hash_state
  wp_apply wp_init_map $$ [] with %l Hm
  · itrivial
  unfold compute_hash
  wp_pures
  imod hv1.hv_auth_init L' with ⟨%γ2, Hview⟩
  imod abstract_tapes_alloc (GF := GF) ∅ with ⟨%γ1, Htauth, -⟩
  iapply HΦ
  imodintro
  iexists γ1, γ2
  imodintro
  unfold coll_free_hashfun hashfun
  iframe Hview
  isplitl [Hm Htauth]
  · iexists l
    isplitr
    · ipureintro; rfl
    isplitl [Hm]
    · rw [Std.ExtTreeMap.map_eq_empty_iff.mpr rfl]
      iexact Hm
    isplitr
    · ipureintro
      simp
    rw [Std.ExtTreeMap.map_eq_empty_iff.mpr rfl]
    iframe Htauth
    iapply (BigSepM.bigSepM_empty (M := val_map)).2
    itrivial
  ipureintro
  unfold tape_m_elements
  rw [Std.ExtTreeMap.toList_eq_nil_iff.mpr rfl, Std.ExtTreeMap.toList_eq_nil_iff.mpr rfl]
  simp

/-- Rocq: `coll_free_insert`. -/
theorem coll_free_insert (m : hmap) (n z : ℕ) (_Hnone : m[n]? = none) (Hcoll : coll_free m)
    (HForall : ∀ x ∈ m.toList, z ≠ x.2) : coll_free (m.insert n z) := by
  intro k1 k2 Hk1 Hk2 Heq
  have hval : ∀ k v, m[k]? = some v → z ≠ v := fun k v h =>
    HForall (k, v) (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr h)
  simp only [Std.ExtTreeMap.getD_eq_getD_getElem?, Std.ExtTreeMap.getElem?_insert] at Heq Hk1 Hk2
  by_cases h1 : n = k1 <;> by_cases h2 : n = k2
  · exact h1 ▸ h2
  · have c1 : compare n k1 = .eq := by simpa using h1
    have c2 : compare n k2 ≠ .eq := by simpa using h2
    simp only [c1, c2, ite_true, ite_false, Option.getD_some] at Heq Hk2
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp Hk2
    rw [hv, Option.getD_some] at Heq
    exact absurd Heq (hval k2 v hv)
  · have c1 : compare n k1 ≠ .eq := by simpa using h1
    have c2 : compare n k2 = .eq := by simpa using h2
    simp only [c1, c2, ite_true, ite_false, Option.getD_some] at Heq Hk1
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp Hk1
    rw [hv, Option.getD_some] at Heq
    exact absurd Heq.symm (hval k1 v hv)
  · have c1 : compare n k1 ≠ .eq := by simpa using h1
    have c2 : compare n k2 ≠ .eq := by simpa using h2
    simp only [c1, c2, ite_false] at Heq Hk1 Hk2
    apply Hcoll k1 k2 Hk1 Hk2
    simpa only [Std.ExtTreeMap.getD_eq_getD_getElem?] using Heq

/-- Rocq: `wp_hashfun_prev`. -/
theorem wp_hashfun_prev (E : CoPset) (f : val) (m : hmap) (n b : ℕ) (tape_m : val_map (List ℕ))
    (γ : GName) (α : Loc) (Hlookup : m[n]? = some b) :
    {{ hashfun L val_size f m tape_m γ }} cpl(&f #n #α) @ E
    {{ RET LitV (LitInt (b : ℤ)); hashfun L val_size f m tape_m γ }} := by
  iintro %Φ Hhash HΦ
  unfold hashfun
  icases Hhash with ⟨%hm, %Hf, H, %Hbound, Hrest⟩
  subst Hf
  unfold compute_hash_specialized
  wp_pures
  wp_apply wp_get hm _ n $$ H with %vret ⟨Hhash, %Hv⟩
  subst Hv
  rw [Std.ExtTreeMap.getElem?_map, Hlookup]
  simp only [Option.map_some, opt_to_val]
  wp_pures
  iapply HΦ
  iexists hm
  iframe
  ipureintro
  exact ⟨rfl, Hbound⟩

/-- Rocq: `wp_coll_free_hashfun_prev`. -/
theorem wp_coll_free_hashfun_prev (E : CoPset) (f : val) (m : hmap) (tape_m : val_map (List ℕ))
    (γ1 : GName) (γ2 : hv1.hv_name) (n b : ℕ) (α : Loc) (Hlookup : m[n]? = some b) :
    {{ coll_free_hashfun L L' val_size f m tape_m γ1 γ2 }} cpl(&f #n #α) @ E
    {{ RET LitV (LitInt (b : ℤ));
        coll_free_hashfun L L' val_size f m tape_m γ1 γ2 ∗ hv1.hv_frag L' n b γ2 }} := by
  unfold coll_free_hashfun
  iintro %Φ ⟨Hhash, Hauth, %Hnd⟩ HΦ
  unfold hashfun
  icases Hhash with ⟨%hm, %Hf, H, %Hbound, Hrest⟩
  subst Hf
  unfold compute_hash_specialized
  wp_pures
  wp_apply wp_get hm _ n $$ H with %vret ⟨Hhash, %Hv⟩
  subst Hv
  rw [Std.ExtTreeMap.getElem?_map, Hlookup]
  simp only [Option.map_some, opt_to_val]
  wp_pures
  ihave ⟨Hauth, Hfrag⟩ := hv1.hv_auth_duplicate_frag L' m n b γ2 Hlookup $$ Hauth
  imodintro
  iapply HΦ
  iframe
  ipureintro
  exact ⟨⟨rfl, Hbound⟩, Hnd⟩

/-- Rocq: `wp_coll_free_hashfun_frag_prev`. -/
theorem wp_coll_free_hashfun_frag_prev (E : CoPset) (f : val) (m : hmap)
    (tape_m : val_map (List ℕ)) (γ1 : GName) (γ2 : hv1.hv_name) (n b : ℕ) (α : Loc) :
    {{ coll_free_hashfun L L' val_size f m tape_m γ1 γ2 ∗ hv1.hv_frag L' n b γ2 }}
      cpl(&f #n #α) @ E
    {{ RET LitV (LitInt (b : ℤ)); coll_free_hashfun L L' val_size f m tape_m γ1 γ2 }} := by
  iintro %Φ ⟨H, #Hfrag⟩ HΦ
  unfold coll_free_hashfun
  icases H with ⟨Hhash, Hauth, %Hnd⟩
  ihave %Hlk := hv1.hv_auth_frag_agree L' m γ2 n b $$ [Hauth]
  · iframe Hauth Hfrag
  iapply wp_coll_free_hashfun_prev L L' val_size E f m tape_m γ1 γ2 n b α Hlk $$ [Hhash Hauth]
  · unfold coll_free_hashfun
    iframe
    ipureintro
    exact Hnd
  iintro !> ⟨H1, -⟩
  iapply HΦ
  unfold coll_free_hashfun
  iexact H1

/-- Rocq: `wp_hash_allocate_tape`. -/
theorem wp_hash_allocate_tape (f : val) (m : hmap) (tape_m : val_map (List ℕ)) (γ1 : GName)
    (γ2 : hv1.hv_name) (E : CoPset) :
    {{ coll_free_hashfun L L' val_size f m tape_m γ1 γ2 }} cpl(&(allocate_tape val_size) #()) @ E
    {{ α, RET α; coll_free_hashfun L L' val_size f m (tape_m.insert α []) γ1 γ2 ∗
        hash_tape val_size α [] γ1 }} := by
  unfold coll_free_hashfun hashfun
  iintro %Φ ⟨⟨%hm, %Hf, Hmap, %Hforall, Hauth, Htapes⟩, Hview, %Hnd⟩ HΦ
  unfold allocate_tape
  wp_pures
  iapply pgl_wp_fupd
  wp_apply r1.rand_allocate_tape_spec L E val_size $$ [] with %v Htape
  · itrivial
  ihave %H0 : ⌜tape_m[v]? = none⌝ $$ [Htape Htapes]
  · cases K : tape_m[v]? with
    | none => ipureintro; rfl
    | some t =>
      ihave Ht := (BigSepM.bigSepM_lookup (M := val_map) (i := v) (x := t) K) $$ Htapes
      iexfalso
      iapply r1.rand_tapes_exclusive L v _ _ $$ Htape Ht
  have H0' : (tape_m.map (fun _ x => (val_size, x)))[v]? = none := by
    rw [Std.ExtTreeMap.getElem?_map, H0]; rfl
  imod abstract_tapes_new γ1 _ v val_size [] H0' $$ Hauth with ⟨Hauth, Hfrag⟩
  imodintro
  iapply HΦ
  unfold hash_tape
  iframe Hfrag Hview
  rw [tapes_map_insert]
  isplitl
  · iexists hm
    iframe Hmap Hauth
    isplitr
    · ipureintro
      exact Hf
    isplitr
    · ipureintro
      exact Hforall
    rw [← val_map_insert_eq]
    iapply (BigSepM.bigSepM_insert (M := val_map)
      (Φ := fun α t => r1.rand_tapes L α (val_size, t)) H0).2
    iframe
  ipureintro
  refine (List.Perm.nodup_iff ?_).mpr Hnd
  refine List.Perm.append_right _ ?_
  simpa using tape_m_elements_insert_none tape_m v [] H0

end seq_hash_impl

end Coneris.Examples.HashDir.SeqHashImpl
