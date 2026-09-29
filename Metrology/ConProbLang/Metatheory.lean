module

public import Metrology.ConProbLang.Lang

/-!
# Metatheory of `con_prob_lang`

Ported from clutch/theories/con_prob_lang/metatheory.v

Closedness and (parallel) substitution lemmas, the deterministic/probabilistic head-step
characterisations, and lemmas about tape updates and `prim_step`. Everything lives in
`ConProbLang.con_prob_lang` (like `Lang.lean`). The syntactic part follows iris-lean's
`HeapLang/Metatheory.lean` (proofs by functional induction `subst.induct`,
`subst_map.induct`, `is_closed_expr.induct`, since `expr`/`val` is a mutual inductive).

## Rocq → Lean mapping
* `stringset` is `Finset String` (abbrev `stringset`); `{[f]} ∪ X` is `insert f X`.
  `set_binder_insert` is a (public) def. The `SetUnfoldElemOf` instance
  `set_unfold_elem_of_insert_binder` is the simp lemma `mem_set_binder_insert`.
* `is_closed_expr`/`is_closed_val` return `Bool`; hypotheses are written `… = true`.
* `gmap string val` is `varmap val := Std.ExtTreeMap String val compare`; `vs !! x` is `vs[x]?`,
  `<[x:=v]> vs` is `vs.insert x v`, `delete x vs` is `vs.erase x`, `{[x:=v]}` is
  `(∅ : varmap val).insert x v`. stdpp's `binder_insert`/`binder_delete` are defined here, with
  `lookup_binder_insert`, `lookup_binder_delete`, `binder_delete_empty`,
  `binder_delete_delete`, `binder_delete_insert`.
* `map_Forall (λ _ v, P v) m` (in `heap_closed_alloc`) is `∀ l v, m[l]? = some v → P v`; as in
  `Lang.lean`, Rocq's left-biased `heap_array .. ∪ heap σ` is `heap σ ∪ heap_array ..`.
* `σ.(tapes) !!! α` is `σ.tapes[α]!`; `α ∈ dom σ.(tapes)` is `α ∈ σ.tapes`.
* `det_head_step_rel.CmpXchgDS`: Rocq's `let b := bool_decide (vl = v1) in ..` is inlined as
  `decide (vl = v1)`. `is_det_head_step`: `bool_decide (is_Some ..)` is `Option.isSome`, the
  `bool_decide (∃ ..)` tests match on the heap lookup, and `vals_compare_safe` is tested with
  the new Boolean `vals_compare_safeb` (the `Decidable (vals_compare_safe ..)` instance of
  `Lang.lean` cannot be evaluated outside that module).
* `prim_step` (of the `con_prob_lang` language) is written `prim_step (Λ := con_prob_lang)`;
  `fill` is `con_prob_lang.fill` from `Lang.lean`.
* `ex_seriesC_prim_step_mult_fn_con_prob_lang` is stated as `Summable` with an `ℝ≥0∞`-valued
  `f` (trivial in `ℝ≥0∞`).
* `prim_step_finite_options` is proved via finite supports (`fin_supp`) instead of Rocq's case
  analysis through `det_or_prob_or_dzero`.

## Added helpers (not in Rocq)
`set_binder_insert_mono`, `varmap`, `binder_insert`, `binder_delete` (+ lemmas listed above),
`varmap_erase_insert_eq`, `varmap_erase_insert_ne`, `subst_map_of_lookup_none`,
`val_is_unboxedb`, `val_is_unboxedb_iff`, `vals_compare_safeb`, `vals_compare_safeb_iff`,
`det_head_step_rel_head_step_rel`, `map_insert_insert_ne`, `prim_step_eq_head_step`,
`fin_supp`, `fin_supp_dret`, `fin_supp_dzero`, `fin_supp_dmap`, `fin_supp_dunifP`,
`head_step_fin_supp`.

## Omissions
* The local Ltacs `solve_step_det` and `inv_det_head_step` (only used in `is_det_head_step_true`).
* All coupling lemmas after `prim_step_empty_tape_preserve` (`ARcoupl_state_step_dunifP`,
  `Rcoupl_rand_rand`, ..., `Rcoupl_fragmented_rand_rand_inj`): they are commented out in the Rocq
  source ("commenting out couplings atm").
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Prob

namespace ConProbLang

namespace con_prob_lang

/-! ## Closedness and substitution -/

/-- Rocq (stdpp): `stringset`. -/
abbrev stringset := Finset String

/-- Rocq: `set_binder_insert` (a `Local Definition`). Adding a binder to a set of
identifiers. -/
def set_binder_insert (x : binder) (X : stringset) : stringset :=
  match x with
  | BAnon => X
  | BNamed f => insert f X

mutual
/-- Rocq: `is_closed_expr`. Check if expression `e` is closed w.r.t. the set `X` of variable
names, and that all the values in `e` are closed. -/
def is_closed_expr (X : stringset) (e : expr) : Bool :=
  match e with
  | Val v => is_closed_val v
  | Var x => decide (x ∈ X)
  | Rec f x e => is_closed_expr (set_binder_insert f (set_binder_insert x X)) e
  | UnOp _ e | Fst e | Snd e | InjL e | InjR e | Load e => is_closed_expr X e
  | App e1 e2 | BinOp _ e1 e2 | Pair e1 e2 | AllocN e1 e2 | Store e1 e2 | Rand e1 e2 =>
     is_closed_expr X e1 && is_closed_expr X e2
  | If e0 e1 e2 | Case e0 e1 e2 =>
     is_closed_expr X e0 && is_closed_expr X e1 && is_closed_expr X e2
  | AllocTape e => is_closed_expr X e
  | Tick e => is_closed_expr X e
  | Fork e => is_closed_expr X e
  | CmpXchg e0 e1 e2 => is_closed_expr X e0 && is_closed_expr X e1 && is_closed_expr X e2
  | Xchg e1 e2 => is_closed_expr X e1 && is_closed_expr X e2
  | FAA e1 e2 => is_closed_expr X e1 && is_closed_expr X e2
/-- Rocq: `is_closed_val`. -/
def is_closed_val (v : val) : Bool :=
  match v with
  | LitV _ => true
  | RecV f x e => is_closed_expr (set_binder_insert f (set_binder_insert x ∅)) e
  | PairV v1 v2 => is_closed_val v1 && is_closed_val v2
  | InjLV v | InjRV v => is_closed_val v
end

/-- Rocq (stdpp): `gmap string val`, the maps used for parallel substitution. -/
abbrev varmap (V : Type) := Std.ExtTreeMap String V compare

/-- Rocq (stdpp): `binder_insert`. -/
def binder_insert {V : Type} (b : binder) (v : V) (vs : varmap V) : varmap V :=
  match b with
  | BAnon => vs
  | BNamed x => vs.insert x v

/-- Rocq (stdpp): `binder_delete`. -/
def binder_delete {V : Type} (b : binder) (vs : varmap V) : varmap V :=
  match b with
  | BAnon => vs
  | BNamed x => vs.erase x

/-- Rocq: `subst_map`. Parallel substitution. -/
def subst_map (vs : varmap val) (e : expr) : expr :=
  match e with
  | Val _ => e
  | Var y => match vs[y]? with
    | some v => Val v
    | none => Var y
  | Rec f y e => Rec f y (subst_map (binder_delete y (binder_delete f vs)) e)
  | App e1 e2 => App (subst_map vs e1) (subst_map vs e2)
  | UnOp op e => UnOp op (subst_map vs e)
  | BinOp op e1 e2 => BinOp op (subst_map vs e1) (subst_map vs e2)
  | If e0 e1 e2 => If (subst_map vs e0) (subst_map vs e1) (subst_map vs e2)
  | Pair e1 e2 => Pair (subst_map vs e1) (subst_map vs e2)
  | Fst e => Fst (subst_map vs e)
  | Snd e => Snd (subst_map vs e)
  | InjL e => InjL (subst_map vs e)
  | InjR e => InjR (subst_map vs e)
  | Case e0 e1 e2 => Case (subst_map vs e0) (subst_map vs e1) (subst_map vs e2)
  | AllocN e1 e2 => AllocN (subst_map vs e1) (subst_map vs e2)
  | Load e => Load (subst_map vs e)
  | Store e1 e2 => Store (subst_map vs e1) (subst_map vs e2)
  | AllocTape e => AllocTape (subst_map vs e)
  | Rand e1 e2 => Rand (subst_map vs e1) (subst_map vs e2)
  | Tick e => Tick (subst_map vs e)
  | Fork e => Fork (subst_map vs e)
  | CmpXchg e0 e1 e2 => CmpXchg (subst_map vs e0) (subst_map vs e1) (subst_map vs e2)
  | Xchg e1 e2 => Xchg (subst_map vs e1) (subst_map vs e2)
  | FAA e1 e2 => FAA (subst_map vs e1) (subst_map vs e2)

/-! Properties -/

/-- Rocq: `set_unfold_elem_of_insert_binder` (a `SetUnfoldElemOf` instance). -/
@[simp] theorem mem_set_binder_insert (x : binder) (y : String) (X : stringset) :
    y ∈ set_binder_insert x X ↔ y ∈ X ∨ BNamed y = x := by
  cases x <;> simp [set_binder_insert, or_comm, eq_comm]

theorem set_binder_insert_mono (b : binder) {X Y : stringset} (h : X ⊆ Y) :
    set_binder_insert b X ⊆ set_binder_insert b Y := by
  intro y; simp only [mem_set_binder_insert]; exact Or.imp_left (@h y)

/-- Rocq: `is_closed_weaken`. -/
theorem is_closed_weaken (X Y : stringset) (e : expr) (h : is_closed_expr X e = true)
    (hXY : X ⊆ Y) : is_closed_expr Y e = true := by
  induction X, e using is_closed_expr.induct (motive_2 := fun _ => True) generalizing Y <;>
    (try simp_all [is_closed_expr])
  case case2 h => exact hXY h
  case case3 ih => exact ih _ (set_binder_insert_mono _ (set_binder_insert_mono _ hXY))

/-- Rocq: `is_closed_weaken_empty`. -/
theorem is_closed_weaken_empty (X : stringset) (e : expr) (h : is_closed_expr ∅ e = true) :
    is_closed_expr X e = true :=
  is_closed_weaken ∅ X e h (Finset.empty_subset _)

/-- Rocq: `is_closed_subst`. -/
theorem is_closed_subst (X : stringset) (e : expr) (y : String) (v : val)
    (hv : is_closed_val v = true) (he : is_closed_expr (insert y X) e = true) :
    is_closed_expr X (subst y v e) = true := by
  induction e using subst.induct (x := y) generalizing X <;>
    simp_all [subst, is_closed_expr]
  case case3 => grind
  case case4 f y' e ih =>
    split
    · next h =>
      refine ih _ (is_closed_weaken _ _ _ he fun z hz => ?_)
      simp only [mem_set_binder_insert, Finset.mem_insert] at hz ⊢
      grind
    · next h =>
      refine is_closed_weaken _ _ _ he fun z hz => ?_
      simp only [mem_set_binder_insert, Finset.mem_insert] at hz ⊢
      grind

/-- Rocq: `is_closed_subst'`. -/
theorem is_closed_subst' (X : stringset) (e : expr) (x : binder) (v : val)
    (hv : is_closed_val v = true) (he : is_closed_expr (set_binder_insert x X) e = true) :
    is_closed_expr X (subst' x v e) = true := by
  cases x
  · exact he
  · exact is_closed_subst _ _ _ _ hv he

/-- Rocq: `subst_is_closed`. -/
theorem subst_is_closed (X : stringset) (e : expr) (x : String) (es : val)
    (he : is_closed_expr X e = true) (hx : x ∉ X) : subst x es e = e := by
  induction e using subst.induct (x := x) generalizing X <;>
    simp_all [subst, is_closed_expr]
  case case4 ih =>
    intro h1 h2
    exact ih _ he (by simp only [mem_set_binder_insert]; grind)
  all_goals grind

/-- Rocq: `subst_is_closed_empty`. -/
theorem subst_is_closed_empty (e : expr) (x : String) (v : val)
    (he : is_closed_expr ∅ e = true) : subst x v e = e :=
  subst_is_closed ∅ e x v he (Finset.notMem_empty _)

/-- Rocq: `subst_subst`. -/
theorem subst_subst (e : expr) (x : String) (v v' : val) :
    subst x v (subst x v' e) = subst x v' e := by
  induction e using subst.induct (x := x) <;> simp_all [subst]

/-- Rocq: `subst_subst'`. -/
theorem subst_subst' (e : expr) (x : binder) (v v' : val) :
    subst' x v (subst' x v' e) = subst' x v' e := by
  cases x
  · rfl
  · exact subst_subst _ _ _ _

/-- Rocq: `subst_subst_ne`. -/
theorem subst_subst_ne (e : expr) (x y : String) (v v' : val) (hxy : x ≠ y) :
    subst x v (subst y v' e) = subst y v' (subst x v e) := by
  induction e using subst.induct (x := x) <;> simp_all [subst]
  case case2 => simp [Ne.symm hxy, subst]
  case case3 z hz => split <;> simp_all [subst]
  case case4 => split <;> split <;> simp_all

/-- Rocq: `subst_subst_ne'`. -/
theorem subst_subst_ne' (e : expr) (x y : binder) (v v' : val) (hxy : x ≠ y) :
    subst' x v (subst' y v' e) = subst' y v' (subst' x v e) := by
  cases x <;> cases y <;> simp only [subst'_BAnon, subst'_BNamed]
  exact subst_subst_ne _ _ _ _ _ (fun h => hxy (by rw [h]))

/-- Rocq: `subst_rec'`. -/
theorem subst_rec' (f y : binder) (e : expr) (x : binder) (v : val)
    (h : x = f ∨ x = y ∨ x = BAnon) : subst' x v (Rec f y e) = Rec f y e := by
  cases x
  · rfl
  · simp only [subst'_BNamed, subst]; grind

/-- Rocq: `subst_rec_ne'`. -/
theorem subst_rec_ne' (f y : binder) (e : expr) (x : binder) (v : val)
    (hf : x ≠ f ∨ f = BAnon) (hy : x ≠ y ∨ y = BAnon) :
    subst' x v (Rec f y e) = Rec f y (subst' x v e) := by
  cases x
  · rfl
  · simp only [subst'_BNamed, subst]; grind

/-- Rocq: `bin_op_eval_closed`. -/
theorem bin_op_eval_closed (op : bin_op) (v1 v2 v' : val) (_ : is_closed_val v1 = true)
    (_ : is_closed_val v2 = true) (h : bin_op_eval op v1 v2 = some v') :
    is_closed_val v' = true := by
  unfold bin_op_eval at h
  split at h
  · split at h
    · cases h; rfl
    · cases h
  · split at h
    · cases h; rfl
    · simp at h; obtain ⟨a, -, rfl⟩ := h; rfl
    · simp at h; obtain ⟨a, -, rfl⟩ := h; rfl
    · cases h

/-- Rocq: `heap_closed_alloc`. (Rocq's `map_Forall P m` is `∀ l v, m[l]? = some v → P l v`;
Rocq's union `heap_array .. ∪ heap σ` is written `heap σ ∪ heap_array ..`, as Std's union is
right-biased.) -/
theorem heap_closed_alloc (σ : state) (l : Loc) (n : ℤ) (w : val) (_ : 0 < n)
    (Hw : is_closed_val w = true)
    (Hσ : ∀ (l : Loc) (v : val), σ.heap[l]? = some v → is_closed_val v = true)
    (_ : ∀ i : ℤ, 0 ≤ i → i < n → σ.heap[l +ₗ i]? = none) :
    ∀ (k : Loc) (v : val), (σ.heap ∪ heap_array l (List.replicate n.toNat w))[k]? = some v →
      is_closed_val v = true := by
  intro k v hk
  rw [map_getElem?_union] at hk
  rcases h : (heap_array l (List.replicate n.toNat w))[k]? with _ | v'
  · rw [h, Option.none_or] at hk
    exact Hσ k v hk
  · rw [h, Option.some_or] at hk
    cases hk
    obtain ⟨j, -, -, hj⟩ := (heap_array_lookup _ _ _ _).1 h
    rw [List.getElem?_replicate] at hj
    split at hj
    · cases hj; exact Hw
    · cases hj

/-! Parallel substitution lemmas -/

section binder_map

variable {V : Type}

@[simp] theorem lookup_binder_insert (b : binder) (v : V) (vs : varmap V) (y : String) :
    (binder_insert b v vs)[y]? = if BNamed y = b then some v else vs[y]? := by
  cases b
  · simp [binder_insert]
  · simp only [binder_insert, Std.ExtTreeMap.getElem?_insert, Std.compare_eq_iff_eq]; simp [eq_comm]

@[simp] theorem lookup_binder_delete (b : binder) (vs : varmap V) (y : String) :
    (binder_delete b vs)[y]? = if BNamed y = b then none else vs[y]? := by
  cases b
  · simp [binder_delete]
  · simp only [binder_delete, Std.ExtTreeMap.getElem?_erase, Std.compare_eq_iff_eq]; simp [eq_comm]

/-- Rocq (stdpp): `binder_delete_empty`. -/
theorem binder_delete_empty (b : binder) : binder_delete b (∅ : varmap V) = ∅ := by
  cases b <;> simp [binder_delete]

/-- Rocq (stdpp): `binder_delete_delete`. -/
theorem binder_delete_delete (b : binder) (x : String) (vs : varmap V) :
    binder_delete b (vs.erase x) = (binder_delete b vs).erase x := by
  ext y : 1; simp [Std.ExtTreeMap.getElem?_erase]; grind

/-- Rocq (stdpp): `binder_delete_insert`. -/
theorem binder_delete_insert (b : binder) (x : String) (v : V) (vs : varmap V)
    (h : BNamed x ≠ b) :
    binder_delete b (vs.insert x v) = (binder_delete b vs).insert x v := by
  ext y : 1; simp [Std.ExtTreeMap.getElem?_insert]; grind

theorem varmap_erase_insert_eq (vs : varmap V) (x : String) (v : V) :
    (vs.insert x v).erase x = vs.erase x := by
  ext y : 1
  simp only [Std.ExtTreeMap.getElem?_erase, Std.ExtTreeMap.getElem?_insert, Std.compare_eq_iff_eq]
  grind

theorem varmap_erase_insert_ne (vs : varmap V) (x y : String) (v : V) (h : x ≠ y) :
    (vs.insert x v).erase y = (vs.erase y).insert x v := by
  ext z : 1
  simp only [Std.ExtTreeMap.getElem?_erase, Std.ExtTreeMap.getElem?_insert, Std.compare_eq_iff_eq]
  grind

end binder_map

theorem subst_map_of_lookup_none (vs : varmap val) (e : expr) (h : ∀ y : String, vs[y]? = none) :
    subst_map vs e = e := by
  induction vs, e using subst_map.induct <;> simp_all [subst_map]

/-- Rocq: `subst_map_empty`. -/
theorem subst_map_empty (e : expr) : subst_map ∅ e = e :=
  subst_map_of_lookup_none _ _ (fun _ => Std.ExtTreeMap.getElem?_empty)

/-- Rocq: `subst_map_insert`. -/
theorem subst_map_insert (x : String) (v : val) (vs : varmap val) (e : expr) :
    subst_map (vs.insert x v) e = subst x v (subst_map (vs.erase x) e) := by
  induction e using subst.induct (x := x) generalizing vs <;>
    simp_all [subst_map, subst, Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getElem?_erase]
  case case3 => split <;> simp_all [subst]
  case case4 f y e ih =>
    split
    · next h =>
      rw [binder_delete_insert _ _ _ _ (by grind), binder_delete_insert _ _ _ _ (by grind), ih,
        binder_delete_delete, binder_delete_delete]
    · next h =>
      congr 1
      ext z : 1
      simp only [lookup_binder_delete, Std.ExtTreeMap.getElem?_insert,
        Std.ExtTreeMap.getElem?_erase, Std.compare_eq_iff_eq]
      grind

/-- Rocq: `subst_map_singleton`. -/
theorem subst_map_singleton (x : String) (v : val) (e : expr) :
    subst_map ((∅ : varmap val).insert x v) e = subst x v e := by
  rw [subst_map_insert, Std.ExtTreeMap.erase_empty, subst_map_empty]

/-- Rocq: `subst_map_binder_insert`. -/
theorem subst_map_binder_insert (b : binder) (v : val) (vs : varmap val) (e : expr) :
    subst_map (binder_insert b v vs) e = subst' b v (subst_map (binder_delete b vs) e) := by
  cases b
  · rfl
  · exact subst_map_insert _ _ _ _

/-- Rocq: `subst_map_binder_insert_empty`. -/
theorem subst_map_binder_insert_empty (b : binder) (v : val) (e : expr) :
    subst_map (binder_insert b v ∅) e = subst' b v e := by
  rw [subst_map_binder_insert, binder_delete_empty, subst_map_empty]

/-- Rocq: `subst_map_binder_insert_2`. -/
theorem subst_map_binder_insert_2 (b1 : binder) (v1 : val) (b2 : binder) (v2 : val)
    (vs : varmap val) (e : expr) :
    subst_map (binder_insert b1 v1 (binder_insert b2 v2 vs)) e =
      subst' b2 v2 (subst' b1 v1 (subst_map (binder_delete b2 (binder_delete b1 vs)) e)) := by
  cases b1 with
  | BAnon => exact subst_map_binder_insert b2 v2 vs e
  | BNamed s1 =>
    cases b2 with
    | BAnon => exact subst_map_insert _ _ _ _
    | BNamed s2 =>
      simp only [binder_insert, binder_delete, subst'_BNamed]
      rw [subst_map_insert]
      by_cases h : s1 = s2
      · subst h
        rw [varmap_erase_insert_eq, subst_subst]
        congr 2
        ext z : 1
        simp only [Std.ExtTreeMap.getElem?_erase, Std.compare_eq_iff_eq]
        grind
      · rw [varmap_erase_insert_ne _ _ _ _ (Ne.symm h), subst_map_insert,
          subst_subst_ne _ _ _ _ _ h]

/-- Rocq: `subst_map_binder_insert_2_empty`. -/
theorem subst_map_binder_insert_2_empty (b1 : binder) (v1 : val) (b2 : binder) (v2 : val)
    (e : expr) :
    subst_map (binder_insert b1 v1 (binder_insert b2 v2 ∅)) e = subst' b2 v2 (subst' b1 v1 e) := by
  rw [subst_map_binder_insert_2, binder_delete_empty, binder_delete_empty, subst_map_empty]

/-- Rocq: `subst_map_is_closed`. -/
theorem subst_map_is_closed (X : stringset) (e : expr) (vs : varmap val)
    (he : is_closed_expr X e = true) (hX : ∀ x, x ∈ X → vs[x]? = none) :
    subst_map vs e = e := by
  induction vs, e using subst_map.induct generalizing X <;>
    simp_all [subst_map, is_closed_expr]
  case case4 ih =>
    refine ih _ he fun x hx h1 h2 => ?_
    simp only [mem_set_binder_insert] at hx
    grind
  all_goals grind

/-- Rocq: `subst_map_is_closed_empty`. -/
theorem subst_map_is_closed_empty (e : expr) (vs : varmap val) (he : is_closed_expr ∅ e = true) :
    subst_map vs e = e :=
  subst_map_is_closed ∅ e vs he (fun _ hx => absurd hx (Finset.notMem_empty _))

/-! ## Some useful lemmas to reason about language properties -/

/-- Rocq: `det_head_step_rel`. (Rocq's `let b := bool_decide (vl = v1) in ..` in `CmpXchgDS` is
inlined as `decide (vl = v1)`.) -/
inductive det_head_step_rel : expr → state → expr → state → List expr → Prop where
  | RecDS (f x : binder) (e : expr) (σ : state) :
    det_head_step_rel (Rec f x e) σ (Val <| RecV f x e) σ []
  | PairDS (v1 v2 : val) (σ : state) :
    det_head_step_rel (Pair (Val v1) (Val v2)) σ (Val <| PairV v1 v2) σ []
  | InjLDS (v : val) (σ : state) :
    det_head_step_rel (InjL <| Val v) σ (Val <| InjLV v) σ []
  | InjRDS (v : val) (σ : state) :
    det_head_step_rel (InjR <| Val v) σ (Val <| InjRV v) σ []
  | BetaDS (f x : binder) (e1 : expr) (v2 : val) (e' : expr) (σ : state) :
    e' = subst' x v2 (subst' f (RecV f x e1) e1) →
    det_head_step_rel (App (Val <| RecV f x e1) (Val v2)) σ e' σ []
  | UnOpDS (op : un_op) (v v' : val) (σ : state) :
    un_op_eval op v = some v' →
    det_head_step_rel (UnOp op (Val v)) σ (Val v') σ []
  | BinOpDS (op : bin_op) (v1 v2 v' : val) (σ : state) :
    bin_op_eval op v1 v2 = some v' →
    det_head_step_rel (BinOp op (Val v1) (Val v2)) σ (Val v') σ []
  | IfTrueDS (e1 e2 : expr) (σ : state) :
    det_head_step_rel (If (Val <| LitV <| LitBool true) e1 e2) σ e1 σ []
  | IfFalseDS (e1 e2 : expr) (σ : state) :
    det_head_step_rel (If (Val <| LitV <| LitBool false) e1 e2) σ e2 σ []
  | FstDS (v1 v2 : val) (σ : state) :
    det_head_step_rel (Fst (Val <| PairV v1 v2)) σ (Val v1) σ []
  | SndDS (v1 v2 : val) (σ : state) :
    det_head_step_rel (Snd (Val <| PairV v1 v2)) σ (Val v2) σ []
  | CaseLDS (v : val) (e1 e2 : expr) (σ : state) :
    det_head_step_rel (Case (Val <| InjLV v) e1 e2) σ (App e1 (Val v)) σ []
  | CaseRDS (v : val) (e1 e2 : expr) (σ : state) :
    det_head_step_rel (Case (Val <| InjRV v) e1 e2) σ (App e2 (Val v)) σ []
  | AllocNDS (z : ℤ) (N : ℕ) (v : val) (σ : state) (l : Loc) :
    l = fresh_loc σ.heap →
    N = z.toNat →
    0 < N →
    det_head_step_rel (AllocN (Val (LitV (LitInt z))) (Val v)) σ
      (Val <| LitV <| LitLoc l) (state_upd_heap_N l N v σ) []
  | LoadDS (l : Loc) (v : val) (σ : state) :
    σ.heap[l]? = some v →
    det_head_step_rel (Load (Val <| LitV <| LitLoc l)) σ (Val v) σ []
  | StoreDS (l : Loc) (v w : val) (σ : state) :
    σ.heap[l]? = some v →
    det_head_step_rel (Store (Val <| LitV <| LitLoc l) (Val w)) σ
      (Val <| LitV LitUnit) (state_upd_heap (·.insert l w) σ) []
  | TickDS (z : ℤ) (σ : state) :
    det_head_step_rel (Tick (Val <| LitV <| LitInt z)) σ (Val <| LitV <| LitUnit) σ []
  | ForkDS (e : expr) (σ : state) :
    det_head_step_rel (Fork e) σ (Val <| LitV <| LitUnit) σ [e]
  | CmpXchgDS (l : Loc) (v1 v2 : val) (σ : state) (vl : val) :
    σ.heap[l]? = some vl →
    vals_compare_safe vl v1 →
    det_head_step_rel (CmpXchg (Val <| LitV <| LitLoc l) (Val v1) (Val v2)) σ
      (Val <| PairV vl (LitV <| LitBool (decide (vl = v1))))
      (if decide (vl = v1) then state_upd_heap (·.insert l v2) σ else σ) []
  | XchgDS (l : Loc) (v1 v2 : val) (σ : state) :
    σ.heap[l]? = some v1 →
    det_head_step_rel (Xchg (Val <| LitV <| LitLoc l) (Val v2)) σ
      (Val v1) (state_upd_heap (·.insert l v2) σ) []
  | FaaDS (l : Loc) (i1 i2 : ℤ) (σ : state) :
    σ.heap[l]? = some (LitV (LitInt i1)) →
    det_head_step_rel (FAA (Val <| LitV <| LitLoc l) (Val <| LitV (LitInt i2))) σ
      (Val <| LitV (LitInt i1)) (state_upd_heap (·.insert l (LitV (LitInt (i1 + i2)))) σ) []

export det_head_step_rel (RecDS PairDS InjLDS InjRDS BetaDS UnOpDS BinOpDS IfTrueDS IfFalseDS
  FstDS SndDS CaseLDS CaseRDS AllocNDS LoadDS StoreDS TickDS ForkDS CmpXchgDS XchgDS FaaDS)

/-- Rocq: `det_head_step_pred`. -/
inductive det_head_step_pred : expr → state → Prop where
  | RecDSP (f x : binder) (e : expr) (σ : state) : det_head_step_pred (Rec f x e) σ
  | PairDSP (v1 v2 : val) (σ : state) : det_head_step_pred (Pair (Val v1) (Val v2)) σ
  | InjLDSP (v : val) (σ : state) : det_head_step_pred (InjL <| Val v) σ
  | InjRDSP (v : val) (σ : state) : det_head_step_pred (InjR <| Val v) σ
  | BetaDSP (f x : binder) (e1 : expr) (v2 : val) (σ : state) :
    det_head_step_pred (App (Val <| RecV f x e1) (Val v2)) σ
  | UnOpDSP (op : un_op) (v : val) (σ : state) (v' : val) :
    un_op_eval op v = some v' →
    det_head_step_pred (UnOp op (Val v)) σ
  | BinOpDSP (op : bin_op) (v1 v2 : val) (σ : state) (v' : val) :
    bin_op_eval op v1 v2 = some v' →
    det_head_step_pred (BinOp op (Val v1) (Val v2)) σ
  | IfTrueDSP (e1 e2 : expr) (σ : state) :
    det_head_step_pred (If (Val <| LitV <| LitBool true) e1 e2) σ
  | IfFalseDSP (e1 e2 : expr) (σ : state) :
    det_head_step_pred (If (Val <| LitV <| LitBool false) e1 e2) σ
  | FstDSP (v1 v2 : val) (σ : state) : det_head_step_pred (Fst (Val <| PairV v1 v2)) σ
  | SndDSP (v1 v2 : val) (σ : state) : det_head_step_pred (Snd (Val <| PairV v1 v2)) σ
  | CaseLDSP (v : val) (e1 e2 : expr) (σ : state) :
    det_head_step_pred (Case (Val <| InjLV v) e1 e2) σ
  | CaseRDSP (v : val) (e1 e2 : expr) (σ : state) :
    det_head_step_pred (Case (Val <| InjRV v) e1 e2) σ
  | AllocNDSP (z : ℤ) (N : ℕ) (v : val) (σ : state) (l : Loc) :
    l = fresh_loc σ.heap →
    N = z.toNat →
    0 < N →
    det_head_step_pred (AllocN (Val (LitV (LitInt z))) (Val v)) σ
  | LoadDSP (l : Loc) (v : val) (σ : state) :
    σ.heap[l]? = some v →
    det_head_step_pred (Load (Val <| LitV <| LitLoc l)) σ
  | StoreDSP (l : Loc) (v w : val) (σ : state) :
    σ.heap[l]? = some v →
    det_head_step_pred (Store (Val <| LitV <| LitLoc l) (Val w)) σ
  | TickDSP (z : ℤ) (σ : state) : det_head_step_pred (Tick (Val <| LitV <| LitInt z)) σ
  | ForkDSP (e : expr) (σ : state) : det_head_step_pred (Fork e) σ
  | CmpXchgDSP (σ : state) (l : Loc) (vl v1 v2 : val) :
    σ.heap[l]? = some vl →
    vals_compare_safe vl v1 →
    det_head_step_pred (CmpXchg (Val <| LitV <| LitLoc l) (Val v1) (Val v2)) σ
  | XchgDSP (σ : state) (l : Loc) (v1 v2 : val) :
    σ.heap[l]? = some v1 →
    det_head_step_pred (Xchg (Val <| LitV <| LitLoc l) (Val v2)) σ
  | FaaDSP (σ : state) (l : Loc) (i1 i2 : ℤ) :
    σ.heap[l]? = some (LitV (LitInt i1)) →
    det_head_step_pred (FAA (Val <| LitV <| LitLoc l) (Val <| LitV <| LitInt i2)) σ

export det_head_step_pred (RecDSP PairDSP InjLDSP InjRDSP BetaDSP UnOpDSP BinOpDSP IfTrueDSP
  IfFalseDSP FstDSP SndDSP CaseLDSP CaseRDSP AllocNDSP LoadDSP StoreDSP TickDSP ForkDSP
  CmpXchgDSP XchgDSP FaaDSP)

/-- Boolean version of `val_is_unboxed` (used in `is_det_head_step`; evaluating the
`Decidable (vals_compare_safe ..)` instance of `Lang.lean` fails outside that module). -/
def val_is_unboxedb (v : val) : Bool :=
  match v with
  | LitV _ => true
  | InjLV (LitV _) => true
  | InjRV (LitV _) => true
  | _ => false

theorem val_is_unboxedb_iff (v : val) : val_is_unboxedb v = true ↔ val_is_unboxed v := by
  have hl : ∀ l : base_lit, lit_is_unboxed l := fun l => by cases l <;> exact trivial
  cases v with
  | LitV l => exact iff_of_true rfl (hl l)
  | RecV => exact iff_of_false (by simp [val_is_unboxedb]) (fun h => (h : False))
  | PairV => exact iff_of_false (by simp [val_is_unboxedb]) (fun h => (h : False))
  | InjLV v =>
    cases v with
    | LitV l => exact iff_of_true rfl (hl l)
    | _ => exact iff_of_false (by simp [val_is_unboxedb]) (fun h => (h : False))
  | InjRV v =>
    cases v with
    | LitV l => exact iff_of_true rfl (hl l)
    | _ => exact iff_of_false (by simp [val_is_unboxedb]) (fun h => (h : False))

/-- Boolean version of `vals_compare_safe`. -/
def vals_compare_safeb (vl v1 : val) : Bool := val_is_unboxedb vl || val_is_unboxedb v1

theorem vals_compare_safeb_iff (vl v1 : val) :
    vals_compare_safeb vl v1 = true ↔ vals_compare_safe vl v1 := by
  rw [vals_compare_safeb, Bool.or_eq_true, val_is_unboxedb_iff, val_is_unboxedb_iff]; rfl

/-- Rocq: `is_det_head_step`. (Rocq's `bool_decide (is_Some ..)` is `Option.isSome`; the
`bool_decide (∃ ..)` tests are written by matching on the heap lookup.) -/
def is_det_head_step (e1 : expr) (σ1 : state) : Bool :=
  match e1 with
  | Rec _ _ _ => true
  | Pair (Val _) (Val _) => true
  | InjL (Val _) => true
  | InjR (Val _) => true
  | App (Val (RecV _ _ _)) (Val _) => true
  | UnOp op (Val v) => (un_op_eval op v).isSome
  | BinOp op (Val v1) (Val v2) => (bin_op_eval op v1 v2).isSome
  | If (Val (LitV (LitBool true))) _ _ => true
  | If (Val (LitV (LitBool false))) _ _ => true
  | Fst (Val (PairV _ _)) => true
  | Snd (Val (PairV _ _)) => true
  | Case (Val (InjLV _)) _ _ => true
  | Case (Val (InjRV _)) _ _ => true
  | AllocN (Val (LitV (LitInt z))) (Val _) => decide (0 < z.toNat)
  | Load (Val (LitV (LitLoc l))) => (σ1.heap[l]?).isSome
  | Store (Val (LitV (LitLoc l))) (Val _) => (σ1.heap[l]?).isSome
  | Tick (Val (LitV (LitInt _))) => true
  | Fork _ => true
  | CmpXchg (Val (LitV (LitLoc l))) (Val v1) (Val _) =>
      match σ1.heap[l]? with
      | some vl => vals_compare_safeb vl v1
      | none => false
  | Xchg (Val (LitV (LitLoc l))) (Val _) => (σ1.heap[l]?).isSome
  | FAA (Val (LitV (LitLoc l))) (Val (LitV (LitInt _))) =>
      match σ1.heap[l]? with
      | some (LitV (LitInt _)) => true
      | _ => false
  | _ => false

/-- Rocq: `det_step_eq_tapes`. -/
theorem det_step_eq_tapes (e1 : expr) (σ1 : state) (e2 : expr) (σ2 : state) (efs : List expr)
    (h : det_head_step_rel e1 σ1 e2 σ2 efs) : σ1.tapes = σ2.tapes := by
  cases h <;> try rfl
  split <;> rfl

/-- Rocq: `prob_head_step_pred`. -/
inductive prob_head_step_pred : expr → state → Prop where
  | AllocTapePSP (σ : state) (N : ℕ) (z : ℤ) :
    N = z.toNat →
    prob_head_step_pred (AllocTape (Val (LitV (LitInt z)))) σ
  | RandTapePSP (α : Loc) (σ : state) (N : ℕ) (n : Fin (N + 1)) (ns : List (Fin (N + 1)))
      (z : ℤ) :
    N = z.toNat →
    σ.tapes[α]? = some ⟨N, n :: ns⟩ →
    prob_head_step_pred (Rand (Val (LitV (LitInt z))) (Val (LitV (LitLbl α)))) σ
  | RandEmptyPSP (N : ℕ) (α : Loc) (σ : state) (z : ℤ) :
    N = z.toNat →
    σ.tapes[α]? = some ⟨N, []⟩ →
    prob_head_step_pred (Rand (Val (LitV (LitInt z))) (Val (LitV (LitLbl α)))) σ
  | RandTapeOtherPSP (N M : ℕ) (α : Loc) (σ : state) (ns : List (Fin (N + 1))) (z : ℤ) :
    N ≠ M →
    M = z.toNat →
    σ.tapes[α]? = some ⟨N, ns⟩ →
    prob_head_step_pred (Rand (Val (LitV (LitInt z))) (Val (LitV (LitLbl α)))) σ
  | RandNoTapePSP (N : ℕ) (σ : state) (z : ℤ) :
    N = z.toNat →
    prob_head_step_pred (Rand (Val (LitV (LitInt z))) (Val (LitV LitUnit))) σ

export prob_head_step_pred (AllocTapePSP RandTapePSP RandEmptyPSP RandTapeOtherPSP RandNoTapePSP)

/-- Rocq: `head_step_pred`. -/
def head_step_pred (e1 : expr) (σ1 : state) : Prop :=
  det_head_step_pred e1 σ1 ∨ prob_head_step_pred e1 σ1

/-- Rocq: `det_step_is_unique`. -/
theorem det_step_is_unique (e1 : expr) (σ1 : state) (e2 : expr) (σ2 : state) (e3 : expr)
    (σ3 : state) (efs efs' : List expr) (H1 : det_head_step_rel e1 σ1 e2 σ2 efs)
    (H2 : det_head_step_rel e1 σ1 e3 σ3 efs') : e2 = e3 ∧ σ2 = σ3 ∧ efs = efs' := by
  cases H1 <;> cases H2 <;> simp_all

/-- Rocq: `det_step_pred_ex_rel`. -/
theorem det_step_pred_ex_rel (e1 : expr) (σ1 : state) :
    det_head_step_pred e1 σ1 ↔ ∃ e2 σ2 efs, det_head_step_rel e1 σ1 e2 σ2 efs := by
  constructor
  · intro H
    cases H <;> subst_vars <;> exact ⟨_, _, _, by constructor <;> first | rfl | assumption⟩
  · rintro ⟨e2, σ2, efs, H⟩
    cases H <;> subst_vars <;> constructor <;> first | rfl | assumption

/-- Rocq: `is_det_head_step_true`. -/
theorem is_det_head_step_true (e1 : expr) (σ1 : state) :
    is_det_head_step e1 σ1 = true ↔ det_head_step_pred e1 σ1 := by
  constructor
  · intro H
    unfold is_det_head_step at H
    split at H <;> (try simp only [Option.isSome_iff_exists, decide_eq_true_eq] at H)
    all_goals first
      | (constructor; done)
      | (obtain ⟨_, h⟩ := H; constructor <;> assumption)
      | exact AllocNDSP _ _ _ _ _ rfl rfl H
      | (split at H
         exact CmpXchgDSP _ _ _ _ _ ‹_› ((vals_compare_safeb_iff _ _).1 H)
         cases H)
      | (split at H
         exact FaaDSP _ _ _ _ ‹_›
         cases H)
      | cases H
  · intro H
    cases H <;> simp_all [is_det_head_step, vals_compare_safeb_iff]

/-- Rocq: `det_head_step_singleton`. -/
theorem det_head_step_singleton (e1 : expr) (σ1 : state) (e2 : expr) (σ2 : state)
    (efs : List expr) (Hdet : det_head_step_rel e1 σ1 e2 σ2 efs) :
    head_step e1 σ1 = dret (e2, σ2, efs) := by
  apply pmf_1_eq_dret
  cases Hdet <;> subst_vars <;> simp_all [head_step] <;> exact dret_1_1 _ _ rfl

/-- Rocq: `val_not_head_step`. -/
theorem val_not_head_step (e1 : expr) (σ1 : state) (h : ∃ v, to_val e1 = some v) :
    ¬ head_step_pred e1 σ1 := by
  obtain ⟨v, hv⟩ := h
  obtain rfl := (of_to_val _ _ hv).symm
  rintro (Hs | Hs) <;> cases Hs

/-- Helper (not in Rocq): a deterministic head step is a head step. -/
theorem det_head_step_rel_head_step_rel (e1 : expr) (σ1 : state) (e2 : expr) (σ2 : state)
    (efs : List expr) (H : det_head_step_rel e1 σ1 e2 σ2 efs) :
    head_step_rel e1 σ1 e2 σ2 efs := by
  cases H
  case CmpXchgDS => exact CmpXchgS _ _ _ _ _ _ ‹_› ‹_› rfl
  all_goals subst_vars; constructor <;> first | rfl | assumption

/-- Rocq: `head_step_pred_ex_rel`. -/
theorem head_step_pred_ex_rel (e1 : expr) (σ1 : state) :
    head_step_pred e1 σ1 ↔ ∃ e2 σ2 efs, head_step_rel e1 σ1 e2 σ2 efs := by
  constructor
  · rintro (Hdet | Hdet)
    · obtain ⟨e2, σ2, efs, H⟩ := (det_step_pred_ex_rel _ _).1 Hdet
      exact ⟨e2, σ2, efs, det_head_step_rel_head_step_rel _ _ _ _ _ H⟩
    · cases Hdet <;> subst_vars
      · exact ⟨_, _, _, AllocTapeS _ _ _ _ rfl rfl⟩
      · exact ⟨_, _, _, RandTapeS _ _ _ _ _ _ rfl ‹_›⟩
      · exact ⟨_, _, _, RandTapeEmptyS _ _ _ 0 _ rfl ‹_›⟩
      · exact ⟨_, _, _, RandTapeOtherS _ _ _ _ _ 0 _ rfl ‹_› (Ne.symm ‹_›)⟩
      · exact ⟨_, _, _, RandNoTapeS _ _ 0 _ rfl⟩
  · rintro ⟨e2, σ2, efs, H⟩
    cases H <;> subst_vars
    case RandNoTapeS => exact Or.inr (RandNoTapePSP _ _ _ rfl)
    case AllocTapeS => exact Or.inr (AllocTapePSP _ _ _ rfl)
    case RandTapeS h => exact Or.inr (RandTapePSP _ _ _ _ _ _ rfl h)
    case RandTapeEmptyS h => exact Or.inr (RandEmptyPSP _ _ _ _ rfl h)
    case RandTapeOtherS => exact Or.inr (RandTapeOtherPSP _ _ _ _ _ _ (Ne.symm ‹_›) rfl ‹_›)
    all_goals exact Or.inl (by constructor <;> first | rfl | assumption)

/-- Rocq: `not_head_step_pred_dzero`. -/
theorem not_head_step_pred_dzero (e1 : expr) (σ1 : state) :
    ¬ head_step_pred e1 σ1 ↔ head_step e1 σ1 = dzero := by
  constructor
  · intro Hnstep
    apply dzero_ext
    rintro ⟨e2, σ2, efs⟩
    by_contra H1
    have H1 := (head_step_support_equiv_rel _ _ _ _ _).1 (pos_iff_ne_zero.2 H1)
    exact Hnstep ((head_step_pred_ex_rel _ _).2 ⟨_, _, _, H1⟩)
  · intro Hhead Hp
    obtain ⟨e2, σ2, efs, Hstep⟩ := (head_step_pred_ex_rel _ _).1 Hp
    have := (head_step_support_equiv_rel _ _ _ _ _).2 Hstep
    rw [Hhead, dzero_0] at this
    exact lt_irrefl _ this

/-- Rocq: `det_or_prob_or_dzero`. -/
theorem det_or_prob_or_dzero (e1 : expr) (σ1 : state) :
    det_head_step_pred e1 σ1 ∨ prob_head_step_pred e1 σ1 ∨ head_step e1 σ1 = dzero := by
  by_cases h : head_step_pred e1 σ1
  · rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ((not_head_step_pred_dzero _ _).1 h))

/-- Rocq: `head_step_dzero_upd_tapes`. -/
theorem head_step_dzero_upd_tapes (α : Loc) (e : expr) (σ : state) (N : ℕ)
    (zs : List (Fin (N + 1))) (z : Fin (N + 1)) (Hdom : α ∈ σ.tapes)
    (Hz : head_step e σ = dzero) :
    head_step e (state_upd_tapes (·.insert α ⟨N, zs ++ [z]⟩) σ) = dzero := by
  apply dzero_ext
  intro ρ
  by_contra H
  obtain ⟨ρ', hρ'⟩ := head_step_reducible_transfer e
    (state_upd_tapes (·.insert α ⟨N, zs ++ [z]⟩) σ) σ rfl
    (fun l t hl => by
      simp only [state_upd_tapes_tapes, map_getElem?_insert] at hl
      split at hl
      · subst_vars; exact (map_mem_iff _ _).1 Hdom
      · exact ⟨t, hl⟩)
    ⟨ρ, pos_iff_ne_zero.2 H⟩
  rw [Hz, dzero_0] at hρ'
  exact lt_irrefl _ hρ'

/-- Rocq: `head_step_get_active`. -/
theorem head_step_get_active (α : Loc) (σ σ' : state) (e e' : expr) (efs : List expr)
    (H : α ∈ σ.tapes) (Hh : 0 < head_step e σ (e', σ', efs)) : α ∈ σ'.tapes := by
  rw [head_step_support_equiv_rel] at Hh
  cases Hh <;> simp_all [state_upd_heap_N]
  split <;> simp_all

/-- Rocq: `prim_step_get_active`. -/
theorem prim_step_get_active (α : Loc) (σ σ' : state) (e e' : expr) (efs : List expr)
    (H1 : α ∈ σ.tapes) (H2 : 0 < prim_step (Λ := con_prob_lang) e σ (e', σ', efs)) :
    α ∈ σ'.tapes := by
  obtain ⟨K, e1', e2', -, -, hh⟩ :=
    (conEctxLanguage.prim_step_iff (Λ := con_prob_ectx_lang) _ _ _ _ _).1 H2
  exact head_step_get_active α σ σ' e1' e2' efs H1 hh

/-- Rocq: `det_head_step_upd_tapes`. -/
theorem det_head_step_upd_tapes (N : ℕ) (e1 : expr) (σ1 : state) (e2 : expr) (σ2 : state)
    (efs : List expr) (α : Loc) (z : Fin (N + 1)) (zs : List (Fin (N + 1)))
    (H : det_head_step_rel e1 σ1 e2 σ2 efs) (_ : σ1.tapes[α]? = some ⟨N, zs⟩) :
    det_head_step_rel
      e1 (state_upd_tapes (·.insert α ⟨N, zs ++ [z]⟩) σ1)
      e2 (state_upd_tapes (·.insert α ⟨N, zs ++ [z]⟩) σ2) efs := by
  cases H with
  | CmpXchgDS l v1 v2 _ vl hl hs =>
    have := CmpXchgDS (σ := state_upd_tapes (·.insert α ⟨N, zs ++ [z]⟩) σ1) l v1 v2 vl hl hs
    split at this <;> simp_all [state_upd_heap, state_upd_tapes]
  | _ => constructor <;> first | rfl | assumption

/-- Rocq: `upd_tape_some`. -/
theorem upd_tape_some (σ : state) (α : Loc) (N : ℕ) (n : Fin (N + 1)) (ns : List (Fin (N + 1)))
    (_ : σ.tapes[α]? = some ⟨N, ns⟩) :
    (state_upd_tapes (·.insert α ⟨N, ns ++ [n]⟩) σ).tapes[α]? = some ⟨N, ns ++ [n]⟩ := by
  simp [state_upd_tapes]

/-- Rocq: `upd_tape_some_trivial`. (Rocq's `tapes σ !!! α` is `σ.tapes[α]!`.) -/
theorem upd_tape_some_trivial (σ : state) (α : Loc) (bs : tape) (H : σ.tapes[α]? = some bs) :
    state_upd_tapes (·.insert α σ.tapes[α]!) σ = σ := by
  rw [Std.ExtTreeMap.getElem!_eq_get!_getElem?, H, Option.get!_some]
  cases σ
  simp only [state_upd_tapes] at H ⊢
  rw [map_insert_id _ _ _ H]

/-- Helper (not in Rocq): inserts at distinct keys commute. -/
theorem map_insert_insert_ne {V : Type*} (m : Std.ExtTreeMap Loc V) (k k' : Loc) (v v' : V)
    (h : k ≠ k') : (m.insert k v).insert k' v' = (m.insert k' v').insert k v := by
  ext a : 1
  simp only [map_getElem?_insert]
  split <;> split <;> simp_all

/-- Rocq: `upd_diff_tape_comm`. -/
theorem upd_diff_tape_comm (σ : state) (α β : Loc) (bs bs' : tape) (h : α ≠ β) :
    state_upd_tapes (·.insert β bs) (state_upd_tapes (·.insert α bs') σ) =
      state_upd_tapes (·.insert α bs') (state_upd_tapes (·.insert β bs) σ) := by
  simp only [state_upd_tapes, map_insert_insert_ne _ _ _ _ _ h]

/-- Rocq: `upd_diff_tape_tot`. -/
theorem upd_diff_tape_tot (σ : state) (α β : Loc) (bs : tape) (h : α ≠ β) :
    σ.tapes[α]! = (state_upd_tapes (·.insert β bs) σ).tapes[α]! := by
  simp only [Std.ExtTreeMap.getElem!_eq_get!_getElem?, state_upd_tapes_tapes,
    map_getElem?_insert_ne _ _ _ _ (Ne.symm h)]

/-- Rocq: `upd_tape_twice`. -/
theorem upd_tape_twice (σ : state) (β : Loc) (bs bs' : tape) :
    state_upd_tapes (·.insert β bs) (state_upd_tapes (·.insert β bs') σ) =
      state_upd_tapes (·.insert β bs) σ := by
  simp only [state_upd_tapes, map_insert_insert]

/-- Rocq: `fresh_loc_upd_some`. -/
theorem fresh_loc_upd_some (σ : state) (α : Loc) (bs bs' : tape) (Hα : σ.tapes[α]? = some bs) :
    fresh_loc σ.tapes = fresh_loc (σ.tapes.insert α bs') := by
  apply fresh_loc_eq_dom
  intro l
  rw [Std.ExtTreeMap.mem_insert]
  constructor
  · exact Or.inr
  · rintro (h | h)
    · rw [(compare_eq_iff_eq).1 h] at Hα; exact (map_mem_iff _ _).2 ⟨_, Hα⟩
    · exact h

/-- Rocq: `elem_fresh_ne`. -/
theorem elem_fresh_ne {V : Type*} (ls : Std.ExtTreeMap Loc V) (k : Loc) (v : V)
    (h : ls[k]? = some v) : fresh_loc ls ≠ k := by
  rintro rfl
  exact fresh_loc_is_fresh ls ((map_mem_iff _ _).2 ⟨v, h⟩)

/-- Rocq: `fresh_loc_upd_swap`. -/
theorem fresh_loc_upd_swap (σ : state) (α : Loc) (bs bs' bs'' : tape)
    (H : σ.tapes[α]? = some bs) :
    state_upd_tapes (·.insert (fresh_loc σ.tapes) bs') (state_upd_tapes (·.insert α bs'') σ) =
      state_upd_tapes (·.insert α bs'') (state_upd_tapes (·.insert (fresh_loc σ.tapes) bs') σ) :=
  upd_diff_tape_comm σ α (fresh_loc σ.tapes) bs' bs'' (elem_fresh_ne _ _ _ H).symm

/-- Rocq: `fresh_loc_lookup`. -/
theorem fresh_loc_lookup (σ : state) (α : Loc) (bs bs' : tape) (H : σ.tapes[α]? = some bs) :
    (state_upd_tapes (·.insert (fresh_loc σ.tapes) bs') σ).tapes[α]? = some bs := by
  rw [state_upd_tapes_tapes, map_getElem?_insert_ne _ _ _ _ (elem_fresh_ne _ _ _ H)]
  exact H

/-- Helper (not in Rocq): on a head-reducible expression, `prim_step` of `con_prob_lang` is
`head_step`. -/
theorem prim_step_eq_head_step (e : expr) (σ : state)
    (h : ∃ e' σ' efs, head_step_rel e σ e' σ' efs) :
    prim_step (Λ := con_prob_lang) e σ = head_step e σ := by
  obtain ⟨e', σ', efs, h⟩ := h
  exact conEctxLanguage.head_prim_step_eq (Λ := con_prob_ectx_lang) e σ (head_reducible_of_rel h)

/-- Rocq: `prim_step_empty_tape`. -/
theorem prim_step_empty_tape (σ : state) (α : Loc) (z : ℤ) (K : List ectx_item) (N : ℕ)
    (H : σ.tapes[α]? = some ⟨N, []⟩) :
    prim_step (Λ := con_prob_lang) (fill K (Rand (Val (LitV (LitInt z))) (Val (LitV (LitLbl α)))))
      σ =
    prim_step (Λ := con_prob_lang) (fill K (Rand (Val (LitV (LitInt z))) (Val (LitV LitUnit)))) σ := by
  have h1 := fill_dmap (Λ := con_prob_lang) (K := fill K)
    (Rand (Val (LitV (LitInt z))) (Val (LitV (LitLbl α)))) σ rfl
  have h2 := fill_dmap (Λ := con_prob_lang) (K := fill K)
    (Rand (Val (LitV (LitInt z))) (Val (LitV LitUnit))) σ rfl
  rw [h1, h2]
  congr 1
  rw [prim_step_eq_head_step _ _ (rand_lbl_head_step_rel σ α z _ H),
    prim_step_eq_head_step _ _ ⟨_, _, _, RandNoTapeS z _ 0 σ rfl⟩]
  simp only [head_step, H]
  split
  · subst_vars; rfl
  · rfl

/-- Helper (not in Rocq): `μ` has finite support. -/
def fin_supp {A : Type*} [Countable A] (μ : Distr A) : Prop := ∃ lis : List A, ∀ x, 0 < μ x → x ∈ lis

theorem fin_supp_dret {A : Type*} [Countable A] (a : A) : fin_supp (dret a) :=
  ⟨[a], fun x hx => by rw [dret_pos a x hx]; exact List.mem_singleton_self a⟩

theorem fin_supp_dzero {A : Type*} [Countable A] : fin_supp (dzero : Distr A) :=
  ⟨[], fun x hx => by rw [dzero_0] at hx; exact absurd hx (lt_irrefl _)⟩

theorem fin_supp_dmap {A B : Type*} [Countable A] [Countable B] (f : A → B) (μ : Distr A)
    (h : fin_supp μ) : fin_supp (dmap f μ) := by
  obtain ⟨lis, hl⟩ := h
  refine ⟨lis.map f, fun x hx => ?_⟩
  obtain ⟨a, rfl, ha⟩ := (dmap_pos _ _ _).1 hx
  exact List.mem_map_of_mem (hl a ha)

theorem fin_supp_dunifP (N : ℕ) : fin_supp (dunifP N) :=
  ⟨List.finRange (N + 1), fun x _ => List.mem_finRange x⟩

theorem head_step_fin_supp (e : expr) (σ : state) : fin_supp (head_step e σ) := by
  unfold head_step
  split <;> (try dsimp only) <;> (repeat' split) <;>
    first
    | exact fin_supp_dret _
    | exact fin_supp_dzero
    | exact fin_supp_dmap _ _ (fin_supp_dunifP _)

/-- Rocq: `prim_step_finite_options`. -/
theorem prim_step_finite_options (e : expr) (σ : state) :
    ∃ lis : List (expr × state × List expr),
      ∀ x, 0 < prim_step (Λ := con_prob_lang) e σ x → x ∈ lis :=
  fin_supp_dmap _ _ (head_step_fin_supp _ _)

/-- Rocq: `ex_seriesC_prim_step_mult_fn_con_prob_lang`. (Trivial in `ℝ≥0∞`.) -/
theorem ex_seriesC_prim_step_mult_fn_con_prob_lang (e : expr) (σ : state)
    (f : expr × state × List expr → ℝ≥0∞) :
    Summable (fun x => prim_step (Λ := con_prob_lang) e σ x * f x) :=
  ENNReal.summable

/-- Rocq: `empty_lists_state`. -/
def empty_lists_state (σ : state) : Prop :=
  ∀ (α : Loc) (ls : tape), σ.tapes[α]? = some ls → ∃ N, ls = (⟨N, []⟩ : tape)

/-- Rocq: `prim_step_empty_tape_preserve`. -/
theorem prim_step_empty_tape_preserve (e : expr) (σ : state) (Hempty : empty_lists_state σ) :
    ∀ e' σ' efs, 0 < prim_step (Λ := con_prob_lang) e σ (e', σ', efs) → empty_lists_state σ' := by
  intro e' σ' efs H
  obtain ⟨K, e1', e2', -, -, hh⟩ :=
    (conEctxLanguage.prim_step_iff (Λ := con_prob_ectx_lang) _ _ _ _ _).1 H
  have hh : 0 < head_step e1' σ (e2', σ', efs) := hh
  rw [head_step_support_equiv_rel] at hh
  cases hh with
  | AllocTapeS z N _ l =>
    intro β ls hβ
    simp only [state_upd_tapes_tapes, map_getElem?_insert] at hβ
    split at hβ
    · cases hβ; exact ⟨_, rfl⟩
    · exact Hempty _ _ hβ
  | RandTapeS l z N n ns _ _ h =>
    obtain ⟨M, hM⟩ := Hempty _ _ h
    cases hM
  | CmpXchgS =>
    split
    · exact Hempty
    · exact Hempty
  | _ => exact Hempty

end con_prob_lang

end ConProbLang
