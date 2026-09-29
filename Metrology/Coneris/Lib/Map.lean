module

public import Metrology.Coneris.ProofMode

/-!
# A simple map for Coneris

Ported from clutch/theories/coneris/lib/map.v

A simple map as an associative linked list, based on the examples from the transfinite Iris
repo.

## Rocq → Lean mapping
* Programs are written with the `cpl_val(...)` notation: `match: e with NONE => e1 | SOME "p"
  => e2 end` is `match e with | none() => e1 | some(p) => e2`, `NONE`/`SOME e` are
  `none()`/`some(e)`, `ref e` is `ref(e)`, `λ:<>, e` is `λ <>, e`. Rocq's `cons_list !"m" x`
  and `find_list !"m" "k"` are written `&cons_list (!m) x`, `&find_list (!m) k` (in the Lean
  notation `!e` is not an application argument without parentheses).
* `{{{ P }}} e @ E {{{ x, RET v; Q }}}` is iris-lean's `{{ P }} (e) @ s; E {{ x, RET v; Q }}`,
  generalized over the stuckness `s`.
* `gmap nat val` is `Std.ExtTreeMap ℕ val compare` (abbreviation `natmap`), `m !! n` is
  `m[n]?`, `<[n := v]> m` is `m.insert n v`, `∅` is `∅`.
* stdpp's `list_to_map` (a right fold of `insert`, so that the first binding of a key wins) is
  the local helper `list_to_map` (a `List.foldr`); note that `Std.ExtTreeMap.ofList` is a left
  fold (the last binding wins) and is therefore not used.
* `bool_decide (k' = k)` is the Lean `if k' = k then .. else ..` (decidable equality);
  `bool_decide (z < 0)%Z` is `if z < 0 then .. else ..`.
* `#k` for `k : nat` is `LitV (LitInt (k : ℤ))`; `LitV (LitLoc l)` is kept.
* `NONEV`/`SOMEV` are the derived forms of `Metrology.ConProbLang.Notation`.
* Proofs by `iInduction` are Lean inductions on the (closed) Texan-triple statements.

## Added
* `natmap`, `list_to_map`, `list_to_map_cons` (stdpp's `list_to_map` and `list_to_map_cons`).
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang
open Coneris

namespace Coneris.Lib.Map

/-! ## Programs -/

/-- Rocq: `find_list`. -/
def find_list : val :=
  cpl_val(rec find h k :=
    match !h with
    | none() => none()
    | some(p) =>
        let kv := fst(p) in
        let next := snd(p) in
        if fst(kv) = k then some(snd(kv)) else find next k)

/-- Rocq: `cons_list`. -/
def cons_list : val :=
  cpl_val(λ h v, ref(some((v, h))))

/-- Rocq: `init_list`. -/
def init_list : val :=
  cpl_val(λ <>, ref(none()))

/-- Rocq: `init_map`. -/
def init_map : val :=
  cpl_val(λ <>, ref(&init_list #()))

/-- Rocq: `get`. -/
def get : val :=
  cpl_val(λ m k, &find_list (!m) k)

/-- Rocq: `set`. -/
def set : val :=
  cpl_val(λ m k v, m ← &cons_list (!m) (k, v))

/-- Sanity check: the transcription of `find_list` is the intended AST. -/
example : find_list =
    val.RecV (.BNamed "find") (.BNamed "h") (expr.Rec .BAnon (.BNamed "k")
      (expr.Case (expr.Load (expr.Var "h"))
        (Lam .BAnon (expr.InjL (expr.Val (val.LitV .LitUnit))))
        (Lam (.BNamed "p")
          (Let (.BNamed "kv") (expr.Fst (expr.Var "p"))
            (Let (.BNamed "next") (expr.Snd (expr.Var "p"))
              (expr.If (expr.BinOp .EqOp (expr.Fst (expr.Var "kv")) (expr.Var "k"))
                (expr.InjR (expr.Snd (expr.Var "kv")))
                (expr.App (expr.App (expr.Var "find") (expr.Var "next")) (expr.Var "k")))))))) :=
  rfl

/-- Sanity check: the transcription of `set` is the intended AST. -/
example : set =
    val.RecV .BAnon (.BNamed "m") (expr.Rec .BAnon (.BNamed "k") (expr.Rec .BAnon (.BNamed "v")
      (expr.Store (expr.Var "m")
        (expr.App (expr.App (expr.Val cons_list) (expr.Load (expr.Var "m")))
          (expr.Pair (expr.Var "k") (expr.Var "v")))))) :=
  rfl

/-- Sanity check: the transcription of `cons_list` is the intended AST. -/
example : cons_list =
    val.RecV .BAnon (.BNamed "h") (expr.Rec .BAnon (.BNamed "v")
      (Alloc (expr.InjR (expr.Pair (expr.Var "v") (expr.Var "h"))))) :=
  rfl

/-! ## Pure model -/

/-- Rocq: `gmap nat val`. -/
abbrev natmap : Type := Std.ExtTreeMap ℕ val compare

/-- Rocq (stdpp): `list_to_map`, specialised to `gmap nat val`: a right fold of `insert`, so
the first binding of a key in the list wins. -/
def list_to_map (vs : List (ℕ × val)) : natmap :=
  vs.foldr (fun kv m => m.insert kv.1 kv.2) ∅

/-- Rocq (stdpp): `list_to_map_cons`. -/
theorem list_to_map_cons (k : ℕ) (v : val) (vs : List (ℕ × val)) :
    list_to_map ((k, v) :: vs) = (list_to_map vs).insert k v := rfl

/-- Rocq: `find_list_gallina`. -/
def find_list_gallina : List (ℕ × val) → ℕ → Option val
  | [], _ => none
  | (k', v') :: vs, k => if k' = k then some v' else find_list_gallina vs k

/-- Rocq: `opt_to_val`. -/
def opt_to_val : Option val → val
  | some v => SOMEV v
  | none => NONEV

/-- Rocq: `find_list_gallina_map_lookup`. -/
theorem find_list_gallina_map_lookup (vs : List (ℕ × val)) (m : natmap) (n : ℕ)
    (Heq : list_to_map vs = m) : find_list_gallina vs n = m[n]? := by
  subst Heq
  induction vs with
  | nil => simp [list_to_map, find_list_gallina]
  | cons kv vs IH =>
    obtain ⟨k, v⟩ := kv
    rw [list_to_map_cons, Std.ExtTreeMap.getElem?_insert]
    by_cases h : k = n
    · subst h; simp [find_list_gallina]
    · simp [find_list_gallina, h, IH]

section map

variable {GF : BundledGFunctors} [conerisGS GF]
variable {s : Stuckness} {E : CoPset}

/-! ## Linked lists -/

/-- Rocq: `assoc_list` (Impl). -/
def assoc_list : Loc → List (ℕ × val) → IProp GF
  | l, [] => l ↦ NONEV
  | l, (k, v) :: vs =>
    iprop(∃ l' : Loc, l ↦ SOMEV (PairV (PairV (LitV (LitInt (k : ℤ))) v) (LitV (LitLoc l'))) ∗
      assoc_list l' vs)

/-- Rocq: `timeless_assoc_list`. -/
instance timeless_assoc_list (l : Loc) (vs : List (ℕ × val)) :
    Timeless (assoc_list l vs : IProp GF) := by
  induction vs generalizing l with
  | nil => unfold assoc_list; infer_instance
  | cons kv vs IH =>
    obtain ⟨k, v⟩ := kv
    unfold assoc_list; infer_instance

/-- Rocq: `wp_init_list`. -/
theorem wp_init_list :
    {{ True }} (cpl(&init_list #())) @ s; E
    {{ l, RET LitV (LitLoc l); (assoc_list l [] : IProp GF) }} := by
  simp only [assoc_list]
  iintro %Φ - HΦ
  wp_lam
  wp_pures
  wp_alloc l as Hl
  imodintro
  iapply HΦ
  iexact Hl

/-- Rocq: `wp_cons_list`. -/
theorem wp_cons_list (l : Loc) (vs : List (ℕ × val)) (k : ℕ) (v : val) :
    {{ assoc_list l vs }} (cpl(&cons_list #l v((#k, &v)))) @ s; E
    {{ l', RET LitV (LitLoc l'); (assoc_list l' ((k, v) :: vs) : IProp GF) }} := by
  simp only [assoc_list]
  iintro %Φ H HΦ
  wp_lam
  wp_pures
  wp_alloc l' as H'
  imodintro
  iapply HΦ
  iexists l
  iframe

/-- Rocq: `wp_find_list`. -/
theorem wp_find_list (l : Loc) (vs : List (ℕ × val)) (k : ℕ) :
    {{ assoc_list l vs }} (cpl(&find_list #l #k)) @ s; E
    {{ v, RET v; (assoc_list l vs ∗ ⌜v = opt_to_val (find_list_gallina vs k)⌝ : IProp GF) }} := by
  induction vs generalizing l with
  | nil =>
    simp only [assoc_list]
    iintro %Φ Hl HΦ
    wp_rec
    wp_pures
    wp_load
    wp_pures
    imodintro
    iapply HΦ
    iframe
    ipureintro
    rfl
  | cons kv vs IH =>
    obtain ⟨k', v'⟩ := kv
    simp only [assoc_list]
    iintro %Φ ⟨%l', Hl, Hassoc⟩ HΦ
    wp_rec
    wp_pures
    wp_load
    wp_pures
    by_cases Hcase : k' = k
    · rw [decide_eq_true Hcase]
      wp_pures
      imodintro
      iapply HΦ
      isplitl
      · iexists l'
        iframe
      ipureintro
      simp [find_list_gallina, Hcase, opt_to_val]
    · rw [decide_eq_false Hcase]
      wp_pures
      iapply IH l' $$ Hassoc
      inext
      iintro %v ⟨Hassoc, %Hv⟩
      iapply HΦ
      isplitl
      · iexists l'
        iframe
      ipureintro
      simp [find_list_gallina, Hcase, Hv]

/-- Rocq: `wp_find_list_Z`. -/
theorem wp_find_list_Z (l : Loc) (vs : List (ℕ × val)) (z : ℤ) :
    {{ assoc_list l vs }} (cpl(&find_list #l #z)) @ s; E
    {{ v, RET v; (assoc_list l vs ∗
        ⌜v = if z < 0 then opt_to_val none
             else opt_to_val (find_list_gallina vs z.toNat)⌝ : IProp GF) }} := by
  induction vs generalizing l with
  | nil =>
    simp only [assoc_list]
    iintro %Φ Hl HΦ
    wp_rec
    wp_pures
    wp_load
    wp_pures
    imodintro
    iapply HΦ
    iframe
    ipureintro
    split <;> rfl
  | cons kv vs IH =>
    obtain ⟨k', v'⟩ := kv
    simp only [assoc_list]
    iintro %Φ ⟨%l', Hl, Hassoc⟩ HΦ
    wp_rec
    wp_pures
    wp_load
    wp_pures
    by_cases Hbool : (k' : ℤ) = z
    · rw [decide_eq_true Hbool]
      wp_pures
      imodintro
      iapply HΦ
      isplitl
      · iexists l'
        iframe
      ipureintro
      subst Hbool
      simp [find_list_gallina, opt_to_val]
    · rw [decide_eq_false Hbool]
      wp_pures
      iapply IH l' $$ Hassoc
      inext
      iintro %v ⟨Hassoc, %Hv⟩
      iapply HΦ
      isplitl
      · iexists l'
        iframe
      ipureintro
      split
      · simp_all
      · have Hne : k' ≠ z.toNat := by omega
        simp_all [find_list_gallina]

/-! ## Maps -/

/-- Rocq: `map_list`. -/
def map_list (lm : Loc) (m : natmap) : IProp GF :=
  iprop(∃ (lv : Loc) (vs : List (ℕ × val)),
    lm ↦ LitV (LitLoc lv) ∗ ⌜list_to_map vs = m⌝ ∗ assoc_list lv vs)

/-- Rocq: `timeless_map_list`. -/
instance timeless_map_list (l : Loc) (m : natmap) : Timeless (map_list l m : IProp GF) := by
  unfold map_list; infer_instance

/-- Rocq: `wp_init_map`. -/
theorem wp_init_map :
    {{ True }} (cpl(&init_map #())) @ s; E
    {{ l, RET LitV (LitLoc l); (map_list l ∅ : IProp GF) }} := by
  unfold map_list
  iintro %Φ - HΦ
  wp_lam
  wp_pures
  wp_apply wp_init_list $$ [] with %l Halloc
  · itrivial
  wp_alloc lm as Hlm
  imodintro
  iapply HΦ
  iexists l, []
  iframe
  ipureintro
  rfl

/-- Rocq: `wp_get`. -/
theorem wp_get (lm : Loc) (m : natmap) (n : ℕ) :
    {{ map_list lm m }} (cpl(&get #lm #n)) @ s; E
    {{ res, RET res; (map_list lm m ∗ ⌜res = opt_to_val m[n]?⌝ : IProp GF) }} := by
  unfold map_list
  iintro %Φ Hm HΦ
  wp_lam
  wp_pures
  icases Hm with ⟨%ll, %vs, Hll, %Heq, Hassoc⟩
  wp_load
  wp_apply wp_find_list ll vs n $$ Hassoc with %vret ⟨Hassoc, %Hm⟩
  iapply HΦ
  isplitl
  · iexists ll, vs
    iframe
    ipureintro
    exact Heq
  ipureintro
  rw [Hm, find_list_gallina_map_lookup vs m n Heq]

/-- Rocq: `wp_get_Z`. -/
theorem wp_get_Z (lm : Loc) (m : natmap) (z : ℤ) :
    {{ map_list lm m }} (cpl(&get #lm #z)) @ s; E
    {{ res, RET res; (map_list lm m ∗
        ⌜res = if z < 0 then opt_to_val none else opt_to_val m[z.toNat]?⌝ : IProp GF) }} := by
  unfold map_list
  iintro %Φ Hm HΦ
  wp_lam
  wp_pures
  icases Hm with ⟨%ll, %vs, Hll, %Heq, Hassoc⟩
  wp_load
  wp_apply wp_find_list_Z ll vs z $$ Hassoc with %vret ⟨Hassoc, %Hm⟩
  iapply HΦ
  isplitl
  · iexists ll, vs
    iframe
    ipureintro
    exact Heq
  ipureintro
  rw [Hm, find_list_gallina_map_lookup vs m z.toNat Heq]

/-- Rocq: `wp_set`. -/
theorem wp_set (lm : Loc) (m : natmap) (n : ℕ) (v : val) :
    {{ map_list lm m }} (cpl(&set #lm #n &v)) @ s; E
    {{ RET LitV LitUnit; (map_list lm (m.insert n v) : IProp GF) }} := by
  unfold map_list
  iintro %Φ Hm HΦ
  wp_lam
  wp_pures
  icases Hm with ⟨%ll, %vs, Hll, %Heq, Hassoc⟩
  wp_load
  wp_pures
  wp_apply wp_cons_list ll vs n v $$ Hassoc with %l' Hassoc'
  wp_apply wp_store $$ Hll with Hll
  iapply HΦ
  iexists l', (n, v) :: vs
  iframe
  ipureintro
  rw [list_to_map_cons, Heq]

end map

end Coneris.Lib.Map
