module

public import Metrology.Coneris.ProofMode
public import Metrology.ConProbLang.Common.ConInject

/-!
# Lists in `con_prob_lang` (programs)

Ported from clutch/theories/coneris/lib/list.v (section `list_code`, `inject_list`,
`Inject_list`).

The Rocq file is split into several Lean modules:
* `Coneris.Lib.List` (this file): the programs, `inject_list`, `Inject_list`.
* `Coneris.Lib.ListSpec`: `is_list`, `is_list_inject`, the specs of `list_nil`, `list_cons`,
  `list_head`, `list_tail`, `list_length` (section `list_specs`, first part).
* `Coneris.Lib.ListIter`: the specs of `list_iter`, `list_iteri` (section `list_specs`).
* `Coneris.Lib.ListFold`: the specs of `list_fold`, `list_sub`, `list_nth` (section
  `list_specs`).
* `Coneris.Lib.ListRemove`: the specs of `list_remove_nth`, `list_remove_nth_total`,
  `list_find_remove`, `list_rev`, `list_append`, `list_forall`, `list_is_empty`,
  `list_filter`, `list_split` and the pure lemmas `is_list_eq`, `is_list_inv_l`, `is_list_snoc`
  (end of section `list_specs`).
* `Coneris.Lib.ListMap`: section `list_specs_extra` (`list_map`, `list_mapi`, `list_make`,
  `list_seq`, `list_seq_fun`).
* `Coneris.Lib.ListHO`: section `list_specs_HO` (lists of arbitrary values).

## Rocq → Lean
* The programs are `val`s written with the `cpl_val(...)` notation, except `list_nil`, which is
  an `expr` (Rocq: `Definition list_nil := NONE`). Variables are Lean identifiers (Rocq: string
  literals); references to other program definitions are escaped with `&`.
* The Rocq expression notations `[]`, `x :: l`, `[x]`, `[x; y; ..; z]` (for `list_nil`,
  `list_cons`) are not provided (they would clash with Lean's list notation); write
  `&list_nil` and `v(&list_cons) x l`.
* `Inject_list` is an instance of `Inject (List A) val` (Rocq: `Global Program Instance`; the
  obligation is the injectivity proof `inject_list_inj`).
* The whole unit is imported by `Coneris.Lib.ListAll`.

## Omitted
* The expression notations `[]`, `::`, `[x]`, `[x; y; ..; z]` (see above).

## Added (not in Rocq)
* `inject_list_inj` (the obligation of `Inject_list`), `inject_list_nil`, `inject_list_cons`.
* Proof helper tactics `wp_decide` and `wp_pures'` (see their docstrings): the core
  side-condition tactic `wp_solve_side` fails on `vals_compare_safe (#↑n) (#0)` (the
  `simp only [..., true_or, ...]` branch is ambiguous with `Iris.BI.true_or`), and `wp_pures`
  cannot see through the definition `list_nil` inside substitutions.
-/

@[expose] public section

open ConProbLang ConProbLang.con_prob_lang

namespace Coneris.Lib.List

/-! ## Programs (Rocq: section `list_code`) -/

/-- Rocq: `list_nil`. -/
def list_nil : expr := NONE

/-- Rocq: `list_cons`. -/
def list_cons : val := cpl_val(λ elem list, some((elem, list)))

/-- Rocq: `list_head`. -/
def list_head : val :=
  cpl_val(λ l, match l with
    | some(a) => some(fst(a))
    | none() => none())

/-- Rocq: `list_tail`. -/
def list_tail : val :=
  cpl_val(λ l, match l with
    | some(a) => snd(a)
    | none() => none())

/-- Rocq: `list_fold`. -/
def list_fold : val :=
  cpl_val(rec list_fold handler acc l :=
    match l with
    | some(a) =>
      let f := fst(a);
      let s := snd(a);
      let acc := handler acc f;
      list_fold handler acc s
    | none() => acc)

/-- Rocq: `list_iter`. -/
def list_iter : val :=
  cpl_val(rec list_iter handler l :=
    match l with
    | some(a) =>
      let tail := snd(a);
      handler (fst(a));
      list_iter handler tail
    | none() => #())

/-- Rocq: `list_iteri_loop`. -/
def list_iteri_loop : val :=
  cpl_val(rec list_iteri_loop handler i l :=
    match l with
    | some(a) =>
      let tail := snd(a);
      handler i (fst(a));
      list_iteri_loop handler (i + #1) tail
    | none() => #())

/-- Rocq: `list_iteri`. -/
def list_iteri : val := cpl_val(λ handler l, v(&list_iteri_loop) handler #0 l)

/-- Rocq: `list_mapi_loop`. -/
def list_mapi_loop : val :=
  cpl_val(rec list_mapi_loop f k l :=
    match l with
    | some(a) => v(&list_cons) (f k (fst(a))) (list_mapi_loop f (k + #1) (snd(a)))
    | none() => none())

/-- Rocq: `list_mapi`. -/
def list_mapi : val := cpl_val(λ f l, v(&list_mapi_loop) f #0 l)

/-- Rocq: `list_map`. -/
def list_map : val :=
  cpl_val(rec list_map f l :=
    match l with
    | some(a) => v(&list_cons) (f (fst(a))) (list_map f (snd(a)))
    | none() => none())

/-- Rocq: `list_zip`. -/
def list_zip : val :=
  cpl_val(rec list_zip f l1 l2 :=
    match l1 with
    | some(a1) =>
      (match l2 with
        | some(a2) => v(&list_cons) ((fst(a1), fst(a2))) (list_zip f (snd(a1)) (snd(a2)))
        | none() => none())
    | none() => none())

/-- Rocq: `list_filter`. -/
def list_filter : val :=
  cpl_val(rec list_filter f l :=
    match l with
    | some(a) =>
      let r := list_filter f (snd(a));
      (if f (fst(a))
       then v(&list_cons) (fst(a)) r
       else r)
    | none() => none())

/-- Rocq: `list_length`. -/
def list_length : val :=
  cpl_val(rec list_length l :=
    match l with
    | some(a) => #1 + (list_length (snd(a)))
    | none() => #0)

/-- Rocq: `list_nth`. -/
def list_nth : val :=
  cpl_val(rec list_nth l i :=
    match l with
    | some(a) =>
      (if i = #0
       then some(fst(a))
       else list_nth (snd(a)) (i - #1))
    | none() => none())

/-- Rocq: `list_mem`. -/
def list_mem : val :=
  cpl_val(rec list_mem x l :=
    match l with
    | some(a) =>
      let head := fst(a);
      let tail := snd(a);
      (x = head) || (list_mem x tail)
    | none() => #false)

/-- Rocq: `list_remove_nth`. -/
def list_remove_nth : val :=
  cpl_val(rec list_remove_nth l i :=
    match l with
    | some(a) =>
      let head := fst(a);
      let tail := snd(a);
      (if i = #0
       then some((head, tail))
       else
         let r := list_remove_nth tail (i - #1);
         (match r with
          | some(b) =>
            let head' := fst(b);
            let tail' := snd(b);
            some((head', v(&list_cons) head tail'))
          | none() => none()))
    | none() => &list_nil)

/-- Rocq: `list_remove_nth_total`. -/
def list_remove_nth_total : val :=
  cpl_val(rec list_remove_nth_total l i :=
    match l with
    | some(a) =>
      (if i = #0
       then snd(a)
       else v(&list_cons) (fst(a)) (list_remove_nth_total (snd(a)) (i - #1)))
    | none() => &list_nil)

/-- Rocq: `list_find_remove`. -/
def list_find_remove : val :=
  cpl_val(rec list_find_remove f l :=
    match l with
    | some(a) =>
      let head := fst(a);
      let tail := snd(a);
      (if f head
       then some((head, tail))
       else
         let r := list_find_remove f tail;
         (match r with
          | some(b) =>
            let head' := fst(b);
            let tail' := snd(b);
            some((head', v(&list_cons) head tail'))
          | none() => none()))
    | none() => none())

/-- Rocq: `list_sub`. -/
def list_sub : val :=
  cpl_val(rec list_sub i l :=
    (if i ≤ #0
     then &list_nil
     else
       (match l with
        | some(a) => v(&list_cons) (fst(a)) (list_sub (i - #1) (snd(a)))
        | none() => &list_nil)))

/-- Rocq: `list_rev_aux`. -/
def list_rev_aux : val :=
  cpl_val(rec list_rev_aux l acc :=
    match l with
    | none() => acc
    | some(p) =>
      let h := fst(p);
      let t := snd(p);
      let acc' := v(&list_cons) h acc;
      list_rev_aux t acc')

/-- Rocq: `list_rev`. -/
def list_rev : val := cpl_val(λ l, v(&list_rev_aux) l &list_nil)

/-- Rocq: `list_append`. -/
def list_append : val :=
  cpl_val(rec list_append l r :=
    match l with
    | none() => r
    | some(p) =>
      let h := fst(p);
      let t := snd(p);
      v(&list_cons) h (list_append t r))

/-- Rocq: `list_is_empty`. -/
def list_is_empty : val :=
  cpl_val(λ l, match l with
    | none() => #true
    | some(_p) => #false)

/-- Rocq: `list_forall`. -/
def list_forall : val :=
  cpl_val(rec list_forall test l :=
    match l with
    | none() => #true
    | some(p) =>
      let h := fst(p);
      let t := snd(p);
      (test h) && (list_forall test t))

/-- Rocq: `list_make`. -/
def list_make : val :=
  cpl_val(rec list_make len init :=
    (if len = #0
     then &list_nil
     else v(&list_cons) init (list_make (len - #1) init)))

/-- Rocq: `list_init`. -/
def list_init : val :=
  cpl_val(λ len f,
    letrec aux acc i :=
      (if i = len
       then v(&list_rev) acc
       else aux (v(&list_cons) (f i) acc) (i + #1)) in
    aux &list_nil #0)

/-- Rocq: `list_seq`. -/
def list_seq : val :=
  cpl_val(rec list_seq st ln :=
    (if ln ≤ #0
     then &list_nil
     else v(&list_cons) st (list_seq (st + #1) (ln - #1))))

/-- Rocq: `list_seq_fun`. -/
def list_seq_fun : val :=
  cpl_val(rec list_seq_fun st ln f :=
    (if ln ≤ #0
     then &list_nil
     else v(&list_cons) (f st) (list_seq_fun (st + #1) (ln - #1) f)))

/-- Rocq: `list_update`. -/
def list_update : val :=
  cpl_val(rec list_update l i v :=
    match l with
    | some(a) =>
      (if i = #0
       then v(&list_cons) v (v(&list_tail) l)
       else v(&list_cons) (fst(a)) (list_update (snd(a)) (i - #1) v))
    | none() => &list_nil)

/-- Rocq: `list_suf`. -/
def list_suf : val :=
  cpl_val(rec list_suf i l :=
    (if i = #0
     then l
     else
       (match l with
        | none() => none()
        | some(p) => list_suf (i - #1) (snd(p)))))

/-- Rocq: `list_inf_ofs`. -/
def list_inf_ofs : val :=
  cpl_val(λ i ofs l,
    (if ofs ≤ #0
     then &list_nil
     else v(&list_sub) ofs (v(&list_suf) i l)))

/-- Rocq: `list_inf`. -/
def list_inf : val := cpl_val(λ i j l, v(&list_inf_ofs) i ((j - i) + #1) l)

/-- Rocq: `list_split`. -/
def list_split : val :=
  cpl_val(rec list_split i l :=
    (if i ≤ #0
     then (&list_nil, l)
     else
       (match l with
        | none() => (&list_nil, &list_nil)
        | some(p) =>
          let x := fst(p);
          let tl := snd(p);
          let ps := list_split (i - #1) tl;
          (v(&list_cons) x (fst(ps)), snd(ps)))))

/-! ## Injecting lists -/

/-- Rocq: `inject_list`. -/
def inject_list {A : Type} [Inject A val] : List A → val
  | [] => NONEV
  | x :: xs' => SOMEV (PairV (inject x) (inject_list xs'))

/-- The obligation of Rocq's `Inject_list`. -/
theorem inject_list_inj {A : Type} [Inject A val] :
    Function.Injective (inject_list (A := A)) := by
  intro xs
  induction xs with
  | nil => rintro (_ | ⟨y, ys⟩) h <;> simp_all [inject_list]
  | cons x xs IH =>
    rintro (_ | ⟨y, ys⟩) h
    · simp [inject_list] at h
    · simp only [inject_list, val.InjRV.injEq, val.PairV.injEq] at h
      rw [Inject.inject_inj h.1, IH h.2]

/-- Rocq: `Inject_list`. -/
instance Inject_list {A : Type} [Inject A val] : Inject (List A) val where
  inject := inject_list
  inject_inj := inject_list_inj

theorem inject_list_nil {A : Type} [Inject A val] : inject ([] : List A) = NONEV := rfl

theorem inject_list_cons {A : Type} [Inject A val] (x : A) (xs : List A) :
    inject (x :: xs) = SOMEV (PairV (inject x) (inject xs)) := rfl

/-! ## Proof helpers (not in Rocq) -/

/-- Rewrite the first `decide p` in the goal to `true` or `false`, proving `p` or `¬ p` by
`omega` (Rocq: `case_bool_decide` followed by `lia`). -/
macro "wp_decide" : tactic => `(tactic| first
  | (rw [decide_eq_true (by omega)])
  | (rw [decide_eq_false (by omega)]))

/-- `wp_pures`, also unfolding `list_nil` (which blocks the substitutions of `wp_pures`), stepping comparisons of integer literals (whose `vals_compare_safe` side
condition the core side-condition tactic does not solve for non-numeral literals) and deciding
the resulting (in)equalities between integers with `omega`. -/
macro "wp_pures'" : tactic => `(tactic| repeat (first
  | (fail_if_no_progress wp_pures)
  | (fail_if_no_progress simp only [list_nil])
  | (wp_op; exact Or.inl trivial)
  | wp_decide))

end Coneris.Lib.List
