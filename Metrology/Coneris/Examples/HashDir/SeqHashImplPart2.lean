module

public import Metrology.Coneris.Examples.HashDir.SeqHashImpl

/-!
# A sequential hash implementation against the collision-free hash view interface
(part 2: presampling)

Ported from clutch/theories/coneris/examples/hash/seq_hash_impl.v (`coll_free_hash_presample`).

## Rocq → Lean mapping
* `coll_free_hash_presample` (same name). Errors are `ℝ≥0∞`:
  `nnreal_div (nnreal_nat a) (nnreal_nat b)` is `(a : ℝ≥0∞) / (b : ℝ≥0∞)`, and the natural
  subtraction `S val_size - k` is kept (`k` the number of used hash values
  `length (map_to_list m) + length (tape_m_elements tape_m)`). If `S val_size - k = 0`, Rocq's
  `nnreal_div _ 0` is `0` and the Lean `_ / 0` is `∞`; this case cannot occur, since the premise
  `↯ (k / (val_size + 1))` gives `k < val_size + 1` (`ec_valid`).
* Rocq's error function `ε2` (with `bool_decide (fin_to_nat x ∈ ...)`) is `presample_err`; the
  `SeriesC` computation of Rocq is the helper `presample_err_sum` (a finite sum over
  `Fin (val_size + 1)`), which is an equality in `ℝ≥0∞` (Rocq proves `≤` by `right`, i.e.
  equality).
* The `Forall` over the tape elements (Rocq: `Hforall2`) is the helper `rand_tapes_bigSepM_valid`.

## Added
* `presample_err`, `presample_err_sum`, `card_filter_mem_fin`, `rand_tapes_bigSepM_valid`.
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

/-! ## The error arithmetic -/

/-- Helper (Rocq: the error function `ε2` of `coll_free_hash_presample`): `1` on the values in
`bad`, `c` elsewhere. -/
def presample_err (N : ℕ) (bad : List ℕ) (c : ℝ≥0∞) (x : Fin (N + 1)) : ℝ≥0∞ :=
  if (x : ℕ) ∈ bad then 1 else c

/-- Helper: the number of elements of `Fin (N + 1)` in a duplicate-free list of values `≤ N`. -/
theorem card_filter_mem_fin (N : ℕ) (bad : List ℕ) (hnd : bad.Nodup) (hb : ∀ x ∈ bad, x ≤ N) :
    (Finset.univ.filter (fun x : Fin (N + 1) => (x : ℕ) ∈ bad)).card = bad.length := by
  rw [← Finset.card_map Fin.valEmbedding, ← List.toFinset_card_of_nodup hnd]
  congr 1
  ext y
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
    List.mem_toFinset]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact hx
  · intro hy; exact ⟨⟨y, Nat.lt_succ_of_le (hb y hy)⟩, hy, rfl⟩

/-- Helper: the `SeriesC` computation of `coll_free_hash_presample`. -/
theorem presample_err_sum (N : ℕ) (bad : List ℕ) (hnd : bad.Nodup) (hb : ∀ x ∈ bad, x ≤ N)
    (hlt : bad.length < N + 1) (ε : ℝ≥0∞) :
    ∑' x : Fin (N + 1), 1 / ((N : ℝ≥0∞) + 1) *
      presample_err N bad ((((N + 1 : ℕ) : ℝ≥0∞) / ((N + 1 - bad.length : ℕ) : ℝ≥0∞)) * ε) x
      ≤ ε + (bad.length : ℝ≥0∞) / ((N + 1 : ℕ) : ℝ≥0∞) := by
  rw [add_comm ε]
  unfold presample_err
  rw [tsum_fintype, ← Finset.mul_sum, Finset.sum_ite, Finset.sum_const, Finset.sum_const,
    nsmul_eq_mul, nsmul_eq_mul, mul_one, card_filter_mem_fin N bad hnd hb]
  have hcard' : (Finset.univ.filter (fun x : Fin (N + 1) => ¬ (x : ℕ) ∈ bad)).card =
      N + 1 - bad.length := by
    have := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun x : Fin (N + 1) => (x : ℕ) ∈ bad)
    rw [card_filter_mem_fin N bad hnd hb, Finset.card_univ, Fintype.card_fin] at this
    omega
  rw [hcard', ← mul_assoc, ENNReal.mul_div_cancel (by rw [Ne, Nat.cast_eq_zero]; omega) (by simp)]
  apply le_of_eq
  have h1 : ((N : ℝ≥0∞) + 1) ≠ 0 := by simp
  have h2 : ((N : ℝ≥0∞) + 1) ≠ ∞ := by simp
  push_cast
  rw [mul_add, ← mul_assoc, one_div, ENNReal.inv_mul_cancel h1 h2, one_mul, ENNReal.div_eq_inv_mul]

section seq_hash_impl

variable {GF : BundledGFunctors} [conerisGS GF] [r1 : rand_spec GF] (L : r1.randG GF)
variable [hv1 : hash_view GF] (L' : hv1.hvG GF) [HinG' : abstract_tapesGS GF]
variable (val_size : ℕ)

/-- Helper (Rocq: `Hforall2` in `coll_free_hash_presample`): all the tape elements are bounded. -/
theorem rand_tapes_bigSepM_valid (tape_m : val_map (List ℕ)) :
    ([∗map] α ↦ t ∈ tape_m, r1.rand_tapes L α (val_size, t)) ⊢
      ([∗map] α ↦ t ∈ tape_m, r1.rand_tapes L α (val_size, t)) ∗
        ⌜∀ x ∈ tape_m_elements tape_m, x ≤ val_size⌝ := by
  refine (BigSepM.bigSepM_mono (M := val_map)
    (Ψ := fun α t => iprop(r1.rand_tapes L α (val_size, t) ∗ ⌜∀ n ∈ t, n ≤ val_size⌝))
    fun {α t} _ => persistent_entails_left (wand_entails (r1.rand_tapes_valid L α val_size t))).trans ?_
  rw [BigSepM.bigSepM_sep_eq]
  refine sep_mono_right (BigSepM.bigSepM_pure_intro.trans (pure_mono ?_))
  intro hall x hx
  unfold tape_m_elements at hx
  obtain ⟨l, hl, hxl⟩ := List.mem_flatten.mp hx
  obtain ⟨⟨a, t⟩, hp, rfl⟩ := List.mem_map.mp hl
  exact hall a t (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hp) x hxl

/-- Rocq: `coll_free_hash_presample`. Not the most general. Theoretically, you can even choose
how to distribute the residue error. -/
theorem coll_free_hash_presample (f : val) (m : hmap) (tape_m : val_map (List ℕ)) (γ1 : GName)
    (γ2 : hv1.hv_name) (α : val) (E : CoPset) (ε : ℝ≥0∞) (ns : List ℕ) :
    ⊢ coll_free_hashfun L L' val_size f m tape_m γ1 γ2 -∗
      hash_tape val_size α ns γ1 -∗
      ↯ (((m.toList.length + (tape_m_elements tape_m).length : ℕ) : ℝ≥0∞) /
          ((val_size + 1 : ℕ) : ℝ≥0∞)) -∗
      ↯ ε -∗
      state_update E E iprop(∃ (n : ℕ),
        ↯ ((((val_size + 1 : ℕ) : ℝ≥0∞) /
            ((val_size + 1 - (m.toList.length + (tape_m_elements tape_m).length) : ℕ) : ℝ≥0∞)) *
            ε) ∗
        hash_tape val_size α (ns ++ [n]) γ1 ∗
        coll_free_hashfun L L' val_size f m (tape_m.insert α (ns ++ [n])) γ1 γ2) := by
  unfold coll_free_hashfun hashfun hash_tape
  iintro ⟨⟨%hm, %Hf, Hmap, %Hforall, Hauth, Htapes⟩, Hview, %Hnd⟩ Hfrag Herr1 Herr2
  ihave %Hineq := ErrorCredit.valid $$ Herr1
  ihave %Hlookup := abstract_tapes_agree _ _ _ _ _ $$ Hauth Hfrag
  have Hlk := tapes_lookup_of_map tape_m α val_size val_size ns Hlookup
  ihave ⟨Htapes, %Hforall2⟩ := rand_tapes_bigSepM_valid L val_size tape_m $$ Htapes
  ihave ⟨Htape, Htapes2⟩ := (BigSepM.bigSepM_insert_acc (M := val_map)
    (Φ := fun α t => r1.rand_tapes L α (val_size, t)) Hlk) $$ Htapes
  ihave Herr := ErrorCredit.combine $$ [Herr1 Herr2]
  · iframe
  -- the list of used hash values
  let bad := tape_m_elements tape_m ++ m.toList.map (fun p => p.2)
  have hlen : m.toList.length + (tape_m_elements tape_m).length = bad.length := by
    simp only [bad, List.length_append, List.length_map]; omega
  have hb : ∀ x ∈ bad, x ≤ val_size := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact Hforall2 x hx
    · obtain ⟨⟨k, v⟩, hp, rfl⟩ := List.mem_map.mp hx
      exact (Hforall k v (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hp)).2
  have hlt : bad.length < val_size + 1 := by
    rw [← hlen]
    have h1 : ((val_size + 1 : ℕ) : ℝ≥0∞) ≠ 0 := by simp
    rw [ENNReal.div_lt_iff (Or.inl h1) (Or.inl (by simp)), one_mul] at Hineq
    exact_mod_cast Hineq
  rw [hlen]
  imod r1.rand_tapes_presample L E α val_size ns _
    (presample_err val_size bad
      ((((val_size + 1 : ℕ) : ℝ≥0∞) / ((val_size + 1 - bad.length : ℕ) : ℝ≥0∞)) * ε))
    (presample_err_sum val_size bad Hnd hb hlt ε) $$ Htape Herr with ⟨%n, Herr, Htape⟩
  by_cases hn : (n : ℕ) ∈ bad
  · unfold presample_err
    simp only [hn, ite_true]
    iexfalso
    iapply ErrorCredit.contradict le_rfl $$ Herr
  unfold presample_err
  simp only [hn, ite_false]
  imod abstract_tapes_presample γ1 _ α val_size ns n $$ Hauth Hfrag with ⟨Hauth, Hfrag⟩
  ihave Htapes := Htapes2 $$ %(ns ++ [(n : ℕ)]) Htape
  imodintro
  iexists n
  iframe Herr Hfrag Hview
  simp only [val_map_insert_eq]
  rw [tapes_map_insert]
  isplitl
  · iexists hm
    iframe Hmap Hauth Htapes
    ipureintro
    exact ⟨Hf, Hforall⟩
  ipureintro
  -- `NoDup` of the new used values
  have hperm : (tape_m_elements (tape_m.insert α (ns ++ [(n : ℕ)])) ++
      m.toList.map (fun p => p.2)).Perm ((n : ℕ) :: bad) := by
    have h1 := tape_m_elements_insert tape_m α (ns ++ [(n : ℕ)])
    have h2 := tape_m_elements_lookup tape_m α ns Hlk
    refine (h1.append_right _).trans ?_
    simp only [bad]
    refine List.Perm.trans ?_ (List.Perm.cons _ (h2.append_right _)).symm
    simp only [List.append_assoc, List.singleton_append]
    exact List.perm_middle
  exact hperm.nodup_iff.mpr (List.nodup_cons.mpr ⟨hn, Hnd⟩)

end seq_hash_impl

end Coneris.Examples.HashDir.SeqHashImpl
