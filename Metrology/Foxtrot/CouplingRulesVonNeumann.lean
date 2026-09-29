module

public import Metrology.Foxtrot.CouplingRules

/-!
# Coupling rules of Foxtrot: the von Neumann coin lemmas

Ported from clutch/theories/foxtrot/coupling_rules.v (lines 1619–2967).

## Rocq → Lean map
* `pupd_couple_von_neumann_1 l1 l2 α β ns ns' j K E` ↦ `pupd_couple_von_neumann_1` (same
  argument order; `{N}` implicit, as in Rocq). The hypotheses are named
  `Hl1 Hl2 Hnodup Hlen Hlen' Hpos` as in the Rocq `iIntros`.
* `pupd_couple_von_neumann_2 l1 l2 α ns j K j' K' E ε` ↦ `pupd_couple_von_neumann_2`
  (hypotheses `Hl1 Hl2 Hnodup Hlen Hlen' Hlen'' _Hpos`).
* Rocq's inline constructions ↦ local helpers:
  - the bijection `f : fin (S N) * fin (S N) → fin (S (S N * S N - 1))` obtained from
    `finite_bijective` ↦ `vn_enc` (`vn_X N = (N + 1) * (N + 1) - 1`, `vn_X_succ`);
  - `fragmented_f'` / `fragmented_f_alt` + `nat_to_fin` ↦ `vn_pt` (`vn_pt_val`, `vn_nat`);
  - `fragmented_f` ↦ `vn_g` (`vn_g_inj`, `vn_g_bound`, `vn_enc_symm_g`, `vn_g_iff`);
  - `f_decompose` (= `f_inv f_decompose'`) ↦ `vn_D` (`vn_D_one`, `vn_D_zero`, `vn_D_bij`,
    `vn_dunifP_D`);
  - the `elem_of_app` / `NoDup_app` reasoning ↦ `vn_mem_l1`, `vn_mem_l2`, `vn_not_mem_l1`;
  - the LHS double state step of `von_neumann_1` ↦ `vn1_upd`, `vn1_lhs`;
  - the RHS scheduler of `von_neumann_1` (sample a number in `[0, S N * S N)`, step `j` iff it
    is one of the `2 * length l1` accepted values, otherwise stutter) ↦ `vn1_osch`,
    `vn_sample_stutter_lim_exec`, `vn1_ρb`, `vn1_acc`, `vn1_rej`, `vn1_osch_lim_exec`;
  - the RHS of `von_neumann_2` (two `rand #N` steps of `j` and `j'`, via `two_step_osch` of
    `Foxtrot.CouplingRules`) ↦ `vn2_ρ1`, `vn2_ρ2`, `vn2_G`, `vn2_osch_lim_exec`, `vn2_G_inj`,
    `vn2_G_lookup`;
  - the final `ec_eq` computation of `von_neumann_2` ↦ `vn2_err_eq` (via `frag_err_eq`).

## Design choices / deviations
* `Forall (λ x, x.1 <= N /\ x.2 <= N) l` is `∀ x ∈ l, x.1 ≤ N ∧ x.2 ≤ N`; `NoDup` is
  `List.Nodup`; `(2 * length l1 <= S N * S N)%nat` is `2 * l1.length ≤ (N + 1) * (N + 1)`.
* `if bool_decide ((x,y) ∈ l1) then .. else ..` is the (classically decided)
  `if (x, y) ∈ l1 then .. else ..`.
* `rand #1` / `rand #N` is `Rand (Val (LitV (LitInt 1))) (Val (LitV LitUnit))` (resp.
  `LitInt (N : ℤ)`); `#x` for `x : nat` is `Val (LitV (LitInt (x : ℤ)))`.
* Errors are `ℝ≥0∞`. The amplified error
  `((N+1)*(N+1))%nat / ((N+1)*(N+1) - 2 * length l1)%nat * ε` keeps Rocq's shape: both the
  numerator and the denominator are natural numbers cast to `ℝ≥0∞`, and the subtraction is
  the (truncated) `ℕ` subtraction as in Rocq. `Hlen'' : 2 * l1.length < (N + 1) * (N + 1)`
  makes the denominator positive, so the `x / 0 = ∞` convention never applies.
* Rocq's `nnreal_minus ε_now ε'` is the truncated `εnow - ε`, used only under
  `ε ≤ εnow` (from `ErrorCredit.supply_bound`), and `ε_now + ε' * 2 * length l1 / (S N * S N -
  2 * length l1)` is `εnow + δ` with
  `δ = ε * (2 * L - 1 + 1 : ℕ) / (vn_X N - (2 * L - 1) : ℕ)` (`L = length l1`; the same value,
  since `0 < L` and `2 * L < (N + 1) * (N + 1)`). The bound `Rmax ε_now1 ε_now2` is
  `max (εnow - ε) (εnow + δ)`.
* The hypothesis `(ε > 0)%R` of `pupd_couple_von_neumann_2` is kept (as `_Hpos : 0 < ε`)
  for fidelity, although, as in Rocq, the proof does not use it.
* The couplings are proved by rewriting both sides into `dbind` / `dmap` of uniform
  distributions (`dunifP_decompose`, `ARcoupl_dbind'`, `ARcoupl_map`, `ARcoupl_eq`,
  `ARcoupl_dret`), with the coupling relations stated up front, instead of Rocq's
  `instantiate`d relations and `SeriesC` manipulations.
* The Rocq `Local Opaque INR` / `Local Transparent INR` directives have no counterpart.

## Omitted
Nothing: lines 1619–2967 contain only these two lemmas (no commented-out lemmas).
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang

namespace Foxtrot

set_option quotPrecheck false in
/-- The state type of `con_lang_mdp con_prob_lang` (reducibly `cfg`). -/
local notation "CPState" => (con_lang_mdp con_prob_lang).mdpstate

/-! ## Local helpers (not in Rocq) -/

section vn_helpers

/-- Helper: `(N + 1) * (N + 1) - 1` (Rocq: `S N * S N - 1`). -/
abbrev vn_X (N : ℕ) : ℕ := (N + 1) * (N + 1) - 1

theorem vn_X_succ (N : ℕ) : vn_X N + 1 = (N + 1) * (N + 1) := by
  have : 0 < (N + 1) * (N + 1) := Nat.mul_pos (by omega) (by omega)
  unfold vn_X
  omega

/-- Helper (Rocq: the bijection `f : fin (S N) * fin (S N) → fin (S (S N * S N - 1))` obtained
from `finite_bijective`). -/
def vn_enc (N : ℕ) : Fin (N + 1) × Fin (N + 1) ≃ Fin (vn_X N + 1) :=
  finProdFinEquiv.trans (finCongr (vn_X_succ N).symm)

/-- Helper: the pair of naturals underlying a pair of `Fin`s. -/
def vn_nat {N : ℕ} (p : Fin (N + 1) × Fin (N + 1)) : ℕ × ℕ := ((p.1 : ℕ), (p.2 : ℕ))

/-- Helper (Rocq: `fragmented_f'` / `fragmented_f_alt` followed by `nat_to_fin`): the `m`-th
element of `l`, as a pair of `Fin`s (clamped, so that no bound hypothesis is needed). -/
def vn_pt (N : ℕ) (l : List (ℕ × ℕ)) (m : ℕ) : Fin (N + 1) × Fin (N + 1) :=
  if h : m < l.length then
    (⟨min l[m].1 N, by omega⟩, ⟨min l[m].2 N, by omega⟩)
  else (0, 0)

theorem vn_pt_val (N : ℕ) (l : List (ℕ × ℕ)) (Hb : ∀ x ∈ l, x.1 ≤ N ∧ x.2 ≤ N) (m : ℕ)
    (h : m < l.length) : vn_nat (vn_pt N l m) = l[m] := by
  have := Hb l[m] (List.getElem_mem h)
  simp only [vn_nat, vn_pt, h, ↓reduceDIte]
  exact Prod.ext (by simp only; omega) (by simp only; omega)

/-- Helper (Rocq: `fragmented_f`): the injection of `[0, length l)` into `[0, (N+1)^2)` along
the elements of `l`, extended injectively to all of `ℕ`. -/
def vn_g (N : ℕ) (l : List (ℕ × ℕ)) (m : ℕ) : ℕ :=
  if m < l.length then (vn_enc N (vn_pt N l m) : ℕ) else m + (vn_X N + 1)

theorem vn_g_inj (N : ℕ) (l : List (ℕ × ℕ)) (Hb : ∀ x ∈ l, x.1 ≤ N ∧ x.2 ≤ N)
    (Hnd : l.Nodup) : Function.Injective (vn_g N l) := by
  intro m m' h
  unfold vn_g at h
  by_cases hm : m < l.length <;> by_cases hm' : m' < l.length <;>
    simp only [hm, hm', ↓reduceIte] at h
  · have h1 := (vn_enc N).injective (Fin.ext h)
    have h2 := congrArg vn_nat h1
    rw [vn_pt_val N l Hb m hm, vn_pt_val N l Hb m' hm'] at h2
    exact (List.Nodup.getElem_inj_iff Hnd).1 h2
  · have := (vn_enc N (vn_pt N l m)).isLt
    omega
  · have := (vn_enc N (vn_pt N l m')).isLt
    omega
  · omega

theorem vn_g_bound (N : ℕ) (l : List (ℕ × ℕ)) (M : ℕ) (hM : M + 1 = l.length) :
    ∀ m, m < M + 1 → vn_g N l m < vn_X N + 1 := by
  intro m hm
  have hm' : m < l.length := by omega
  simp only [vn_g, hm', ↓reduceIte]
  exact Fin.isLt _

theorem vn_enc_symm_g (N : ℕ) (l : List (ℕ × ℕ)) (m : ℕ) (hm : m < l.length)
    (h : vn_g N l m < vn_X N + 1) :
    (vn_enc N).symm ⟨vn_g N l m, h⟩ = vn_pt N l m := by
  rw [Equiv.symm_apply_eq]
  apply Fin.ext
  simp only [vn_g, hm, ↓reduceIte]

theorem vn_g_iff (N : ℕ) (l : List (ℕ × ℕ)) (Hb : ∀ x ∈ l, x.1 ≤ N ∧ x.2 ≤ N) (M : ℕ)
    (hM : M + 1 = l.length) (k : Fin (vn_X N + 1)) :
    (∃ m : Fin (M + 1), vn_g N l m = (k : ℕ)) ↔ vn_nat ((vn_enc N).symm k) ∈ l := by
  constructor
  · rintro ⟨m, hm⟩
    have hml : (m : ℕ) < l.length := by omega
    have hk : k = ⟨vn_g N l m, vn_g_bound N l M hM m m.isLt⟩ := Fin.ext hm.symm
    rw [hk, vn_enc_symm_g N l m hml, vn_pt_val N l Hb m hml]
    exact List.getElem_mem hml
  · intro hmem
    obtain ⟨i, hi, hieq⟩ := List.getElem_of_mem hmem
    refine ⟨⟨i, by omega⟩, ?_⟩
    have hpt : vn_pt N l i = (vn_enc N).symm k := by
      have h1 := vn_pt_val N l Hb i hi
      rw [hieq] at h1
      exact Prod.ext (Fin.ext (congrArg Prod.fst h1)) (Fin.ext (congrArg Prod.snd h1))
    simp only [vn_g, hi, ↓reduceIte, hpt, Equiv.apply_symm_apply]

/-- Helper (Rocq: `f_decompose` = `f_inv f_decompose'`): the bijection
`[0,1] × [0, L) → [0, 2L)`, `(1, i) ↦ i`, `(0, i) ↦ L + i`. -/
def vn_D (L : ℕ) (p : Fin 2 × Fin (L - 1 + 1)) : Fin (2 * L - 1 + 1) :=
  if p.1 = 1 then ⟨p.2, by have := p.2.isLt; omega⟩
  else ⟨L + p.2, by have := p.2.isLt; omega⟩

theorem vn_D_one (L : ℕ) (i : Fin (L - 1 + 1)) : ((vn_D L (1, i) : Fin _) : ℕ) = i := by
  simp [vn_D]

theorem vn_D_zero (L : ℕ) (i : Fin (L - 1 + 1)) : ((vn_D L (0, i) : Fin _) : ℕ) = L + i := by
  simp [vn_D]

theorem vn_D_bij (L : ℕ) (hL : 0 < L) : Function.Bijective (vn_D L) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, by simp only [Fintype.card_prod, Fintype.card_fin]; omega⟩
  rintro ⟨b, i⟩ ⟨b', i'⟩ h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  have hi' := i'.isLt
  fin_cases b <;> fin_cases b' <;> simp [vn_D] at hv <;>
    first | omega | exact Prod.ext rfl (Fin.ext hv)

theorem vn_dunifP_D (L : ℕ) (hL : 0 < L) :
    dunifP (2 * L - 1) =
      (dunifP 1 ≫= fun b => dmap (fun i => vn_D L (b, i)) (dunifP (L - 1))) :=
  dunifP_decompose 1 (L - 1) (2 * L - 1) (vn_D L) (vn_D_bij L hL) (by omega)

theorem vn_mem_l1 (N : ℕ) (l1 l2 : List (ℕ × ℕ)) (Hb : ∀ x ∈ l1 ++ l2, x.1 ≤ N ∧ x.2 ≤ N)
    (Hlen : l1.length = l2.length) (i : Fin (l1.length - 1 + 1)) (hL : 0 < l1.length) :
    vn_nat (vn_pt N (l1 ++ l2) (vn_D l1.length (1, i))) ∈ l1 := by
  have hi : (i : ℕ) < l1.length := by have := i.isLt; omega
  rw [vn_D_one, vn_pt_val N _ Hb _ (by simp; omega), List.getElem_append_left hi]
  exact List.getElem_mem hi

theorem vn_mem_l2 (N : ℕ) (l1 l2 : List (ℕ × ℕ)) (Hb : ∀ x ∈ l1 ++ l2, x.1 ≤ N ∧ x.2 ≤ N)
    (Hlen : l1.length = l2.length) (i : Fin (l1.length - 1 + 1)) (hL : 0 < l1.length) :
    vn_nat (vn_pt N (l1 ++ l2) (vn_D l1.length (0, i))) ∈ l2 := by
  have hi : (i : ℕ) < l2.length := by have := i.isLt; omega
  rw [vn_D_zero, vn_pt_val N _ Hb _ (by simp; omega),
    List.getElem_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  exact List.getElem_mem hi

theorem vn_not_mem_l1 (l1 l2 : List (ℕ × ℕ)) (Hnd : (l1 ++ l2).Nodup) (x : ℕ × ℕ)
    (h : x ∈ l2) : x ∉ l1 :=
  fun h' => List.disjoint_of_nodup_append Hnd h' h

/-! ### Helpers for `pupd_couple_von_neumann_1` -/

/-- Helper: the state after appending `p.1` to `α`'s tape and `p.2` to `β`'s tape. -/
def vn1_upd (σ : state) (α β : Loc) (N : ℕ) (fs fs' : List (Fin (N + 1)))
    (p : Fin (N + 1) × Fin (N + 1)) : state :=
  state_upd_tapes (·.insert β ⟨N, fs' ++ [p.2]⟩)
    (state_upd_tapes (·.insert α ⟨N, fs ++ [p.1]⟩) σ)

/-- Helper (Rocq: inline in `pupd_couple_von_neumann_1`): presampling on `α` and then on `β`
is a uniform sample of `[0, (N+1)^2)`, decoded as a pair. -/
theorem vn1_lhs (σ : state) (α β : Loc) (N : ℕ) (fs fs' : List (Fin (N + 1)))
    (H : σ.tapes[α]? = some ⟨N, fs⟩) (H' : σ.tapes[β]? = some ⟨N, fs'⟩) (hne : α ≠ β) :
    (con_prob_lang.state_step σ α ≫= fun σ' => con_prob_lang.state_step σ' β) =
      dmap (fun k => vn1_upd σ α β N fs fs' ((vn_enc N).symm k)) (dunifP (vn_X N)) := by
  rw [dunifP_decompose N N (vn_X N) (vn_enc N) (vn_enc N).bijective rfl, dmap_dbind]
  rw [state_step_unfold σ α N fs H, dmap, ← dbind_assoc]
  refine dbind_ext_right _ _ _ fun a => ?_
  rw [dret_id_left]
  have H'' : (state_upd_tapes (·.insert α ⟨N, fs ++ [a]⟩) σ).tapes[β]? = some ⟨N, fs'⟩ := by
    rw [state_upd_tapes_tapes, map_getElem?_insert_ne _ _ _ _ hne, H']
  rw [state_step_unfold _ β N fs' H'', dmap_comp]
  congr 1
  funext c
  simp [vn1_upd]

/-- Helper: the limit execution of the scheduler that samples a thread id `h a` (with `a ∼ μ`)
out of bounds, records it with a stutter step, and stops. -/
theorem vn_sample_stutter_lim_exec {A : Type} [Countable A] (μ : Distr A) (h : A → ℕ)
    (ρ : CPState) (hlen : ∀ a, ρ.1.length ≤ h a) :
    osch_lim_exec (full_info_cons_osch (fun _ => dmap h μ)
        (fun _ => full_info_inhabitant)).fi_osch ([], ρ) =
      dmap (fun a => (([(cfg_to_cfg' ρ, h a)] : full_info_state), ρ)) μ := by
  rw [full_info_cons_osch_lim_exec, dmap]
  refine (dbind_assoc (β := ℕ) _ _ _).symm.trans ?_
  rw [dmap]
  refine dbind_ext_right _ _ _ fun a => ?_
  refine (dret_id_left (α := ℕ) _ _).trans ?_
  rw [out_of_bounds_step' _ _ (hlen a)]
  refine (dret_id_left (α := CPState) _ _).trans ?_
  have := full_info_lift_osch_lim_exec [(cfg_to_cfg' ρ, h a)] full_info_inhabitant [] ρ
  simp only [List.append_nil] at this
  refine this.trans ?_
  rw [full_info_inhabitant_lim_exec, dmap_dret]
  rfl

open Classical in
/-- Helper (Rocq: the scheduler inline in `pupd_couple_von_neumann_1`). It samples
`k ∈ [0, (N+1)^2)`; if `k` is in the image of `vn_g N l` on `[0, M]` it steps thread `j` and
then records a sample `i ∈ [0, L)` with a stutter step on thread `len + i`; otherwise it records
`k` with a stutter step on thread `len + k`. -/
def vn1_osch (N : ℕ) (l : List (ℕ × ℕ)) (M L j len : ℕ) : full_info_oscheduler :=
  full_info_cons_osch
    (fun _ => dmap (fun k : Fin (vn_X N + 1) =>
      if ∃ m : Fin (M + 1), vn_g N l m = (k : ℕ) then j else len + (k : ℕ)) (dunifP (vn_X N)))
    (fun x => if x = j then
        full_info_cons_osch (fun _ => dmap (fun i : Fin (L - 1 + 1) => len + (i : ℕ))
          (dunifP (L - 1))) (fun _ => full_info_inhabitant)
      else full_info_inhabitant)

/-- Helper: the RHS configuration after thread `j` sampled `b`. -/
def vn1_ρb (ρ : CPState) (j : ℕ) (K : List ectx_item) (b : Fin 2) : CPState :=
  ((ρ.1.set j (fill K (Val (LitV (LitInt ((b : ℕ) : ℤ))))), ρ.2) : CPState)

/-- Helper: an accepted outcome of `vn1_osch`. -/
def vn1_acc (L : ℕ) (ρ : CPState) (j : ℕ) (K : List ectx_item) (b : Fin 2)
    (i : Fin (L - 1 + 1)) : full_info_state × CPState :=
  ([(cfg_to_cfg' ρ, j), (cfg_to_cfg' (vn1_ρb ρ j K b), ρ.1.length + (i : ℕ))], vn1_ρb ρ j K b)

/-- Helper: a rejected outcome of `vn1_osch`. -/
def vn1_rej (ρ : CPState) (k : ℕ) : full_info_state × CPState :=
  ([(cfg_to_cfg' ρ, ρ.1.length + k)], ρ)

open Classical in
/-- Helper: the limit execution of `vn1_osch`. -/
theorem vn1_osch_lim_exec (N : ℕ) (l : List (ℕ × ℕ)) (M L j : ℕ) (K : List ectx_item)
    (ρ : CPState)
    (Hsome : ρ.1[j]? = some (fill K (Rand (Val (LitV (LitInt 1))) (Val (LitV LitUnit))))) :
    osch_lim_exec (vn1_osch N l M L j ρ.1.length).fi_osch ([], ρ) =
      dunifP (vn_X N) ≫= fun k : Fin (vn_X N + 1) =>
        if ∃ m : Fin (M + 1), vn_g N l m = (k : ℕ) then
          (dunifP 1 ≫= fun b => dmap (vn1_acc L ρ j K b) (dunifP (L - 1)))
        else dret (vn1_rej ρ k) := by
  have Hj : j < ρ.1.length := (List.getElem?_eq_some_iff.1 Hsome).1
  unfold vn1_osch
  rw [full_info_cons_osch_lim_exec, dmap]
  refine (dbind_assoc (β := ℕ) _ _ _).symm.trans ?_
  refine dbind_ext_right _ _ _ fun k => ?_
  refine (dret_id_left (α := ℕ) _ _).trans ?_
  by_cases h : ∃ m : Fin (M + 1), vn_g N l m = (k : ℕ)
  · simp only [h, ↓reduceIte]
    rw [step'_fill_rand j ρ K 1 Hsome, dmap]
    refine (dbind_assoc (β := CPState) _ _ _).symm.trans ?_
    refine dbind_ext_right _ _ _ fun b => ?_
    refine (dret_id_left (α := CPState) _ _).trans ?_
    have := full_info_lift_osch_lim_exec [(cfg_to_cfg' ρ, j)]
      (full_info_cons_osch (fun _ => dmap (fun i : Fin (L - 1 + 1) => ρ.1.length + (i : ℕ))
          (dunifP (L - 1))) (fun _ => full_info_inhabitant)) [] (vn1_ρb ρ j K b)
    simp only [List.append_nil] at this
    refine this.trans ?_
    rw [vn_sample_stutter_lim_exec _ _ _ (fun i => by simp [vn1_ρb]), dmap_comp]
    rfl
  · simp only [h, ↓reduceIte]
    rw [out_of_bounds_step' _ _ (Nat.le_add_right _ _)]
    refine (dret_id_left (α := CPState) _ _).trans ?_
    have hne : ¬ (ρ.1.length + (k : ℕ) = j) := by omega
    simp only [hne, ↓reduceIte]
    have := full_info_lift_osch_lim_exec [(cfg_to_cfg' ρ, ρ.1.length + (k : ℕ))]
      full_info_inhabitant [] ρ
    simp only [List.append_nil] at this
    refine this.trans ?_
    rw [full_info_inhabitant_lim_exec, dmap_dret]
    rfl

/-! ### Helpers for `pupd_couple_von_neumann_2` -/

/-- Helper: the RHS configuration after thread `j` sampled `n`. -/
def vn2_ρ1 (ρ : CPState) (j : ℕ) (K : List ectx_item) (n : ℕ) : CPState :=
  ((ρ.1.set j (fill K (Val (LitV (LitInt (n : ℤ))))), ρ.2) : CPState)

/-- Helper: the RHS configuration after thread `j` sampled `n` and thread `j'` sampled `m`. -/
def vn2_ρ2 (ρ : CPState) (j : ℕ) (K : List ectx_item) (j' : ℕ) (K' : List ectx_item)
    (n m : ℕ) : CPState :=
  (((ρ.1.set j (fill K (Val (LitV (LitInt (n : ℤ)))))).set j'
    (fill K' (Val (LitV (LitInt (m : ℤ))))), ρ.2) : CPState)

/-- Helper: the outcome of `two_step_osch j j'` on two `rand #N`s for the encoded pair `k`. -/
def vn2_G (N : ℕ) (ρ : CPState) (j : ℕ) (K : List ectx_item) (j' : ℕ) (K' : List ectx_item)
    (k : Fin (vn_X N + 1)) : full_info_state × CPState :=
  ([(cfg_to_cfg' ρ, j), (cfg_to_cfg' (vn2_ρ1 ρ j K ((vn_enc N).symm k).1), j'),
    (cfg_to_cfg' (vn2_ρ2 ρ j K j' K' ((vn_enc N).symm k).1 ((vn_enc N).symm k).2),
      (vn2_ρ2 ρ j K j' K' ((vn_enc N).symm k).1 ((vn_enc N).symm k).2).1.length)],
    vn2_ρ2 ρ j K j' K' ((vn_enc N).symm k).1 ((vn_enc N).symm k).2)

/-- Helper (Rocq: inline in `pupd_couple_von_neumann_2`): the limit execution of
`two_step_osch j j'` on two `rand #N`s, as a uniform sample of `[0, (N+1)^2)`. -/
theorem vn2_osch_lim_exec (N : ℕ) (j j' : ℕ) (K K' : List ectx_item) (ρ : CPState)
    (hne : j ≠ j')
    (Hsome : ρ.1[j]? = some (fill K (Rand (Val (LitV (LitInt (N : ℤ)))) (Val (LitV LitUnit)))))
    (Hsome' : ρ.1[j']? = some (fill K' (Rand (Val (LitV (LitInt (N : ℤ)))) (Val (LitV LitUnit))))) :
    osch_lim_exec (two_step_osch j j').fi_osch ([], ρ) =
      dmap (vn2_G N ρ j K j' K') (dunifP (vn_X N)) := by
  rw [two_step_osch_lim_exec j j' K K' N N ρ hne Hsome Hsome',
    dunifP_decompose N N (vn_X N) (vn_enc N) (vn_enc N).bijective rfl, dmap_dbind]
  refine dbind_ext_right _ _ _ fun n => ?_
  rw [dmap_comp]
  congr 1
  funext m
  simp only [Function.comp, vn2_G, vn2_ρ1, vn2_ρ2, Equiv.symm_apply_apply, List.length_set]
  rfl

/-- Helper: the histories of `vn2_G` determine the encoded pair. -/
theorem vn2_G_inj (N : ℕ) (ρ : CPState) (j : ℕ) (K : List ectx_item) (j' : ℕ)
    (K' : List ectx_item) (Hj : j < ρ.1.length) (Hj' : j' < ρ.1.length)
    (k1 k2 : Fin (vn_X N + 1))
    (h : (vn2_G N ρ j K j' K' k1).1 = (vn2_G N ρ j K j' K' k2).1) : k1 = k2 := by
  have ha := congrArg (fun L : full_info_state => (L[1]?).map (fun q => q.1.1[j]?)) h
  simp only [vn2_G, vn2_ρ1, cfg_to_cfg', List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.map_some, List.getElem?_set_self Hj, Option.some.injEq] at ha
  have hb := congrArg (fun L : full_info_state => (L[2]?).map (fun q => q.1.1[j']?)) h
  have Hj'' : ∀ n : ℕ, j' < (ρ.1.set j (fill K (Val (LitV (LitInt (n : ℤ)))))).length :=
    fun _ => by simp only [List.length_set]; exact Hj'
  simp only [vn2_G, vn2_ρ2, cfg_to_cfg', List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.map_some, List.getElem?_set_self (Hj'' _), Option.some.injEq] at hb
  have h1 := fill_lit_nat_inj K ha
  have h2 := fill_lit_nat_inj K' hb
  exact (vn_enc N).symm.injective (Prod.ext (Fin.ext h1) (Fin.ext h2))

/-- Helper: reading the pair sampled by threads `j` and `j'` back from a `vn2_G` outcome. -/
theorem vn2_G_lookup (N : ℕ) (ρ : CPState) (j : ℕ) (K : List ectx_item) (j' : ℕ)
    (K' : List ectx_item) (Hj : j < ρ.1.length) (Hj' : j' < ρ.1.length) (hne : j ≠ j')
    (k : Fin (vn_X N + 1)) :
    (vn2_G N ρ j K j' K' k).2.1[j]? =
        some (fill K (Val (LitV (LitInt ((((vn_enc N).symm k).1 : ℕ) : ℤ))))) ∧
      (vn2_G N ρ j K j' K' k).2.1[j']? =
        some (fill K' (Val (LitV (LitInt ((((vn_enc N).symm k).2 : ℕ) : ℤ))))) := by
  have Hj'' : j' < (ρ.1.set j (fill K (Val (LitV (LitInt
      ((((vn_enc N).symm k).1 : ℕ) : ℤ)))))).length := by
    simp only [List.length_set]; exact Hj'
  simp only [vn2_G, vn2_ρ2]
  exact ⟨by rw [List.getElem?_set_ne (Ne.symm hne), List.getElem?_set_self Hj],
    List.getElem?_set_self Hj''⟩

/-- Helper (Rocq: the final `ec_eq` computation of `pupd_couple_von_neumann_2`). -/
theorem vn2_err_eq (N L : ℕ) (hL : 0 < L) (Hlen : 2 * L < (N + 1) * (N + 1)) (ε : ℝ≥0∞) :
    ε + ε * ((2 * L - 1 + 1 : ℕ) : ℝ≥0∞) / ((vn_X N - (2 * L - 1) : ℕ) : ℝ≥0∞) =
      (((N + 1) * (N + 1) : ℕ) : ℝ≥0∞) / (((N + 1) * (N + 1) - 2 * L : ℕ) : ℝ≥0∞) * ε := by
  have Hineq : 2 * L - 1 < vn_X N := by unfold vn_X; omega
  rw [frag_err_eq (vn_X N) (2 * L - 1) Hineq ε, vn_X_succ N, ← ENNReal.natCast_sub]
  congr 3
  omega

end vn_helpers

/-! ## The von Neumann coin lemmas -/

section rules

variable {GF : BundledGFunctors} [foxtrotGS GF]

/-- Rocq: `pupd_couple_von_neumann_1`. Presampling a pair `(x, y)` on the tapes `α` and `β`,
coupled with the RHS `rand #1`: pairs in `l1` make the RHS return `1`, pairs in `l2` make it
return `0`, and other pairs leave the RHS untouched. -/
theorem pupd_couple_von_neumann_1 {N : ℕ} (l1 l2 : List (ℕ × ℕ)) (α β : Loc)
    (ns ns' : List ℕ) (j : ℕ) (K : List ectx_item) (E : CoPset)
    (Hl1 : ∀ x ∈ l1, x.1 ≤ N ∧ x.2 ≤ N) (Hl2 : ∀ x ∈ l2, x.1 ≤ N ∧ x.2 ≤ N)
    (Hnodup : (l1 ++ l2).Nodup) (Hlen : l1.length = l2.length) (Hlen' : 0 < l1.length)
    (Hpos : 2 * l1.length ≤ (N + 1) * (N + 1)) :
    ▷ α ↪N (N; ns) ⊢@{IProp GF} ▷ β ↪N (N; ns') -∗
      j ⤇ fill K (Rand (Val (LitV (LitInt 1))) (Val (LitV LitUnit))) -∗
      pupd E E iprop(∃ x y : ℕ, ⌜x ≤ N⌝ ∗ ⌜y ≤ N⌝ ∗ α ↪N (N; ns ++ [x]) ∗
        β ↪N (N; ns' ++ [y]) ∗
        (if (x, y) ∈ l1 then j ⤇ fill K (Val (LitV (LitInt 1)))
          else if (x, y) ∈ l2 then j ⤇ fill K (Val (LitV (LitInt 0)))
          else j ⤇ fill K (Rand (Val (LitV (LitInt 1))) (Val (LitV LitUnit))))) := by
  classical
  unfold pupd pupd_def
  simp only [foxtrotGS_state_interp_eq, foxtrotGS_spec_interp_eq, foxtrotGS_err_interp_eq]
  iintro Hα Hβ Hr %σ %⟨l, s'⟩ %εnow ⟨⟨Hh, Ht⟩, Hs, Hε⟩
  imod Hα
  imod Hβ
  iunfold nat_tape at Hα
  iunfold nat_tape at Hβ
  icases Hα with ⟨%fs, %Hfs, Hα⟩
  icases Hβ with ⟨%fs', %Hfs', Hβ⟩
  ihave %Hne := ghost_map_elem_ne _ _ _ _ _ _ $$ Hα Hβ
  unfold tapes_auth
  icombine Ht Hα gives %H
  icombine Ht Hβ gives %H'
  rw [ext_get?_eq] at H H'
  ihave %Hlookup := spec_auth_prog_agree l s' j _ $$ Hs Hr
  have Hj : j < l.length := (List.getElem?_eq_some_iff.1 Hlookup).1
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  have Hb : ∀ x ∈ l1 ++ l2, x.1 ≤ N ∧ x.2 ≤ N := fun x hx =>
    (List.mem_append.1 hx).elim (Hl1 x) (Hl2 x)
  have hM : 2 * l1.length - 1 + 1 = (l1 ++ l2).length := by
    rw [List.length_append]; omega
  let U : Fin (vn_X N + 1) → state := fun k => vn1_upd σ α β N fs fs' ((vn_enc N).symm k)
  let g' : Fin (2 * l1.length - 1 + 1) → Fin (vn_X N + 1) := fun m =>
    ⟨vn_g N (l1 ++ l2) m, vn_g_bound N _ _ hM m m.isLt⟩
  let S : state → full_info_state × CPState → Prop := fun σ' y =>
    (∃ b i, σ' = U (g' (vn_D l1.length (b, i))) ∧
      y = vn1_acc l1.length ((l, s') : CPState) j K b i) ∨
    (∃ k : Fin (vn_X N + 1),
      (¬ ∃ m : Fin (2 * l1.length - 1 + 1), vn_g N (l1 ++ l2) m = (k : ℕ)) ∧
      σ' = U k ∧ y = vn1_rej ((l, s') : CPState) k)
  have Hlim := vn1_osch_lim_exec N (l1 ++ l2) (2 * l1.length - 1) l1.length j K
    ((l, s') : CPState) Hlookup
  have Hμ := vn1_lhs σ α β N fs fs' H H' Hne
  have Hβσ : ∀ a : Fin (N + 1), (state_upd_tapes (·.insert α ⟨N, fs ++ [a]⟩) σ).tapes[β]? =
      some ⟨N, fs'⟩ := fun a => by
    rw [state_upd_tapes_tapes, map_getElem?_insert_ne _ _ _ _ Hne, H']
  iapply spec_coupl_rec σ ((l, s') : CPState) εnow _
  iexists S, (con_prob_lang.state_step σ α ≫= fun σ' => con_prob_lang.state_step σ' β),
    vn1_osch N (l1 ++ l2) (2 * l1.length - 1) l1.length j l.length, 0, (fun _ => εnow), εnow
  isplitr
  · ipureintro
    refine sch_erasable_dbind (Λ := con_prob_lang) tape_oblivious_sch _ _ σ
      (state_step_sch_erasable σ α _ H) fun σ' hσ' => ?_
    rw [state_step_unfold σ α N fs H, dmap_pos] at hσ'
    obtain ⟨a, rfl, -⟩ := hσ'
    exact state_step_sch_erasable _ β _ (Hβσ a)
  isplitr
  · ipureintro
    exact fun _ => le_rfl
  isplitr
  · ipureintro
    rw [zero_add, Expval_const]
    exact mul_le_of_le_one_right zero_le (pmf_SeriesC _)
  isplitr
  · ipureintro
    have HL : (con_prob_lang.state_step σ α ≫= fun σ' => con_prob_lang.state_step σ' β) =
        dunifP (vn_X N) ≫= fun k : Fin (vn_X N + 1) => dmap U
          (if ∃ m : Fin (2 * l1.length - 1 + 1), vn_g N (l1 ++ l2) m = (k : ℕ) then
            dmap g' (dunifP (2 * l1.length - 1)) else dret k) := by
      rw [Hμ]
      conv_lhs => rw [dunif_fragmented (vn_X N) (2 * l1.length - 1) (vn_g N (l1 ++ l2))
        (vn_g_inj N _ Hb Hnodup) (vn_g_bound N _ _ hM) (by rw [vn_X]; omega)]
      exact dmap_dbind _ _ _
    rw [HL]
    refine ARcoupl_mono _ _ _ _ _ _ _ _ (fun _ => rfl)
      (fun b => (congrArg (fun μ => μ b) Hlim).symm) (fun _ _ h => h) le_rfl ?_
    refine ARcoupl_dbind' 0 0 0 _ _ _ _ (· = ·) S (add_zero _).symm (fun k k' hk => ?_)
      (ARcoupl_eq _)
    subst hk
    by_cases h : ∃ m : Fin (2 * l1.length - 1 + 1), vn_g N (l1 ++ l2) m = (k : ℕ)
    · simp only [h, ↓reduceIte]
      rw [dmap_comp, vn_dunifP_D l1.length Hlen', dmap_dbind]
      refine ARcoupl_dbind' 0 0 0 _ _ _ _ (· = ·) S (add_zero _).symm (fun b b' hb => ?_)
        (ARcoupl_eq _)
      subst hb
      rw [dmap_comp]
      apply ARcoupl_map
      refine ARcoupl_mono _ _ _ _ _ _ _ _ (fun _ => rfl) (fun _ => rfl) ?_ le_rfl
        (ARcoupl_eq _)
      rintro i i' rfl
      exact Or.inl ⟨b, i, rfl, rfl⟩
    · simp only [h, ↓reduceIte, dmap_dret]
      exact ARcoupl_dret _ _ S _ (Or.inr ⟨k, h, rfl, rfl⟩)
  isplitr
  · ipureintro
    have key : ∀ {σ' : state} {L' : full_info_state} {y : CPState}, S σ' (L', y) →
        (∃ b i, σ' = U (g' (vn_D l1.length (b, i))) ∧
          L' = (vn1_acc l1.length ((l, s') : CPState) j K b i).1 ∧
          y = (vn1_acc l1.length ((l, s') : CPState) j K b i).2) ∨
        (∃ k : Fin (vn_X N + 1), σ' = U k ∧ L' = (vn1_rej ((l, s') : CPState) k).1 ∧
          y = (vn1_rej ((l, s') : CPState) k).2) := by
      rintro σ' L' y (⟨b, i, rfl, h⟩ | ⟨k, -, rfl, h⟩)
      · exact Or.inl ⟨b, i, rfl, congrArg Prod.fst h, congrArg Prod.snd h⟩
      · exact Or.inr ⟨k, rfl, congrArg Prod.fst h, congrArg Prod.snd h⟩
    rintro σx σy L' ρx ρy hx hy
    rcases key hx with ⟨b1, i1, rfl, hL1, hy1⟩ | ⟨k1, rfl, hL1, hy1⟩ <;>
      rcases key hy with ⟨b2, i2, rfl, hL2, hy2⟩ | ⟨k2, rfl, hL2, hy2⟩
    · have hb := congrArg (fun L : full_info_state => (L[1]?).map (fun q => q.1.1[j]?))
        (hL1.symm.trans hL2)
      simp only [vn1_acc, vn1_ρb, cfg_to_cfg', List.getElem?_cons_succ,
        List.getElem?_cons_zero, Option.map_some, List.getElem?_set_self Hj,
        Option.some.injEq] at hb
      have hbb : b1 = b2 := Fin.ext (fill_lit_nat_inj K hb)
      have hi := congrArg (fun L : full_info_state => (L[1]?).map Prod.snd)
        (hL1.symm.trans hL2)
      simp only [vn1_acc, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.map_some,
        Option.some.injEq, Nat.add_left_cancel_iff] at hi
      have hii : i1 = i2 := Fin.ext hi
      subst hbb hii
      exact ⟨rfl, hy1.trans hy2.symm⟩
    · have := congrArg List.length (hL1.symm.trans hL2)
      simp [vn1_acc, vn1_rej] at this
    · have := congrArg List.length (hL1.symm.trans hL2)
      simp [vn1_acc, vn1_rej] at this
    · have hk := congrArg (fun L : full_info_state => (L[0]?).map Prod.snd)
        (hL1.symm.trans hL2)
      simp only [vn1_rej, List.getElem?_cons_zero, Option.map_some, Option.some.injEq,
        Nat.add_left_cancel_iff] at hk
      have hkk : k1 = k2 := Fin.ext hk
      subst hkk
      exact ⟨rfl, hy1.trans hy2.symm⟩
  iintro %σ2 %L' %ρ' %HS
  rcases HS with ⟨b, i, rfl, h⟩ | ⟨k, hk, rfl, h⟩
  · -- accepted
    have hρ : ρ' = vn1_ρb ((l, s') : CPState) j K b := congrArg Prod.snd h
    subst hρ
    have hm : ((vn_D l1.length (b, i) : Fin _) : ℕ) < (l1 ++ l2).length := by
      have := (vn_D l1.length (b, i)).isLt
      omega
    obtain ⟨p, hp⟩ : ∃ p, p = vn_pt N (l1 ++ l2) (vn_D l1.length (b, i)) := ⟨_, rfl⟩
    have hU : U (g' (vn_D l1.length (b, i))) = vn1_upd σ α β N fs fs' p := by
      simp only [U, g']
      rw [vn_enc_symm_g N _ _ hm, hp]
    rw [hU]
    beta_reduce
    simp only [vn1_ρb]
    imod spec_update_prog l s' j _ (fill K (Val (LitV (LitInt ((b : ℕ) : ℤ))))) $$ Hs Hr
      with ⟨Hs, Hr⟩
    imod ghost_map_update (⟨N, fs ++ [p.1]⟩ : tape) $$ Ht Hα with ⟨Ht, Hα⟩
    rw [ext_insert_eq]
    imod ghost_map_update (⟨N, fs' ++ [p.2]⟩ : tape) $$ Ht Hβ with ⟨Ht, Hβ⟩
    rw [ext_insert_eq]
    imodintro
    iapply spec_coupl_ret_pair (vn1_upd σ α β N fs fs' p)
      (l.set j (fill K (Val (LitV (LitInt ((b : ℕ) : ℤ)))))) s' _ εnow
    imod Hclose
    imodintro
    simp only [vn1_upd, state_upd_tapes_heap', state_upd_tapes_tapes]
    iframe Hh Ht Hs Hε
    iexists (p.1 : ℕ), (p.2 : ℕ)
    isplitr
    · ipureintro
      exact Nat.lt_succ_iff.1 p.1.2
    isplitr
    · ipureintro
      exact Nat.lt_succ_iff.1 p.2.2
    isplitl [Hα]
    · iunfold nat_tape
      iexists fs ++ [p.1]
      iframe Hα
      ipureintro
      simp [Hfs]
    isplitl [Hβ]
    · iunfold nat_tape
      iexists fs' ++ [p.2]
      iframe Hβ
      ipureintro
      simp [Hfs']
    have hb01 : b = 0 ∨ b = 1 := by fin_cases b <;> simp
    rcases hb01 with rfl | rfl
    · have hmem2 : vn_nat p ∈ l2 := hp ▸ vn_mem_l2 N l1 l2 Hb Hlen i Hlen'
      have hmem1 : vn_nat p ∉ l1 := vn_not_mem_l1 l1 l2 Hnodup _ hmem2
      simp only [vn_nat] at hmem1 hmem2
      simp only [hmem1, hmem2, ↓reduceIte, Fin.val_zero, Nat.cast_zero]
      iexact Hr
    · have hmem1 : vn_nat p ∈ l1 := hp ▸ vn_mem_l1 N l1 l2 Hb Hlen i Hlen'
      simp only [vn_nat] at hmem1
      simp only [hmem1, ↓reduceIte, Fin.val_one, Nat.cast_one]
      iexact Hr
  · -- rejected
    have hρ : ρ' = ((l, s') : CPState) := congrArg Prod.snd h
    subst hρ
    have hnot : vn_nat ((vn_enc N).symm k) ∉ l1 ++ l2 := fun hmem =>
      hk ((vn_g_iff N _ Hb _ hM k).2 hmem)
    have hnot1 : vn_nat ((vn_enc N).symm k) ∉ l1 := fun h' => hnot (List.mem_append_left _ h')
    have hnot2 : vn_nat ((vn_enc N).symm k) ∉ l2 := fun h' => hnot (List.mem_append_right _ h')
    simp only [vn_nat] at hnot1 hnot2
    beta_reduce
    imod ghost_map_update (⟨N, fs ++ [((vn_enc N).symm k).1]⟩ : tape) $$ Ht Hα with ⟨Ht, Hα⟩
    rw [ext_insert_eq]
    imod ghost_map_update (⟨N, fs' ++ [((vn_enc N).symm k).2]⟩ : tape) $$ Ht Hβ with ⟨Ht, Hβ⟩
    rw [ext_insert_eq]
    imodintro
    iapply spec_coupl_ret_pair (U k) l s' _ εnow
    imod Hclose
    imodintro
    simp only [U, vn1_upd, state_upd_tapes_heap', state_upd_tapes_tapes]
    iframe Hh Ht Hs Hε
    iexists (((vn_enc N).symm k).1 : ℕ), (((vn_enc N).symm k).2 : ℕ)
    isplitr
    · ipureintro
      exact Nat.lt_succ_iff.1 ((vn_enc N).symm k).1.2
    isplitr
    · ipureintro
      exact Nat.lt_succ_iff.1 ((vn_enc N).symm k).2.2
    isplitl [Hα]
    · iunfold nat_tape
      iexists fs ++ [((vn_enc N).symm k).1]
      iframe Hα
      ipureintro
      simp [Hfs]
    isplitl [Hβ]
    · iunfold nat_tape
      iexists fs' ++ [((vn_enc N).symm k).2]
      iframe Hβ
      ipureintro
      simp [Hfs']
    simp only [hnot1, hnot2, ↓reduceIte]
    iexact Hr

/-- Rocq: `pupd_couple_von_neumann_2`. The RHS samples a pair `(x, y)` with two `rand #N`s,
coupled with presampling on the tape `α` of bound `1`: pairs in `l1` append `1` to `α`, pairs
in `l2` append `0`, and other pairs leave `α` untouched but amplify the error credits. -/
theorem pupd_couple_von_neumann_2 {N : ℕ} (l1 l2 : List (ℕ × ℕ)) (α : Loc) (ns : List ℕ)
    (j : ℕ) (K : List ectx_item) (j' : ℕ) (K' : List ectx_item) (E : CoPset) (ε : ℝ≥0∞)
    (Hl1 : ∀ x ∈ l1, x.1 ≤ N ∧ x.2 ≤ N) (Hl2 : ∀ x ∈ l2, x.1 ≤ N ∧ x.2 ≤ N)
    (Hnodup : (l1 ++ l2).Nodup) (Hlen : l1.length = l2.length) (Hlen' : 0 < l1.length)
    (Hlen'' : 2 * l1.length < (N + 1) * (N + 1)) (_Hpos : 0 < ε) :
    j ⤇ fill K (Rand (Val (LitV (LitInt (N : ℤ)))) (Val (LitV LitUnit))) ⊢@{IProp GF}
      j' ⤇ fill K' (Rand (Val (LitV (LitInt (N : ℤ)))) (Val (LitV LitUnit))) -∗
      ▷ α ↪N (1; ns) -∗ ↯ ε -∗
      pupd E E iprop(∃ x y : ℕ, ⌜x ≤ N⌝ ∗ ⌜y ≤ N⌝ ∗ j ⤇ fill K (Val (LitV (LitInt (x : ℤ)))) ∗
        j' ⤇ fill K' (Val (LitV (LitInt (y : ℤ)))) ∗
        (if (x, y) ∈ l1 then α ↪N (1; ns ++ [1])
          else if (x, y) ∈ l2 then α ↪N (1; ns ++ [0])
          else (α ↪N (1; ns)) ∗
            ↯ ((((N + 1) * (N + 1) : ℕ) : ℝ≥0∞) /
              (((N + 1) * (N + 1) - 2 * l1.length : ℕ) : ℝ≥0∞) * ε))) := by
  classical
  unfold pupd pupd_def
  simp only [foxtrotGS_state_interp_eq, foxtrotGS_spec_interp_eq, foxtrotGS_err_interp_eq]
  iintro Hr Hr' Hα Herr %σ %⟨l, s'⟩ %εnow ⟨⟨Hh, Ht⟩, Hs, Hε⟩
  imod Hα
  iunfold nat_tape at Hα
  icases Hα with ⟨%fs, %Hfs, Hα⟩
  unfold tapes_auth
  icombine Ht Hα gives %H
  rw [ext_get?_eq] at H
  ihave %Hlookup := spec_auth_prog_agree l s' j _ $$ Hs Hr
  ihave %Hlookup' := spec_auth_prog_agree l s' j' _ $$ Hs Hr'
  ihave %Hne := spec_prog_frag_ne j j' _ _ $$ Hr Hr'
  ihave %Hle := ErrorCredit.supply_bound $$ Hε Herr
  have Hjl : j < l.length := (List.getElem?_eq_some_iff.1 Hlookup).1
  have Hjl' : j' < l.length := (List.getElem?_eq_some_iff.1 Hlookup').1
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  have Hb : ∀ x ∈ l1 ++ l2, x.1 ≤ N ∧ x.2 ≤ N := fun x hx =>
    (List.mem_append.1 hx).elim (Hl1 x) (Hl2 x)
  have hM : 2 * l1.length - 1 + 1 = (l1 ++ l2).length := by
    rw [List.length_append]; omega
  have Hineq : 2 * l1.length - 1 < vn_X N := by unfold vn_X; omega
  let δ : ℝ≥0∞ := ε * ((2 * l1.length - 1 + 1 : ℕ) : ℝ≥0∞) /
    ((vn_X N - (2 * l1.length - 1) : ℕ) : ℝ≥0∞)
  let g' : Fin (2 * l1.length - 1 + 1) → Fin (vn_X N + 1) := fun m =>
    ⟨vn_g N (l1 ++ l2) m, vn_g_bound N _ _ hM m m.isLt⟩
  let G := vn2_G N ((l, s') : CPState) j K j' K'
  let upd : Fin 2 → state := fun b => state_upd_tapes (·.insert α ⟨1, fs ++ [b]⟩) σ
  let E2 : CPState → ℝ≥0∞ := fun ρ =>
    if ∃ m : Fin (2 * l1.length - 1 + 1),
        ρ.1[j]? = some (fill K (Val (LitV (LitInt
          ((((vn_pt N (l1 ++ l2) m).1 : ℕ) : ℤ)))))) ∧
        ρ.1[j']? = some (fill K' (Val (LitV (LitInt
          ((((vn_pt N (l1 ++ l2) m).2 : ℕ) : ℤ))))))
    then εnow - ε else εnow + δ
  have hE2 : ∀ k, E2 (G k).2 =
      if ∃ m : Fin (2 * l1.length - 1 + 1), vn_g N (l1 ++ l2) m = (k : ℕ)
      then εnow - ε else εnow + δ := by
    intro k
    obtain ⟨h1, h2⟩ := vn2_G_lookup N ((l, s') : CPState) j K j' K' Hjl Hjl' Hne k
    refine if_congr ?_ rfl rfl
    simp only [G, h1, h2, Option.some.injEq]
    constructor
    · rintro ⟨m, hm1, hm2⟩
      have hml : (m : ℕ) < (l1 ++ l2).length := by omega
      have hpt : vn_pt N (l1 ++ l2) m = (vn_enc N).symm k :=
        Prod.ext (Fin.ext (fill_lit_nat_inj K hm1).symm) (Fin.ext (fill_lit_nat_inj K' hm2).symm)
      refine ⟨m, ?_⟩
      simp only [vn_g, hml, ↓reduceIte, hpt, Equiv.apply_symm_apply]
    · rintro ⟨m, hm⟩
      have hml : (m : ℕ) < (l1 ++ l2).length := by omega
      have hk : k = g' m := Fin.ext hm.symm
      have hpt : (vn_enc N).symm k = vn_pt N (l1 ++ l2) m := by
        rw [hk]; exact vn_enc_symm_g N _ _ hml _
      exact ⟨m, by rw [hpt], by rw [hpt]⟩
  have Hlim : osch_lim_exec (two_step_osch j j').fi_osch ([], ((l, s') : CPState)) =
      dmap G (dunifP (vn_X N)) :=
    vn2_osch_lim_exec N j j' K K' ((l, s') : CPState) Hne Hlookup Hlookup'
  let S : state → full_info_state × CPState → Prop := fun σ' y =>
    (∃ b i, σ' = upd b ∧ y = G (g' (vn_D l1.length (b, i)))) ∨
    (∃ k : Fin (vn_X N + 1),
      (¬ ∃ m : Fin (2 * l1.length - 1 + 1), vn_g N (l1 ++ l2) m = (k : ℕ)) ∧
      σ' = σ ∧ y = G k)
  iapply spec_coupl_rec σ ((l, s') : CPState) εnow _
  iexists S, (dunifP (vn_X N) ≫= fun k : Fin (vn_X N + 1) =>
      if decide (∃ m : Fin (2 * l1.length - 1 + 1), vn_g N (l1 ++ l2) m = (k : ℕ))
      then con_prob_lang.state_step σ α else dret σ),
    two_step_osch j j', 0, (fun p => E2 p.2), max (εnow - ε) (εnow + δ)
  isplitr
  · ipureintro
    have H1 := state_step_sch_erasable σ α ⟨1, fs⟩ H
    have H2 := dret_sch_erasable (Λ := con_prob_lang) σ tape_oblivious_sch
    exact sch_erasable_dbind_predicate (Λ := con_prob_lang) tape_oblivious_sch (dunifP (vn_X N))
      (con_prob_lang.state_step σ α) (dret σ) σ
      (fun k : Fin (vn_X N + 1) =>
        decide (∃ m : Fin (2 * l1.length - 1 + 1), vn_g N (l1 ++ l2) m = (k : ℕ)))
      (dunifP_mass _) H1 H2
  isplitr
  · ipureintro
    intro y
    show E2 y.2 ≤ _
    simp only [E2]
    split
    · exact le_max_left _ _
    · exact le_max_right _ _
  isplitr
  · ipureintro
    rw [zero_add, Hlim, Expval_dmap]
    refine le_of_eq ?_
    unfold Expval
    rw [← frag_expval_calc (vn_X N) (2 * l1.length - 1) (vn_g N (l1 ++ l2))
      (vn_g_inj N _ Hb Hnodup) (vn_g_bound N _ _ hM) Hineq εnow ε Hle]
    exact tsum_congr fun k => congrArg _ (hE2 k)
  isplitr
  · ipureintro
    have HR : dmap G (dunifP (vn_X N)) = dunifP (vn_X N) ≫= fun k : Fin (vn_X N + 1) =>
        dmap G (if ∃ m : Fin (2 * l1.length - 1 + 1), vn_g N (l1 ++ l2) m = (k : ℕ) then
          dmap g' (dunifP (2 * l1.length - 1)) else dret k) := by
      conv_lhs => rw [dunif_fragmented (vn_X N) (2 * l1.length - 1) (vn_g N (l1 ++ l2))
        (vn_g_inj N _ Hb Hnodup) (vn_g_bound N _ _ hM) Hineq.le]
      exact dmap_dbind _ _ _
    refine ARcoupl_mono _ _ _ _ _ _ _ _ (fun _ => rfl)
      (fun b => (congrArg (fun μ => μ b) (Hlim.trans HR)).symm) (fun _ _ h => h) le_rfl ?_
    refine ARcoupl_dbind' 0 0 0 _ _ _ _ (· = ·) S (add_zero _).symm (fun k k' hk => ?_)
      (ARcoupl_eq _)
    subst hk
    by_cases h : ∃ m : Fin (2 * l1.length - 1 + 1), vn_g N (l1 ++ l2) m = (k : ℕ)
    · simp only [h, _root_.decide_true, ↓reduceIte]
      rw [state_step_unfold σ α 1 fs H, dmap_comp, vn_dunifP_D l1.length Hlen', dmap_dbind]
      refine ARcoupl_dbind' 0 0 0 (fun b => dret (upd b)) _ _ _ (· = ·) S (add_zero _).symm
        (fun b b' hb => ?_) (ARcoupl_eq _)
      subst hb
      rw [← dbind_const (dunifP (l1.length - 1)) (dret (upd b)) (dunifP_mass _), dmap_comp,
        dmap]
      refine ARcoupl_dbind' 0 0 0 _ _ _ _ (· = ·) S (add_zero _).symm (fun i i' hi => ?_)
        (ARcoupl_eq _)
      subst hi
      exact ARcoupl_dret _ _ S _ (Or.inl ⟨b, i, rfl, rfl⟩)
    · simp only [h, _root_.decide_false, Bool.false_eq_true, ↓reduceIte, dmap_dret]
      exact ARcoupl_dret _ _ S _ (Or.inr ⟨k, h, rfl, rfl⟩)
  isplitr
  · ipureintro
    have key : ∀ {σ' : state} {L' : full_info_state} {y : CPState}, S σ' (L', y) →
        ∃ k : Fin (vn_X N + 1), L' = (G k).1 ∧ y = (G k).2 ∧
          ((∃ b i, k = g' (vn_D l1.length (b, i)) ∧ σ' = upd b) ∨
            ((¬ ∃ m : Fin (2 * l1.length - 1 + 1), vn_g N (l1 ++ l2) m = (k : ℕ)) ∧
              σ' = σ)) := by
      rintro σ' L' y (⟨b, i, rfl, h⟩ | ⟨k, hk, rfl, h⟩)
      · exact ⟨_, congrArg Prod.fst h, congrArg Prod.snd h, Or.inl ⟨b, i, rfl, rfl⟩⟩
      · exact ⟨k, congrArg Prod.fst h, congrArg Prod.snd h, Or.inr ⟨hk, rfl⟩⟩
    rintro σx σy L' ρx ρy hx hy
    obtain ⟨k1, hL1, hy1, h1⟩ := key hx
    obtain ⟨k2, hL2, hy2, h2⟩ := key hy
    have hk := vn2_G_inj N ((l, s') : CPState) j K j' K' Hjl Hjl' k1 k2 (hL1.symm.trans hL2)
    subst hk
    refine ⟨?_, hy1.trans hy2.symm⟩
    rcases h1 with ⟨b1, i1, hk1, rfl⟩ | ⟨hn1, rfl⟩ <;>
      rcases h2 with ⟨b2, i2, hk2, rfl⟩ | ⟨hn2, rfl⟩
    · have hD := vn_g_inj N _ Hb Hnodup (congrArg Fin.val (hk1.symm.trans hk2))
      have := (vn_D_bij l1.length Hlen').1 (Fin.ext hD)
      rw [(Prod.mk.inj this).1]
    · exact absurd ⟨_, (congrArg Fin.val hk1).symm⟩ hn2
    · exact absurd ⟨_, (congrArg Fin.val hk2).symm⟩ hn1
    · rfl
  iintro %σ2 %L' %ρ' %HS
  rcases HS with ⟨b, i, rfl, h⟩ | ⟨k, hk, rfl, h⟩
  · -- accepted
    have hρ : ρ' = (G (g' (vn_D l1.length (b, i)))).2 := congrArg Prod.snd h
    subst hρ
    have hm : ((vn_D l1.length (b, i) : Fin _) : ℕ) < (l1 ++ l2).length := by
      have := (vn_D l1.length (b, i)).isLt
      omega
    have hX : E2 (G (g' (vn_D l1.length (b, i)))).2 = εnow - ε := by
      rw [hE2]
      simp only [show ∃ m : Fin (2 * l1.length - 1 + 1),
        vn_g N (l1 ++ l2) m = ((g' (vn_D l1.length (b, i)) : Fin _) : ℕ) from ⟨_, rfl⟩,
        ↓reduceIte]
    obtain ⟨p, hp⟩ : ∃ p, p = vn_pt N (l1 ++ l2) (vn_D l1.length (b, i)) := ⟨_, rfl⟩
    have hpk : (vn_enc N).symm (g' (vn_D l1.length (b, i))) = p := by
      rw [hp]; exact vn_enc_symm_g N _ _ hm _
    beta_reduce
    rw [hX]
    simp only [G, vn2_G, hpk, vn2_ρ2]
    imod spec_update_prog l s' j _ (fill K (Val (LitV (LitInt ((p.1 : ℕ) : ℤ))))) $$ Hs Hr
      with ⟨Hs, Hr⟩
    imod spec_update_prog (l.set j (fill K (Val (LitV (LitInt ((p.1 : ℕ) : ℤ)))))) s' j' _
      (fill K' (Val (LitV (LitInt ((p.2 : ℕ) : ℤ))))) $$ Hs Hr' with ⟨Hs, Hr'⟩
    imod ghost_map_update (⟨1, fs ++ [b]⟩ : tape) $$ Ht Hα with ⟨Ht, Hα⟩
    rw [ext_insert_eq]
    imod ErrorCredit.supply_decrease $$ Hε Herr with Hε
    imodintro
    iapply spec_coupl_ret_pair (upd b)
      ((l.set j (fill K (Val (LitV (LitInt ((p.1 : ℕ) : ℤ)))))).set j'
        (fill K' (Val (LitV (LitInt ((p.2 : ℕ) : ℤ)))))) s' _ (εnow - ε)
    imod Hclose
    imodintro
    simp only [upd, state_upd_tapes_heap', state_upd_tapes_tapes]
    iframe Hh Ht Hs Hε
    iexists (p.1 : ℕ), (p.2 : ℕ)
    isplitr
    · ipureintro
      exact Nat.lt_succ_iff.1 p.1.2
    isplitr
    · ipureintro
      exact Nat.lt_succ_iff.1 p.2.2
    iframe Hr Hr'
    have hb01 : b = 0 ∨ b = 1 := by fin_cases b <;> simp
    rcases hb01 with rfl | rfl
    · have hmem2 : vn_nat p ∈ l2 := hp ▸ vn_mem_l2 N l1 l2 Hb Hlen i Hlen'
      have hmem1 : vn_nat p ∉ l1 := vn_not_mem_l1 l1 l2 Hnodup _ hmem2
      simp only [vn_nat] at hmem1 hmem2
      simp only [hmem1, hmem2, ↓reduceIte]
      iunfold nat_tape
      iexists fs ++ [0]
      iframe Hα
      ipureintro
      simp [Hfs]
    · have hmem1 : vn_nat p ∈ l1 := hp ▸ vn_mem_l1 N l1 l2 Hb Hlen i Hlen'
      simp only [vn_nat] at hmem1
      simp only [hmem1, ↓reduceIte]
      iunfold nat_tape
      iexists fs ++ [1]
      iframe Hα
      ipureintro
      simp [Hfs]
  · -- rejected
    have hρ : ρ' = (G k).2 := congrArg Prod.snd h
    subst hρ
    have hX : E2 (G k).2 = εnow + δ := by
      rw [hE2]
      simp only [hk, ↓reduceIte]
    have hnot : vn_nat ((vn_enc N).symm k) ∉ l1 ++ l2 := fun hmem =>
      hk ((vn_g_iff N _ Hb _ hM k).2 hmem)
    have hnot1 : vn_nat ((vn_enc N).symm k) ∉ l1 := fun h' => hnot (List.mem_append_left _ h')
    have hnot2 : vn_nat ((vn_enc N).symm k) ∉ l2 := fun h' => hnot (List.mem_append_right _ h')
    simp only [vn_nat] at hnot1 hnot2
    obtain ⟨p, hp⟩ : ∃ p, p = (vn_enc N).symm k := ⟨_, rfl⟩
    rw [← hp] at hnot1 hnot2
    beta_reduce
    rw [hX]
    simp only [G, vn2_G, ← hp, vn2_ρ2]
    imod spec_update_prog l s' j _ (fill K (Val (LitV (LitInt ((p.1 : ℕ) : ℤ))))) $$ Hs Hr
      with ⟨Hs, Hr⟩
    imod spec_update_prog (l.set j (fill K (Val (LitV (LitInt ((p.1 : ℕ) : ℤ)))))) s' j' _
      (fill K' (Val (LitV (LitInt ((p.2 : ℕ) : ℤ))))) $$ Hs Hr' with ⟨Hs, Hr'⟩
    by_cases h1 : 1 ≤ εnow + δ
    · imodintro
      iapply spec_coupl_ret_err_ge_1 _
        (((l.set j (fill K (Val (LitV (LitInt ((p.1 : ℕ) : ℤ)))))).set j'
          (fill K' (Val (LitV (LitInt ((p.2 : ℕ) : ℤ))))), s') : CPState) _ _ h1
    imodintro
    iapply spec_coupl_ret_pair _
      ((l.set j (fill K (Val (LitV (LitInt ((p.1 : ℕ) : ℤ)))))).set j'
        (fill K' (Val (LitV (LitInt ((p.2 : ℕ) : ℤ)))))) s' _ (εnow + δ)
    imod ErrorCredit.supply_increase (ε₂ := δ) (lt_of_not_ge h1) $$ Hε with ⟨Hε, Hδ⟩
    icombine Herr Hδ as Herr
    imod Hclose
    imodintro
    iframe Hh Ht Hs Hε
    iexists (p.1 : ℕ), (p.2 : ℕ)
    isplitr
    · ipureintro
      exact Nat.lt_succ_iff.1 p.1.2
    isplitr
    · ipureintro
      exact Nat.lt_succ_iff.1 p.2.2
    iframe Hr Hr'
    simp only [hnot1, hnot2, ↓reduceIte]
    isplitl [Hα]
    · iunfold nat_tape
      iexists fs
      iframe Hα
      ipureintro
      exact Hfs
    · iapply ErrorCredit.ext (vn2_err_eq N l1.length Hlen' Hlen'' ε) $$ Herr

end rules

end Foxtrot
