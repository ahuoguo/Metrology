module

public import Metrology.Foxtrot.Examples.AlgebraicEq3Steps
public import Metrology.Foxtrot.Examples.AlgebraicEq3Assoc
public import Metrology.Foxtrot.Examples.AlgebraicEq3Par

/-!
# Algebraic theory (part 5: `eq3`)

Ported from clutch/theories/foxtrot/examples/algebraic.v (section `eq3`).

## Rocq → Lean map
* `eq3_1`, `eq3_2`, `eq3`: same names; the section variables (including `Hineq`, `Hineq'`)
  are explicit arguments.
* `eq3_step_toss_toss`: the last step of `eq3_2` (after `subst; start H1 H2 H3`), with the Rocq
  case split `decide (r>0 /\ 0<((q+1)*(s+1))-p*r)` turned into a hypothesis with three cases
  (`r = 0`; `p = q+1 ∧ r = s+1`; the main case, with the factors `k`, `k'` given to
  `wp_toss_simplify`).
* `eq3_arith`: the arithmetic of that step (Rocq: the long `Nat.*` rewriting chains and `lia`).
* The Rocq `remember`s are `generalize`s.
-/

@[expose] public section

noncomputable section

open Iris Iris.BI Iris.Std Iris.ProofMode OFE COFE ConProbLang ConProbLang.con_prob_lang
open Foxtrot.BinaryRel Foxtrot.Lib.Toss

namespace Foxtrot.Examples.Algebraic

section eq3

/-- The last step of the Rocq proof of `eq3_2` (after `subst; start H1 H2 H3`), for abstract
bounds `A B C D` satisfying one of the three cases of the Rocq case analysis
`decide (r > 0 ∧ 0 < (q+1)*(s+1) - p*r)`: `r = 0`, the degenerate case `p = q + 1 ∧ r = s + 1`
(both tosses always pick `e1`) and the main case (handled by `wp_toss_simplify`, twice). -/
theorem eq3_step_toss_toss (e1 e2 e3 : expr) (τ : type) (A B C D p q r s : ℕ)
    (H1 : ∅ ⊢ₜ e1 : τ) (H2 : ∅ ⊢ₜ e2 : τ) (H3 : ∅ ⊢ₜ e3 : τ)
    (H : (r = 0 ∧ A = 0) ∨ (A = B + 1 ∧ C = D + 1 ∧ r = s + 1 ∧ p = q + 1) ∨
      (∃ k k', 0 < k ∧ 0 < k' ∧ B = (s + 1) * k - 1 ∧ A = k * r ∧
        D = (q + 1) * k' - 1 ∧ C = k' * p)) :
    ∅ ⊨ toss A B (toss C D e1 e2) e3 ≤ctx≤ toss r s (toss p q e1 e2) e3 : τ := by
  apply refines_sound foxtrotSigma
  intro _ Δ
  ihave H1 := refines_typed τ Δ e1 H1
  ihave H2 := refines_typed τ Δ e2 H2
  ihave H3 := refines_typed τ Δ e3 H3
  unfold_rel
  iintro %K %j Hspec
  rcases H with ⟨rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨k, k', Hk, Hk', HB, HA, HD, HC⟩
  · unfold toss
    wp_apply (wp_rand B B (Int.toNat_natCast _).symm) with %n %Hn
    · itrivial
    tp_bind j (Rand _ _)
    imod pupd_rand j _ s s ⊤ (Int.toNat_natCast _).symm $$ Hspec with ⟨%m, Hspec, %Hm⟩
    tp_pures j
    wp_pures
    case_bool_decide <;> try omega
    case_bool_decide <;> try omega
    tp_pures j
    wp_pures
    iapply H3 $$ Hspec
  · unfold toss
    wp_apply (wp_rand B B (Int.toNat_natCast _).symm) with %n %Hn
    · itrivial
    tp_bind j (Rand _ _)
    imod pupd_rand j _ s s ⊤ (Int.toNat_natCast _).symm $$ Hspec with ⟨%m, Hspec, %Hm⟩
    tp_pures j
    wp_pures
    case_bool_decide <;> try omega
    case_bool_decide <;> try omega
    tp_pures j
    wp_pures
    wp_apply (wp_rand D D (Int.toNat_natCast _).symm) with %n' %Hn'
    · itrivial
    tp_bind j (Rand _ _)
    imod pupd_rand j _ q q ⊤ (Int.toNat_natCast _).symm $$ Hspec with ⟨%m', Hspec, %Hm'⟩
    tp_pures j
    wp_pures
    case_bool_decide <;> try omega
    case_bool_decide <;> try omega
    tp_pures j
    wp_pures
    iapply H1 $$ Hspec
  · wp_apply (wp_toss_simplify r s k A B (toss C D e1 e2) e3 (toss p q e1 e2) e3 j K ⊤ _
      Hk HB HA) $$ [] [] Hspec
    · imodintro
      iintro Hspec
      wp_apply (wp_toss_simplify p q k' C D e1 e2 e1 e2 j K ⊤ _ Hk' HD HC) $$ [] [] Hspec
      · imodintro
        iintro Hspec
        iapply H1 $$ Hspec
      · imodintro
        iintro Hspec
        iapply H2 $$ Hspec
      · iintro %v Hv
        iexact Hv
    · imodintro
      iintro Hspec
      iapply H3 $$ Hspec
    · iintro %v Hv
      iexact Hv

/-- The arithmetic of the last step of the Rocq proof of `eq3_2` (the Rocq `lia`/`Nat.*`
rewriting chains): the bounds produced by the `remember`ed chain of refinements fall in one of
the three cases of `eq3_step_toss_toss`. -/
theorem eq3_arith (p q r s s' p' q' r' p'' r'' q1 p1 r1 s1 : ℕ) (Hpq : p ≤ q + 1)
    (Hrs : r ≤ s + 1)
    (hs' : (q + 1) * (s + 1) - p * r - 1 = s') (hp' : p * r = p')
    (hq' : (q + 1) * (s + 1) - 1 = q') (hr' : r * (q + 1 - p) = r')
    (hp'' : q' + 1 - p' = p'') (hr'' : s' + 1 - r' = r'')
    (hq1 : (q' + 1) * (s' + 1) - p'' * r'' - 1 = q1) (hp1 : p'' * (s' + 1 - r'') = p1)
    (hr1 : p'' * r'' = r1) (hs1 : (q' + 1) * (s' + 1) - 1 = s1) :
    (r = 0 ∧ s1 + 1 - r1 = 0) ∨
    (s1 + 1 - r1 = s1 + 1 ∧ q1 + 1 - p1 = q1 + 1 ∧ r = s + 1 ∧ p = q + 1) ∨
    (∃ k k', 0 < k ∧ 0 < k' ∧ s1 = (s + 1) * k - 1 ∧ s1 + 1 - r1 = k * r ∧
      q1 = (q + 1) * k' - 1 ∧ q1 + 1 - p1 = k' * p) := by
  subst hp'
  have hPN : p * r ≤ (q + 1) * (s + 1) := Nat.mul_le_mul Hpq Hrs
  have hQr : (q + 1) * r ≤ (q + 1) * (s + 1) := Nat.mul_le_mul_left _ Hrs
  have hPQr : p * r ≤ (q + 1) * r := Nat.mul_le_mul_right _ Hpq
  have hr'e : r' = (q + 1) * r - p * r := by
    rw [← hr', Nat.mul_sub, Nat.mul_comm r (q + 1), Nat.mul_comm r p]
  have hN1 : 1 ≤ (q + 1) * (s + 1) := Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
  generalize hN : (q + 1) * (s + 1) = N at *
  generalize hQr' : (q + 1) * r = Qr at *
  generalize hP : p * r = P at *
  have hq'1 : q' + 1 = N := by omega
  rw [hq'1] at hq1 hs1
  by_cases hr0 : r = 0
  · left
    subst hr0
    have hP0 : P = 0 := by rw [← hP, Nat.mul_zero]
    have hs'1 : s' + 1 = N := by omega
    have hr''N : r'' = N := by omega
    have hp''N : p'' = N := by omega
    rw [hs'1] at hs1
    rw [hr''N, hp''N] at hr1
    have : 1 ≤ N * N := Nat.mul_pos hN1 hN1
    exact ⟨rfl, by omega⟩
  by_cases hM : N - P = 0
  · right; left
    have hPN' : P = N := by omega
    have hpq : p = q + 1 := by
      by_contra h
      have : p * r < (q + 1) * r :=
        Nat.mul_lt_mul_of_pos_right (by omega) (Nat.pos_of_ne_zero hr0)
      omega
    have hrs : r = s + 1 := by
      by_contra h
      have : (q + 1) * r < (q + 1) * (s + 1) :=
        Nat.mul_lt_mul_of_pos_left (by omega) (Nat.succ_pos _)
      omega
    have hs'0 : s' + 1 = 1 := by omega
    have hr''1 : r'' = 1 := by omega
    have hp''0 : p'' = 0 := by omega
    rw [hs'0] at hs1 hq1 hp1
    rw [hp''0] at hr1 hq1 hp1
    simp only [Nat.mul_one, Nat.zero_mul] at hs1 hq1 hp1 hr1
    exact ⟨by omega, by omega, hrs, hpq⟩
  · right; right
    generalize hMd : N - P = M at *
    have hMpos : 0 < M := Nat.pos_of_ne_zero hM
    have hs'1 : s' + 1 = M := by omega
    have hp''M : p'' = M := by omega
    have hr''e : r'' = N - Qr := by omega
    rw [hs'1] at hs1 hq1 hp1
    rw [hp''M, hr''e] at hr1 hq1 hp1
    have f1 : M * (N - Qr) + M * Qr = N * M := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hQr, Nat.mul_comm]
    have f2 : M * (M - (N - Qr)) + M * P = M * Qr := by
      rw [← Nat.mul_add, show M - (N - Qr) + P = Qr by omega]
    have f3 : 1 ≤ N * M := Nat.mul_pos hN1 hMpos
    have f4 : N * M = (s + 1) * ((q + 1) * M) := by rw [← hN]; ring
    have f5 : M * Qr = (q + 1) * M * r := by rw [← hQr']; ring
    have f6 : M * Qr = (q + 1) * (r * M) := by rw [← hQr']; ring
    have f7 : M * P = r * M * p := by rw [← hP]; ring
    have f8 : 1 ≤ M * Qr := by
      rw [← hQr']
      exact Nat.mul_pos hMpos (Nat.mul_pos (Nat.succ_pos _) (Nat.pos_of_ne_zero hr0))
    refine ⟨(q + 1) * M, r * M, Nat.mul_pos (Nat.succ_pos _) hMpos,
      Nat.mul_pos (Nat.pos_of_ne_zero hr0) hMpos, ?_, ?_, ?_, ?_⟩
    all_goals
      generalize N * M = a1 at *
      generalize M * (N - Qr) = a2 at *
      generalize M * Qr = a3 at *
      generalize M * (M - (N - Qr)) = a4 at *
      generalize M * P = a5 at *
      generalize (s + 1) * ((q + 1) * M) = a6 at *
      generalize (q + 1) * M * r = a7 at *
      generalize (q + 1) * (r * M) = a8 at *
      generalize r * M * p = a9 at *
      omega

variable (e1 e2 e3 : expr) (τ : type) (p q r s : ℕ) (Hineq : p ≤ q + 1) (Hineq' : r ≤ s + 1)

include Hineq Hineq' in
/-- Rocq: `eq3_1`. -/
theorem eq3_1 (H1 : ∅ ⊢ₜ e1 : τ) (H2 : ∅ ⊢ₜ e2 : τ) (H3 : ∅ ⊢ₜ e3 : τ) :
    ∅ ⊨ toss r s (toss p q e1 e2) e3 ≤ctx≤
      toss (p * r) ((q + 1) * (s + 1) - 1) e1
        (toss (r * (q + 1 - p)) ((q + 1) * (s + 1) - p * r - 1) e2 e3) : τ :=
  ctx_refines_transitive _ _ _ _ _ (eq3_step_tapes e1 e2 e3 τ p q r s H1 H2 H3) <|
  ctx_refines_transitive _ _ _ _ _
    (eq3_step_assoc e1 e2 e3 τ p q r s _ _ _ _ Hineq Hineq' rfl rfl rfl rfl H1 H2 H3) <|
  ctx_refines_transitive _ _ _ _ _ (eq3_step_par_tapes e1 e2 e3 τ _ _ _ _ H1 H2 H3)
    (eq3_step_untape e1 e2 e3 τ _ _ _ _ H1 H2 H3)

include Hineq Hineq' in
/-- Rocq: `eq3_2`. -/
theorem eq3_2 (H1 : ∅ ⊢ₜ e1 : τ) (H2 : ∅ ⊢ₜ e2 : τ) (H3 : ∅ ⊢ₜ e3 : τ) :
    ∅ ⊨ toss (p * r) ((q + 1) * (s + 1) - 1) e1
        (toss (r * (q + 1 - p)) ((q + 1) * (s + 1) - p * r - 1) e2 e3) ≤ctx≤
      toss r s (toss p q e1 e2) e3 : τ := by
  generalize hs' : (q + 1) * (s + 1) - p * r - 1 = s'
  generalize hp' : p * r = p'
  generalize hq' : (q + 1) * (s + 1) - 1 = q'
  generalize hr' : r * (q + 1 - p) = r'
  refine ctx_refines_transitive _ _ _ _ _ (eq3_step_flip e1 e2 e3 τ p' q' r' s' H1 H2 H3) ?_
  generalize hp'' : q' + 1 - p' = p''
  generalize hr'' : s' + 1 - r' = r''
  refine ctx_refines_transitive _ _ _ _ _
    (eq3_step_tapes e3 e2 e1 τ r'' s' p'' q' H3 H2 H1) ?_
  refine ctx_refines_transitive _ _ _ _ _
    (eq3_step_assoc e3 e2 e1 τ r'' s' p'' q' ((q' + 1) * (s' + 1) - 1)
      ((q' + 1) * (s' + 1) - p'' * r'' - 1) (p'' * r'') (p'' * (s' + 1 - r''))
      (by omega) (by omega) (by rw [Nat.mul_comm]) (by rw [Nat.mul_comm, Nat.mul_comm p''])
      (Nat.mul_comm _ _) rfl H3 H2 H1) ?_
  refine ctx_refines_transitive _ _ _ _ _ (eq3_step_par_tapes e3 e2 e1 τ _ _ _ _ H3 H2 H1) ?_
  refine ctx_refines_transitive _ _ _ _ _ (eq3_step_untape e3 e2 e1 τ _ _ _ _ H3 H2 H1) ?_
  generalize hq1 : (q' + 1) * (s' + 1) - p'' * r'' - 1 = q1
  generalize hp1 : p'' * (s' + 1 - r'') = p1
  generalize hr1 : p'' * r'' = r1
  generalize hs1 : (q' + 1) * (s' + 1) - 1 = s1
  refine ctx_refines_transitive _ _ _ _ _ (eq3_step_flip e3 e2 e1 τ r1 s1 p1 q1 H3 H2 H1) ?_
  exact eq3_step_toss_toss e1 e2 e3 τ _ _ _ _ p q r s H1 H2 H3
    (eq3_arith p q r s s' p' q' r' p'' r'' q1 p1 r1 s1 Hineq Hineq' hs' hp' hq' hr' hp'' hr''
      hq1 hp1 hr1 hs1)

include Hineq Hineq' in
/-- Rocq: `eq3`. -/
theorem eq3 (H1 : ∅ ⊢ₜ e1 : τ) (H2 : ∅ ⊢ₜ e2 : τ) (H3 : ∅ ⊢ₜ e3 : τ) :
    ∅ ⊨ toss r s (toss p q e1 e2) e3 =ctx=
      toss (p * r) ((q + 1) * (s + 1) - 1) e1
        (toss (r * (q + 1 - p)) ((q + 1) * (s + 1) - p * r - 1) e2 e3) : τ :=
  ⟨eq3_1 e1 e2 e3 τ p q r s Hineq Hineq' H1 H2 H3,
    eq3_2 e1 e2 e3 τ p q r s Hineq Hineq' H1 H2 H3⟩

end eq3

end Foxtrot.Examples.Algebraic
