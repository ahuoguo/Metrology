module

public import Metrology.Foxtrot.Examples.Algebraic

/-!
# Algebraic theory (part 4: the parallel steps of `eq3`)

Ported from clutch/theories/foxtrot/examples/algebraic.v (section `eq3`).

## Rocq → Lean map
* `eq3_step_par_tapes`: the third step of `eq3_1` / fourth step of `eq3_2` (tapes introduced
  on the RHS of a parallel composition, `tp_par` + `wp_par` + `wp_couple_rand_rand_lbl`).
* `eq3_step_untape`: the fourth step of `eq3_1` / fifth step of `eq3_2` (the LHS tapes are
  presampled against the RHS `rand`s with `pupd_couple_tape_rand`, then `wp_par`).
* Rocq's `do 9 tp_pure j` is `iterate 9 tp_pure j`.
-/

@[expose] public section

noncomputable section

open Iris Iris.BI Iris.Std Iris.ProofMode OFE COFE ConProbLang ConProbLang.con_prob_lang
open Foxtrot.BinaryRel Foxtrot.Lib.Toss Foxtrot.Lib.Par

namespace Foxtrot.Examples.Algebraic

section eq3

/-- The third step of `eq3_1` (fourth of `eq3_2`). -/
theorem eq3_step_par_tapes (e1 e2 e3 : expr) (τ : type) (X Y a b : ℕ)
    (H1 : ∅ ⊢ₜ e1 : τ) (H2 : ∅ ⊢ₜ e2 : τ) (H3 : ∅ ⊢ₜ e3 : τ) :
    ∅ ⊨ cpl(let (x, y) := (rand(#X) ‖ rand(#Y));
            if x < #a then &e1 else if y < #b then &e2 else &e3) ≤ctx≤
      cpl(let (α, β) := (alloc(#X), alloc(#Y));
          let (x, y) := (rand(α) #X ‖ rand(β) #Y);
          if x < #a then &e1 else if y < #b then &e2 else &e3) : τ := by
  apply refines_sound spawnFoxtrotRSigma
  intro _ Δ
  ihave H1 := refines_typed τ Δ e1 H1
  ihave H2 := refines_typed τ Δ e2 H2
  ihave H3 := refines_typed τ Δ e3 H3
  unfold_rel
  iintro %K %j Hspec
  tp_allocnattape j β as Hβ
  tp_allocnattape j α as Hα
  iterate 9 tp_pure j
  wp_pures
  tp_bind j cpl(rand(#lbl(α)) #X ‖ rand(#lbl(β)) #Y)
  imod tp_par j _ _ _ ⊤ $$ Hspec with ⟨%j1, %j2, %K1, %K2, Hspec1, Hspec2, Hcont⟩
  wp_bind cpl(&par v(λ _, rand(#X)) v(λ _, rand(#Y)))
  iapply wp_par
    (fun v => iprop(∃ n : ℕ, ⌜v = LitV (LitInt (n : ℤ))⌝ ∗ j1 ⤇ fill K1 (Val v)))
    (fun v => iprop(∃ n : ℕ, ⌜v = LitV (LitInt (n : ℤ))⌝ ∗ j2 ⤇ fill K2 (Val v)))
    $$ [Hspec1 Hα] [Hspec2 Hβ]
  · wp_apply (wp_couple_rand_rand_lbl X _root_.id Function.bijective_id X _ α j1
      (Int.toNat_natCast _).symm (fun n hn => hn)) $$ [Hα Hspec1] with %n ⟨-, Hspec1, %Hn⟩
    · iframe Hα Hspec1
    simp only [id_eq]
    iexists n
    iframe Hspec1
    ipureintro
    rfl
  · wp_apply (wp_couple_rand_rand_lbl Y _root_.id Function.bijective_id Y _ β j2
      (Int.toNat_natCast _).symm (fun n hn => hn)) $$ [Hβ Hspec2] with %n ⟨-, Hspec2, %Hn⟩
    · iframe Hβ Hspec2
    simp only [id_eq]
    iexists n
    iframe Hspec2
    ipureintro
    rfl
  iintro %v1 %v2 ⟨⟨%n1, %Hv1, Hspec1⟩, ⟨%n2, %Hv2, Hspec2⟩⟩
  subst Hv1 Hv2
  inext
  wp_pures
  imod Hcont $$ [Hspec1 Hspec2] with Hspec
  · iframe Hspec1 Hspec2
  tp_pures j
  solve_subst
  case_bool_decide <;> wp_pures <;> tp_pures j
  · iapply H1 $$ Hspec
  · case_bool_decide <;> wp_pures <;> tp_pures j
    · iapply H2 $$ Hspec
    · iapply H3 $$ Hspec

/-- The fourth step of `eq3_1` (fifth of `eq3_2`). -/
theorem eq3_step_untape (e1 e2 e3 : expr) (τ : type) (X Y a b : ℕ)
    (H1 : ∅ ⊢ₜ e1 : τ) (H2 : ∅ ⊢ₜ e2 : τ) (H3 : ∅ ⊢ₜ e3 : τ) :
    ∅ ⊨ cpl(let (α, β) := (alloc(#X), alloc(#Y));
            let (x, y) := (rand(α) #X ‖ rand(β) #Y);
            if x < #a then &e1 else if y < #b then &e2 else &e3) ≤ctx≤
      toss a X e1 (toss b Y e2 e3) : τ := by
  apply refines_sound spawnFoxtrotRSigma
  intro _ Δ
  ihave H1 := refines_typed τ Δ e1 H1
  ihave H2 := refines_typed τ Δ e2 H2
  ihave H3 := refines_typed τ Δ e3 H3
  unfold_rel
  iintro %K %j Hspec
  wp_alloctape β as Hβ
  wp_alloctape α as Hα
  wp_pures
  unfold toss
  tp_bind j (Rand _ _)
  imod pupd_couple_tape_rand X _root_.id Function.bijective_id _ ⊤ α X [] j
    (Int.toNat_natCast _).symm (fun n hn => hn) $$ Hα Hspec with ⟨%n, Hα, Hspec, %Hn⟩
  simp only [id_eq, List.nil_append]
  tp_pures j
  solve_subst
  case_bool_decide as Hna
  · tp_pures j
    wp_bind cpl(&par v(λ _, rand(#lbl(α)) #X) v(λ _, rand(#lbl(β)) #Y))
    iapply wp_par (fun v => iprop(⌜v = LitV (LitInt (n : ℤ))⌝)) (fun _ => iprop(True))
      $$ [Hα] [Hβ]
    · wp_randtape
      ipureintro
      rfl
    · imod pupd_presample Y ⊤ [] β $$ Hβ with ⟨%m, Hβ, %Hm⟩
      simp only [List.nil_append]
      wp_randtape
      itrivial
    iintro %v1 %v2 ⟨%Hv1, -⟩
    subst Hv1
    inext
    wp_pures
    solve_subst
    case_bool_decide <;> try omega
    wp_pures
    iapply H1 $$ Hspec
  · tp_pures j
    tp_bind j (Rand _ _)
    imod pupd_couple_tape_rand Y _root_.id Function.bijective_id _ ⊤ β Y [] j
      (Int.toNat_natCast _).symm (fun n hn => hn) $$ Hβ Hspec with ⟨%n', Hβ, Hspec, %Hn'⟩
    simp only [id_eq, List.nil_append]
    tp_pures j
    wp_bind cpl(&par v(λ _, rand(#lbl(α)) #X) v(λ _, rand(#lbl(β)) #Y))
    iapply wp_par (fun v => iprop(⌜v = LitV (LitInt (n : ℤ))⌝))
      (fun v => iprop(⌜v = LitV (LitInt (n' : ℤ))⌝)) $$ [Hα] [Hβ]
    · wp_randtape
      ipureintro
      rfl
    · wp_randtape
      ipureintro
      rfl
    iintro %v1 %v2 ⟨%Hv1, %Hv2⟩
    subst Hv1 Hv2
    inext
    wp_pures
    solve_subst
    rw [decide_eq_false Hna]
    wp_pures
    case_bool_decide <;> tp_pures j <;> wp_pures
    all_goals first
      | iapply H2 $$ Hspec
      | iapply H3 $$ Hspec

end eq3

end Foxtrot.Examples.Algebraic
