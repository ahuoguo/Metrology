module

public import Metrology.Foxtrot.Examples.Algebraic

/-!
# Algebraic theory (part 3: the associativity step of `eq3`)

Ported from clutch/theories/foxtrot/examples/algebraic.v (section `eq3`).

## Rocq → Lean map
* `eq3_step_assoc`: the second `ctx_refines_transitive` step of `eq3_1` (and the third step of
  `eq3_2`, instantiated): two tape samplings against two parallel `rand`s, by
  `pupd_couple_associativity`. The bounds `X`, `Y`, `a`, `b` of the parallel program are
  parameters with defining equations, so that `eq3_2` can instantiate the lemma at its
  (commuted) products.
* Rocq `e1 ||| e2` is `e1 ‖ e2` (`Foxtrot.Lib.Par`).
-/

@[expose] public section

noncomputable section

open Iris Iris.BI Iris.Std Iris.ProofMode OFE COFE ConProbLang ConProbLang.con_prob_lang
open Foxtrot.BinaryRel Foxtrot.Lib.Toss Foxtrot.Lib.Par

namespace Foxtrot.Examples.Algebraic

section eq3

/-- The second step of `eq3_1` (third of `eq3_2`): associativity by `pupd_couple_associativity`. -/
theorem eq3_step_assoc (e1 e2 e3 : expr) (τ : type) (p q r s X Y a b : ℕ)
    (Hpq : p ≤ q + 1) (Hrs : r ≤ s + 1)
    (hX : X = (q + 1) * (s + 1) - 1) (hY : Y = (q + 1) * (s + 1) - p * r - 1)
    (ha : a = p * r) (hb : b = r * (q + 1 - p))
    (H1 : ∅ ⊢ₜ e1 : τ) (H2 : ∅ ⊢ₜ e2 : τ) (H3 : ∅ ⊢ₜ e3 : τ) :
    ∅ ⊨ cpl(let α := alloc(#s);
            let β := alloc(#q);
            if rand(α) #s < #r
            then if rand(β) #q < #p then &e1 else &e2
            else &e3) ≤ctx≤
      cpl(let (x, y) := (rand(#X) ‖ rand(#Y));
          if x < #a then &e1 else if y < #b then &e2 else &e3) : τ := by
  apply refines_sound spawnFoxtrotRSigma
  intro _ Δ
  ihave H1 := refines_typed τ Δ e1 H1
  ihave H2 := refines_typed τ Δ e2 H2
  ihave H3 := refines_typed τ Δ e3 H3
  unfold_rel
  iintro %K %j Hspec
  wp_alloctape α as Hα
  wp_pures
  wp_alloctape β as Hβ
  wp_pures
  solve_subst
  tp_bind j cpl(rand(#X) ‖ rand(#Y))
  imod tp_par j _ _ _ ⊤ $$ Hspec with ⟨%j1, %j2, %K1, %K2, Hspec1, Hspec2, Hcont⟩
  imod pupd_couple_associativity α β [] [] j1 K1 j2 K2 ⊤ Hpq Hrs hX hY $$ Hα Hβ Hspec1 Hspec2
    with ⟨%resl, %resl', %resr, %resr', %Hl, %Hl', %Hr, %Hr', Hα, Hβ, Hspec1, Hspec2, %Hcond⟩
  imod Hcont $$ [Hspec1 Hspec2] with Hspec
  · iframe Hspec1 Hspec2
  subst ha hb
  tp_pures j
  solve_subst
  simp only [List.nil_append]
  split_ifs at Hcond with h1 h2
  · case_bool_decide <;> try omega
    tp_pures j
    wp_randtape
    wp_pures
    case_bool_decide <;> try omega
    wp_pures
    wp_randtape
    wp_pures
    case_bool_decide <;> try omega
    wp_pures
    iapply H1 $$ Hspec
  · case_bool_decide <;> try omega
    tp_pures j
    case_bool_decide <;> try omega
    tp_pures j
    wp_randtape
    wp_pures
    case_bool_decide <;> try omega
    wp_pures
    wp_randtape
    wp_pures
    case_bool_decide <;> try omega
    wp_pures
    iapply H2 $$ Hspec
  · case_bool_decide <;> try omega
    tp_pures j
    case_bool_decide <;> try omega
    tp_pures j
    wp_randtape
    wp_pures
    case_bool_decide <;> try omega
    wp_pures
    iapply H3 $$ Hspec

end eq3

end Foxtrot.Examples.Algebraic
