module

public import Metrology.Foxtrot.Lib.Par
public import Metrology.Foxtrot.Lib.Sampler
public import Metrology.Foxtrot.AdequacyInstance
public import Metrology.Foxtrot.BinaryRel.BinarySoundness
public import Iris.Instances.Lib.GhostVar

/-!
# A one-time pad with a message produced by unknown code

Ported from clutch/theories/foxtrot/examples/encryption_unknown.v

Similar to the one-time pad of `Foxtrot.Examples.Encryption`, but now the message is produced
by unknown code `f`, only assumed to satisfy the abstract sampler spec
`sample_spec N f` of `Foxtrot.Lib.Sampler`. `encr_prog` is contextually equivalent to
`rand_prog` (`rand #N`), via the intermediate program `encr_prog'` that samples from tapes.

## Rocq → Lean map
* `coupling_f`, `coupling_f_Bij`, `encr_prog`, `rand_prog`, `encr_prog'`,
  `wp_encr_prog_encr_prog'`, `wp_encr_prog'_rand_prog`, `wp_rand_prog_encr_prog`,
  `encr_prog_refines_rand_prog`, `rand_prog_refines_encr_prog`, `encr_prog_eq_rand_prog`:
  same names (namespace `Foxtrot.Examples.EncryptionUnknown`).
* `#[spawnΣ; foxtrotRΣ; ghost_varΣ bool]` is `encrSigma` (with the instances
  `foxtrotRGpreS_encrSigma`, `spawnG_encrSigma`, `ghostVarG_encrSigma`); `foxtrotRΣ` is
  `Foxtrot.foxtrotSigma` (with the added instance `foxtrotRGpreS_foxtrotSigma`). These are
  copies of the ones of `Foxtrot.Examples.Encryption` (the Rocq files are independent too).

## Deviations
* The section variables `N : nat`, `f : val` and `Hsample : sample_spec N f` are arguments of
  the definitions and lemmas (`Proof using Hsample` is automatic).
* `encr_prog'` is defined outside `Section proof` (it depends only on `Hsample`, not on the
  `foxtrotRGS`/`spawnG`/`ghost_varG` context of that section, which Rocq discards anyway).
* `sample_allocate_tape`/`sample_with_tape` are the fields of `sample_spec N f`, written
  `sample_allocate_tape (tb := N) (sample_without_tape := f)` in the program.
* `fin (S N)` samples (from `sample_tape_presample`, `sample_tape_spec_couple'`,
  `sample_without_tape_spec'`) are `Fin (N + 1)`; `fin_to_nat_lt n` is `n.isLt`, and the proof
  generalizes `(n : ℕ)` to a natural number `n` (Rocq keeps the coercion `fin_to_nat n`).
* As in `Foxtrot.Examples.Encryption`: `#(N+1)` is `#((N : ℤ) + 1)`, `` `rem` `` is `%`,
  `e1 ||| e2` is `e1 ‖ e2`, `Bij f` is `Function.Bijective f` (proved via `Nat.ModEq`),
  Texan triples are at mask `⊤` with arbitrary stuckness, `ghost_var γ (1/2) b` is
  `γ ↪VAR{.own (1 : Qp).half} b`, the bijection/side conditions of the coupling rules are
  explicit, `rewrite /interp/=` is `rw [interp_TNat]`, `unfold_rel` is
  `unfold refines refines_def`, and unused section instances are dropped with `omit`.

## Omitted
* The commented-out `coupling_f'`.
-/

@[expose] public section

open Iris Iris.BI Iris.Std Iris.ProofMode OFE ConProbLang ConProbLang.con_prob_lang
open Foxtrot.Lib.Spawn Foxtrot.Lib.Par Foxtrot.Lib.Sampler Foxtrot.Lib.Sampler.sample_spec
open Foxtrot.BinaryRel

namespace Foxtrot.Examples.EncryptionUnknown

section encr

variable (N : ℕ)

/-- Rocq: `coupling_f`. -/
def coupling_f (n : ℕ) (_ : n ≤ N) : ℕ → ℕ :=
  fun x => if x ≤ N then (x + n) % (N + 1) else x

/-- Rocq: `coupling_f_Bij`. -/
theorem coupling_f_Bij (n : ℕ) (Hn : n ≤ N) : Function.Bijective (coupling_f N n Hn) := by
  constructor
  · intro x y
    unfold coupling_f
    split_ifs with H1 H2 H2
    · intro Heq
      have h := Nat.ModEq.add_right_cancel' n (Heq : (x + n) ≡ (y + n) [MOD N + 1])
      unfold Nat.ModEq at h
      rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
    · intro Heq
      have := Nat.mod_lt (x + n) (by omega : 0 < N + 1)
      omega
    · intro Heq
      have := Nat.mod_lt (y + n) (by omega : 0 < N + 1)
      omega
    · exact id
  · intro x
    unfold coupling_f
    by_cases hx : x ≤ N
    · refine ⟨(x + (N + 1) - n) % (N + 1), ?_⟩
      have := Nat.mod_lt (x + (N + 1) - n) (by omega : 0 < N + 1)
      simp only [show (x + (N + 1) - n) % (N + 1) ≤ N by omega, ↓reduceIte]
      rw [Nat.mod_add_mod, show x + (N + 1) - n + n = x + (N + 1) by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · exact ⟨x, by simp only [hx, ↓reduceIte]⟩

variable (f : val)

/-- Rocq: `encr_prog`. -/
def encr_prog : expr := cpl(
  let x := ref(#0) in
  ((let msg := &f #() in
    faa(x, msg))
     ‖
     (let key := rand(#N) in
     faa(x, key))
  );
  !x % #(((N : ℤ) + 1 : ℤ)))

/-- Rocq: `rand_prog`. -/
def rand_prog : expr := cpl(rand(#N))

variable [Hsample : sample_spec N f]

/-- Rocq: `encr_prog'` (defined inside `Section proof` in Rocq; it only depends on
`Hsample`). -/
def encr_prog' : expr := cpl(
  let x := ref(#0) in
  let α := &(sample_allocate_tape (tb := N) (sample_without_tape := f)) #() in
  let α' := alloc(#N) in
  ((let msg := &(sample_with_tape (tb := N) (sample_without_tape := f)) α in
    faa(x, msg))
     ‖
     (let key := rand(α') #N in
     faa(x, key))
  );
  !x % #(((N : ℤ) + 1 : ℤ)))

section proof

variable {GF : BundledGFunctors} [foxtrotRGS GF] [spawnG GF] [GhostVarG GF Bool]
variable {s : Stuckness}

omit [GhostVarG GF Bool] in
/-- Rocq: `wp_encr_prog_encr_prog'`. -/
theorem wp_encr_prog_encr_prog' (K : List ectx_item) (j : ℕ) :
    {{ j ⤇ fill K (encr_prog' N f) }} (encr_prog N f) @ s; ⊤
    {{ v, RET v; (iprop(∃ v' : val, j ⤇ fill K (Val v') ∗ lrel_nat v v') : IProp GF) }} := by
  iintro %Φ Hspec HΦ
  unfold encr_prog encr_prog'
  tp_alloc j as l' Hl'
  wp_alloc l as Hl
  tp_pures j
  wp_pures
  tp_bind j (App (Val (sample_allocate_tape N f)) _)
  imod sample_allocate_tape_spec' ⊤ j _ $$ Hspec with ⟨%α, Hα, Hspec⟩
  tp_pures j
  tp_allocnattape j α' as Hα'
  tp_pure j
  tp_pure j
  tp_bind j (App (App (Val par) _) _)
  imod tp_par j _ _ _ ⊤ $$ Hspec with ⟨%j1, %j2, %K1, %K2, Hspec1, Hspec2, Hcont⟩
  imod inv_alloc nroot ⊤ iprop(∃ n : ℕ, l ↦ LitV (LitInt (n : ℤ)) ∗ l' ↦ₛ LitV (LitInt (n : ℤ)))
    $$ [Hl Hl'] with #Hinv
  · inext
    iexists 0
    iframe Hl Hl'
  wp_apply wp_par (fun _ => iprop(∃ v1 : val, j1 ⤇ fill K1 (Val v1)))
    (fun _ => iprop(∃ v2 : val, j2 ⤇ fill K2 (Val v2))) $$ [Hα Hspec1] [Hα' Hspec2]
  · tp_bind j1 (App (Val (sample_with_tape N f)) _)
    wp_apply (sample_tape_spec_couple' ⊤ α j1 _) $$ [Hα Hspec1] with %n ⟨-, Hspec1⟩
    · iframe Hα Hspec1
    tp_pures j1
    wp_pures
    iinv Hinv with ⟨%m, >H, >H'⟩ Hclose
    tp_faa j1
    wp_faa
    rw [show (m : ℤ) + ((n : ℕ) : ℤ) = ((m + n : ℕ) : ℤ) by push_cast; rfl]
    imod Hclose $$ [H H']
    · inext
      iexists m + n
      iframe H H'
    imodintro
    iexists _
    iexact Hspec1
  · tp_bind j2 (Rand _ _)
    wp_apply (wp_couple_rand_rand_lbl N id Function.bijective_id (N : ℤ) _ α' j2 (by simp)
      (fun n hn => hn)) $$ [Hα' Hspec2] with %n ⟨-, Hspec2, %Hn⟩
    · iframe Hα' Hspec2
    simp only [id_eq]
    tp_pures j2
    wp_pures
    iinv Hinv with ⟨%m, >H, >H'⟩ Hclose
    tp_faa j2
    wp_faa
    rw [show (m : ℤ) + (n : ℤ) = ((m + n : ℕ) : ℤ) by push_cast; rfl]
    imod Hclose $$ [H H']
    · inext
      iexists m + n
      iframe H H'
    imodintro
    iexists _
    iexact Hspec2
  · iintro %v1 %v2 ⟨⟨%v1', Hspec1⟩, ⟨%v2', Hspec2⟩⟩
    inext
    wp_pures
    imod Hcont $$ %v1' %v2' %⊤ [Hspec1 Hspec2] with Hspec
    · iframe Hspec1 Hspec2
    tp_pures j
    wp_bind (Load _)
    tp_bind j (Load _)
    iinv Hinv with ⟨%m, >H, >H'⟩ Hclose
    tp_load j
    wp_load
    imod Hclose $$ [H H']
    · inext
      iexists m
      iframe H H'
    imodintro
    tp_pures j
    wp_pures
    iapply HΦ
    iexists _
    iframe Hspec
    imodintro
    unfold lrel_nat
    iexists m % (N + 1)
    ipureintro
    have h : ((m : ℤ)).tmod ((N : ℤ) + 1) = ((m % (N + 1) : ℕ) : ℤ) := by norm_cast
    rw [h]
    exact ⟨rfl, rfl⟩


/-- Rocq: `wp_encr_prog'_rand_prog`. -/
theorem wp_encr_prog'_rand_prog (K : List ectx_item) (j : ℕ) :
    {{ j ⤇ fill K (rand_prog N) }} (encr_prog' N f) @ s; ⊤
    {{ v, RET v; (iprop(∃ v' : val, j ⤇ fill K (Val v') ∗ lrel_nat v v') : IProp GF) }} := by
  iintro %Φ Hspec HΦ
  unfold encr_prog' rand_prog
  wp_alloc l as Hl
  wp_pures
  wp_apply (sample_allocate_tape_spec ⊤) $$ [] with %α Hα
  · itrivial
  wp_pures
  wp_alloctape α' as Hα'
  wp_pures
  imod sample_tape_presample ⊤ α [] $$ Hα with ⟨%nf, Hα⟩
  have K1 := nf.isLt
  have Hineq : (nf : ℕ) ≤ N := by omega
  generalize (nf : ℕ) = n at Hineq ⊢
  imod pupd_couple_tape_rand N (coupling_f N n Hineq) (coupling_f_Bij N n Hineq) K ⊤ α' (N : ℤ)
    [] j (by simp) (fun n' Hn' => by
      unfold coupling_f
      simp only [show n' ≤ N by omega, ↓reduceIte]
      exact Nat.mod_lt _ (by omega)) $$ Hα' Hspec with ⟨%n', Hα', Hspec, %Hn'⟩
  simp only [List.nil_append, coupling_f, Hn', ↓reduceIte]
  imod ghost_var_alloc (GF := GF) false with ⟨%γ1, Hγ1, Hγ1'⟩
  imod ghost_var_alloc (GF := GF) false with ⟨%γ2, Hγ2, Hγ2'⟩
  imod inv_alloc nroot ⊤ iprop(∃ b1 b2 : Bool, (γ1 ↪VAR{.own (1 : Qp).half} b1) ∗
      (γ2 ↪VAR{.own (1 : Qp).half} b2) ∗
      l ↦ LitV (LitInt ((if b1 then (n : ℤ) else 0) + (if b2 then (n' : ℤ) else 0))))
    $$ [Hγ1' Hγ2' Hl] with #Hinv
  · inext
    iexists false, false
    simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
    iframe Hγ1' Hγ2' Hl
  wp_apply wp_par (fun _ => iprop(γ1 ↪VAR{.own (1 : Qp).half} true))
    (fun _ => iprop(γ2 ↪VAR{.own (1 : Qp).half} true)) $$ [Hα Hγ1] [Hα' Hγ2]
  · wp_apply (sample_tape_spec_some ⊤ α n []) $$ Hα with -
    wp_pures
    iinv Hinv with ⟨%b1, %b2, >Hg1, >Hg2, >Hl⟩ Hclose
    ihave %Heq := ghost_var_agree $$ Hγ1 Hg1
    subst Heq
    wp_faa
    imod ghost_var_update_halves true γ1 _ _ $$ Hγ1 Hg1 with ⟨Hγ1, Hg1⟩
    imod Hclose $$ [Hg1 Hg2 Hl]
    · inext
      iexists true, b2
      rw [show (if false = true then (n : ℤ) else 0) + (if b2 = true then (n' : ℤ) else 0) + n =
        (if true = true then (n : ℤ) else 0) + (if b2 = true then (n' : ℤ) else 0) by
        simp only [Bool.false_eq_true, ↓reduceIte]; omega]
      iframe Hg1 Hg2 Hl
    imodintro
    iexact Hγ1
  · wp_apply (wp_rand_tape N α' n' [] (N : ℤ) (by simp)) $$ Hα' with ⟨-, %_⟩
    wp_pures
    iinv Hinv with ⟨%b1, %b2, >Hg1, >Hg2, >Hl⟩ Hclose
    ihave %Heq := ghost_var_agree $$ Hγ2 Hg2
    subst Heq
    wp_faa
    imod ghost_var_update_halves true γ2 _ _ $$ Hγ2 Hg2 with ⟨Hγ2, Hg2⟩
    imod Hclose $$ [Hg1 Hg2 Hl]
    · inext
      iexists b1, true
      rw [show (if b1 = true then (n : ℤ) else 0) + (if false = true then (n' : ℤ) else 0) + n' =
        (if b1 = true then (n : ℤ) else 0) + (if true = true then (n' : ℤ) else 0) by
        simp only [Bool.false_eq_true, ↓reduceIte]; omega]
      iframe Hg1 Hg2 Hl
    imodintro
    iexact Hγ2
  · iintro %v1 %v2 ⟨Hγ1, Hγ2⟩
    inext
    wp_pures
    wp_bind (Load _)
    iinv Hinv with ⟨%b1, %b2, >Hg1, >Hg2, >Hl⟩ Hclose
    ihave %Heq1 := ghost_var_agree $$ Hγ1 Hg1
    ihave %Heq2 := ghost_var_agree $$ Hγ2 Hg2
    subst Heq1 Heq2
    wp_load
    imod Hclose $$ [Hg1 Hg2 Hl]
    · inext
      iexists true, true
      iframe Hg1 Hg2 Hl
    imodintro
    wp_pures
    iapply HΦ
    iexists _
    iframe Hspec
    unfold lrel_nat
    iexists (n' + n) % (N + 1)
    ipureintro
    have h : ((n : ℤ) + (n' : ℤ)).tmod ((N : ℤ) + 1) = (((n' + n) % (N + 1) : ℕ) : ℤ) := by
      rw [Nat.add_comm n' n]
      norm_cast
    rw [h]
    exact ⟨rfl, rfl⟩

end proof

section proof'

variable {GF : BundledGFunctors} [foxtrotRGS GF]
variable {s : Stuckness}

/-- Rocq: `wp_rand_prog_encr_prog`. -/
theorem wp_rand_prog_encr_prog (K : List ectx_item) (j : ℕ) :
    {{ j ⤇ fill K (encr_prog N f) }} (rand_prog N) @ s; ⊤
    {{ v, RET v; (iprop(∃ v' : val, j ⤇ fill K (Val v') ∗ lrel_nat v v') : IProp GF) }} := by
  iintro %Φ Hspec HΦ
  unfold encr_prog rand_prog
  iapply wp_pupd
  tp_alloc j as l Hl
  tp_pure j
  tp_pure j
  tp_bind j (App (App (Val par) _) _)
  imod tp_par j _ _ _ ⊤ $$ Hspec with ⟨%j1, %j2, %K1, %K2, Hspec1, Hspec2, Hcont⟩
  tp_bind j1 (App (Val f) _)
  imod sample_without_tape_spec' (tb := N) ⊤ j1 _ $$ Hspec1 with ⟨%nf, Hspec1⟩
  have K1 := nf.isLt
  have Hn : (nf : ℕ) ≤ N := by omega
  generalize (nf : ℕ) = n at Hn ⊢
  tp_pures j1
  tp_faa j1
  rw [show (0 : ℤ) + (n : ℤ) = (n : ℤ) by omega]
  tp_bind j2 (Rand _ _)
  wp_apply (wp_couple_rand_rand' N (coupling_f N n Hn) (coupling_f_Bij N n Hn) j2 (N : ℤ) _
    (by simp) (fun n' Hn' => by
      unfold coupling_f
      simp only [show n' ≤ N by omega, ↓reduceIte]
      exact Nat.mod_lt _ (by omega))) $$ Hspec2 with %n' ⟨%Hn', Hspec2⟩
  tp_pures j2
  tp_faa j2
  imod Hcont $$ %_ %_ %⊤ [Hspec1 Hspec2] with Hspec
  · iframe Hspec1 Hspec2
  tp_pures j
  tp_load j
  tp_pures j
  imodintro
  simp only [coupling_f, Hn', ↓reduceIte]
  iapply HΦ
  iexists _
  iframe Hspec
  unfold lrel_nat
  iexists (n' + n) % (N + 1)
  ipureintro
  have h : ((n : ℤ) + (n' : ℤ)).tmod ((N : ℤ) + 1) = (((n' + n) % (N + 1) : ℕ) : ℤ) := by
    rw [Nat.add_comm n' n]
    norm_cast
  rw [h]
  exact ⟨rfl, rfl⟩

end proof'

end encr

/-! ## Contextual equivalence -/

/-- Rocq: `#[spawnΣ; foxtrotRΣ; ghost_varΣ bool]`: the functors of `foxtrotSigma`, the token
functor of `spawnG` and the ghost variables of `ghost_varG Σ bool`. -/
def encrSigma : BundledGFunctors
  | 8 => ⟨TokenF, by infer_instance⟩
  | 9 => ⟨GhostVarF Bool, by infer_instance⟩
  | n => foxtrotSigma n

instance foxtrotRGpreS_encrSigma : foxtrotRGpreS encrSigma where
  foxtrotRGpreS_foxtrot := {
    foxtrotGpreS_iris := {
      toWsatGpreS := ⟨⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩⟩
      toLcGpreS := ⟨⟨3, rfl⟩⟩ }
    foxtrotGpreS_heap := ⟨⟨4, rfl⟩⟩
    foxtrotGpreS_tapes := ⟨⟨5, rfl⟩⟩
    foxtrotGpreS_spec := ⟨⟨⟨6, rfl⟩⟩, ⟨⟨4, rfl⟩⟩, ⟨⟨5, rfl⟩⟩⟩
    foxtrotGpreS_err := ⟨⟨7, rfl⟩⟩ }

instance spawnG_encrSigma : spawnG encrSigma where
  spawn_tokG := ⟨8, rfl⟩

instance ghostVarG_encrSigma : GhostVarG encrSigma Bool where
  elemG := ⟨9, rfl⟩

/-- Rocq: `foxtrotRΣ` with `subG_foxtrotRGPreS`: `foxtrotSigma` satisfies `foxtrotRGpreS`. -/
instance foxtrotRGpreS_foxtrotSigma : foxtrotRGpreS foxtrotSigma where
  foxtrotRGpreS_foxtrot := foxtrotGpreS_foxtrotSigma

variable (N : ℕ) (f : val) [Hsample : sample_spec N f]

/-- Rocq: `encr_prog_refines_rand_prog`. -/
theorem encr_prog_refines_rand_prog :
    (∅ : varmap type) ⊨ encr_prog N f ≤ctx≤ rand_prog N : TNat := by
  refine ctx_refines_transitive _ _ _ (encr_prog' N f) _ ?_ ?_
  · refine refines_sound encrSigma _ _ _ fun Δ => ?_
    rw [interp_TNat]
    unfold refines refines_def
    iintro %K %j Hspec
    wp_apply wp_encr_prog_encr_prog' N f K j $$ Hspec with %v ⟨%v', Hv', Hv⟩
    iexists v'
    iframe Hv' Hv
  · refine refines_sound encrSigma _ _ _ fun Δ => ?_
    rw [interp_TNat]
    unfold refines refines_def
    iintro %K %j Hspec
    wp_apply wp_encr_prog'_rand_prog N f K j $$ Hspec with %v ⟨%v', Hv', Hv⟩
    iexists v'
    iframe Hv' Hv

/-- Rocq: `rand_prog_refines_encr_prog`. -/
theorem rand_prog_refines_encr_prog :
    (∅ : varmap type) ⊨ rand_prog N ≤ctx≤ encr_prog N f : TNat := by
  refine refines_sound foxtrotSigma _ _ _ fun Δ => ?_
  rw [interp_TNat]
  unfold refines refines_def
  iintro %K %j Hspec
  wp_apply wp_rand_prog_encr_prog N f K j $$ Hspec with %v ⟨%v', Hv', Hv⟩
  iexists v'
  iframe Hv' Hv

/-- Rocq: `encr_prog_eq_rand_prog`. -/
theorem encr_prog_eq_rand_prog :
    (∅ : varmap type) ⊨ encr_prog N f =ctx= rand_prog N : TNat :=
  ⟨encr_prog_refines_rand_prog N f, rand_prog_refines_encr_prog N f⟩

end Foxtrot.Examples.EncryptionUnknown
