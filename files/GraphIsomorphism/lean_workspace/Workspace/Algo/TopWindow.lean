import Workspace.Algo.TopRound
import Workspace.TopAction.TopAction2

/-!
# Sec. 12: checking the window-call bound

Corollary 12.0.6 has a bound of `6k`. Its alternating-image branch has
`3k` calls. For equal constant strings every window test succeeds, so the
symmetric-image branch makes all `6k` calls. Thus an exact implementation
of this reduction cannot have a bound of `3k` in that branch.
-/

namespace Algo

open Equiv (Perm)
open Babai

section Counts

variable {Ω A : Type*} [Fintype Ω] [DecidableEq Ω]

theorem calls_length_chainReduction_const (N : Subgroup (Perm Ω)) (a : A)
    (ws : List (Set Ω)) (σ : Perm Ω) (M : Subgroup (Perm Ω)) :
    (chainReduction N (fun _ => a) (fun _ => a) ws σ M).calls.length = ws.length := by
  classical
  induction ws generalizing σ M with
  | nil => rfl
  | cons w ws ih =>
    have hn : (SIInstance.answer
        (⟨(M : Set (Perm Ω)), w, (fun _ => a), strAct (fun _ => a) σ⁻¹⟩ :
          SIInstance Ω A)).Nonempty := ⟨1, M.one_mem, fun _ _ => rfl⟩
    rw [chainReduction, SIReduction.calls_call, dif_pos hn, List.length_cons, ih,
      List.length_cons]

/-- Exact call counts are preserved by expansion when every expanded call
has the same length and gives the original answer. -/
theorem calls_expand_length_eq_of_calls {β : Type*}
    {f : SIInstance Ω A → SIReduction Ω A (Set (Perm Ω))}
    {P : SIInstance Ω A → Prop} (hf : ∀ I, P I → (f I).run = I.answer) {c : ℕ}
    (hc : ∀ I, P I → (f I).calls.length = c) :
    ∀ R : SIReduction Ω A β, (∀ I ∈ R.calls, P I) →
      (R.expand f).calls.length = R.calls.length * c := by
  intro R
  induction R with
  | done a => intro _; simp [SIReduction.expand]
  | call I k ih =>
    intro hR
    have hPI := hR I (by simp)
    rw [SIReduction.expand, SIReduction.calls_bind, List.length_append, hf I hPI, hc I hPI,
      ih I.answer (fun J hJ => hR J (by simp [hJ])), SIReduction.calls_call,
      List.length_cons]
    ring

theorem calls_top1_const_strings {H : Type*} [Group H] {G : Subgroup (Perm Ω)}
    (ϕ : G →* H) (S : List H) (a : A) :
    ∀ I ∈ (TopAction1Reduction ϕ (fun _ => a) (fun _ => a) S).calls,
      I.x = (fun _ => a) ∧ I.y = (fun _ => a) := by
  classical
  intro I hI
  rw [TopAction1Reduction, SIReduction.calls_bind, SIReduction.calls_done,
    List.append_nil, calls_liftAll] at hI
  obtain ⟨τ, _, rfl⟩ := List.mem_map.1 hI
  exact ⟨rfl, rfl⟩

/-- Corollary 12.0.6: the alternating-image branch makes all `3k` calls
on equal constant strings. -/
theorem calls_length_giantAReduction_const {m : ℕ} (hm : 3 ≤ m)
    {G : Subgroup (Perm Ω)} (ϕ : G →* alternatingGroup (Fin m)) (a : A) :
    (giantAReduction ϕ (fun _ => a) (fun _ => a)).calls.length =
      3 * (orbitList (kerSubgroup ϕ)).length := by
  rw [giantAReduction]
  have h := calls_expand_length_eq_of_calls
    (P := fun I : SIInstance Ω A =>
      I.K = (kerSubgroup ϕ : Set (Perm Ω)) ∧ I.Δ = Set.univ ∧
        I.x = (fun _ => a) ∧ I.y = (fun _ => a))
    (f := chainOverOrbits (kerSubgroup ϕ))
    (fun I hI => run_chainOverOrbits hI.1 hI.2.1)
    (c := (orbitList (kerSubgroup ϕ)).length)
    (fun I hI => by
      simp only [chainOverOrbits, hI.2.2.1, hI.2.2.2]
      exact calls_length_chainReduction_const _ _ _ _ _)
    (TopAction1Reduction ϕ (fun _ => a) (fun _ => a) (altGens m))
    (fun I hI =>
      ⟨(calls_wrt_TopAction1 ϕ _ _ I hI).1, (calls_wrt_TopAction1 ϕ _ _ I hI).2,
        calls_top1_const_strings ϕ (altGens m) a I hI⟩)
  rw [calls_length_TopAction1Reduction, (altGens_spec m hm).1] at h
  exact h

/-- Corollary 12.0.6: the symmetric-image branch makes all `6k` calls
on equal constant strings. The factor two is the two-branch descent. -/
theorem calls_length_topAction2Reduction_const {m : ℕ} (hm : 3 ≤ m)
    {G : Subgroup (Perm Ω)} (ϕ : G →* Perm (Fin m))
    (hodd : ¬ϕ.range ≤ alternatingGroup (Fin m)) (a : A) :
    (topAction2Reduction ϕ (fun _ => a) (fun _ => a)).calls.length = 6 * orbCount ϕ := by
  classical
  rw [topAction2Reduction, dif_neg hodd, SIReduction.calls_bind,
    SIReduction.calls_bind, SIReduction.calls_done, List.length_append, List.length_append]
  have he : strAct (fun _ : Ω => a) (oddRep ϕ)⁻¹ = (fun _ => a) := rfl
  rw [he, calls_length_giantAReduction_const hm, orbitList_altHom, length_orbitList]
  change 3 * orbCount ϕ + (3 * orbCount ϕ + 0) = 6 * orbCount ϕ
  omega

end Counts

/-- A concrete input satisfying all the hypotheses of Corollary 12.0.6
whose mathematical reduction has more than `3k` calls. This rules out the
`3k` bound for an exact implementation of the full two-branch reduction. -/
theorem topAction2_three_k_counterexample :
    ∃ (G : Subgroup (Perm (Fin 20))) (ϕ : G →* Perm (Fin 20)),
      IsTransitive G ∧ IsGiantRep ϕ ∧ LargeK 20 (Nat.card (Fin 20)) ∧
        orbCount ϕ = 20 ∧
        (topAction2Reduction ϕ (fun _ => (0 : ℕ)) (fun _ => 0)).calls.length = 120 ∧
        3 * orbCount ϕ <
          (topAction2Reduction ϕ (fun _ => (0 : ℕ)) (fun _ => 0)).calls.length := by
  classical
  let G : Subgroup (Perm (Fin 20)) := ⊤
  let ϕ : G →* Perm (Fin 20) := G.subtype
  have hG : IsTransitive G := by
    refine ⟨0, ?_⟩
    ext z
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    exact ⟨⟨Equiv.swap 0 z, trivial⟩, by simp [Subgroup.smul_def]⟩
  have hgiant : IsGiantRep ϕ := by
    rw [IsGiantRep, Subgroup.subtype_range]
    exact le_top
  have hm : LargeK 20 (Nat.card (Fin 20)) := by
    rw [LargeK, max_lt_iff]
    refine ⟨by norm_num, ?_⟩
    have hlt : Real.logb 2 (Nat.card (Fin 20)) < 18 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fin]
      rw [Real.logb_lt_iff_lt_rpow (by norm_num) (by norm_num)]
      have h2 : (2 : ℝ) ^ (18 : ℝ) = (2 : ℝ) ^ (18 : ℕ) := by
        rw [← Real.rpow_natCast (2 : ℝ) 18]
        norm_num
      rw [h2]
      norm_num
    push_cast
    linarith
  have hodd : ¬ϕ.range ≤ alternatingGroup (Fin 20) := by
    intro h
    have hs := h (show Equiv.swap (0 : Fin 20) 1 ∈ ϕ.range from
      ⟨⟨Equiv.swap 0 1, trivial⟩, rfl⟩)
    have hn : (0 : Fin 20) ≠ 1 := by decide
    simpa [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_swap hn] using hs
  have hk : orbCount ϕ = 20 := by
    let N := kerSubgroup ϕ
    have hN : ∀ s : N, (s : Perm (Fin 20)) = 1 := by
      intro s
      obtain ⟨hs, he⟩ := mem_kerSubgroup.1 s.2
      exact he
    let q : Fin 20 → MulAction.orbitRel.Quotient N (Fin 20) := Quotient.mk''
    have hq : Function.Bijective q := by
      constructor
      · intro a b hab
        obtain ⟨s, hs⟩ := MulAction.mem_orbit_iff.1
          (MulAction.orbitRel_apply.1 (Quotient.eq''.1 hab))
        simpa [Subgroup.smul_def, hN s] using hs.symm
      · exact Quotient.mk_surjective
    have hc := Nat.card_congr (Equiv.ofBijective q hq)
    change Nat.card (MulAction.orbitRel.Quotient N (Fin 20)) = 20
    simpa using hc.symm
  have hc : (topAction2Reduction ϕ (fun _ => (0 : ℕ)) (fun _ => 0)).calls.length = 120 := by
    rw [calls_length_topAction2Reduction_const (by omega) ϕ hodd, hk]
  exact ⟨G, ϕ, hG, hgiant, hm, hk, hc, by rw [hk, hc]; decide⟩

/-- `LoopMatch` cannot hide calls. With a correct child oracle, a matching
reduction has at most the raw loop's budget many calls. -/
theorem LoopMatch.calls_length_le {ι ω α Ω A : Type*} (R : Round ι ω α)
    {decI : ι → SIInstance Ω A} {decA : α → Set (Perm Ω)}
    (rec : ι → α) (hrec : ∀ J, decA (rec J) = (decI J).answer)
    {I : ι} {w j : ℕ} {s : ω} {T : SIReduction Ω A (Set (Perm Ω))}
    (h : LoopMatch R decI decA I w j s T) : T.calls.length ≤ w := by
  induction h with
  | done w j s a hc ha => simp
  | call w j s J k hc hnext ih =>
    rw [SIReduction.calls_call, List.length_cons]
    exact Nat.succ_le_succ (ih (rec J) (hrec J))

end Algo
