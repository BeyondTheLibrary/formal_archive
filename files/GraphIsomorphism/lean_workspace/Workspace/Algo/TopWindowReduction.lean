import Workspace.Algo.TopOrbits
import Workspace.Algo.TopRound

/-!
# Sec. 12: expanding the computed lifting tests into window calls

Use the computed kernel orbits and the coset form of the Chain Rule.
This separates the choices made by the RAM routines from the classical
choices in `Babai.giantAReduction`.
-/

namespace Algo

open RAM RAM.Targets
open Equiv (Perm)
open Babai (SIReduction SIInstance)

/-- Every call of the coset Chain Rule uses one of the supplied windows. -/
theorem calls_cosetChain {Ω A : Type*} (x y : Ω → A)
    (ws : List (Set Ω)) (C : Set (Perm Ω)) :
    (cosetChain x y ws C).calls.length ≤ ws.length ∧
      ∀ I ∈ (cosetChain x y ws C).calls, I.Δ ∈ ws := by
  classical
  induction ws generalizing C with
  | nil => simp [cosetChain]
  | cons w ws ih =>
    rw [cosetChain]
    by_cases hC : C = ∅
    · simp [if_pos hC]
    · rw [if_neg hC, SIReduction.calls_call]
      obtain ⟨hc, hw⟩ := ih (SIInstance.answer ⟨C, w, x, y⟩)
      refine ⟨by simpa using Nat.succ_le_succ hc, ?_⟩
      intro I hI
      rcases List.mem_cons.1 hI with rfl | hI
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hw I hI)

/-- The kernel instance expanded over the computed orbit order. -/
noncomputable def topKernelReduction (n : ℕ) (p : RawAction) (I : SIInstance (Fin n) ℕ) :
    SIReduction (Fin n) ℕ (Set (Perm (Fin n))) :=
  cosetChain I.x I.y ((topKernelWindows p).map (winSet n)) I.K

/-- The computed orbit expansion gives the original full-window answer. -/
theorem run_topKernelReduction {n : ℕ} (p : RawAction) (hd : p.1.1.length = n)
    (I : SIInstance (Fin n) ℕ) (hwin : I.Δ = Set.univ) :
    (topKernelReduction n p I).run = I.answer := by
  rw [topKernelReduction, run_cosetChain, topKernelWindows, topKernel,
    iUnion_decoded_winOrbits (wf_tidyGens hd _) hd, SIInstance.answer, hwin]

theorem calls_length_topKernelReduction (n : ℕ) (p : RawAction) (I : SIInstance (Fin n) ℕ) :
    (topKernelReduction n p I).calls.length ≤ (topKernelWindows p).length := by
  simpa using (calls_cosetChain I.x I.y ((topKernelWindows p).map (winSet n)) I.K).1

theorem calls_topKernelReduction_window (n : ℕ) (p : RawAction) (I : SIInstance (Fin n) ℕ) :
    ∀ J ∈ (topKernelReduction n p I).calls,
      J.Δ ∈ (topKernelWindows p).map (winSet n) :=
  (calls_cosetChain I.x I.y ((topKernelWindows p).map (winSet n)) I.K).2

/-- Proposition 12.0.5 followed by the Chain Rule, as in Corollary
12.0.6. Both the lifts and the orbit order are the computed choices. -/
noncomputable def top1WindowReduction (n : ℕ) (p : RawTop1) :
    SIReduction (Fin n) ℕ (Option (Set (Perm (Fin n)))) :=
  (top1Fold n (top1Inputs p) (some ∅)).expand (topKernelReduction n p.1)

/-- Expanding the kernel tests preserves the complete decision and answer. -/
theorem run_top1WindowReduction (n : ℕ) (p : RawTop1) (hd : p.1.1.1.length = n) :
    (top1WindowReduction n p).run = (top1Fold n (top1Inputs p) (some ∅)).run := by
  rw [top1WindowReduction]
  apply SIReduction.run_expand_of_calls (P := fun I => I.Δ = Set.univ)
    (fun I hI => run_topKernelReduction p.1 hd I hI)
  intro I hI
  rw [calls_top1Fold] at hI
  obtain ⟨q, _, rfl⟩ := List.mem_map.1 hI
  rfl

/-- Corollary 12.0.6: each top test costs at most one call per kernel orbit. -/
theorem calls_length_top1WindowReduction (n : ℕ) (p : RawTop1)
    (hd : p.1.1.1.length = n) :
    (top1WindowReduction n p).calls.length ≤
      (p.2.1.length + 1) * (topKernelWindows p.1).length := by
  rw [top1WindowReduction]
  have h := SIReduction.calls_expand_length_le_of_calls
    (P := fun I : SIInstance (Fin n) ℕ => I.Δ = Set.univ)
    (f := topKernelReduction n p.1)
    (fun I hI => run_topKernelReduction p.1 hd I hI)
    (fun I _ => calls_length_topKernelReduction n p.1 I)
    (top1Fold n (top1Inputs p) (some ∅))
    (fun I hI => by
      rw [calls_top1Fold] at hI
      obtain ⟨q, _, rfl⟩ := List.mem_map.1 hI
      rfl)
  simpa [calls_top1Fold] using h

theorem calls_top1WindowReduction_window (n : ℕ) (p : RawTop1)
    (hd : p.1.1.1.length = n) :
    ∀ J ∈ (top1WindowReduction n p).calls,
      J.Δ ∈ (topKernelWindows p.1).map (winSet n) := by
  rw [top1WindowReduction]
  exact SIReduction.mem_calls_expand_of_calls
    (P := fun I : SIInstance (Fin n) ℕ => I.Δ = Set.univ)
    (fun I hI => run_topKernelReduction p.1 hd I hI)
    (fun I _ => calls_topKernelReduction_window n p.1 I)
    (top1Fold n (top1Inputs p) (some ∅))
    (fun I hI => by
      rw [calls_top1Fold] at hI
      obtain ⟨q, _, rfl⟩ := List.mem_map.1 hI
      rfl)

/-- Proposition 12.0.5 expanded over the kernel windows agrees with
the original top-action test for any supplied target generators. -/
theorem run_top1WindowReduction_eq {n m : ℕ} {dom gdom : List ℕ}
    {gens : List (Perm (Fin n))} {imgs : List (Perm (Fin m))}
    {H : Subgroup (Perm (Fin m))} (ϕ : genGroup gens →* H)
    (hd : dom.length = n) (hm : gdom.length = m) (hI : ImgsOf gens imgs (H.subtype.comp ϕ))
    (S : List H) (x y : Fin n → ℕ) :
    (top1WindowReduction n (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))),
      S.map (fun τ => encPerm m τ.val), encStrN x, encStrN y)).run =
      (Babai.TopAction1Reduction ϕ x y S).run := by
  rw [run_top1WindowReduction n _ hd, run_top1Fold_eq_targetReduction ϕ hd hm hI]

/-- The three-test alternating branch has the bound `3k`. -/
theorem calls_length_top1WindowReduction_three {n m : ℕ} {dom gdom : List ℕ}
    {gens : List (Perm (Fin n))} {imgs : List (Perm (Fin m))}
    {ϕ : genGroup gens →* Perm (Fin m)} (hd : dom.length = n) (hm : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (x y : RawStr) :
    (top1WindowReduction n (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))),
      topAltGens gdom, x, y)).calls.length ≤ 3 * Babai.orbCount ϕ := by
  refine (calls_length_top1WindowReduction n _ hd).trans ?_
  simp only [length_topAltGens]
  exact Nat.mul_le_mul_left 3 (length_topKernelWindows_le hd hm hI)

/-- Corollary 12.0.6: the two branches together use at most `6k`
window calls, for any target string in the second branch. -/
theorem calls_length_top1WindowReduction_pair {n m : ℕ} {dom gdom : List ℕ}
    {gens : List (Perm (Fin n))} {imgs : List (Perm (Fin m))}
    {ϕ : genGroup gens →* Perm (Fin m)} (hd : dom.length = n) (hm : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (x y y' : RawStr) :
    (top1WindowReduction n (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))),
      topAltGens gdom, x, y)).calls.length +
    (top1WindowReduction n (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))),
      topAltGens gdom, x, y')).calls.length ≤ 6 * Babai.orbCount ϕ := by
  have h1 := calls_length_top1WindowReduction_three hd hm hI x y
  have h2 := calls_length_top1WindowReduction_three hd hm hI x y'
  omega

/-- Corollary 12.0.6: the computed branch has the same window bound
as the original reduction. -/
theorem calls_top1WindowReduction_size {n m : ℕ} {dom gdom : List ℕ}
    {gens : List (Perm (Fin n))} {imgs : List (Perm (Fin m))}
    {ϕ : genGroup gens →* Perm (Fin m)} (hd : dom.length = n) (hm : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (S : RawGens) (x y : RawStr)
    (hG : Babai.IsTransitive (genGroup gens)) (hgiant : Babai.IsGiantRep ϕ)
    (hlarge : Babai.LargeK m (Nat.card (Fin n))) :
    ∀ I ∈ (top1WindowReduction n
      (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), S, x, y)).calls,
      Babai.orbCount ϕ * I.windowSize = n := by
  intro I hI'
  obtain ⟨w, hw, he⟩ := List.mem_map.1 (calls_top1WindowReduction_window n _ hd I hI')
  rw [SIInstance.windowSize, ← he, mul_comm]
  exact topKernelWindows_size hd hm hI hw hG hgiant hlarge

/-- Restricting the source to the alternating preimage does not change
the lift of an even top permutation. -/
theorem liftingSet_altHom {n m : ℕ} {G : Subgroup (Perm (Fin n))}
    (ϕ : G →* Perm (Fin m)) (x y : Fin n → ℕ) (τ : alternatingGroup (Fin m)) :
    Babai.liftingSet ϕ x y τ.val = Babai.liftingSet (Babai.altHom ϕ) x y τ := by
  ext g
  constructor
  · rintro ⟨⟨hg, he⟩, hi⟩
    have hga : g ∈ Babai.preimageAlt ϕ := Babai.mem_preimageAlt'.2 ⟨hg, he ▸ τ.property⟩
    exact ⟨⟨hga, Subtype.ext he⟩, hga, hi.2⟩
  · rintro ⟨⟨hg, he⟩, hi⟩
    have hgG := Babai.preimageAlt_le ϕ hg
    exact ⟨⟨hgG, congrArg Subtype.val he⟩, hgG, hi.2⟩

/-- The computed even tests are TopAction1 for the alternating preimage,
also when the original top image is symmetric. -/
theorem run_top1WindowReduction_altHom {n m : ℕ} {dom gdom : List ℕ}
    {gens : List (Perm (Fin n))} {imgs : List (Perm (Fin m))}
    {ϕ : genGroup gens →* Perm (Fin m)} (hd : dom.length = n) (hm : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (S : List (alternatingGroup (Fin m))) (x y : Fin n → ℕ) :
    (top1WindowReduction n (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))),
      S.map (fun τ => encPerm m τ.val), encStrN x, encStrN y)).run =
      (Babai.TopAction1Reduction (Babai.altHom ϕ) x y S).run := by
  classical
  rw [run_top1WindowReduction n _ hd]
  have h := run_top1Fold_eq_TopAction1Reduction hd hm hI (S.map Subtype.val) x y
  rw [List.map_map] at h
  refine h.trans ?_
  simp only [Babai.TopAction1Reduction, SIReduction.run_bind, Babai.run_liftAll,
    SIReduction.run_done]
  have he : (1 :: S.map Subtype.val).map (Babai.liftingSet ϕ x y) =
      (1 :: S).map (Babai.liftingSet (Babai.altHom ϕ) x y) := by
    simp only [List.map_cons, List.map_map]
    apply congrArg₂ List.cons (liftingSet_altHom ϕ x y 1)
    exact List.map_congr_left (fun τ _ => liftingSet_altHom ϕ x y τ)
  rw [he]

/-- Corollary 12.0.6: the computed three-test branch has the same run
as `Babai.giantAReduction` on the alternating preimage. -/
theorem run_top1WindowReduction_eq_giantA {n m : ℕ} {dom gdom : List ℕ}
    {gens : List (Perm (Fin n))} {imgs : List (Perm (Fin m))}
    {ϕ : genGroup gens →* Perm (Fin m)} (hd : dom.length = n) (hm : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (hm3 : 3 ≤ m) (x y : Fin n → ℕ) :
    (top1WindowReduction n (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))),
      topAltGens gdom, encStrN x, encStrN y)).run =
      (Babai.giantAReduction (Babai.altHom ϕ) x y).run := by
  conv_lhs => rw [← map_topAltGensTyped gdom hm hm3]
  rw [run_top1WindowReduction_altHom hd hm hI,
    Babai.run_TopAction1Reduction _ _ _ _ (topAltGensTyped_spec gdom hm hm3).2,
    Babai.run_giantAReduction hm3]

end Algo
