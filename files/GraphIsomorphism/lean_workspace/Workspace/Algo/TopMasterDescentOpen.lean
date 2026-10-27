import Workspace.Algo.TopMasterDescentSpec

/-! # Kernel descent calls the master machine directly
Normalization keeps the fold bounded. Its state relation preserves every
next orbit instance. The shared admission check is then vacuous because
each actual kernel-orbit window is smaller than the parent window.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv

 theorem masterDescFoldRead_decode {n : ℕ} {I J : AggnRecomputeNode} {j : ℕ}
    {s : AggnRecomputeState} (hJ : aggnrChild (I, j, s) = some J) :
    aggnrDecode n J = decWinSI n (masterDescFoldRead J) := by
  obtain ⟨_, _, _, _, _, _, rfl⟩ := aggnrChild_some hJ
  rfl

 theorem masterAdmittedRound_descent_match {S : Type} (a b : ℕ) {F : MasterOps S}
    {n : ℕ} {P : AggnRecomputeInput} {p : RawMasterSI}
    (hx : P.1.2.2.2.1.length = n) (hparent : p.1.2.2.2.1 = P.1.2.2.2.1)
    (hp : masterWindowSize p ≤ masterDegree p)
    (u : AggnRecomputeState → S)
    (hw : F.width p = masterDescFoldWidth P)
    (hc : ∀ j s, F.child (p, j, u s) = masterDescFoldChild (P, j, s))
    (hi : F.init p = u (masterDescFoldInit P))
    (hu : ∀ j s A, F.combine (p, j, u s, A) = u (masterDescFoldCombine (P, j, s, A)))
    (hf : ∀ s, F.finish (p, u s) = masterDescFoldFinish (P, s))
    {T : SIReduction (Fin n) ℕ (Set (Perm (Fin n)))}
    (h : LoopMatch (aggnrRound n (fun _ => none)) (aggnrDecode n) (decCoset n)
      (P, none) (masterDescFoldWidth P) 0 (aggnrInit (P, none)) T)
    (hT : ∀ J ∈ T.calls, MasterCallLetters (2 * n + 1) J ∧ J.windowSize < masterWindowSize p ∧
      ∃ G : Subgroup (Perm (Fin n)), IsCosetInstance G J) :
    LoopMatch (masterAdmittedRound a b F) (fun J => decWinSI n J.1) (decCoset n)
      p (F.width p) 0 (F.init p) T := by
  have hn : p.1.2.2.2.1.length = n := hparent ▸ hx
  rw [hw, hi]
  apply loopMatch_simulation (P, none) p
    (fun s v => ∃ t, v = u t ∧ MasterDescFoldRel n s t)
    (fun J => MasterCallLetters (2 * n + 1) J ∧ J.windowSize < masterWindowSize p ∧
      ∃ G : Subgroup (Perm (Fin n)), IsCosetInstance G J)
    (R := aggnrRound n (fun _ => none)) (M := masterAdmittedRound a b F)
    (decI := aggnrDecode n) (decN := fun J => decWinSI n J.1) (decA := decCoset n)
    _ _ _ _ _ _ _ T h hT _ ⟨_, rfl, masterDescFoldRel_norm hx _⟩
  · intro j s v hv hs
    obtain ⟨t, rfl, ht⟩ := hv
    have he := masterDescFoldRel_child hx ht j
    change aggnrChild ((P, none), j, s) = none at hs
    rw [hs, Option.map_none] at he
    have ht' : aggnrChild ((P, none), j, t) = none := Option.map_eq_none_iff.mp he.symm
    change masterGuardedChild a b F (p, j, u t) = none
    unfold masterGuardedChild
    rw [hc, masterDescFoldChild, ht', Option.map_none]
    split_ifs <;> rfl
  · intro j s v J hv hJ hV
    obtain ⟨t, rfl, ht⟩ := hv
    change aggnrChild ((P, none), j, s) = some J at hJ
    have he := masterDescFoldRel_child hx ht j
    rw [hJ, Option.map_some] at he
    obtain ⟨K, hK, heK⟩ := Option.map_eq_some_iff.mp he.symm
    have hd := (masterDescFoldRead_decode hK).symm.trans heK
    have hvread : MasterCallLetters (2 * n + 1) (decWinSI n (masterDescFoldRead K)) ∧
        (decWinSI n (masterDescFoldRead K)).windowSize < masterWindowSize p ∧
        ∃ G : Subgroup (Perm (Fin n)), IsCosetInstance G (decWinSI n (masterDescFoldRead K)) :=
      hd.symm ▸ hV
    refine ⟨masterCheckedCall (p.1.2.2.2.1, masterDescFoldRead K), ?_,
      (masterCheckedCall_decode hn _ hvread.1).trans hd⟩
    have hj := (aggnrChild_some hK).choose_spec.2.2.2.2.1
    change j < masterDescFoldWidth P at hj
    change masterGuardedChild a b F (p, j, u t) = _
    unfold masterGuardedChild
    rw [hw, if_pos hj, hc, masterDescFoldChild, hK, Option.map_some, ← hparent]
    obtain ⟨hL, hlt, G, hG⟩ := hvread
    have hdeg : masterDegree p = n := hn
    subst hdeg
    exact masterCheckedCall_admitted a b _ hp hlt hL hG
  · intro j s v A hv
    obtain ⟨t, rfl, ht⟩ := hv
    refine ⟨masterDescFoldCombine (P, j, t, A), hu j t A, masterDescFoldRel_combine hx ht j A⟩
  · intro s v hv
    obtain ⟨t, rfl, ht⟩ := hv
    change decCoset n (F.finish (p, u t)) = decCoset n s.2.2.2
    rw [hf, masterDescFoldFinish, decCoset_top2NormC hx]
    exact ht.2.2.2.symm

end Algo
