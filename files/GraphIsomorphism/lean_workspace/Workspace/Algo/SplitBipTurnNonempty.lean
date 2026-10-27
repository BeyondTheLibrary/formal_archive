import Workspace.Algo.SplitBipTurnChildren

/-! The executable turn retains at least one actual version. Early
numberings, case graph families, and Design Lemma returning tuples each
supply a witness, independently of the natural early-exit constant.
-/
namespace Algo
open Babai RAM
open scoped Classical
set_option maxHeartbeats 1000000
namespace SbipNodeRep
variable {m : ℕ} {I : RawSbipNode} {X : Pt (BipBlockInputs (Fin m))}
    (h : SbipNodeRep m I X)
include h

theorem cases_nonempty (hd : ¬ AllClassesSmall X) (h6 : ¬ Step6Imprimitive X) :
    ∃ q,q ∈ sbipTurnCases (sbipTurnCase I.1) := by
  obtain ⟨name,e,hc,hs,hf,hnd,he,hp,hr⟩ := h.names
  obtain ⟨e9,he9⟩ := sbipGraphStep9_equiv_exists X name (sbipTurnGraphInput I.1) hc hnd e he hp hr
    h.alpha h.denominator h.left_nodup hd
  have hr9 := sbipGraphStep9Input_right_names X name (sbipTurnGraphInput I.1) hc hnd e he hp hr
    h.alpha h.denominator h.left_nodup hd e9 he9
  have hne : (step8Obj X).blocks.Nonempty := by
    apply (Set.ncard_pos (Set.toFinite _)).1
    have hh := two_le_step8NumBlocks hd
    change 2 ≤ (step8Obj X).blocks.ncard at hh
    omega
  obtain ⟨B,hB⟩ := hne
  have hmem : ∃ b,b ∈ (sbipTurnCase I.1).2.1.2.2 := by
    refine ⟨sbipGraphNumberedBlock (step8Obj X) (sbipGraphConstituent (sbipTurnGraphInput I.1)) e9
      ⟨B,hB⟩,?_⟩
    have hh := Set.mem_image_of_mem
      (sbipGraphNumberedBlock (step8Obj X) (sbipGraphConstituent (sbipTurnGraphInput I.1)) e9)
      (Set.mem_univ ⟨B,hB⟩)
    rw [hr9] at hh
    exact hh
  have hcases := sbipGraphStep9Input_case X name (sbipTurnGraphInput I.1) hc hnd e he hp hr
    h.alpha h.denominator h.left_nodup hd e9 he9
  unfold sbipTurnCases
  split
  next hi =>
    unfold sbipTurnImp
    split
    · obtain ⟨b,hb⟩ := hmem
      exact ⟨_,List.mem_map.2 ⟨b,hb,rfl⟩⟩
    · obtain ⟨q,hq⟩ := impStep2Graphs_nonempty (r := (sbipTurnCase I.1).2.1)
      exact ⟨_,List.mem_map.2 ⟨q,hq,rfl⟩⟩
  next hi =>
    split
    next hcl =>
      have hn := sbipGraphStep9Input_designNames X name (sbipTurnGraphInput I.1) hc hnd e he hp hr
        h.alpha h.denominator h.left_nodup hd e9 he9 h6 (hcases.2.1.1 hcl).2
      have hw := sbipGraphStep9Input_wf (sbipTurnGraphInput I.1)
      obtain ⟨e₁,he₁⟩ := splitNameEquiv_exists _ hn.inj₁ _ hw.left_nodup hn.left
      obtain ⟨e₂,he₂⟩ := splitNameEquiv_exists _ hn.inj₂ _ hw.right_nodup hn.right
      unfold sbipTurnDesign
      cases hcase : designCase12 (sbipTurnCase I.1).2 with
      | some q => exact ⟨_,List.mem_singleton_self _⟩
      | none =>
        simp only [Option.elim_none]
        obtain ⟨h1,h2⟩ := (designCase12_none _).1 hcase
        change designCase1 (sbipGraphStep9Input (sbipTurnGraphInput I.1)) = false at h1
        change designCase2 (sbipGraphStep9Input (sbipTurnGraphInput I.1)) = false at h2
        let U := step9DesignObj X hd h6 (hcases.2.1.1 hcl).2
        let bbd : Pt (BlkBlockDesignInputs (Fin m)) := ⟨step7Set X,
          ⟨(U,alphaNew X),twothirds_le_alphaNew hd,alphaNew_lt_one hd,step8Obj_numBlocks_lt X hd⟩⟩
        have hn1 : ¬ U.IsCase1 := fun hh => by
          have hh' := (designCase1_spec hn e₁ he₁ e₂ he₂).2 hh
          rw [h1] at hh'
          cases hh'
        have hn2 : ¬ U.IsCase2 := fun hh => by
          have hh' := (designCase2_spec hn e₁ he₁ e₂ he₂).2 hh
          rw [h2] at hh'
          cases hh'
        obtain ⟨q,hq⟩ := designCallReadFamily_nonempty hn e₁ he₁ e₂ he₂
          (BlkBlockDesignInputs.numBlocks_lt_n₁ bbd) hn1 hn2
        refine ⟨_,List.mem_map.2 ⟨(q.1,designCase3Graph ((sbipTurnCase I.1).2.1,q.2)),?_,rfl⟩⟩
        exact (designCase3Graphs_mem _ _ _).2 ⟨q.2,hq,rfl⟩
    next hcl =>
      obtain ⟨b,hb⟩ := hmem
      exact ⟨_,List.mem_map.2 ⟨b,hb,rfl⟩⟩

theorem after35_nonempty (hd : ¬ AllClassesSmall X) : ∃ q,q ∈ sbipTurnAfter35 I.1 := by
  obtain ⟨name,e,hc,hs,hf,hnd,he,hp,hr⟩ := h.names
  unfold sbipTurnAfter35
  split
  · exact ⟨_,List.mem_singleton_self _⟩
  next hi =>
    exact h.cases_nonempty hd (fun hh => hi ((sbipGraphComponentTable_test X
      (sbipTurnGraphInput I.1) name hc hnd e he hp hr h.alpha h.denominator h.left_nodup hd).2 hh))

theorem large_nonempty : ∃ q,q ∈ sbipTurnLarge I.1 := by
  unfold sbipTurnLarge
  cases he : (sbipGraphSteps35 (sbipTurnGraphInput I.1)).2 with
  | none => exact ⟨_,List.mem_singleton_self _⟩
  | some q => exact h.after35_nonempty (h.dominant_of_continue (by rw [he]; simp))

theorem turn_nonempty (c : ℕ) : ∃ q,q ∈ sbipTurn c I.1 := by
  unfold sbipTurn
  split
  next hs =>
    obtain ⟨q,hq⟩ := sbipGraphEarly1_nonempty c (sbipTurnGraphInput I.1)
      (by simpa only [sbipGraphSmall1,decide_eq_true_eq] using hs)
    exact ⟨_,List.mem_map.2 ⟨q,hq,rfl⟩⟩
  next hs =>
    split
    next hs2 =>
      obtain ⟨q,hq⟩ := sbipGraphEarly2_nonempty c I.1.2.1.1
        (by simpa only [sbipGraphSmall2,decide_eq_true_eq] using hs2)
      exact ⟨_,List.mem_map.2 ⟨q,hq,rfl⟩⟩
    next hs2 => exact h.large_nonempty

end SbipNodeRep
end Algo
