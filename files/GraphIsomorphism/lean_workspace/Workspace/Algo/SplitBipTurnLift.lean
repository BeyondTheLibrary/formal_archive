import Workspace.Algo.SplitBipTurnChildren

/-! A recursive partition is extended once at its actual parent. The
named decoder sees exactly the paper's complement block and color shift.
A Johnson answer retains its original ambient point names.
-/
namespace Algo
open Babai RAM
open scoped Classical

private theorem sbipWinEquiv_get {m : ℕ} (L : List ℕ) (hn : L.Nodup)
    (hb : ∀ a ∈ L,a < m) (x : ↥(winSet m L)) :
    L[((winEquiv m L hn hb).symm x).val] = x.val.val := by
  simpa only [List.getD_eq_getElem _ _ ((winEquiv m L hn hb).symm x).isLt] using
    winEquiv_symm_val L hn hb x

/-- Exact extension, including its labels rather than only alpha validity. -/
theorem sbipNamedPartition_extend {m : ℕ} (V W : List ℕ)
    (hV : V.Nodup) (hbV : ∀ a ∈ V,a < m)
    (hW : W.Nodup) (hbW : ∀ a ∈ W,a < m) (q : RawColPart) :
    (decColPartition V.length (rawExtendPartition ((V,W),q))).pushforward (winEquiv m V hV hbV) =
      extendPartition (winSet m V) (winSet m W)
        ((decColPartition W.length q).pushforward (winEquiv m W hW hbW)) := by
  let P := (decColPartition W.length q).pushforward (winEquiv m W hW hbW)
  apply ColoredPartition.ext
  · funext x
    exact rawExtendPartition_color P Fin.val (winEquiv m V hV hbV).symm
      (sbipWinEquiv_get V hV hbV) (winEquiv m W hW hbW).symm (sbipWinEquiv_get W hW hbW)
      hW (fun _ => Iff.rfl) (fun _ => rfl) x
  · apply Setoid.ext
    intro x y
    exact rawExtendPartition_part P Fin.val (winEquiv m V hV hbV).symm
      (sbipWinEquiv_get V hV hbV) (winEquiv m W hW hbW).symm (sbipWinEquiv_get W hW hbW)
      hW (fun _ => Iff.rfl) (fun _ _ => Iff.rfl) x y

/-- A recursive entry can only occur after the actual Step 5 continuation. -/
theorem sbipTurnChild_continue (c : ℕ) (I : RawSbipNode) (o : RawAlignOutcome)
    (g : RawSbipStored) (hout : (o,some g) ∈ sbipTurn c I.1) :
    (sbipGraphSteps35 (sbipTurnGraphInput I.1)).2 ≠ none := by
  unfold sbipTurn at hout
  split at hout
  next hs =>
    obtain ⟨q,hq,he⟩ := List.mem_map.1 hout
    have hh := congrArg Prod.snd he
    cases hh
  next hs =>
    split at hout
    next hs2 =>
      obtain ⟨q,hq,he⟩ := List.mem_map.1 hout
      have hh := congrArg Prod.snd he
      cases hh
    next hs2 =>
      intro he
      unfold sbipTurnLarge at hout
      simp only [he,Option.elim_none,List.mem_singleton] at hout
      have hh := congrArg Prod.snd hout
      cases hh

namespace SbipNodeRep
variable {m : ℕ} {I J : RawSbipNode} {X Y : Pt (BipBlockInputs (Fin m))}
    (h : SbipNodeRep m I X) (hJ : SbipNodeRep m J Y)
include h hJ

theorem lift_good (hd : ¬ AllClassesSmall X)
    (hV : BipBlockInputs.V₁ Y = step8V₁ X) (ha : BipBlockInputs.alpha Y = alphaNew X)
    (o : RawAlignOutcome) (ho : SbipReturnGood J Y o) :
    SbipReturnGood I X (sbipNodeLift ((I.1.2.1.1.1.1,J.1.2.1.1.1.1),o)) := by
  obtain ⟨Z,hdec,hgood⟩ := ho
  rcases o with ⟨p,j⟩
  cases p with
  | some p =>
    cases j with
    | some j => simp [sbipDecodeNamed,decAlignOutcome] at hdec
    | none =>
      have hz := (Option.some.inj ((sbipDecodeNamed_partition _ hJ.left_nodup hJ.point_lt p).symm.trans hdec))
      subst Z
      apply h.partition_good
      let V := winSet m I.1.2.1.1.1.1
      let W := winSet m J.1.2.1.1.1.1
      let P := (decColPartition J.1.2.1.1.1.1.length p).pushforward
        (winEquiv m J.1.2.1.1.1.1 hJ.left_nodup hJ.point_lt)
      letI : Fintype ↥V := Fintype.ofFinite _
      letI : Fintype ↥W := Fintype.ofFinite _
      have hWV : W ⊆ V := by
        dsimp only [W,V]
        rw [hJ.point_set,hV,h.point_set]
        exact step8V₁_subset X
      have hbalance : BipBlockInputs.alpha Y * (W.ncard : ℝ) =
          BipBlockInputs.alpha X * (V.ncard : ℝ) := by
        change BipBlockInputs.alpha Y * ((winSet m J.1.2.1.1.1.1).ncard : ℝ) = _
        rw [hJ.point_set,hV,ha]
        change _ = BipBlockInputs.alpha X * ((winSet m I.1.2.1.1.1.1).ncard : ℝ)
        rw [h.point_set]
        exact alphaNew_mul_step8V₁ hd
      have hbeta : 1/2 ≤ BipBlockInputs.alpha X := by
        have hh := X.obj.2.1
        change (2:ℝ)/3 ≤ BipBlockInputs.alpha X at hh
        linarith
      have hP : P.IsAlphaPartition (BipBlockInputs.alpha Y) := hgood.2
      exact rawExtendPartition_valid P Fin.val (winEquiv m _ h.left_nodup h.point_lt).symm
        (sbipWinEquiv_get _ h.left_nodup h.point_lt)
        (winEquiv m _ hJ.left_nodup hJ.point_lt).symm
        (sbipWinEquiv_get _ hJ.left_nodup hJ.point_lt) hJ.left_nodup
        (fun _ => Iff.rfl) (fun _ => rfl) (fun _ _ => Iff.rfl)
        (extendPartition.isAlphaPartition hWV inferInstance inferInstance P
          (by rw [ha]; exact (alphaNew_lt_one hd).le) hbeta hbalance hP)
  | none =>
    cases j with
    | none => simp [sbipDecodeNamed,decAlignOutcome] at hdec
    | some j =>
      change decAlignOutcome m (rawAlignJohnson j) = some Z at hdec
      change (if hw : j.WF m (rawJDeg j) j.2.1 then some (decAlignJohnson j hw) else none) = some Z at hdec
      split at hdec
      next hw =>
        have hz := Option.some.inj hdec
        subst Z
        apply h.johnson_good j hw
        have hsub := hgood.1
        have hsize := hgood.2
        refine ⟨?_,?_⟩
        · rw [h.point_set]
          rw [hV] at hsub
          exact hsub.trans (step8V₁_subset X)
        · rw [h.point_set,← alphaNew_mul_step8V₁ hd,← ha,← hV]
          exact hsize
      next hw => cases hdec

include h in
omit hJ in
theorem nodeGraph_dominant (c : ℕ) (g : RawSbipStored) (hg : g ∈ sbipNodeGraphs c I) :
    ¬ AllClassesSmall X := by
  obtain ⟨o,ho⟩ := (sbipTurnChildren_mem _ g).1 hg
  exact h.dominant_of_continue (sbipTurnChild_continue c I o g ho)

end SbipNodeRep
/-- The answer fold preserves validity at the actual parent. -/
theorem sbipNodeCombine_good {m c j : ℕ} {I J : RawSbipNode}
    (hc : sbipNodeChild c (I,j) = some J) (s A : RawSbipAnswers)
    (hs : SbipAnswersGood m I s) (hA : SbipAnswersGood m J A) :
    SbipAnswersGood m I (sbipNodeCombine c (I,j,s,A)) := by
  intro X h o ho
  obtain ⟨g,hg,hJ,_⟩ := sbipNodeChild_some hc
  have hgD : (sbipNodeGraphs c I).getD j default = g := by
    simp only [List.getD_eq_getElem?_getD,hg,Option.getD_some]
  obtain ⟨Y,hy,hV,ha,_⟩ := h.nodeChild_good hc
  have hd := h.nodeGraph_dominant c g (List.mem_of_getElem? hg)
  change o ∈ s ++ A.map _ at ho
  rcases List.mem_append.1 ho with ho | ho
  · exact hs X h o ho
  · obtain ⟨p,hp,rfl⟩ := List.mem_map.1 ho
    simp only [hgD]
    have hleft : J.1.2.1.1.1.1 = g.1.1.1 := by rw [hJ]; rfl
    rw [← hleft]
    exact h.lift_good hy hd hV ha p (hA Y hy p hp)

/-- Every finite recursive value has only valid returned outcomes. The
separate nonempty theorem requires enough fuel for the raw measure. -/
theorem sbipValue_good (m c f : ℕ) (I : RawSbipNode) :
    SbipAnswersGood m I ((sbipRound c).value f I) := by
  induction f generalizing I with
  | zero => intro X h o ho; cases ho
  | succ f ih =>
    rw [Round.value_succ]
    have loop : ∀ w j s,SbipAnswersGood m I s →
        SbipAnswersGood m I ((sbipRound c).loopAux ((sbipRound c).value f) w I j s) := by
      intro w
      induction w with
      | zero => intro j s hs; exact hs
      | succ w hw =>
        intro j s hs
        cases hc : sbipNodeChild c (I,j) with
        | none =>
          rw [(sbipRound c).loopAux_succ_none (show (sbipRound c).child (I,j,s) = none from hc)]
          exact hs
        | some J =>
          rw [(sbipRound c).loopAux_succ_some (show (sbipRound c).child (I,j,s) = some J from hc)]
          exact hw (j+1) _ (sbipNodeCombine_good hc s _ hs (ih J))
    exact loop _ _ _ (sbipNodeInit_good m c I)

end Algo
