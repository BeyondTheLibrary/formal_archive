import Workspace.Algo.SplitBipTurnDesignChildBase

/-! The literal DesignCase branch tests choose the graph supplied to the
next turn. Each graph uses the same dictionary as its actual case input. -/
namespace Algo
open Babai RAM
open scoped Classical
set_option maxHeartbeats 1000000

private theorem designCase12_graph_tests (z : RawDesignLocal) (L : List ℕ)
    (o : RawAlignOutcome) (g : RawDesignGraph)
    (hout : designCase12 z = some ((L,o),some g)) :
    designCase1 z.1 ≠ true ∧ designCase2 z.1 = true ∧
      ((designTie z.1 = true ∧ g = designTieGraph z.1) ∨
       (designTie z.1 ≠ true ∧ designSelectC z.1 ≠ true ∧ g = designOtherGraph z.1)) := by
  unfold designCase12 designCase2Exit designDominantExit at hout
  split_ifs at hout <;>
    simp_all [designJohnsonExit,designGraphExit,designPartExit]

namespace SbipNodeRep
variable {m : ℕ} {I : RawSbipNode} {X : Pt (BipBlockInputs (Fin m))}
    (h : SbipNodeRep m I X) (hd : ¬ AllClassesSmall X)
include h hd

theorem design_child_good (h6 : ¬ Step6Imprimitive X) (hcl : Step9Clique X)
    (o : RawAlignOutcome) (g : RawSbipStored)
    (hout : (o,some g) ∈ sbipTurnDesign (sbipTurnCase I.1)) : SbipChildGood I X g := by
  letI : Fintype ↥(step7Set X) := Fintype.ofFinite _
  letI : DecidableEq ↥(step7Set X) := Classical.decEq _
  obtain ⟨name,e,hc,hs,hf,hnd,he,hp,hr⟩ := h.names
  obtain ⟨eD,heD,hD⟩ := sbipGraphStep9Dictionary_equiv_exists X name (fun x => x.val.val)
    I.1.2 hs hc hnd e he hp hr h.alpha h.denominator h.left_nodup hd
  let e9 := eD.trans (finCongr (sbipGraphStep9Dictionary_length I.1.2))
  have he9 : ∀ A,(sbipGraphCaseVertices (sbipGraphConstituent (sbipTurnGraphInput I.1)))[(e9 A).val] =
      sbipGraphStep8Name X name A := heD
  have hn := sbipGraphStep9Input_designNames X name (sbipTurnGraphInput I.1) hc hnd e he hp hr
    h.alpha h.denominator h.left_nodup hd e9 he9 h6 hcl
  have hw := sbipGraphStep9Input_wf (sbipTurnGraphInput I.1)
  obtain ⟨e₁,he₁⟩ := splitNameEquiv_exists _ hn.inj₁ _ hw.left_nodup hn.left
  obtain ⟨e₂,he₂⟩ := splitNameEquiv_exists _ hn.inj₂ _ hw.right_nodup hn.right
  let U := step9DesignObj X hd h6 hcl
  have hpoint : Function.Injective (fun x : ↥(step7Set X) => x.val.val) :=
    fun _ _ hh => Subtype.ext (Fin.ext hh)
  have hbound (x : ↥(step7Set X)) : x.val.val < I.1.1.length := by
    rw [show I.1.1.length = m from h.ground]
    exact x.val.isLt
  have hsize : (sbipTurnCase I.1).2.1.1.1.length = (sbipGraphStep9Dictionary I.1.2).length := by
    simp [sbipTurnCase,sbipTurnGraphInput,sbipGraphStep9Input,sbipGraphNumbered,
      sbipGraphStep9Dictionary_length]
  have hcolors (A : ↥U.vtxSet) :
      binColor ((sbipTurnCase I.1).2.1.1,(eD A,eD A)) = U.c A.val A.val :=
    sbipGraphStep9Input_color X name (sbipTurnGraphInput I.1) hc hnd e he hp hr
      h.alpha h.denominator h.left_nodup hd e9 he9 A A
  let bbd : Pt (BlkBlockDesignInputs (Fin m)) := ⟨step7Set X,
    ⟨(U,alphaNew X),twothirds_le_alphaNew hd,alphaNew_lt_one hd,step8Obj_numBlocks_lt X hd⟩⟩
  have hlt : U.n₂ < U.n₁ := BlkBlockDesignInputs.numBlocks_lt_n₁ bbd
  unfold sbipTurnDesign at hout
  cases hcase : designCase12 (sbipTurnCase I.1).2 with
  | none =>
    simp only [hcase,Option.elim_none] at hout
    obtain ⟨q,hq,ho⟩ := List.mem_map.1 hout
    obtain ⟨d,hdout,hqd⟩ := (designCase3Graphs_mem _ q.1 q.2).1 hq
    have hg := congrArg Prod.snd ho
    change some (designStored ((I.1.1,sbipGraphStep9Dictionary I.1.2),q.2)) = some g at hg
    rw [← Option.some.inj hg,hqd]
    obtain ⟨h1,h2⟩ := (designCase12_none _).1 hcase
    have hn1 : ¬ U.IsCase1 := fun hh => by
      have := (designCase1_spec hn e₁ he₁ e₂ he₂).2 hh
      change designCase1 (sbipGraphStep9Input (sbipTurnGraphInput I.1)) = false at h1
      rw [h1] at this
      cases this
    have hn2 : ¬ U.IsCase2 := fun hh => by
      have := (designCase2_spec hn e₁ he₁ e₂ he₂).2 hh
      change designCase2 (sbipGraphStep9Input (sbipTurnGraphInput I.1)) = false at h2
      rw [h2] at this
      cases this
    apply h.design_restricted_child hd h6 hcl
      (designReadSelectedSet _ _ d) (designReadMathHint e₂ d) _
      (designCallReadStored_complete hn hw (fun x => x.val.val) (sbipGraphStep9Dictionary I.1.2)
        eD hD hpoint (fun _ => rfl) (fun _ => rfl) hsize hcolors I.1.1 hbound e₂ he₂ hdout)
      (designReadSelectedSet_sub d)
      (designCallReadSelected_defect hn hw e₁ he₁ e₂ he₂ hdout)
    exact designCallReadSelected_progress hn hw e₁ he₁ e₂ he₂ hlt hn1 hn2 hdout
  | some q =>
    simp only [hcase,Option.elim_some,List.mem_singleton] at hout
    rcases q with ⟨⟨L,ro⟩,q⟩
    cases q with
    | none =>
      have hh := congrArg Prod.snd hout
      cases hh
    | some q =>
      have hg := congrArg Prod.snd hout
      change some g = some (designStored ((I.1.1,sbipGraphStep9Dictionary I.1.2),q)) at hg
      rw [Option.some.inj hg]
      obtain ⟨h1,h2,htest⟩ := designCase12_graph_tests _ L ro q hcase
      have hn1 : ¬ U.IsCase1 := fun hh => h1 ((designCase1_spec hn e₁ he₁ e₂ he₂).2 hh)
      have hn2 : U.IsCase2 := (designCase2_spec hn e₁ he₁ e₂ he₂).1 h2
      rcases htest with ⟨ht,rfl⟩ | ⟨ht,hsel,rfl⟩
      · apply h.design_restricted_child hd h6 hcl U.blocks U.twinHint _
          (designTieStored_complete hn hw (fun x => x.val.val) (sbipGraphStep9Dictionary I.1.2)
            eD hD hpoint (fun _ => rfl) (fun _ => rfl) hsize hcolors I.1.1 hbound e₂ he₂)
          subset_rfl (BlkCaseObj.symDefect₁_blocks U)
        exact Or.inr ⟨le_rfl,U.hasHint_twinHint hlt hn1 ((designTie_spec hn e₁ he₁ e₂ he₂).1 ht)⟩
      · have hst := designOtherStored_complete hn hw (fun x => x.val.val)
          (sbipGraphStep9Dictionary I.1.2) eD hD hpoint (fun _ => rfl) (fun _ => rfl)
          hsize hcolors I.1.1 hbound e₂ he₂
        rw [← designLinkGraph_zero_hint (X := U)] at hst
        apply h.design_restricted_child hd h6 hcl (U.blocks \ U.bigTwin) (fun _ _ => 0) _
          hst Set.diff_subset (designSelectC_complement hn e₁ he₁ e₂ he₂ hsel)
        have hnt : U.bigTwin ≠ U.blocks := fun hh => ht ((designTie_spec hn e₁ he₁ e₂ he₂).2 hh)
        obtain ⟨hsub,hcard,_,_⟩ := U.bigTwin_spec hn2 hnt
        have hc := Set.ncard_diff_add_ncard_of_subset hsub (Set.toFinite _)
        apply Or.inl
        change 10 * (U.blocks \ U.bigTwin).ncard ≤ 9 * U.n₂
        change (U.blocks \ U.bigTwin).ncard + U.bigTwin.ncard = U.n₂ at hc
        omega

end SbipNodeRep
end Algo
