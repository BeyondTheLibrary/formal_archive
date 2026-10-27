import Workspace.Algo.SplitBipTurnDesignChild
import Workspace.Algo.SplitBipTurnDesignReturnFamily

/-! The DesignCase children with their explicit next inputs. The next
input of a restricted link graph is the hinted restriction itself, carried
with the updated threshold. Isomorphic parents whose selected block
families and hints correspond give isomorphic next inputs.
-/
namespace Algo
open Babai RAM
open scoped Classical
set_option maxHeartbeats 1000000

private theorem designCase12_graph_tests' (z : RawDesignLocal) (L : List ℕ)
    (o : RawAlignOutcome) (g : RawDesignGraph)
    (hout : designCase12 z = some ((L,o),some g)) :
    designCase1 z.1 ≠ true ∧ designCase2 z.1 = true ∧
      ((designTie z.1 = true ∧ g = designTieGraph z.1) ∨
       (designTie z.1 ≠ true ∧ designSelectC z.1 ≠ true ∧ g = designOtherGraph z.1)) := by
  unfold designCase12 designCase2Exit designDominantExit at hout
  split_ifs at hout <;>
    simp_all [designJohnsonExit,designGraphExit,designPartExit]

namespace SbipNodeRep
variable {m : ℕ} {I J : RawSbipNode} {X Y : Pt (BipBlockInputs (Fin m))}
    (h : SbipNodeRep m I X) (h' : SbipNodeRep m J Y) (hd : ¬ AllClassesSmall X)

section Rep
include h hd

/-- The representation part of `design_child`, with the next input written out. -/
theorem design_child_rep {t : Set (Fin m)} (G : VColBipBlk ↥t ℕ) (g : RawSbipStored)
    (hs : SbipStoredRep G (fun x => x.val.val) g)
    (hadm : letI : Fintype ↥t := Fintype.ofFinite _
      letI : DecidableEq ↥t := Classical.decEq _
      G.IsThm922Input (alphaNew X))
    (hprogress : letI : Fintype ↥t := Fintype.ofFinite _
      letI : DecidableEq ↥t := Classical.decEq _
      10 * G.numBlocks ≤ 9 * step8NumBlocks X ∨
        (G.numBlocks ≤ step8NumBlocks X ∧ G.HasHint)) :
    letI : Fintype ↥t := Fintype.ofFinite _
    letI : DecidableEq ↥t := Classical.decEq _
    SbipNodeRep m (sbipNodeMakeChild (I,g))
      ⟨t,⟨(G,alphaNew X),twothirds_le_alphaNew hd,alphaNew_lt_one hd,hadm⟩⟩ := by
  letI : Fintype ↥t := Fintype.ofFinite _
  letI : DecidableEq ↥t := Classical.decEq _
  have hcount := sbipStoredRep_block_count hs
  have hparent := h.block_count
  have hsteps := step8NumBlocks_le X
  have hpos := two_le_numBlocks_of_step9 hd
  have hle : G.numBlocks ≤ step8NumBlocks X := hprogress.elim (by omega) And.left
  have hnh : ¬ (g.1.1.2.1.length < sbipNodeBlocks I ∧
      10 * g.1.1.2.1.length ≤ 9 * sbipNodeBlocks I) → G.HasHint := by
    intro hnot
    rcases hprogress with hshrink | hh
    · exact False.elim (hnot ⟨by omega,by omega⟩)
    · exact hh.2
  refine ⟨h.ground,hs,h.case_alpha hd,h.case_denominator hd,?_⟩
  intro hz
  apply hnh
  intro hlt
  simp [sbipNodeBit,sbipNodeMakeChild,hlt] at hz

/-- Sec. 9.7: a restricted, hinted link graph kept by DesignCase is a valid
next input, with the parent's updated threshold. -/
theorem design_restricted_rep (h6 : ¬ Step6Imprimitive X) (hcl : Step9Clique X)
    (S : Set (Set ↥(step7Set X))) (c : Set ↥(step7Set X) → Set ↥(step7Set X) → ℕ)
    (g : RawSbipStored)
    (hs : SbipStoredRep ((step9DesignObj X hd h6 hcl).linkGraph.restrictBlkHint S c)
      (fun x => x.val.val) g)
    (hS : S ⊆ (step9DesignObj X hd h6 hcl).blocks)
    (hdef : letI : Fintype ↥(step7Set X) := Fintype.ofFinite _
      letI : DecidableEq ↥(step7Set X) := Classical.decEq _
      (((step9DesignObj X hd h6 hcl).n₁ : ℚ) - 1) / 2 ≤
        ((step9DesignObj X hd h6 hcl).linkGraph.restrictBlk S).symDefect₁)
    (hprogress : letI : Fintype ↥(step7Set X) := Fintype.ofFinite _
      letI : DecidableEq ↥(step7Set X) := Classical.decEq _
      10 * S.ncard ≤ 9 * step8NumBlocks X ∨
        (S.ncard ≤ step8NumBlocks X ∧
          ((step9DesignObj X hd h6 hcl).linkGraph.restrictBlkHint S c).HasHint)) :
    letI : Fintype ↥(step7Set X) := Fintype.ofFinite _
    letI : DecidableEq ↥(step7Set X) := Classical.decEq _
    ∃ hadm,SbipNodeRep m (sbipNodeMakeChild (I,g))
      ⟨step7Set X,⟨((step9DesignObj X hd h6 hcl).linkGraph.restrictBlkHint S c,alphaNew X),
        twothirds_le_alphaNew hd,alphaNew_lt_one hd,hadm⟩⟩ := by
  letI : Fintype ↥(step7Set X) := Fintype.ofFinite _
  letI : DecidableEq ↥(step7Set X) := Classical.decEq _
  let U : Pt (BlkBlockDesignInputs (Fin m)) := ⟨step7Set X,
    ⟨(step9DesignObj X hd h6 hcl,alphaNew X),twothirds_le_alphaNew hd,
      alphaNew_lt_one hd,step8Obj_numBlocks_lt X hd⟩⟩
  have hlt := BlkBlockDesignInputs.numBlocks_lt_n₁ U
  have h3 : 3 ≤ (step9DesignObj X hd h6 hcl).n₁ := by
    have hh := two_le_step8NumBlocks hd
    change step8NumBlocks X < (step9DesignObj X hd h6 hcl).n₁ at hlt
    omega
  have hadm := (restrictObjHint_pred U c hS h3 hdef).2.2
  refine ⟨hadm,h.design_child_rep hd _ g hs hadm ?_⟩
  rwa [VColBipBlk.restrictBlkHint_numBlocks
    (X := (step9DesignObj X hd h6 hcl).linkGraph) hS]

/-- Sec. 9.7, Case 2, the tie: the kept graph is the link graph with the
twin hint, and it is a valid next input. -/
theorem design_tie_rep (h6 : ¬ Step6Imprimitive X) (hcl : Step9Clique X)
    (h1 : designCase1 (sbipTurnCase I.1).2.1 ≠ true)
    (ht : designTie (sbipTurnCase I.1).2.1 = true) :
    letI : Fintype ↥(step7Set X) := Fintype.ofFinite _
    letI : DecidableEq ↥(step7Set X) := Classical.decEq _
    ∃ hadm,SbipNodeRep m (sbipNodeMakeChild (I,designStored ((I.1.1,sbipGraphStep9Dictionary I.1.2),
        designTieGraph (sbipTurnCase I.1).2.1)))
      ⟨step7Set X,⟨((step9DesignObj X hd h6 hcl).linkGraph.restrictBlkHint
        (step9DesignObj X hd h6 hcl).blocks (step9DesignObj X hd h6 hcl).twinHint,alphaNew X),
        twothirds_le_alphaNew hd,alphaNew_lt_one hd,hadm⟩⟩ := by
  letI : Fintype ↥(step7Set X) := Fintype.ofFinite _
  letI : DecidableEq ↥(step7Set X) := Classical.decEq _
  obtain ⟨eD,hn,hD,hcolors⟩ := h.design_case_names hd h6 hcl
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
  let bbd : Pt (BlkBlockDesignInputs (Fin m)) := ⟨step7Set X,
    ⟨(U,alphaNew X),twothirds_le_alphaNew hd,alphaNew_lt_one hd,step8Obj_numBlocks_lt X hd⟩⟩
  have hlt : U.n₂ < U.n₁ := BlkBlockDesignInputs.numBlocks_lt_n₁ bbd
  have hn1 : ¬ U.IsCase1 := fun hh => h1 ((designCase1_spec hn e₁ he₁ e₂ he₂).2 hh)
  exact h.design_restricted_rep hd h6 hcl U.blocks U.twinHint _
    (designTieStored_complete hn hw (fun x => x.val.val) (sbipGraphStep9Dictionary I.1.2)
      eD hD hpoint (fun _ => rfl) (fun _ => rfl) hsize hcolors I.1.1 hbound e₂ he₂)
    subset_rfl (BlkCaseObj.symDefect₁_blocks U)
    (Or.inr ⟨le_rfl,U.hasHint_twinHint hlt hn1 ((designTie_spec hn e₁ he₁ e₂ he₂).1 ht)⟩)

/-- Sec. 9.7, Case 2, Reduce-Part2-by-Color when `C` fails the test: the
kept graph is the link graph restricted to `V₂ ∖ C`, a valid next input. -/
theorem design_other_rep (h6 : ¬ Step6Imprimitive X) (hcl : Step9Clique X)
    (h2 : designCase2 (sbipTurnCase I.1).2.1 = true)
    (ht : designTie (sbipTurnCase I.1).2.1 ≠ true)
    (hsel : designSelectC (sbipTurnCase I.1).2.1 ≠ true) :
    letI : Fintype ↥(step7Set X) := Fintype.ofFinite _
    letI : DecidableEq ↥(step7Set X) := Classical.decEq _
    ∃ hadm,SbipNodeRep m (sbipNodeMakeChild (I,designStored ((I.1.1,sbipGraphStep9Dictionary I.1.2),
        designOtherGraph (sbipTurnCase I.1).2.1)))
      ⟨step7Set X,⟨((step9DesignObj X hd h6 hcl).linkGraph.restrictBlkHint
        ((step9DesignObj X hd h6 hcl).blocks \ (step9DesignObj X hd h6 hcl).bigTwin)
        (fun _ _ => 0),alphaNew X),
        twothirds_le_alphaNew hd,alphaNew_lt_one hd,hadm⟩⟩ := by
  letI : Fintype ↥(step7Set X) := Fintype.ofFinite _
  letI : DecidableEq ↥(step7Set X) := Classical.decEq _
  obtain ⟨eD,hn,hD,hcolors⟩ := h.design_case_names hd h6 hcl
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
  have hn2 : U.IsCase2 := (designCase2_spec hn e₁ he₁ e₂ he₂).1 h2
  have hst := designOtherStored_complete hn hw (fun x => x.val.val)
    (sbipGraphStep9Dictionary I.1.2) eD hD hpoint (fun _ => rfl) (fun _ => rfl)
    hsize hcolors I.1.1 hbound e₂ he₂
  rw [← designLinkGraph_zero_hint (X := U)] at hst
  apply h.design_restricted_rep hd h6 hcl (U.blocks \ U.bigTwin) (fun _ _ => 0) _
    hst Set.diff_subset (designSelectC_complement hn e₁ he₁ e₂ he₂ hsel)
  have hnt : U.bigTwin ≠ U.blocks := fun hh => ht ((designTie_spec hn e₁ he₁ e₂ he₂).2 hh)
  obtain ⟨hsub,hcard,_,_⟩ := U.bigTwin_spec hn2 hnt
  have hc := Set.ncard_diff_add_ncard_of_subset hsub (Set.toFinite _)
  apply Or.inl
  change 10 * (U.blocks \ U.bigTwin).ncard ≤ 9 * U.n₂
  change (U.blocks \ U.bigTwin).ncard + U.bigTwin.ncard = U.n₂ at hc
  omega

end Rep

variable (φ : ↥X.car ≃ ↥Y.car) (hφ : φ ∈ (BipBlockInputs (Fin m)).IsoP X Y)

/-- Sec. 9.7: hinted restrictions of isomorphic Step 9 objects, to block
families and hints that correspond under the restriction of `φ`, are
isomorphic next inputs by that restriction. -/
theorem design_restricted_transport (hd' : ¬ AllClassesSmall Y)
    (h6 : ¬ Step6Imprimitive X) (hcl : Step9Clique X)
    (h6' : ¬ Step6Imprimitive Y) (hcl' : Step9Clique Y)
    {S : Set (Set ↥(step7Set X))} {c : Set ↥(step7Set X) → Set ↥(step7Set X) → ℕ}
    {S' : Set (Set ↥(step7Set Y))} {c' : Set ↥(step7Set Y) → Set ↥(step7Set Y) → ℕ}
    {g g' : RawSbipStored}
    (hadm : letI : Fintype ↥(step7Set X) := Fintype.ofFinite _
      letI : DecidableEq ↥(step7Set X) := Classical.decEq _
      ((step9DesignObj X hd h6 hcl).linkGraph.restrictBlkHint S c).IsThm922Input (alphaNew X))
    (hadm' : letI : Fintype ↥(step7Set Y) := Fintype.ofFinite _
      letI : DecidableEq ↥(step7Set Y) := Classical.decEq _
      ((step9DesignObj Y hd' h6' hcl').linkGraph.restrictBlkHint S' c').IsThm922Input (alphaNew Y))
    (hrep : letI : Fintype ↥(step7Set X) := Fintype.ofFinite _
      letI : DecidableEq ↥(step7Set X) := Classical.decEq _
      SbipNodeRep m (sbipNodeMakeChild (I,g))
        ⟨step7Set X,⟨((step9DesignObj X hd h6 hcl).linkGraph.restrictBlkHint S c,alphaNew X),
          twothirds_le_alphaNew hd,alphaNew_lt_one hd,hadm⟩⟩)
    (hrep' : letI : Fintype ↥(step7Set Y) := Fintype.ofFinite _
      letI : DecidableEq ↥(step7Set Y) := Classical.decEq _
      SbipNodeRep m (sbipNodeMakeChild (J,g'))
        ⟨step7Set Y,⟨((step9DesignObj Y hd' h6' hcl').linkGraph.restrictBlkHint S' c',alphaNew Y),
          twothirds_le_alphaNew hd',alphaNew_lt_one hd',hadm'⟩⟩)
    (hSS : ∀ B,step7Equiv hφ '' B ∈ S' ↔ B ∈ S)
    (hcc : ∀ A B,A ∈ (step9DesignObj X hd h6 hcl).linkGraph.blocks ∩ S →
      B ∈ (step9DesignObj X hd h6 hcl).linkGraph.blocks ∩ S →
      c' (step7Equiv hφ '' A) (step7Equiv hφ '' B) = c A B) :
    ∃ Z Z' : Pt (BipBlockInputs (Fin m)),
      SbipNodeRep m (sbipNodeMakeChild (I,g)) Z ∧
      SbipNodeRep m (sbipNodeMakeChild (J,g')) Z' ∧
      ∃ (hS : Z.car ⊆ X.car) (_hT : Z'.car ⊆ Y.car) (ψ : ↥Z.car ≃ ↥Z'.car),
        ψ ∈ (BipBlockInputs (Fin m)).IsoP Z Z' ∧
        ∀ x,(ψ x).val = (φ ⟨x.val,hS x.property⟩).val := by
  have hU : (step9DesignObj X hd h6 hcl).IsMorphOn (step9DesignObj Y hd' h6' hcl')
      (step7Equiv hφ) :=
    ⟨fun x => (step8Obj_isIsoTo hφ).part₁ x,fun B => (step8Obj_isIsoTo hφ).blocks B,
      fun A B => step8CaseColor_map hφ A B⟩
  exact ⟨_,_,hrep,hrep',step7Set_subset X,step7Set_subset Y,step7Equiv hφ,
    ⟨alphaNew_congr ⟨φ,hφ⟩,
      VColBipBlk.restrictBlkHint_isIsoTo (BlkCaseObj.linkGraph_isIsoTo hU) hSS hcc⟩,
    fun _ => rfl⟩

include h h' hφ hd

/-- Sec. 9.7, Case 2: each graph kept by the actual Cases 1–2 branch (the
tie, or `V₂ ∖ C` after Reduce-Part2-by-Color) has the same kind of kept
graph at an isomorphic parent, with isomorphic next inputs. -/
theorem design12_child_transport (h6 : ¬ Step6Imprimitive X) (hcl : Step9Clique X)
    (L : List ℕ) (o : RawAlignOutcome) (q : RawDesignGraph)
    (hout : designCase12 (sbipTurnCase I.1).2 = some ((L,o),some q)) :
    ∃ L' o' q',designCase12 (sbipTurnCase J.1).2 = some ((L',o'),some q') ∧
      ∃ Z Z' : Pt (BipBlockInputs (Fin m)),
        SbipNodeRep m (sbipNodeMakeChild (I,designStored ((I.1.1,sbipGraphStep9Dictionary I.1.2),q))) Z ∧
        SbipNodeRep m (sbipNodeMakeChild (J,designStored ((J.1.1,sbipGraphStep9Dictionary J.1.2),q'))) Z' ∧
        ∃ (hS : Z.car ⊆ X.car) (_hT : Z'.car ⊆ Y.car) (ψ : ↥Z.car ≃ ↥Z'.car),
          ψ ∈ (BipBlockInputs (Fin m)).IsoP Z Z' ∧
          ∀ x,(ψ x).val = (φ ⟨x.val,hS x.property⟩).val := by
  have hd' : ¬ AllClassesSmall Y := fun hh => hd
    (allClassesSmall_congr ⟨φ.symm,(BipBlockInputs (Fin m)).symm_mem hφ⟩ hh)
  have h6' : ¬ Step6Imprimitive Y := fun hh => h6
    (step6Imprimitive_congr ⟨φ.symm,(BipBlockInputs (Fin m)).symm_mem hφ⟩ hh)
  have hcl' := step9Clique_congr ⟨φ,hφ⟩ hcl
  let U := step9DesignObj X hd h6 hcl
  let U' := step9DesignObj Y hd' h6' hcl'
  have hU : U.IsMorphOn U' (step7Equiv hφ) :=
    ⟨fun x => (step8Obj_isIsoTo hφ).part₁ x,fun B => (step8Obj_isIsoTo hφ).blocks B,
      fun A B => step8CaseColor_map hφ A B⟩
  obtain ⟨h1e,h2e,hte,hce,hse,htwe,hbe⟩ := h.design_tests_transport h' φ hφ hd h6 hcl
  obtain ⟨h1,h2,htest⟩ := designCase12_graph_tests' _ L o q hout
  have h1' : designCase1 (sbipTurnCase J.1).2.1 ≠ true := h1e ▸ h1
  have h2' : designCase2 (sbipTurnCase J.1).2.1 = true := h2e ▸ h2
  rcases htest with ⟨ht,rfl⟩ | ⟨ht,hsel,rfl⟩
  · have ht' : designTie (sbipTurnCase J.1).2.1 = true := hte ▸ ht
    refine ⟨[],(none,none),designTieGraph (sbipTurnCase J.1).2.1,?_,?_⟩
    · simp only [designCase12,designCase2Exit,if_neg h1',if_pos h2',if_pos ht']
      rfl
    obtain ⟨hadm,hrep⟩ := h.design_tie_rep hd h6 hcl h1 ht
    obtain ⟨hadm',hrep'⟩ := h'.design_tie_rep hd' h6' hcl' h1' ht'
    apply design_restricted_transport hd φ hφ hd' h6 hcl h6' hcl' hadm hadm' hrep hrep'
    · exact fun B => hU.blocks B
    · intro A B _ _
      exact hU.twinHint_eq A B
  · have ht' : designTie (sbipTurnCase J.1).2.1 ≠ true := hte ▸ ht
    have hsel' : designSelectC (sbipTurnCase J.1).2.1 ≠ true := hce ▸ hsel
    refine ⟨[],(none,none),designOtherGraph (sbipTurnCase J.1).2.1,?_,?_⟩
    · simp only [designCase12,designCase2Exit,if_neg h1',if_pos h2',if_neg ht',if_neg hsel']
      rfl
    obtain ⟨hadm,hrep⟩ := h.design_other_rep hd h6 hcl h2 ht hsel
    obtain ⟨hadm',hrep'⟩ := h'.design_other_rep hd' h6' hcl' h2' ht' hsel'
    apply design_restricted_transport hd φ hφ hd' h6 hcl h6' hcl' hadm hadm' hrep hrep'
    · intro B
      exact and_congr (hU.blocks B) (not_congr (hU.mem_bigTwin_iff B))
    · intro A B _ _
      rfl

end SbipNodeRep
end Algo
