import Workspace.Algo.SplitBipNodeSize
import Workspace.Algo.SplitBipTurnEarly

/-! Every recursive graph comes from the fresh Step 9 case. The whole
stored family may have quasipolynomial size. Its input has one polynomial
bound in the original input size, even after many recursive turns. -/
namespace Algo
open RAM Babai

def sbipAlphaEnvelope (n : ℕ) : ℕ := 2*n + (2*n+1)*(2*n)

def sbipCaseEnvelope (n : ℕ) : ℕ :=
  8*n + 8*sbipDictionaryBound n + 4*strBound n + 4*sbipCaseSizeBound (2*n) +
    8*sbipAlphaEnvelope n + 16*n + 32

theorem polyBound_sbipAlphaEnvelope : PolyBound sbipAlphaEnvelope := by
  have h := (polyBound_const 2).mul polyBound_id
  exact h.add ((h.add (polyBound_const 1)).mul h)

theorem mono_sbipAlphaEnvelope : Monotone sbipAlphaEnvelope := by
  intro a b hab
  unfold sbipAlphaEnvelope
  gcongr

theorem sbipNode_witness_size (I : RawSbipNode) : Enc.size I.1.1 ≤ Enc.size I :=
  (Combine.size_fst_le I.1.1 I.1.2).trans (Combine.size_fst_le I.1 I.2)

theorem sbipNode_alpha_size_le (I : RawSbipNode) : Enc.size I.1.2.2 ≤ Enc.size I :=
  (Combine.size_snd_le I.1.2.1 I.1.2.2).trans
    ((Combine.size_snd_le I.1.1 I.1.2).trans (Combine.size_fst_le I.1 I.2))

theorem SbipNodeRep.initial_resources {m : ℕ} {I : RawSbipNode}
    {X : Pt (BipBlockInputs (Fin m))} (h : SbipNodeRep m I X) :
    m ≤ Enc.size I ∧ Enc.size I.1.1 ≤ Enc.size I ∧
      sbipNodeAlphaPotential m I ≤ sbipAlphaEnvelope (Enc.size I) := by
  have hw := sbipNode_witness_size I
  have hm : m ≤ Enc.size I := by
    rw [← h.ground]
    exact (length_le_size I.1.1).trans hw
  refine ⟨hm,hw,?_⟩
  have ha := (Combine.size_fst_le I.1.2.2.1 I.1.2.2.2).trans (sbipNode_alpha_size_le I)
  have hb := (Combine.size_snd_le I.1.2.2.1 I.1.2.2.2).trans (sbipNode_alpha_size_le I)
  rw [Small.size_nat] at ha hb
  have hm' : sbipNodeMeasure I ≤ 2 * Enc.size I + 1 := by
    have hh := h.blocks_le.trans hm
    have hi := sbipNodeBit_le I
    unfold sbipNodeMeasure
    omega
  have hh := Nat.mul_le_mul hm' (Nat.mul_le_mul_left 2 ((size_le_self m).trans hm))
  unfold sbipNodeAlphaPotential sbipNodeAlphaBits sbipAlphaEnvelope
  omega

theorem polyBound_sbipCaseEnvelope : PolyBound sbipCaseEnvelope := by
  have hs : PolyBound strBound := (polyBound_const 1).add
    (polyBound_id.mul (((polyBound_const 2).mul (polyBound_id.add (polyBound_const 2))).add
      (polyBound_const 1)))
  have hbase := ((((polyBound_const 8).mul polyBound_id).add
    ((polyBound_const 8).mul polyBound_sbipDictionaryBound)).add
    ((polyBound_const 4).mul hs)).add ((polyBound_const 4).mul
      (polyBound_sbipCaseSizeBound.comp ((polyBound_const 2).mul polyBound_id)))
  exact ((hbase.add ((polyBound_const 8).mul polyBound_sbipAlphaEnvelope)).add
    ((polyBound_const 16).mul polyBound_id)).add (polyBound_const 32)

theorem SbipNodeRep.case_envelope {m n : ℕ} {I : RawSbipNode}
    {X : Pt (BipBlockInputs (Fin m))} (h : SbipNodeRep m I X)
    (hm : m ≤ n) (hw : Enc.size I.1.1 ≤ n)
    (ha : sbipNodeAlphaPotential m I ≤ sbipAlphaEnvelope n) (hd : ¬ AllClassesSmall X) :
    Enc.size (sbipTurnCase I.1) ≤ sbipCaseEnvelope n := by
  have hh := h.case_total_size hd
  have hdict : sbipDictionaryBound m ≤ sbipDictionaryBound n := by
    unfold sbipDictionaryBound strBound
    gcongr
  have hstr : strBound m ≤ strBound n := by unfold strBound; gcongr
  have hc := mono_sbipCaseSizeBound (Nat.mul_le_mul_left 2 hm)
  unfold sbipCaseEnvelope
  omega

theorem sbipTurnChildren_partitions (L : List RawColPart) :
    sbipTurnChildren (L.map sbipTurnPartition) = [] := by
  simp [sbipTurnChildren,sbipTurnIsReturn,sbipTurnPartition,sbipTurnReturn,List.filter_map]

theorem sbipNodeGraphs_cases_or_empty (c : ℕ) (I : RawSbipNode) :
    sbipNodeGraphs c I = [] ∨
      ((sbipGraphSteps35 (sbipTurnGraphInput I.1)).2 ≠ none ∧
        sbipNodeGraphs c I = sbipTurnChildren (sbipTurnCases (sbipTurnCase I.1))) := by
  unfold sbipNodeGraphs sbipTurn
  split
  · exact Or.inl (sbipTurnChildren_partitions _)
  · split
    · exact Or.inl (sbipTurnChildren_partitions _)
    · unfold sbipTurnLarge
      cases he : (sbipGraphSteps35 (sbipTurnGraphInput I.1)).2 with
      | none =>
        left
        simp [sbipTurnChildren,sbipTurnPartition,sbipTurnReturn,sbipTurnIsReturn]
      | some a =>
        simp only [Option.elim_some]
        unfold sbipTurnAfter35
        split
        · left
          simp [sbipTurnChildren,sbipTurnPartition,sbipTurnReturn,sbipTurnIsReturn]
        · exact Or.inr ⟨by simp,rfl⟩

theorem exists_sbipNodeGraphs_bound :
    ∃ K : ℕ → ℕ, QuasiPolyBound K ∧ Monotone K ∧
      ∀ (c n m : ℕ) (I : RawSbipNode) (X : Pt (BipBlockInputs (Fin m))),
        SbipNodeRep m I X → m ≤ n → Enc.size I.1.1 ≤ n →
        sbipNodeAlphaPotential m I ≤ sbipAlphaEnvelope n →
        Enc.size (sbipNodeGraphs c I) ≤ K n := by
  obtain ⟨K,hK,hmK,hk⟩ := (quasiFun_sbipTurnCases.comp_poly
    polyFun_sbipTurnChildren).size.exists_quasiPolyBound
  obtain ⟨S,d,hs⟩ := polyBound_sbipCaseEnvelope
  refine ⟨fun n => K (S * (n+1)^d) + 1,?_,?_,?_⟩
  · exact (hK.comp_poly (polyBound_witness S d)).add ((polyBound_const 1).quasiPoly)
  · intro a b hab
    exact Nat.add_le_add_right (hmK _ _ (polyBound_witness_mono S d hab)) 1
  · intro c n m I X h hm hw ha
    rcases sbipNodeGraphs_cases_or_empty c I with he | ⟨hd,he⟩
    · rw [he,size_nil]
      change 1 ≤ K (S * (n+1)^d) + 1
      omega
    · rw [he]
      exact ((hk _).trans (hmK _ _ ((h.case_envelope hm hw ha
        (h.dominant_of_continue hd)).trans (hs n)))).trans (Nat.le_add_right _ _)

theorem SbipNodeRep.makeChild_size {m n : ℕ} {I : RawSbipNode}
    {X : Pt (BipBlockInputs (Fin m))} (h : SbipNodeRep m I X)
    (hm : m ≤ n) (hw : Enc.size I.1.1 ≤ n)
    (ha : sbipNodeAlphaPotential m I ≤ sbipAlphaEnvelope n) (g : RawSbipStored) :
    Enc.size (sbipNodeMakeChild (I,g)) ≤
      256 * (n + Enc.size g + sbipAlphaEnvelope n + 1) := by
  let J := sbipNodeMakeChild (I,g)
  have hbit : Enc.size J.2 ≤ 3 := by
    dsimp [J,sbipNodeMakeChild]
    split <;> norm_num [Small.size_nat]
  have h1 := Combine.size_pair_le J.1.2.1 J.1.2.2
  have h2 := Combine.size_pair_le J.1.1 J.1.2
  have h3 := Combine.size_pair_le J.1 J.2
  change Enc.size J.1.2 ≤ 2*Enc.size g + 2*Enc.size (sbipTurnCase I.1).2.2 at h1
  change Enc.size J.1 ≤ 2*Enc.size I.1.1 + 2*Enc.size J.1.2 at h2
  change Enc.size J ≤ 2*Enc.size J.1 + 2*Enc.size J.2 at h3
  have hα := h.case_alpha_size
  change Enc.size J ≤ _
  omega

theorem exists_sbipNodeChild_bound :
    ∃ K : ℕ → ℕ, QuasiPolyBound K ∧ Monotone K ∧
      ∀ (c n m : ℕ) (I : RawSbipNode) (X : Pt (BipBlockInputs (Fin m))),
        SbipNodeRep m I X → m ≤ n → Enc.size I.1.1 ≤ n →
        sbipNodeAlphaPotential m I ≤ sbipAlphaEnvelope n →
        ∀ g ∈ sbipNodeGraphs c I, Enc.size (sbipNodeMakeChild (I,g)) ≤ K n := by
  obtain ⟨K,hK,hmK,hk⟩ := exists_sbipNodeGraphs_bound
  refine ⟨fun n => 256 * (n + K n + sbipAlphaEnvelope n + 1),?_,?_,?_⟩
  · exact ((polyBound_const 256).quasiPoly).mul
      (((polyBound_id.quasiPoly.add hK).add polyBound_sbipAlphaEnvelope.quasiPoly).add
        (polyBound_const 1).quasiPoly)
  · intro a b hab
    exact Nat.mul_le_mul_left 256 (Nat.add_le_add_right
      (Nat.add_le_add (Nat.add_le_add hab (hmK hab)) (mono_sbipAlphaEnvelope hab)) 1)
  · intro c n m I X h hm hw ha g hg
    exact (h.makeChild_size hm hw ha g).trans (Nat.mul_le_mul_left 256
      (by have hh := (size_mem_le hg).trans (hk c n m I X h hm hw ha); omega))

end Algo
