import Workspace.Algo.SplitUpccRun

/-! Correctness of the computed three-stage UPCC family. The final
existence theorem chooses the recursive RAM bounds before every input. -/
namespace Algo
open Babai RAM
open scoped Classical

structure UpccInputRep (m : ℕ) (r : RawUpcc)
    (C : (UPCCs (Fin m)).Obj Set.univ) : Prop where
  table : RawWL.WF m 2 r.1
  names : UpccNames (Equiv.Set.univ (Fin m)) r.1 C.1
  denominator : 0 < r.2.2
  lower : (2 : ℝ)/3 ≤ sbipAlphaValue r.2

theorem upccPartitionRep_valid {m : ℕ} {β : ℝ} {q : RawColPart}
    {s : Set (Fin m)} {P : ColoredPartition ↥s ℕ}
    (hr : UpccOutcomeRep (Equiv.Set.univ (Fin m)) (q,none) ⟨s,Sum.inl P⟩)
    (hs : s = Set.univ)
    (hP : @ColoredPartition.IsAlphaPartition _ _ P (Fintype.ofFinite _) β) :
    IsSplitOutcome β Set.univ (decAlignPartition m q) := by
  subst s
  letI : Fintype ↥(Set.univ : Set (Fin m)) := Fintype.ofFinite _
  obtain ⟨_,_,f,_,hc,hp⟩ := hr
  change ∀ x,labAt q.1 (f x).val.val = P.color x at hc
  refine ⟨rfl,?_⟩
  apply ColoredPartition.isAlphaPartition_of_kernel_rel P _ f
  · intro x y
    change P.color x = P.color y ↔ labAt q.1 (f x).val.val = labAt q.1 (f y).val.val
    rw [hc,hc]
  · intro x y
    change P.part x y ↔ cellOf q (f x).val.val = cellOf q (f y).val.val
    constructor
    · intro hxy
      apply Prod.ext
      · change labAt q.1 _ = labAt q.1 _
        rw [hc,hc]
        exact P.part_le_color hxy
      · exact (hp x y).2 hxy
    · intro hxy
      exact (hp x y).1 (congrArg Prod.snd hxy)
  · exact hP

def BipInputRunGood (c t d : ℕ) : Prop :=
  ∀ m r (X : Pt (BipInputs (Fin m))),BipInputRep m r X →
    ∃ A,bipInputRun c t d r = some A ∧ (∃ o,o ∈ A) ∧
      ∀ o ∈ A,∃ Z,sbipDecodeNamed m r.1.2.2.1 o = some Z ∧
        IsSplitOutcome (BipInputs.alpha X) (BipInputs.V₁ X) Z

/-- Every graph outcome of Lemma 9.3.1 supplies the actual singleton
input, including a positive threshold denominator. -/
theorem upccSplitBipInput_rep {m : ℕ} {r : RawUpcc} {q : RawColPart}
    {ab : ℕ × ℕ} {g : RawUpccBip} {s : Set (Fin m)}
    {Y : (BipInputs (Fin m)).Obj s}
    (hd : r.1.1.length = m)
    (hr : UpccOutcomeRep (Equiv.Set.univ (Fin m)) (q,some (ab,g)) ⟨s,Sum.inr Y⟩) :
    BipInputRep m (upccSplitBipInput ((ab,g),(r,(q,some (ab,g))))) ⟨s,Y⟩ := by
  obtain ⟨_,_,ht,hg,ha⟩ := hr
  refine ⟨hd,hg,ha,?_⟩
  change 0 < ab.2
  by_contra hn
  have hz : ab.2 = 0 := by omega
  have hlo := Y.2.1
  rw [hz,Nat.cast_zero,div_zero] at ha
  linarith

theorem upccSplitBranch_valid {c t d m : ℕ} (hsolver : BipInputRunGood c t d)
    {r : RawUpcc} {C : (UPCCs (Fin m)).Obj Set.univ} (h : UpccInputRep m r C)
    {q : RawUpccOutcome} {Z : Pt (Cat.sum (ColoredPartitions (Fin m) ℕ) (BipInputs (Fin m)))}
    (hr : UpccOutcomeRep (Equiv.Set.univ (Fin m)) q Z)
    (hz : IsUPCCToBipOutcome (sbipAlphaValue r.2) ⟨Set.univ,C⟩ Z) :
    (∃ o,o ∈ upccSplitBranch c t d (r,q)) ∧
      ∀ o ∈ upccSplitBranch c t d (r,q),∃ O,decAlignOutcome m o = some O ∧
        IsSplitOutcome (sbipAlphaValue r.2) Set.univ O := by
  have hd : r.1.1.length = m := card_eq_length_dom h.table
  rcases q with ⟨q,qb⟩
  rcases Z with ⟨s,P|Y⟩
  · cases qb with
    | some bg => simp [UpccOutcomeRep] at hr
    | none =>
      have hp := upccPartitionRep_valid hr hz.1 hz.2
      refine ⟨⟨rawAlignPartition q,by simp [upccSplitBranch]⟩,?_⟩
      intro o ho
      have he : o = rawAlignPartition q := by simpa [upccSplitBranch] using ho
      subst o
      exact ⟨_,decAlignOutcome_partition m q,hp⟩
  · cases qb with
    | none => simp [UpccOutcomeRep] at hr
    | some bg =>
      rcases bg with ⟨ab,g⟩
      let I := upccSplitBipInput ((ab,g),(r,(q,some (ab,g))))
      have hI : BipInputRep m I ⟨s,Y⟩ := upccSplitBipInput_rep hd hr
      obtain ⟨A,hA,hne,hgood⟩ := hsolver m I ⟨s,Y⟩ hI
      have he : upccSplitBranch c t d (r,(q,some (ab,g))) =
          A.map (fun o => splitFullLift ((r.1.1,g.1),o)) := by
        simp only [upccSplitBranch,Option.elim_some,upccSplitBipAnswers]
        change ((bipInputRun c t d I).getD []).map
          (fun o => splitFullLift ((r.1.1,g.1),o)) = _
        rw [hA,Option.getD_some]
      rw [he]
      refine ⟨?_,?_⟩
      · obtain ⟨o,ho⟩ := hne
        exact ⟨_,List.mem_map_of_mem ho⟩
      · intro o ho
        obtain ⟨p,hp,rfl⟩ := List.mem_map.1 ho
        obtain ⟨O,hdec,hO⟩ := hgood p hp
        have hs : winSet m g.1 = BipInputs.V₁ ⟨s,Y⟩ := hI.node.point_set
        have hcard : (BipInputs.V₁ (⟨s,Y⟩ : Pt (BipInputs (Fin m)))).ncard =
            Y.1.1.V₁.ncard := Set.ncard_image_of_injective _ Subtype.val_injective
        have hb : 1/2 ≤ sbipAlphaValue r.2 := by have hh := h.lower; linarith
        have hbal : Y.1.2 * ((winSet m g.1).ncard : ℝ) = sbipAlphaValue r.2 * m := by
          rw [hs,hcard]
          simpa only [BipInputs.alpha,Set.ncard_univ,Nat.card_fin] using hz.2.2.2.2
        exact splitFullLift_valid r.1.1 g.1 hd hI.node.left_nodup hI.node.point_lt
          hz.2.2.2.1 hb hbal hdec (by rw [hs]; exact hO)

theorem upccSplitVersion_valid {c t d m : ℕ} (hsolver : BipInputRunGood c t d)
    {r : RawUpcc} {C : (UPCCs (Fin m)).Obj Set.univ} (h : UpccInputRep m r C)
    {i : ℕ} (hi : i < m) :
    (∃ o,o ∈ upccSplitVersion c t d (r,i)) ∧
      ∀ o ∈ upccSplitVersion c t d (r,i),∃ O,decAlignOutcome m o = some O ∧
        IsSplitOutcome (sbipAlphaValue r.2) Set.univ O := by
  have hi' : i < Upcc.widthF r := by
    simpa only [Upcc.widthF,card_eq_length_dom h.table] using hi
  obtain ⟨Z,hr,hz⟩ := Upcc.versionF_spec_index (⟨Set.univ,C⟩ : Pt (UPCCs (Fin m)))
    h.table (Equiv.Set.univ (Fin m)) h.names h.denominator h.lower hi'
  exact upccSplitBranch_valid hsolver h hr hz

/-- One RAM family implements the three printed UPCC stages, with fixed
quasipolynomial time and storage exponents and no supplied solver premise. -/
theorem exists_upccSplitFamily_valid (c : ℕ) :
    ∃ t d,QuasiFun (upccSplitFamily c t d) ∧
      ∀ m r (C : (UPCCs (Fin m)).Obj Set.univ),UpccInputRep m r C →
        (∃ o,o ∈ upccSplitFamily c t d r) ∧
        ∀ o ∈ upccSplitFamily c t d r,∃ O,decAlignOutcome m o = some O ∧
          IsSplitOutcome (sbipAlphaValue r.2) Set.univ O := by
  obtain ⟨t,d,_,hsolver⟩ := exists_bipInputRun_valid c
  refine ⟨t,d,quasiFun_upccSplitFamily c t d,?_⟩
  intro m r C h
  have hd := card_eq_length_dom h.table
  have htwo : 2 ≤ m := by
    simpa only [Set.ncard_univ,Nat.card_fin] using upcc_two_le_ncard C.2
  constructor
  · obtain ⟨o,ho⟩ := (upccSplitVersion_valid hsolver h (i := 0) (by omega)).1
    exact ⟨o,List.mem_flatMap.2 ⟨0,List.mem_range.2 (by omega),ho⟩⟩
  · intro o ho
    obtain ⟨i,hi,ho⟩ := List.mem_flatMap.1 ho
    have him : i < m := by simpa only [List.mem_range,hd] using hi
    exact (upccSplitVersion_valid hsolver h him).2 o ho

end Algo
