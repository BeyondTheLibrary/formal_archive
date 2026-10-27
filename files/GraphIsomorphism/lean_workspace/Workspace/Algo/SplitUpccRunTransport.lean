import Workspace.Algo.SplitBipRunCanonical
import Workspace.Algo.SplitUpccCanonicalSpec
import Workspace.Algo.SplitUpccRunSpec

/-! The outer UPCC routine transports the actual family. Its two inputs
may store vertices and tuple tables in independent orders. Exact decoding
of the individualized version connects it to the paper's canonical object. -/
namespace Algo
open Babai RAM
open scoped Classical

theorem upccPartitionRep_iso {m : ℕ} {q q' : RawColPart}
    {s s' : Set (Fin m)} {P : ColoredPartition ↥s ℕ} {P' : ColoredPartition ↥s' ℕ}
    (hr : UpccOutcomeRep (Equiv.Set.univ (Fin m)) (q,none) ⟨s,Sum.inl P⟩)
    (hr' : UpccOutcomeRep (Equiv.Set.univ (Fin m)) (q',none) ⟨s',Sum.inl P'⟩)
    (g : ↥s ≃ ↥s') (hg : g ∈ (ColoredPartitions (Fin m) ℕ).Iso P P')
    (π : Equiv.Perm (Fin m)) (hπ : ∀ x,(g x).val = π x.val) :
    RawSplitOutcomeIso m π (rawAlignPartition q) (rawAlignPartition q') := by
  obtain ⟨_,_,e,he,hc,hp⟩ := hr
  obtain ⟨_,_,e',he',hc',hp'⟩ := hr'
  have hcolor : ∀ x,labAt q.1 (e x).val.val = P.color x := hc
  have hcolor' : ∀ x,labAt q'.1 (e' x).val.val = P'.color x := hc'
  have hpart : ∀ x y,cellOf q (e x).val.val = cellOf q (e y).val.val ↔ P.part x y := by
    intro x y
    constructor
    · intro hh
      exact (hp x y).1 (congrArg Prod.snd hh)
    · intro hh
      exact Prod.ext (by rw [cellOf_fst,cellOf_fst,hcolor,hcolor]; exact P.part_le_color hh)
        ((hp x y).2 hh)
  have hpart' : ∀ x y,cellOf q' (e' x).val.val = cellOf q' (e' y).val.val ↔ P'.part x y := by
    intro x y
    constructor
    · intro hh
      exact (hp' x y).1 (congrArg Prod.snd hh)
    · intro hh
      exact Prod.ext (by rw [cellOf_fst,cellOf_fst,hcolor',hcolor']; exact P'.part_le_color hh)
        ((hp' x y).2 hh)
  refine ⟨_,_,rfl,rfl,e.symm.trans (g.trans e'),?_,?_,?_⟩
  · intro x
    change (e' (g (e.symm x))).val = π x.val
    rw [he',hπ,← he (e.symm x),Equiv.apply_symm_apply]
  · intro x
    obtain ⟨i,rfl⟩ := e.surjective x
    change labAt q'.1 (e' (g (e.symm (e i)))).val.val = labAt q.1 (e i).val.val
    rw [Equiv.symm_apply_apply,hcolor',hcolor,hg.1]
  · intro x y
    obtain ⟨i,rfl⟩ := e.surjective x
    obtain ⟨j,rfl⟩ := e.surjective y
    change cellOf q (e i).val.val = cellOf q (e j).val.val ↔
      cellOf q' (e' (g (e.symm (e i)))).val.val = cellOf q' (e' (g (e.symm (e j)))).val.val
    rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply,hpart,hpart',hg.2]

theorem upccSplitBranch_transport {c t d m : ℕ} (hsolver : BipInputRunCanonical c t d)
    {r r' : RawUpcc} (hd : r.1.1.length = m) (hd' : r'.1.1.length = m)
    {q q' : RawUpccOutcome}
    {Z Z' : Pt (Cat.sum (ColoredPartitions (Fin m) ℕ) (BipInputs (Fin m)))}
    (hr : UpccOutcomeRep (Equiv.Set.univ (Fin m)) q Z)
    (hr' : UpccOutcomeRep (Equiv.Set.univ (Fin m)) q' Z')
    (g : ↥Z.car ≃ ↥Z'.car)
    (hg : g ∈ (Cat.sum (ColoredPartitions (Fin m) ℕ) (BipInputs (Fin m))).IsoP Z Z')
    (π : Equiv.Perm (Fin m)) (hπ : ∀ x,(g x).val = π x.val)
    {o : RawAlignOutcome} (ho : o ∈ upccSplitBranch c t d (r,q)) :
    ∃ o' ∈ upccSplitBranch c t d (r',q'),RawSplitOutcomeIso m π o o' := by
  rcases q with ⟨qp,qb⟩
  rcases q' with ⟨qp',qb'⟩
  rcases Z with ⟨s,P|Y⟩ <;> rcases Z' with ⟨s',P'|Y'⟩
  · cases qb with
    | some bg => simp [UpccOutcomeRep] at hr
    | none =>
      cases qb' with
      | some bg' => simp [UpccOutcomeRep] at hr'
      | none =>
        have he : o = rawAlignPartition qp := by simpa [upccSplitBranch] using ho
        subst o
        exact ⟨rawAlignPartition qp',by simp [upccSplitBranch],
          upccPartitionRep_iso hr hr' g hg π hπ⟩
  · exact hg.elim
  · exact hg.elim
  · cases qb with
    | none => simp [UpccOutcomeRep] at hr
    | some bg =>
      cases qb' with
      | none => simp [UpccOutcomeRep] at hr'
      | some bg' =>
        rcases bg with ⟨ab,b⟩
        rcases bg' with ⟨ab',b'⟩
        let I := upccSplitBipInput ((ab,b),(r,(qp,some (ab,b))))
        let I' := upccSplitBipInput ((ab',b'),(r',(qp',some (ab',b'))))
        have hI : BipInputRep m I ⟨s,Y⟩ := upccSplitBipInput_rep hd hr
        have hI' : BipInputRep m I' ⟨s',Y'⟩ := upccSplitBipInput_rep hd' hr'
        change o ∈ ((bipInputRun c t d I).getD []).map
          (fun p => splitFullLift ((r.1.1,b.1),p)) at ho
        obtain ⟨p,hp,rfl⟩ := List.mem_map.1 ho
        obtain ⟨p',hp',O,O',hO,hO',hi⟩ := hsolver m I I' ⟨s,Y⟩ ⟨s',Y'⟩
          hI hI' g π hg hπ p hp
        refine ⟨splitFullLift ((r'.1.1,b'.1),p'),?_,?_⟩
        · exact List.mem_map_of_mem hp'
        · exact splitFullLift_iso r.1.1 r'.1.1 b.1 b'.1 hd hd'
            hI.node.left_nodup hI.node.point_lt hI'.node.left_nodup hI'.node.point_lt hO hO' hi

theorem upccSplitVersion_transport {c t d m : ℕ} (hsolver : BipInputRunCanonical c t d)
    {r r' : RawUpcc} {C C' : (UPCCs (Fin m)).Obj Set.univ}
    (h : UpccInputRep m r C) (h' : UpccInputRep m r' C')
    (ha : sbipAlphaValue r.2 = sbipAlphaValue r'.2)
    (φ : ↥(Set.univ : Set (Fin m)) ≃ ↥(Set.univ : Set (Fin m)))
    (hφ : φ ∈ (UPCCs (Fin m)).Iso C C')
    (π : Equiv.Perm (Fin m)) (hπ : ∀ x,(φ x).val = π x.val)
    (x : ↥(Set.univ : Set (Fin m))) {o : RawAlignOutcome}
    (ho : o ∈ upccSplitVersion c t d (r,x.val.val)) :
    ∃ o' ∈ upccSplitVersion c t d (r',(φ x).val.val),RawSplitOutcomeIso m π o o' := by
  have hr := Upcc.versionF_rep_exact (⟨Set.univ,C⟩ : Pt (UPCCs (Fin m))) h.table
    (Equiv.Set.univ (Fin m)) h.names h.denominator h.lower x
  have hr' := Upcc.versionF_rep_exact (⟨Set.univ,C'⟩ : Pt (UPCCs (Fin m))) h'.table
    (Equiv.Set.univ (Fin m)) h'.names h'.denominator h'.lower (φ x)
  change UpccOutcomeRep (Equiv.Set.univ (Fin m)) (Upcc.versionF (r',(φ x).val.val))
    ⟨(upccOutcome (sbipAlphaValue r'.2) C'.1 (φ x)).1.1,
      (upccOutcome (sbipAlphaValue r'.2) C'.1 (φ x)).2⟩ at hr'
  rw [← ha] at hr'
  obtain ⟨g,hg,hgi⟩ := upccOutcome_iso (sbipAlphaValue r.2) h.lower
    (X := ⟨Set.univ,C⟩) (Y := ⟨Set.univ,C'⟩) hφ x
  exact upccSplitBranch_transport hsolver (card_eq_length_dom h.table)
    (card_eq_length_dom h'.table) hr hr' g hgi π
    (fun z => (hg z).trans (hπ _)) ho

theorem upccSplitFamily_transport {c t d m : ℕ} (hsolver : BipInputRunCanonical c t d)
    {r r' : RawUpcc} {C C' : (UPCCs (Fin m)).Obj Set.univ}
    (h : UpccInputRep m r C) (h' : UpccInputRep m r' C')
    (ha : sbipAlphaValue r.2 = sbipAlphaValue r'.2)
    (φ : ↥(Set.univ : Set (Fin m)) ≃ ↥(Set.univ : Set (Fin m)))
    (hφ : φ ∈ (UPCCs (Fin m)).Iso C C')
    (π : Equiv.Perm (Fin m)) (hπ : ∀ x,(φ x).val = π x.val)
    {o : RawAlignOutcome} (ho : o ∈ upccSplitFamily c t d r) :
    ∃ o' ∈ upccSplitFamily c t d r',RawSplitOutcomeIso m π o o' := by
  obtain ⟨i,hi,ho⟩ := List.mem_flatMap.1 ho
  have hi' : i < m := by
    simpa only [card_eq_length_dom h.table] using List.mem_range.1 hi
  let x : ↥(Set.univ : Set (Fin m)) := ⟨⟨i,hi'⟩,Set.mem_univ _⟩
  obtain ⟨o',ho',hi⟩ := upccSplitVersion_transport hsolver h h' ha φ hφ π hπ x ho
  refine ⟨o',List.mem_flatMap.2 ⟨(φ x).val.val,?_,ho'⟩,hi⟩
  apply List.mem_range.2
  rw [card_eq_length_dom h'.table]
  exact (φ x).val.isLt

end Algo
