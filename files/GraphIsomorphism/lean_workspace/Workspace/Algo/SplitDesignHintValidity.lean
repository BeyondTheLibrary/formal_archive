import Workspace.Algo.SplitDesignCase3Defect
import Workspace.Algo.SplitEquipValidity

/-! The stored hint is read on the actual family of blocks. Transporting
its coherent configuration proves the hint condition used by the next turn. -/
namespace Algo
open Babai RAM

section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {X : BlkDesignObj s} {r : RawUpccCase}
    (e₂ : ↥X.blocks ≃ Fin r.2.2.length)

open scoped Classical in
noncomputable def designReadMathHint (o : RawDesignReadOut) (A B : Set ↥s) : ℕ :=
  if hA : A ∈ X.blocks then if hB : B ∈ X.blocks then
    designReadHintAt (o,(e₂ ⟨A,hA⟩,e₂ ⟨B,hB⟩)) else 0 else 0

theorem designReadMathHint_on (o : RawDesignReadOut) (B C : ↥X.blocks) :
    designReadMathHint e₂ o B.val C.val = designReadHintAt (o,(e₂ B,e₂ C)) := by
  simp [designReadMathHint,B.property,C.property]

theorem designReadFirstPositionEquiv_exists (o : RawDesignReadOut)
    (hnd : (designReadFirst o).Nodup) (hL : ∀ i ∈ designReadFirst o, i < r.2.2.length) :
    ∃ e : ↥(designReadFirstSet e₂ o) ≃ Fin (designReadFirst o).length,
      ∀ B, (designReadFirst o)[(e B).val] =
        (e₂ ⟨B.val,designReadFirstSet_sub e₂ o B.property⟩).val := by
  apply splitNameEquiv_exists
    (fun B : ↥(designReadFirstSet e₂ o) =>
      (e₂ ⟨B.val,designReadFirstSet_sub e₂ o B.property⟩).val)
    (fun B C hh => Subtype.ext
      (congrArg (fun D : ↥X.blocks => D.val) (e₂.injective (Fin.ext hh)))) _ hnd
  intro i
  constructor
  · intro hi
    let B := e₂.symm ⟨i,hL i hi⟩
    have hB : B.val ∈ designReadFirstSet e₂ o := (designReadFirstSet_mem e₂ o B).2 (by
      simpa only [B,Equiv.apply_symm_apply] using hi)
    exact ⟨⟨B.val,hB⟩,congrArg Fin.val (e₂.apply_symm_apply _)⟩
  · rintro ⟨B,rfl⟩
    exact (designReadFirstSet_mem e₂ o _).1 B.property

theorem designReadFirstSet_ncard (o : RawDesignReadOut)
    (hnd : (designReadFirst o).Nodup) (hL : ∀ i ∈ designReadFirst o, i < r.2.2.length) :
    (designReadFirstSet e₂ o).ncard = (designReadFirst o).length := by
  obtain ⟨e,_⟩ := designReadFirstPositionEquiv_exists e₂ o hnd hL
  simpa only [Nat.card_coe_set_eq,Nat.card_fin] using Nat.card_congr e

open scoped Classical in
theorem designReadFirst_hasHint {V : Type} (o : RawDesignReadOut)
    (e : ↥(designReadFirstSet e₂ o) ≃ V) (Z : PartitionStructure V)
    (hco : Z.IsCoherent) (hhom : Z.IsHomogeneous) (hrank : 3 ≤ Z.rank)
    (hc : ∀ B C : ↥(designReadFirstSet e₂ o),
      designReadHintAt (o,(e₂ ⟨B.val,designReadFirstSet_sub e₂ o B.property⟩,
        e₂ ⟨C.val,designReadFirstSet_sub e₂ o C.property⟩)) = Z.natColor (e B) (e C)) :
    letI : Fintype ↥s := Fintype.ofFinite _
    letI : DecidableEq ↥s := Classical.decEq _
    (X.linkGraph.restrictBlkHint (designReadFirstSet e₂ o) (designReadMathHint e₂ o)).HasHint := by
  classical
  letI : Fintype ↥s := Fintype.ofFinite _
  letI : DecidableEq ↥s := Classical.decEq _
  have hb : (X.linkGraph.restrictBlkHint (designReadFirstSet e₂ o)
      (designReadMathHint e₂ o)).blocks = designReadFirstSet e₂ o :=
    Set.inter_eq_self_of_subset_right (designReadFirstSet_sub e₂ o)
  let d := (Equiv.setCongr hb).trans e
  refine VColBipBlk.hasHint_of_structure (Z.transport d.symm)
    (PartitionStructure.transport_isCoherent _ hco)
    (PartitionStructure.transport_isHomogeneous _ hhom) hrank ?_
  intro B C
  rw [VColBipBlk.restrictBlkHint_h B.property C.property]
  rw [designReadMathHint_on e₂ o ⟨B.val,B.property.1⟩ ⟨C.val,C.property.1⟩]
  exact hc ⟨B.val,B.property.2⟩ ⟨C.val,C.property.2⟩

open scoped Classical in
theorem designReadUpcc_hasHint (l : List ℕ) (q : RawConfig) (hnd : l.Nodup)
    (hL : ∀ i ∈ l, i < r.2.2.length) (Z : PartitionStructure (Fin l.length))
    (hco : Z.IsCoherent) (hu : Z.IsUniprimitive)
    (hc : ∀ i j : Fin l.length, binColor (q,(i,j)) = Z.natColor i j) :
    letI : Fintype ↥s := Fintype.ofFinite _
    letI : DecidableEq ↥s := Classical.decEq _
    (X.linkGraph.restrictBlkHint (designReadFirstSet e₂ (none,l,some q))
      (designReadMathHint e₂ (none,l,some q))).HasHint := by
  obtain ⟨e,he⟩ := designReadFirstPositionEquiv_exists e₂ (none,l,some q) hnd hL
  obtain ⟨hhom,hrank⟩ := PartitionStructure.isHomogeneous_and_rank_of_isUniprimitive hu
  apply designReadFirst_hasHint e₂ (none,l,some q) e Z hco hhom hrank
  intro B C
  change designUpccHintAt ((l,some q),(_,_)) = _
  rw [← he B,← he C]
  exact (designUpccHintAt_get hnd q (e B) (e C)).trans (hc (e B) (e C))

open scoped Classical in
theorem designReadPartition_hasHint (P : RawColPart) (hlen : P.1.length = r.2.2.length)
    (hP : (decColPartition P.1.length P).IsAlphaPartition (3 / 4))
    (hn : 4 ≤ P.1.length)
    (hbig : 3 * r.2.2.length < 4 * (designReadFirstSet e₂ (designReadPartitionExit P)).ncard) :
    letI : Fintype ↥s := Fintype.ofFinite _
    letI : DecidableEq ↥s := Classical.decEq _
    (X.linkGraph.restrictBlkHint (designReadFirstSet e₂ (designReadPartitionExit P))
      (designReadMathHint e₂ (designReadPartitionExit P))).HasHint := by
  have hL : ∀ i ∈ designReadFirst (designReadPartitionExit P), i < r.2.2.length := by
    intro i hi
    rw [← hlen]
    exact rawEquipFirst_lt hi
  obtain ⟨eB,heB⟩ := designReadFirstPositionEquiv_exists e₂ (designReadPartitionExit P)
    (rawEquipFirst_nodup P) hL
  obtain ⟨eP,heP⟩ := rawEquipFirstEquiv_exists P
  have hcount : (designReadFirstSet e₂ (designReadPartitionExit P)).ncard =
      (rawEquipFirst P).length := by
    simpa only [Nat.card_coe_set_eq,Nat.card_fin] using Nat.card_congr eB
  have hbig' : 3 * P.1.length < 4 * (rawEquipFirstSet P).ncard := by
    rw [rawEquipFirstSet_ncard,hlen]
    rwa [hcount] at hbig
  obtain ⟨Z,hco,hhom,hrank,hcol⟩ := rawEquipFirst_structure P hP hn hbig'
  let e := eB.trans eP.symm
  have hcoord (B : ↥(designReadFirstSet e₂ (designReadPartitionExit P))) :
      (e₂ ⟨B.val,designReadFirstSet_sub e₂ (designReadPartitionExit P) B.property⟩).val =
        (e B).val.val := by
    rw [← heB B]
    have hh := heP (eP.symm (eB B))
    simpa only [Equiv.apply_symm_apply] using hh
  apply designReadFirst_hasHint e₂ (designReadPartitionExit P) e Z hco hhom (by omega)
  intro B C
  change rawEquipHintAt (P,(_,_)) = _
  rw [hcoord B,hcoord C]
  exact hcol (e B) (e C)

end
end Algo
