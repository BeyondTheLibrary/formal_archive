import Workspace.Algo.DesignReadFamilyIso
import Workspace.Algo.SplitDesignReadNames
import Workspace.Algo.SplitEquipValidity
import Workspace.Algo.DesignReadWitness

/-! # Sec. 9.7, Case 3: the Design Lemma call moves with the block positions

Case 3 of Sec. 9.7 (v2.5) applies the Design Lemma to a relational structure on the blocks
and keeps, from each returned object, a first part of the blocks and a hint on pairs of blocks.
On the RAM the blocks are numbered by their positions in the stored list. Two isomorphic
parents may number their blocks differently; the isomorphism then acts on positions by a
permutation `π`. This file shows that the computed read family, its first parts and its hints
move along `π`, given that `π` is an isomorphism of the two stored relations.
-/
namespace Algo
open Babai RAM Equiv
open scoped Classical

/-- The compact Case 3 call, in block positions: every computed entry has a computed entry at
the other parent with outputs related by `π`. -/
theorem designCallReadFamily_iso {r r' : RawUpccCase} (hN : r'.2.2.length = r.2.2.length)
    (hk : (designCallWitness r').length = (designCallWitness r).length)
    (hb : r'.2.1.length = r.2.1.length)
    (hg : (designCallWitness r).length ≤ guardBound 3 r.2.1.length)
    (π : Perm (Fin r.2.2.length))
    (hf : π ∈ KAryRelStruct.Iso
      (decRel r.2.2.length (designCallWitness r).length (designCallRelations r))
      (decRel r.2.2.length (designCallWitness r).length (designCallRelations r')))
    {u : List ℕ × RawDesignReadOut} (hu : u ∈ designCallReadFamily r) :
    ∃ v ∈ designCallReadFamily r',DesignReadOutIso r.2.2.length π u.2 v.2 := by
  unfold designCallReadFamily designCallGIn at hu ⊢
  rw [designAmbientReadFamily_witness hk hb,hN]
  exact ambientDesignReadFamily_iso List.nodup_range (fun _ => List.mem_range)
    List.nodup_range (fun _ => List.mem_range) hg (by norm_num) hf hu

theorem designCallRead_partition_length (r : RawUpccCase) {xs : List ℕ} {o : RawDesignReadOut}
    (ho : (xs,o) ∈ designCallReadFamily r) {P : RawColPart} (hp : o.1 = some P) :
    P.1.length = r.2.2.length := by
  have hout := (designCallReadFamily_mem r xs o).1 ho |>.2
  subst hout
  have hw := designReadExit_partition_wf hp
  simpa [ambientDesignAt,designCallGIn] using hw.1

section Equip

theorem rawEquipColors_labAt {N : ℕ} {P : RawColPart} (hl : P.1.length = N) (j : Fin N) :
    labAt (rawEquipColors P) j =
      Nat.pair (labAt P.1 j) (((decColPartition N P).block j).ncard) := by
  subst hl
  exact rawEquipColors_spec P j

theorem mem_rawEquipFirst_iff {N : ℕ} {P : RawColPart} (hl : P.1.length = N) (i : Fin N) :
    i.val ∈ rawEquipFirst P ↔ i ∈ colorSplit (fun j : Fin N => labAt (rawEquipColors P) j) := by
  have hlen : (rawEquipColors P).length = N := by rw [rawEquipColors_length,hl]
  have hn : 0 < (rawEquipColors P).length := by rw [hlen]; exact Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  exact rawColorSplit_named hn _ (finCongr hlen.symm) (fun _ => rfl) i

/-- The first part of an equipartition is canonical. -/
theorem rawEquipFirst_iso {N : ℕ} {P P' : RawColPart} (hl : P.1.length = N)
    (hl' : P'.1.length = N) {π : Perm (Fin N)} (hc : ColPartIso N P P' π) (i : Fin N) :
    i.val ∈ rawEquipFirst P ↔ (π i).val ∈ rawEquipFirst P' := by
  have hblk : ∀ j,(decColPartition N P').block (π j) = π '' (decColPartition N P).block j := by
    intro j
    ext y
    constructor
    · intro hy
      refine ⟨π.symm y,?_,by simp⟩
      change cellOf P (π.symm y : ℕ) = cellOf P (j : ℕ)
      rw [hc.2]
      simpa using hy
    · rintro ⟨x,hx,rfl⟩
      change cellOf P' (π x : ℕ) = cellOf P' (π j : ℕ)
      exact (hc.2 x j).1 hx
  have hcol : ∀ j : Fin N,labAt (rawEquipColors P') (π j) = labAt (rawEquipColors P) j := by
    intro j
    rw [rawEquipColors_labAt hl',rawEquipColors_labAt hl,hblk,
      Set.ncard_image_of_injective _ π.injective,hc.1]
  rw [mem_rawEquipFirst_iff hl,mem_rawEquipFirst_iff hl',
    ← colorSplit_image (col := fun j : Fin N => labAt (rawEquipColors P) j)
      (col' := fun j : Fin N => labAt (rawEquipColors P') j) π hcol]
  exact ⟨fun h => ⟨i,h,rfl⟩,fun ⟨x,hx,hxi⟩ => (π.injective hxi) ▸ hx⟩

end Equip

section Read
variable {N : ℕ} {o o' : RawDesignReadOut} {π : Perm (Fin N)}

/-- The first part of the read output moves with `π`. -/
theorem designReadFirst_iso (hi : DesignReadOutIso N π o o')
    (hl : ∀ P,o.1 = some P → P.1.length = N) (hl' : ∀ P,o'.1 = some P → P.1.length = N)
    (i : Fin N) : i.val ∈ designReadFirst o ↔ (π i).val ∈ designReadFirst o' := by
  rcases hi with ⟨P,P',rfl,rfl,hc⟩ | ⟨L,L',q,q',rfl,rfl,hw,-⟩
  · exact rawEquipFirst_iso (hl P rfl) (hl' P' rfl) hc i
  · change i.val ∈ L ↔ (π i).val ∈ L'
    change i ∈ winSet N L ↔ π i ∈ winSet N L'
    rw [← hw]
    exact ⟨fun h => ⟨i,h,rfl⟩,fun ⟨x,hx,hxi⟩ => (π.injective hxi) ▸ hx⟩

/-- The hint of the read output moves with `π`. -/
theorem designReadHintAt_iso (hi : DesignReadOutIso N π o o')
    (hl : ∀ P,o.1 = some P → P.1.length = N) (hl' : ∀ P,o'.1 = some P → P.1.length = N)
    (i j : Fin N) :
    designReadHintAt (o',((π i).val,(π j).val)) = designReadHintAt (o,(i.val,j.val)) := by
  have hfirst := designReadFirst_iso hi hl hl'
  rcases hi with ⟨P,P',rfl,rfl,hc⟩ | ⟨L,L',q,q',rfl,rfl,hw,hq⟩
  · simp only [designReadHintAt,Option.elim_some,rawEquipHintAt]
    have hi' := hfirst i
    have hj' := hfirst j
    simp only [designReadFirst,Option.elim_some] at hi' hj'
    have hij : ((π i).val = (π j).val) ↔ (i.val = j.val) := by
      rw [← Fin.ext_iff,← Fin.ext_iff,π.injective.eq_iff]
    have hcell := hc.2 i j
    by_cases hA : i.val ∈ rawEquipFirst P ∧ j.val ∈ rawEquipFirst P
    · have hA' : (π i).val ∈ rawEquipFirst P' ∧ (π j).val ∈ rawEquipFirst P' :=
        ⟨hi'.1 hA.1,hj'.1 hA.2⟩
      simp only [hA,hA',decide_true,Bool.and_self,if_true,hij]
      by_cases he : i.val = j.val
      · simp [he]
      · simp only [he,if_false]
        by_cases hce : cellOf P i.val = cellOf P j.val
        · rw [if_pos hce,if_pos (hcell.1 hce)]
        · rw [if_neg hce,if_neg (fun h => hce (hcell.2 h))]
    · have hA' : ¬ ((π i).val ∈ rawEquipFirst P' ∧ (π j).val ∈ rawEquipFirst P') :=
        fun h => hA ⟨hi'.2 h.1,hj'.2 h.2⟩
      have e1 : (decide (i.val ∈ rawEquipFirst P) && decide (j.val ∈ rawEquipFirst P)) = false := by
        simpa using hA
      have e2 : (decide ((π i).val ∈ rawEquipFirst P') &&
          decide ((π j).val ∈ rawEquipFirst P')) = false := by simpa using hA'
      rw [e1,e2]
      rfl
  · simp only [designReadHintAt,Option.elim_none,designUpccHintAt,Option.elim_some]
    have hi' := hfirst i
    have hj' := hfirst j
    simp only [designReadFirst,Option.elim_none] at hi' hj'
    by_cases hA : i.val ∈ L ∧ j.val ∈ L
    · have hA' : (π i).val ∈ L' ∧ (π j).val ∈ L' := ⟨hi'.1 hA.1,hj'.1 hA.2⟩
      simp only [hA,hA',decide_true,Bool.and_self,if_true]
      exact hq i j hA.1 hA.2
    · have hA' : ¬ ((π i).val ∈ L' ∧ (π j).val ∈ L') := fun h => hA ⟨hi'.2 h.1,hj'.2 h.2⟩
      have e1 : (decide (i.val ∈ L) && decide (j.val ∈ L)) = false := by simpa using hA
      have e2 : (decide ((π i).val ∈ L') && decide ((π j).val ∈ L')) = false := by simpa using hA'
      rw [e1,e2]
      rfl

end Read
end Algo
