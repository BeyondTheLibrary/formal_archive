import Workspace.Algo.AggNodeGuideTuple

/-! # The computed relation is the paper's tuple equivalence

A local morphism maps an ordering of its source support to an ordering of
its target support. Conversely those two orderings define the needed
bijection. This identifies the coset test with the Local guide proof's
relation, including its reflexivity, symmetry, and transitivity.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Classical

section Abstract
variable {n m t : ℕ} {G : Subgroup (Perm (Fin n))} {ϕ : G →* Perm (Fin m)}
  {I : Type*} {y : I → (Fin n → ℕ)}
  (hset : LocalCertSetting G ϕ) (ht : LargeK t (Nat.card (Fin n)))
  (htm : 10*t ≤ Nat.card (Fin m)) [Nonempty (Fin n)]

theorem aggnLocalGuide_equiv_iff {i j : I}
    (u : Fin t ↪ ↥(fixedGamma ϕ (y i) t)) (v : Fin t ↪ ↥(fixedGamma ϕ (y j) t)) :
    (localGuideData ϕ t y hset ht htm).Equiv' ⟨i,u⟩ ⟨j,v⟩ ↔
      ∃ σ : G,σ.val ∈ compareIso ϕ (y i) (y j)
        (Subtype.val '' Set.range u) (Subtype.val '' Set.range v) ∧
        ∀ a : Fin t,ϕ σ (u a).val = (v a).val := by
  constructor
  · rintro ⟨α,⟨σ,hσ,hα⟩,hc⟩
    refine ⟨σ,hσ,?_⟩
    intro a
    exact (hα ⟨u a,⟨a,rfl⟩⟩).symm.trans (congrArg Subtype.val (hc a))
  · rintro ⟨σ,hσ,hcoords⟩
    let eu := Equiv.ofInjective u u.injective
    let ev := Equiv.ofInjective v v.injective
    let α := eu.symm.trans ev
    have hα : ∀ a : ↥(Set.range u),(α a).val.val = ϕ σ a.val.val := by
      rintro ⟨a,⟨k,rfl⟩⟩
      have he : α ⟨u k,⟨k,rfl⟩⟩ = ⟨v k,⟨k,rfl⟩⟩ := by
        change ev (eu.symm (eu k)) = ev k
        rw [Equiv.symm_apply_apply]
      rw [he]
      exact (hcoords k).symm
    refine ⟨α,⟨σ,hσ,hα⟩,?_⟩
    intro a
    change (ev (eu.symm (eu a))).val = v a
    rw [Equiv.symm_apply_apply]
    rfl

end Abstract

/-- A mathematical ordering's raw coordinate list. Only specifications use this name. -/
def aggnTupleName {m t : ℕ} (u : Fin t → Fin m) : List ℕ := List.ofFn fun i => (u i).val

theorem aggnTupleName_length {m t : ℕ} (u : Fin t → Fin m) : (aggnTupleName u).length = t :=
  List.length_ofFn

theorem aggnTupleName_lt {m t : ℕ} (u : Fin t → Fin m) :
    ∀ a ∈ aggnTupleName u,a < m := by
  intro a ha
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
  exact (u i).isLt

theorem aggnTupleName_nodup {m t : ℕ} {u : Fin t → Fin m} (hu : Function.Injective u) :
    (aggnTupleName u).Nodup :=
  List.nodup_ofFn.mpr (Fin.val_injective.comp hu)

theorem aggnTupleName_support {m t : ℕ} (u : Fin t → Fin m) :
    winSet m (aggnTupleName u) = Set.range u := by
  ext a
  simp only [winSet,aggnTupleName,Set.mem_setOf_eq,List.mem_ofFn,Set.mem_range]
  exact exists_congr fun i => Fin.ext_iff.symm

theorem aggnTupleName_point {m t : ℕ} (u : Fin t → Fin m) (i : Fin (aggnTupleName u).length) :
    (winPt m (aggnTupleName u) (aggnTupleName_lt u) i).val =
      u (i.cast (aggnTupleName_length u)) := by
  apply Fin.ext
  change (List.ofFn fun i => (u i).val)[i.val] = _
  rw [List.getElem_ofFn]
  rfl

theorem aggnTupleName_coords {m t : ℕ} (u v : Fin t → Fin m) (π : Perm (Fin m)) :
    (∀ i : Fin (aggnTupleName u).length,
      π (winPt m (aggnTupleName u) (aggnTupleName_lt u) i).val =
        (winPt m (aggnTupleName v) (aggnTupleName_lt v)
          (i.cast ((aggnTupleName_length u).trans (aggnTupleName_length v).symm))).val) ↔
      ∀ i : Fin t,π (u i) = v i := by
  simp only [aggnTupleName_point]
  constructor
  · intro h i
    exact h (i.cast (aggnTupleName_length u).symm)
  · intro h i
    exact h (i.cast (aggnTupleName_length u))

/-- Equality of guide classes is decided by the completed comparison table. -/
theorem aggnGuideTuple_class_spec {c n m : ℕ} {C : AggnPhaseCtx} {tbl : RawAggCompareTable}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)} (hC : AggnPhaseCtxWF c n m C ϕ)
    (htbl : AggnCompareTableFor c ϕ tbl)
    (hset : LocalCertSetting (decGroup n C.1.1.2) ϕ)
    (ht : LargeK C.2.2.2.length (Nat.card (Fin n))) (htm : 10*C.2.2.2.length ≤ m)
    [Nonempty (Fin n)]
    (b : Bool)
    (u : Fin C.2.2.2.length ↪ ↥(fixedGamma ϕ (decStrN n C.2.1) C.2.2.2.length))
    (v : Fin C.2.2.2.length ↪ ↥(fixedGamma ϕ
      (cond b (decStrN n C.2.2.1) (decStrN n C.2.1)) C.2.2.2.length)) :
    aggnGuideTuple ((C.1,tbl),(b,aggnTupleName (fun i => (u i).val),
      aggnTupleName (fun i => (v i).val))) = true ↔
      (localGuideData ϕ C.2.2.2.length
        (fun a : Bool => cond a (decStrN n C.2.2.1) (decStrN n C.2.1))
        hset ht (by simpa only [Nat.card_fin] using htm)).mkClass ⟨false,u⟩ =
      (localGuideData ϕ C.2.2.2.length
        (fun a : Bool => cond a (decStrN n C.2.2.1) (decStrN n C.2.1))
        hset ht (by simpa only [Nat.card_fin] using htm)).mkClass ⟨b,v⟩ := by
  have h := aggnGuideTuple_spec hC htbl hset ht htm b
    (aggnTupleName_nodup (Subtype.val_injective.comp u.injective))
    (aggnTupleName_nodup (Subtype.val_injective.comp v.injective))
    (aggnTupleName_lt _) (aggnTupleName_lt _) (aggnTupleName_length _) (aggnTupleName_length _)
  simp only [Function.comp_def] at h
  rw [h,LocalGuideData.mkClass_eq_iff,aggnLocalGuide_equiv_iff hset ht]
  simp only [aggnTupleName_support,← Set.range_comp,Function.comp_def,aggnTupleName_coords,Bool.cond_false]
  rfl

end Algo
