import Workspace.Algo.SplitImprimitiveScan
import Workspace.Algo.SplitBipDefect

/-! # Section 9.6: form the blocks of the disconnected color

We restrict the table to second-part positions, find the first disconnected
color, and read its components. The resulting lists use the old block names.
Repeated components are removed before constructing the restricted graphs.
-/
namespace Algo
open Babai RAM

def impSecond (r : RawUpccCase) : RawConfig := sbipIndexed (r.1,r.2.2)

theorem polyFun_impSecond : PolyFun impSecond :=
  (polyFun_fst.pair (polyFun_snd.comp polyFun_snd)).comp sbipPoly_indexed

def impComponents (r : RawUpccCase) : RawLab := (sbipStep6 (impSecond r)).2

theorem polyFun_impComponents : PolyFun impComponents :=
  (polyFun_impSecond.comp sbipPoly_step6).comp polyFun_snd

def impGroupPositions (z : RawUpccCase × ℕ) : List ℕ :=
  (List.range z.1.2.2.length).filter (fun j =>
    decide (labAt (impComponents z.1) z.2 = labAt (impComponents z.1) j))

theorem polyFun_impGroupPositions : PolyFun impGroupPositions := by
  have hc : PolyFun (fun z : (RawUpccCase × ℕ) × ℕ => impComponents z.1.1) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_impComponents
  have ht := ((hc.pair (polyFun_fst.comp polyFun_snd)).comp polyFun_labAt).natEq
    ((hc.pair polyFun_snd).comp polyFun_labAt)
  exact (polyFun_id.pair
    (((polyFun_fst.comp polyFun_snd).comp polyFun_snd).comp polyFun_rangeLength)).comp
      (PolyFun.filterParam ht)

def impGroup (z : RawUpccCase × ℕ) : List ℕ :=
  (impGroupPositions z).map (fun j => z.1.2.2.getD j 0)

theorem polyFun_impGroup : PolyFun impGroup :=
  (((polyFun_fst.comp polyFun_snd).comp polyFun_snd).pair polyFun_impGroupPositions).comp
    (PolyFun.mapParam ((polyFun_id.pair (polyFun_const 0)).comp polyFun_getD))

def impGroups (r : RawUpccCase) : List (List ℕ) :=
  dedupG ([],(List.range r.2.2.length).map (fun i => impGroup (r,i)))

theorem polyFun_impGroups : PolyFun impGroups :=
  ((polyFun_const []).pair ((polyFun_id.pair
    ((polyFun_snd.comp polyFun_snd).comp polyFun_rangeLength)).comp
      (PolyFun.mapParam polyFun_impGroup))).comp (polyFun_dedupG polyFun_listNatEq)

/-- A restriction keeps the old table and its original majority-color name. -/
def impRestricted (z : RawUpccCase × List ℕ) : RawBipConstituent :=
  ((z.1.1,impJ z.1),(z.1.2.1,z.2))

theorem polyFun_impRestricted : PolyFun impRestricted :=
  ((polyFun_fst.comp polyFun_fst).pair (polyFun_fst.comp polyFun_impJ)).pair
    (((polyFun_fst.comp polyFun_snd).comp polyFun_fst).pair polyFun_snd)

/-- Step 2(i) keeps precisely the passing block restrictions. -/
def impGoodGroups (r : RawUpccCase) : List (List ℕ) :=
  (impGroups r).filter (fun g => bipHalfDefect (impRestricted (r,g)))

theorem polyFun_impGoodGroups : PolyFun impGoodGroups :=
  (polyFun_id.pair polyFun_impGroups).comp
    (PolyFun.filterParam (polyFun_impRestricted.comp polyFun_bipHalfDefect))

theorem impGroups_mem (r : RawUpccCase) (g : List ℕ) :
    g ∈ impGroups r ↔ ∃ i < r.2.2.length, impGroup (r,i) = g := by
  simp [impGroups,mem_dedupG_nil]

theorem impGroups_nodup (r : RawUpccCase) : (impGroups r).Nodup := nodup_dedupG _

theorem impGroup_mem_right {r : RawUpccCase} {i a : ℕ} (ha : a ∈ impGroup (r,i)) :
    a ∈ r.2.2 := by
  obtain ⟨j,hj,rfl⟩ := List.mem_map.1 ha
  have hj' := List.mem_range.1 (List.mem_filter.1 hj).1
  rw [List.getD_eq_getElem _ _ hj']
  exact List.getElem_mem _

theorem impGroup_nodup {r : RawUpccCase} (hnd : r.2.2.Nodup) (i : ℕ) :
    (impGroup (r,i)).Nodup := by
  apply List.Nodup.map_on _ (List.nodup_range.filter _)
  intro a ha b hb hab
  have ha' := List.mem_range.1 (List.mem_filter.1 ha).1
  have hb' := List.mem_range.1 (List.mem_filter.1 hb).1
  rw [List.getD_eq_getElem _ _ ha',List.getD_eq_getElem _ _ hb'] at hab
  exact (List.Nodup.getElem_inj_iff hnd).1 hab

theorem impGroups_members_nodup {r : RawUpccCase} (hnd : r.2.2.Nodup)
    {g : List ℕ} (hg : g ∈ impGroups r) : g.Nodup := by
  obtain ⟨i,_,rfl⟩ := (impGroups_mem _ _).1 hg
  exact impGroup_nodup hnd i

/-- A named component is unchanged by passing to positions. -/
theorem sbipComponents_named {A : Type*} [Finite A] (p : RawConfig) {n : ℕ}
    (hlen : p.1.length = n) (e : A ≃ Fin n) (c : A → A → ℕ)
    (hc : ∀ u v, binColor (p,(e u,e v)) = c u v) (u v : A) :
    LabRel (sbipStep6 p).2 (e u) (e v) ↔ v ∈ blockOf c u := by
  subst n
  rw [sbipStep6_components,blockOf_map e hc,Set.mem_image_equiv,Equiv.symm_apply_apply]

section Specification
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {X : BlkImprimitiveObj s} {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {r : RawUpccCase} (h : ImpNames X name₁ name₂ r)
    (e : ↥X.blocks ≃ Fin r.2.2.length) (he : ∀ B, r.2.2[(e B).val] = name₂ B)
include h he

theorem impComponents_spec (B C : ↥X.blocks) :
    LabRel (impComponents r) (e B) (e C) ↔ C ∈ X.group B := by
  apply sbipComponents_named (impSecond r) (sbipIndexed_length _ _) e X.c₂
  intro U V
  rw [impSecond,sbipIndexed_get,he,he]
  exact h.blocks U V

/-- A raw component contains exactly the old names of the corresponding group. -/
theorem impGroup_spec (B : ↥X.blocks) (a : ℕ) :
    a ∈ impGroup (r,e B) ↔ ∃ C ∈ X.group B, name₂ C = a := by
  simp only [impGroup,List.mem_map,impGroupPositions,List.mem_filter,List.mem_range,
    decide_eq_true_eq]
  constructor
  · rintro ⟨j,⟨hj,hcomp⟩,ha⟩
    let C := e.symm ⟨j,hj⟩
    have hC : e C = ⟨j,hj⟩ := e.apply_symm_apply _
    refine ⟨C,(impComponents_spec h e he B C).1 ?_,?_⟩
    · change labAt _ _ = labAt _ _
      simpa only [hC] using hcomp
    · rw [List.getD_eq_getElem _ _ hj] at ha
      have hn := he C
      simp only [hC] at hn
      exact hn.symm.trans ha
  · rintro ⟨C,hC,ha⟩
    refine ⟨e C,⟨(e C).isLt,(impComponents_spec h e he B C).2 hC⟩,?_⟩
    rw [List.getD_eq_getElem _ _ (e C).isLt,he C,ha]

/-- Every stored component represents a mathematical group. -/
theorem impGroups_spec (g : List ℕ) (hg : g ∈ impGroups r) :
    ∃ G ∈ X.groups, ∀ a, a ∈ g ↔ ∃ C ∈ G, name₂ C = a := by
  obtain ⟨i,hi,rfl⟩ := (impGroups_mem r g).1 hg
  let B := e.symm ⟨i,hi⟩
  refine ⟨X.group B,⟨B,rfl⟩,?_⟩
  intro a
  have hh := impGroup_spec h e he B a
  simpa only [B,Equiv.apply_symm_apply] using hh

/-- Every mathematical group has a stored representative. -/
theorem impGroups_complete (G : Set ↥X.blocks) (hG : G ∈ X.groups) :
    ∃ g ∈ impGroups r, ∀ a, a ∈ g ↔ ∃ C ∈ G, name₂ C = a := by
  obtain ⟨B,rfl⟩ := hG
  exact ⟨impGroup (r,e B),(impGroups_mem _ _).2 ⟨e B,(e B).isLt,rfl⟩,
    impGroup_spec h e he B⟩

end Specification
end Algo
