import Workspace.Algo.DesignReadVersionsRelabel

/-! # The full computed read-off family transports with the input

Each returning tuple has a corresponding returning tuple, and their actual
outputs are related by the original vertex permutation. This binds the
concrete refinement, scan, component selection, and UPCC recoding.
-/
namespace Algo
open Babai RAM
open scoped Classical

private theorem designRead_forall₂_map {A B C : Type*} (L : List A)
    (f : A → B) (g : A → C) (R : B → C → Prop) (h : ∀ a ∈ L,R (f a) (g a)) :
    List.Forall₂ R (L.map f) (L.map g) := by
  induction L with
  | nil => exact .nil
  | cons a L ih => exact .cons (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

section
variable {n a b c : ℕ} {π : RawPerm} {ks base dom : List ℕ} {rels : RawRelStruct}
    (hπ : RawPerm.WF n π) (hnd : dom.Nodup) (hmem : ∀ i,i ∈ dom ↔ i < n)
    (hg : ks.length ≤ guardBound c base.length)
    (hrels : ∀ R ∈ rels,∀ t ∈ R,∀ i ∈ t,i < n) {α : ℝ} (hb : 0 < b) (hab : α = (a:ℝ)/b)
local notation "g" => (((ks,base,dom),rels),(a,b))
local notation "g'" => (((ks,base,permList π dom),relabelRels (π,rels)),(a,b))
include hπ hnd hmem hg hrels hb hab

/-- Each actual family entry has its corresponding actual relabeled output. -/
theorem ambientDesignReadAt_relabel {xs : List ℕ} (hxs : xs ∈ ambientDesignVersions c g) :
    DesignReadOutIso n (decPerm n π) (designReadExit (ambientDesignAt c g xs))
      (designReadExit (ambientDesignAt c g' (permList π xs))) := by
  obtain ⟨l,hl,x,hx,_⟩ := ambientDesignVersions_witness hnd hmem rfl hg hb hab hxs
  rw [← hx,← designTupleOf_relabel hπ]
  unfold ambientDesignAt
  rw [ambientPipeline321_relabel hπ hnd hmem hg hrels]
  have hp := ambientPipeline321_wf (a := ((ks,base,dom),rels)) hnd hmem hg
  exact designReadIso_exit hp (relabelWL_wf hπ hp) rfl hl.le x hb hab
    (decPerm n π) (designDecWL_relabel_iso hπ hp)

/-- The complete family, including every output branch and color, is canonical. -/
theorem ambientDesignReadFamily_relabel :
    List.Forall₂ (fun u v : List ℕ × RawDesignReadOut =>
      v.1 = permList π u.1 ∧ DesignReadOutIso n (decPerm n π) u.2 v.2)
      (ambientDesignReadFamily c g) (ambientDesignReadFamily c g') := by
  unfold ambientDesignReadFamily
  rw [ambientDesignVersions_relabel hπ hnd hmem hg hrels,List.map_map]
  apply designRead_forall₂_map
  intro xs hxs
  exact ⟨rfl,ambientDesignReadAt_relabel hπ hnd hmem hg hrels hb hab hxs⟩

end
end Algo
