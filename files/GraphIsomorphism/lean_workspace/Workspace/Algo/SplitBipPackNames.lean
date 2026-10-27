import Workspace.Algo.SplitBipPack

/-! Common names for packed recursive graphs. Original points retain their
names below the ambient degree. Block positions receive fresh names above
that degree. These names are injective and enumerate exactly the graph's
point and block lists.
-/
namespace Algo
open Babai RAM
open scoped Classical

/-- A globally zero compact hint stays zero at all names, including padding. -/
theorem sbipRestore_zero (p : RawConfig) (l : List ℕ)
    (hp : ∀ a b, binColor (p,(a,b)) = 0) (a b : ℕ) :
    binColor (sbipRestore (p,l),(a,b)) = 0 := by
  have he : (tuplesOf l 2).map (fun t => sbipRestoreRow ((p,l),t)) =
      (tuplesOf l 2).map (fun t => (t,0)) := by
    apply List.map_congr_left
    intro t _
    simp only [sbipRestoreRow,sbipRestoreAt,hp]
  change (((tuplesOf l 2).map (fun t => sbipRestoreRow ((p,l),t))).lookup [a,b]).getD 0 = 0
  rw [he,lookup_map_const]
  split_ifs <;> rfl

section
variable {α : Type} (G : VColBipBlk α ℕ) (point : α → ℕ) (N : ℕ)
    {k : ℕ} (eB : ↥G.blocks ≃ Fin k)

noncomputable def sbipPackName (A : G.Vtx) : ℕ :=
  if h : A.val ∈ G.blocks then N + eB ⟨A.val,h⟩
  else point (Classical.choose (A.property.resolve_right h))

theorem sbipPackName_point (x : α) (hx : G.part₁ x) :
    sbipPackName G point N eB ⟨{x},Or.inl ⟨x,hx,rfl⟩⟩ = point x := by
  have hb : ({x} : Set α) ∉ G.blocks := fun h => G.blocks_off₁ _ h x rfl hx
  rw [sbipPackName,dif_neg hb]
  apply congrArg point
  exact Set.singleton_injective (Classical.choose_spec
    ((show IsVertexOn G.part₁ G.blocks {x} from Or.inl ⟨x,hx,rfl⟩).resolve_right hb)).2.symm

theorem sbipPackName_block (B : ↥G.blocks) :
    sbipPackName G point N eB ⟨B.val,Or.inr B.property⟩ = N + eB B := by
  rw [sbipPackName,dif_pos B.property]

variable (hp : Function.Injective point) (hlt : ∀ x, G.part₁ x → point x < N)
include hp hlt in
theorem sbipPackName_injective : Function.Injective (sbipPackName G point N eB) := by
  rintro ⟨A,hA⟩ ⟨B,hB⟩ he
  rcases hA with ⟨x,hx,rfl⟩ | hA <;> rcases hB with ⟨y,hy,rfl⟩ | hB
  · rw [sbipPackName_point G point N eB x hx,sbipPackName_point G point N eB y hy] at he
    exact Subtype.ext (congrArg (fun x : α => ({x} : Set α)) (hp he))
  · rw [sbipPackName_point G point N eB x hx,sbipPackName_block G point N eB ⟨B,hB⟩] at he
    have hh := hlt x hx
    omega
  · rw [sbipPackName_block G point N eB ⟨A,hA⟩,sbipPackName_point G point N eB y hy] at he
    have hh := hlt y hy
    omega
  · rw [sbipPackName_block G point N eB ⟨A,hA⟩,
      sbipPackName_block G point N eB ⟨B,hB⟩] at he
    have hh : eB ⟨A,hA⟩ = eB ⟨B,hB⟩ := Fin.ext (by omega)
    exact Subtype.ext (congrArg (fun B : ↥G.blocks => B.val) (eB.injective hh))

include hlt in
theorem sbipPackName_lt_iff (A : G.Vtx) :
    sbipPackName G point N eB A < N ↔ ∃ x, G.part₁ x ∧ A.val = {x} := by
  rcases A with ⟨A,hA⟩
  rcases hA with ⟨x,hx,rfl⟩ | hA
  · rw [sbipPackName_point G point N eB x hx]
    exact ⟨fun _ => ⟨x,hx,rfl⟩,fun _ => hlt x hx⟩
  · rw [sbipPackName_block G point N eB ⟨A,hA⟩]
    constructor
    · omega
    · rintro ⟨x,hx,rfl⟩
      exact (G.blocks_off₁ _ hA x rfl hx).elim

end
end Algo
