import Workspace.Algo.DesignReadIso

/-! # Exact canonicity of the returned UPCC colors -/
namespace Algo
open Babai RAM Equiv
open scoped Classical
set_option quotPrecheck false

section
variable {n k l a b : ℕ} {ks : List ℕ} {p q : RawWL}
  (hp : RawWL.WF n k p) (hq : RawWL.WF n k q) (hk : ks.length = k)
  (hl : l ≤ k) (x : Str (Fin n) l) {α : ℝ} (hb : 0 < b) (hab : α = (a:ℝ)/b)
  (f : Perm (Fin n)) (hf : f ∈ KAryPartStruct.Iso (decWL n k p) (decWL n k q))
local notation "z" => (((ks,tupleOf x),p),(a,b))
local notation "z'" => (((ks,tupleOf (tupleMap f x)),q),(a,b))
local notation "Y" => ((decWL n k p).restrTo hl x)
local notation "Y'" => ((decWL n k q).restrTo hl (tupleMap f x))
local notation "D" => (KAryPartStruct.dominantClass α Y)
local notation "D'" => (KAryPartStruct.dominantClass α Y')
local notation "hi" => (KAryPartStruct.restrTo_canonical _ _ hl x hf)
local notation "d" => (KAryPartStruct.domEquiv (α := α) hi)
local notation "e" => (designDominantEquiv hp hk hl x hb hab)
local notation "e'" => (designDominantEquiv hq hk hl (tupleMap f x) hb hab)
local notation "c" => (fun u v : D => binColor (designDomPairs z,(e u,e v)))
local notation "c'" => (fun u v : D' => binColor (designDomPairs z',(e' u,e' v)))
include hp hq hk hl hb hab hf

theorem designReadIso_dominant_image : f '' winSet n (dominantList z) = winSet n (dominantList z') := by
  rw [designDominant_set hp hk hl x hb hab,
    designDominant_set hq hk hl (tupleMap f x) hb hab]
  exact KAryPartStruct.dominantClass_canonical _ _ hi

/-- Closing gaps in colors preserves their canonical integer names. -/
theorem designReadIso_upcc_colors (h2 : l+2 ≤ k) (u v : D) :
    binColor (designReadUpccTable z',(e' (d u),e' (d v))) =
      binColor (designReadUpccTable z,(e u,e v)) := by
  rw [designReadUpccTable_names z' e',designReadUpccTable_names z e]
  exact PartitionStructure.natColor_ofNamedColoring_map d
    (designReadIso_pairs hp hq hk hl x hb hab f hf h2) u v

/-- The precise stored names, rather than their list positions, carry the UPCC. -/
theorem designReadIso_upcc_old_colors (h2 : l+2 ≤ k) (u v : Fin n)
    (hu : u.val ∈ dominantList z) (hv : v.val ∈ dominantList z) :
    binColor (designReadUpccTable z',(rawLetterIndex (dominantList z',(f u).val),
      rawLetterIndex (dominantList z',(f v).val))) =
    binColor (designReadUpccTable z,(rawLetterIndex (dominantList z,u.val),
      rawLetterIndex (dominantList z,v.val))) := by
  have hud := (mem_dominantList hp hk hl x hb hab u).mp hu
  have hvd := (mem_dominantList hp hk hl x hb hab v).mp hv
  have he := designReadIso_upcc_colors hp hq hk hl x hb hab f hf h2 ⟨u,hud⟩ ⟨v,hvd⟩
  have hiu := designReadIndex_on_dominant hq hk hl (tupleMap f x) hb hab (d ⟨u,hud⟩)
  have hiv := designReadIndex_on_dominant hq hk hl (tupleMap f x) hb hab (d ⟨v,hvd⟩)
  simp only [KAryPartStruct.domEquiv_val] at hiu hiv
  rw [designReadIndex_on_dominant hp hk hl x hb hab ⟨u,hud⟩,
    designReadIndex_on_dominant hp hk hl x hb hab ⟨v,hvd⟩,hiu,hiv]
  exact he

end
end Algo
