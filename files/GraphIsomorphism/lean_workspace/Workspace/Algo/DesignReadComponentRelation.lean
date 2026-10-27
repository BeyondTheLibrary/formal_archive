import Workspace.Algo.DesignReadUpccValidity
import Workspace.Algo.DesignReadBlockFamily

/-! # Exact blocks of the computed component partition

On the dominant set, equal raw component labels are exactly membership in
the same selected weak component. Outside it, each vertex color class
remains a single block. These are the two clauses of `designRel`.
-/
namespace Algo
open Babai RAM Equiv
open scoped Classical
set_option quotPrecheck false

theorem designReadPart_color_of_length {n : ℕ} {z : DIn}
    (hd : z.1.2.1.length = n) (u : Fin n) :
    (decColPartition n (designReadPart z)).color u = restrVColorAt (z,u) := by
  simp [decColPartition,designReadPart,designReadColors,labAt,hd]

theorem designReadPart_rel_of_length {n : ℕ} {z : DIn}
    (hd : z.1.2.1.length = n) (u v : Fin n) :
    (decColPartition n (designReadPart z)).part u v ↔
      restrVColorAt (z,u) = restrVColorAt (z,v) ∧ designReadBlock (z,u) = designReadBlock (z,v) := by
  change cellOf (designReadPart z) u = cellOf (designReadPart z) v ↔ _
  simp [cellOf,designReadPart,designReadColors,labAt,hd,u.isLt,v.isLt]

section
variable {n k l a b : ℕ} {ks : List ℕ} {p : RawWL}
  (hw : RawWL.WF n k p) (hk : ks.length = k) (hl : l ≤ k) (x : Str (Fin n) l)
  {α : ℝ} (hb : 0 < b) (hab : α = (a:ℝ)/b)
local notation "z" => (((ks,tupleOf x),p),(a,b))
local notation "Y" => ((decWL n k p).restrTo hl x)
local notation "D" => (KAryPartStruct.dominantClass α Y)
local notation "e" => (designDominantEquiv hw hk hl x hb hab)
local notation "cols" => (fun u v : D => binColor (designDomPairs z,(e u,e v)))

theorem designReadBlock_on_equiv (u v : D) :
    designReadBlock (z,u.val.val) = designReadBlock (z,v.val.val) ↔ v ∈ blockOf cols u := by
  rw [← designDominantEquiv_name hw hk hl x hb hab u,
    ← designDominantEquiv_name hw hk hl x hb hab v,
    designReadBlock_components z (designDominant_nodup hw x)]
  change (colorDigraph (namedBin (dominantList z).length (designDomPairs z))
    (sbipFirstDisconnected (designDomPairs z))).WeaklyAccessible (e u) (e v) ↔ _
  rw [sbipFirstDisconnected_spec,designDomPairs_length]
  have hm : e v ∈ blockOf (namedBin (dominantList z).length (designDomPairs z)) (e u) ↔
      (colorDigraph (namedBin (dominantList z).length (designDomPairs z))
        (blockColor (namedBin (dominantList z).length (designDomPairs z)))).WeaklyAccessible (e u) (e v) := by
    rw [blockOf,Digraph.weakComponent_eq_weaklyAccessible]
    rfl
  rw [← hm]
  rw [blockOf_map e (fun _ _ => rfl),Set.mem_image_equiv,Equiv.symm_apply_apply]
  rfl

theorem designReadPart_designRel (u v : Fin n) :
    (decColPartition n (designReadPart z)).part u v ↔
      (Y).designRel (designBlockFamily D cols) u v := by
  rw [designReadPart_rel_of_length (card_eq_length_dom hw),
    restrVColorAt_spec hk hl x u,restrVColorAt_spec hk hl x v]
  change (_ ∧ _) ↔ (_ ∧ _)
  apply and_congr_right
  intro hcolor
  have hDom : u ∈ D ↔ v ∈ D := by
    change IsDominant α ((Y).vclass ((Y).vcolor u)) ↔ IsDominant α ((Y).vclass ((Y).vcolor v))
    rw [hcolor]
  by_cases hu : u ∈ D
  · have hv := hDom.mp hu
    rw [designReadBlock_on_equiv hw hk hl x hb hab ⟨u,hu⟩ ⟨v,hv⟩]
    exact (designBlockFamily_rel D cols ⟨u,hu⟩ ⟨v,hv⟩).symm
  · have hv : v ∉ D := fun hv => hu (hDom.mpr hv)
    have hul : u.val ∉ dominantList z := fun h => hu ((mem_dominantList hw hk hl x hb hab u).mp h)
    have hvl : v.val ∉ dominantList z := fun h => hv ((mem_dominantList hw hk hl x hb hab v).mp h)
    rw [designReadBlock_off z hul,designReadBlock_off z hvl]
    simp only [true_iff]
    intro A hA
    have hs := designBlockFamily_subset hA
    exact ⟨fun h => False.elim (hu (hs h)),fun h => False.elim (hv (hs h))⟩

end
end Algo
