import Workspace.Algo.DesignReadNamesValidity
import Workspace.Algo.DesignRelabel
import Workspace.SplitOrJohnson.BlkDictionary

/-! # Transport of the actual read-off under a named table isomorphism

The first disconnected color is selected by its integer name. Preserving
these names carries its weak components and the recoded UPCC to the
corresponding output, independent of the order of the vertex lists.
-/
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

theorem designReadIso_vcolor (u : Fin n) :
    restrVColorAt (z',f u) = restrVColorAt (z,u) := by
  rw [restrVColorAt_spec hk hl (tupleMap f x),restrVColorAt_spec hk hl x]
  exact KAryPartStruct.vcolor_canonical _ _ hi u

theorem designReadIso_dominant (u : Fin n) :
    u.val ∈ dominantList z ↔ (f u).val ∈ dominantList z' := by
  rw [mem_dominantList hp hk hl x hb hab,
    mem_dominantList hq hk hl (tupleMap f x) hb hab]
  exact KAryPartStruct.mem_dominantClass_congr hi u

theorem designReadIso_pairs (h2 : l+2 ≤ k) (u v : D) : c' (d u) (d v) = c u v := by
  dsimp only
  rw [designDomPairs_named hq hk hl (tupleMap f x) hb hab h2,
    designDomPairs_named hp hk hl x hb hab h2]
  exact KAryPartStruct.pairColor_canonical hi u.val v.val

/-- The local position bijection need not preserve list order. -/
noncomputable def designReadIso_positions : Fin (dominantList z).length ≃ Fin (dominantList z').length :=
  (e).symm.trans ((d).trans e')

theorem designReadIso_position_pairs (h2 : l+2 ≤ k) (u v : Fin (dominantList z).length) :
    binColor (designDomPairs z',(designReadIso_positions hp hq hk hl x hb hab f hf u,
      designReadIso_positions hp hq hk hl x hb hab f hf v)) = binColor (designDomPairs z,(u,v)) := by
  have he := designReadIso_pairs hp hq hk hl x hb hab f hf h2 ((e).symm u) ((e).symm v)
  simpa only [Equiv.apply_symm_apply] using he

/-- The component test is invariant under every named table isomorphism. -/
theorem designReadIso_components : designReadHasComponents z' = designReadHasComponents z := by
  by_cases h2 : l+2 ≤ k
  · apply Bool.eq_iff_iff.mpr
    rw [designReadHasComponents_spec,designReadHasComponents_spec]
    simp only [length_tupleOf,hk,and_iff_right h2]
    rw [designDomPairs_length,designDomPairs_length]
    exact exists_congr (fun j => isDisconnectedColor_map
      (designReadIso_positions hp hq hk hl x hb hab f hf)
      (designReadIso_position_pairs hp hq hk hl x hb hab f hf h2) j)
  · simp [designReadHasComponents,designReadHasSkeleton,hk,h2]

/-- The exact rank test is invariant, including the absent-skeleton case. -/
theorem designReadIso_upcc_test : designReadHasUpcc z' = designReadHasUpcc z := by
  by_cases h2 : l+2 ≤ k
  · have he : cliqueRank z = cliqueRank z' := by
      rw [cliqueRank_spec hp hk hl h2 x hb hab,
        cliqueRank_spec hq hk hl h2 (tupleMap f x) hb hab]
      apply PartitionStructure.rank_equiv_congr d
      intro u v u' v'
      rw [PartitionStructure.induced_color_eq_iff,PartitionStructure.induced_color_eq_iff,
        KAryPartStruct.skel2_color_eq_iff',KAryPartStruct.skel2_color_eq_iff']
      simp only [KAryPartStruct.domEquiv_val,KAryPartStruct.pairColor_canonical hi]
    simp only [designReadHasUpcc,designReadHasSkeleton,length_tupleOf,hk,he]
  · simp [designReadHasUpcc,designReadHasSkeleton,hk,h2]

end
end Algo
