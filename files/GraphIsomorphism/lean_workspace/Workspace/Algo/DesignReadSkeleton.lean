import Workspace.Algo.DesignReadPlainValidity

/-! # Exact names for the returned dominant skeleton

The subset list gives a bijection between the mathematical dominant class
and the local domain. Under that bijection every raw pair color is the
restriction's binary skeleton color.
-/
set_option quotPrecheck false
namespace Algo
open Babai RAM Equiv
open scoped Classical

theorem designDomPairs_length (z : DIn) :
    (designDomPairs z).1.length = (dominantList z).length := by
  simp [designDomPairs,designPairIndexed]

section Names
variable {n k l a b : ℕ} {ks : List ℕ} {p : RawWL}
  (hw : RawWL.WF n k p) (hk : ks.length = k) (hl : l ≤ k) (x : Str (Fin n) l)
  {α : ℝ} (hb : 0 < b) (hab : α = (a:ℝ)/b)

local notation "z" => (((ks,tupleOf x),p),(a,b))
local notation "Y" => ((decWL n k p).restrTo hl x)
local notation "D" => (KAryPartStruct.dominantClass α Y)

include hw in
theorem designDominant_nodup : (dominantList z).Nodup := hw.domNodup.filter _

include hw hk hb hab in
theorem designDominant_set : winSet n (dominantList z) = D := by
  ext u
  exact mem_dominantList hw hk hl x hb hab u

noncomputable def designDominantEquiv : D ≃ Fin (dominantList z).length :=
  ((winEquiv n (dominantList z) (designDominant_nodup hw x)
    (fun _ h => lt_of_mem_dominantList hw h)).trans
      (Equiv.setCongr (designDominant_set hw hk hl x hb hab))).symm

theorem designDominantEquiv_name (u : D) :
    (dominantList z)[(designDominantEquiv hw hk hl x hb hab u).val] = u.val.val := by
  let e := winEquiv n (dominantList z) (designDominant_nodup hw x)
    (fun _ h => lt_of_mem_dominantList hw h)
  let v : winSet n (dominantList z) := ⟨u.val,(designDominant_set hw hk hl x hb hab).symm ▸ u.property⟩
  have he := winEquiv_symm_val (dominantList z) (designDominant_nodup hw x)
    (fun _ h => lt_of_mem_dominantList hw h) v
  rw [List.getD_eq_getElem _ _ (e.symm v).isLt] at he
  exact he

theorem designDomPairs_named (h2 : l+2 ≤ k) (u v : D) :
    binColor (designDomPairs z,(designDominantEquiv hw hk hl x hb hab u,
      designDominantEquiv hw hk hl x hb hab v)) =
      (Y).pairColor (by omega) u.val v.val := by
  rw [designDomPairs,designPairIndexed_get]
  change restrPairColorAt (z,((dominantList z)[(designDominantEquiv hw hk hl x hb hab u).val],
    (dominantList z)[(designDominantEquiv hw hk hl x hb hab v).val])) = _
  rw [designDominantEquiv_name,designDominantEquiv_name]
  exact restrPairColorAt_spec hk hl h2 x u.val v.val

end Names

/-- Restricting a coherent skeleton to one vertex color class preserves coherence
and makes it homogeneous. -/
theorem designDominant_coherent {V : Type} {C : Type*} [Fintype V] [DecidableEq V] {q : ℕ}
    {α : ℝ} (hα : 1/2 ≤ α) (Y : KAryPartStruct V C q) (hY : (Y).IsCoherent)
    (hq : 2 ≤ q) (hne : (KAryPartStruct.dominantClass α Y).Nonempty) :
    (((Y).skel2 hq).induced (KAryPartStruct.dominantClass α Y)).IsCoherent ∧
      (((Y).skel2 hq).induced (KAryPartStruct.dominantClass α Y)).IsHomogeneous := by
  obtain ⟨u,hu⟩ := hne
  have he : KAryPartStruct.dominantClass α Y = (Y).vclass ((Y).vcolor u) := by
    ext v
    constructor
    · intro hv
      exact IsDominant.subsingleton hα (Y).vcolor hv hu
    · intro hv
      change (Y).vcolor v = (Y).vcolor u at hv
      exact KAryPartStruct.mem_dominantClass_of_vcolor_eq Y hv hu
  have hc : KAryPartStruct.dominantClass α Y =
      ((Y).skel2 hq).vertexClass (((Y).skel2 hq).vcolor u) := by
    rw [KAryPartStruct.skel2_vertexClass_eq,he]
  have hstable : ((Y).skel2 hq).IsStable (KAryPartStruct.dominantClass α Y) := by
    rw [hc]
    exact PartitionStructure.isStable_vertexClass _ _
  refine ⟨PartitionStructure.induced_isCoherent _ ((Y).skel2_isCoherent hY hq) hstable,?_⟩
  apply PartitionStructure.induced_isHomogeneous
  intro a ha b hb
  rw [hc] at ha hb
  exact ha.trans hb.symm

end Algo
