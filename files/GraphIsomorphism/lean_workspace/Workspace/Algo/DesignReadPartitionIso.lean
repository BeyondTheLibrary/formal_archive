import Workspace.Algo.DesignReadIso

/-! # Canonicity of the computed partition outputs -/
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

theorem designReadIso_plain : ColPartIso n (designReadPlain z) (designReadPlain z') f := by
  rw [colPartIso_iff_coloredPartition]
  constructor
  · intro u
    rw [designReadPlain_color_of_length (card_eq_length_dom hq),
      designReadPlain_color_of_length (card_eq_length_dom hp)]
    exact designReadIso_vcolor hp hq hk hl x hb hab f hf u
  · intro u v
    rw [designReadPlain_rel_of_length (card_eq_length_dom hp),
      designReadPlain_rel_of_length (card_eq_length_dom hq),
      designReadIso_vcolor hp hq hk hl x hb hab f hf u,
      designReadIso_vcolor hp hq hk hl x hb hab f hf v]

/-- The chosen numeric constituent gives corresponding colored partitions. -/
theorem designReadIso_partition_blocks (h2 : l+2 ≤ k) :
    ColPartIso n (designReadPart z) (designReadPart z') f := by
  rw [colPartIso_iff_coloredPartition]
  constructor
  · intro u
    rw [designReadPart_color_of_length (card_eq_length_dom hq),
      designReadPart_color_of_length (card_eq_length_dom hp)]
    exact designReadIso_vcolor hp hq hk hl x hb hab f hf u
  · intro u v
    rw [designReadPart_designRel hp hk hl x hb hab,
      designReadPart_designRel hq hk hl (tupleMap f x) hb hab]
    change (_ ∧ _) ↔ (_ ∧ _)
    rw [KAryPartStruct.vcolor_canonical _ _ hi u,KAryPartStruct.vcolor_canonical _ _ hi v]
    apply and_congr_right
    intro hcolor
    by_cases hu : u ∈ D
    · have hv : v ∈ D := KAryPartStruct.mem_dominantClass_of_vcolor_eq Y hcolor.symm hu
      have hfu : f u ∈ D' := (KAryPartStruct.mem_dominantClass_congr hi u).mp hu
      have hfv : f v ∈ D' := (KAryPartStruct.mem_dominantClass_congr hi v).mp hv
      rw [designBlockFamily_rel D c ⟨u,hu⟩ ⟨v,hv⟩,
        designBlockFamily_rel D' c' ⟨f u,hfu⟩ ⟨f v,hfv⟩]
      change (⟨v,hv⟩ : D) ∈ blockOf c ⟨u,hu⟩ ↔
        d ⟨v,hv⟩ ∈ blockOf c' (d ⟨u,hu⟩)
      rw [blockOf_map d (designReadIso_pairs hp hq hk hl x hb hab f hf h2),
        Set.mem_image_equiv,Equiv.symm_apply_apply]
    · have hv : v ∉ D := fun hv => hu (KAryPartStruct.mem_dominantClass_of_vcolor_eq Y hcolor hv)
      have hfu : f u ∉ D' := fun h => hu ((KAryPartStruct.mem_dominantClass_congr hi u).mpr h)
      have hfv : f v ∉ D' := fun h => hv ((KAryPartStruct.mem_dominantClass_congr hi v).mpr h)
      have hfalse (A : Set (Fin n)) (hA : A ∈ designBlockFamily D c) : u ∉ A ∧ v ∉ A :=
        ⟨fun h => hu (designBlockFamily_subset hA h),fun h => hv (designBlockFamily_subset hA h)⟩
      have hfalse' (A : Set (Fin n)) (hA : A ∈ designBlockFamily D' c') : f u ∉ A ∧ f v ∉ A :=
        ⟨fun h => hfu (designBlockFamily_subset hA h),fun h => hfv (designBlockFamily_subset hA h)⟩
      exact iff_of_true (fun A hA => iff_of_false (hfalse A hA).1 (hfalse A hA).2)
        (fun A hA => iff_of_false (hfalse' A hA).1 (hfalse' A hA).2)

/-- Every actual partition output is carried to the other partition output. -/
theorem designReadIso_partition {P P' : RawColPart}
    (hP : (designReadExit z).1 = some P) (hP' : (designReadExit z').1 = some P') :
    ColPartIso n P P' f := by
  unfold designReadExit at hP hP'
  rw [designReadIso_components hp hq hk hl x hb hab f hf,
    designReadIso_upcc_test hp hq hk hl x hb hab f hf] at hP'
  split at hP
  · rename_i hc
    rw [if_pos hc] at hP'
    have h2 := (designReadHasComponents_spec z).mp hc |>.1
    simp only [length_tupleOf,hk] at h2
    have he := Option.some.inj hP
    have he' := Option.some.inj hP'
    rw [← he,← he']
    exact designReadIso_partition_blocks hp hq hk hl x hb hab f hf h2
  · rename_i hc
    rw [if_neg hc] at hP'
    split at hP
    · simp [designReadUpccExit] at hP
    · rename_i hu
      rw [if_neg hu] at hP'
      have he := Option.some.inj hP
      have he' := Option.some.inj hP'
      rw [← he,← he']
      exact designReadIso_plain hp hq hk hl x hb hab f hf

end
end Algo
