import Workspace.Algo.DesignReadComponentRelation

/-! # Alpha validity of the actual component exit

The passing raw constituent test gives a disconnected non-diagonal color
on the dominant class. Proposition 3.4.4 gives a nontrivial equipartition
there. The exact raw block relation then transfers the Design Lemma's
alpha-partition theorem to the returned encoding.
-/
namespace Algo
open Babai RAM Equiv
open scoped Classical
set_option quotPrecheck false

section
variable {n k l a b : ℕ} {ks : List ℕ} {p : RawWL}
  (hw : RawWL.WF n k p) (hk : ks.length = k) (hl : l ≤ k) (x : Str (Fin n) l)
  {α : ℝ} (hb : 0 < b) (hab : α = (a:ℝ)/b)
local notation "z" => (((ks,tupleOf x),p),(a,b))
local notation "Y" => ((decWL n k p).restrTo hl x)
local notation "D" => (KAryPartStruct.dominantClass α Y)
local notation "e" => (designDominantEquiv hw hk hl x hb hab)
local notation "cols" => (fun u v : D => binColor (designDomPairs z,(e u,e v)))

include hw hk hl hb hab

theorem designReadPart_isAlphaPartition (hα : 1/2 ≤ α) (hcoh : (decWL n k p).IsCoherent)
    (hc : designReadHasComponents z = true) :
    (decColPartition n (designReadPart z)).IsAlphaPartition α := by
  obtain ⟨h2,hdiscRaw⟩ := (designReadHasComponents_spec z).mp hc
  have h2' : l+2 ≤ k := by simpa only [length_tupleOf,hk] using h2
  rw [designDomPairs_length] at hdiscRaw
  have hdisc : ∃ j,IsDisconnectedColor cols j := by
    obtain ⟨j,hj⟩ := hdiscRaw
    exact ⟨j,(isDisconnectedColor_map (c := cols)
      (c' := namedBin (dominantList z).length (designDomPairs z)) e (fun _ _ => rfl) j).mp hj⟩
  have hne : (D).Nonempty := by
    obtain ⟨j,hj⟩ := hdisc
    obtain ⟨u,_,_⟩ := hj.2.1
    exact ⟨u.val,u.property⟩
  have hdom : KAryPartStruct.HasDominantClass α Y := by
    obtain ⟨u,hu⟩ := hne
    exact ⟨(Y).vcolor u,hu⟩
  obtain ⟨hKcoh,hKhom⟩ := designDominant_coherent hα Y
    ((decWL n k p).restrTo_isCoherent hcoh hl x) (by omega) hne
  obtain ⟨hP,hPnt⟩ := designBlockFamily_partition hKcoh hKhom
    (designDomPairs_natKernel hw hk hl x hb hab h2') hdisc
  have hp := KAryPartStruct.designPart_isAlphaPartition_of_dominant hα Y
    (designBlockFamily D cols) hdom hP hPnt
  apply ColoredPartition.isAlphaPartition_of_kernel_rel
    ((Y).designPart (designBlockFamily D cols)) (decColPartition n (designReadPart z))
    (Equiv.refl _) _ _ hp
  · intro u v
    rw [designReadPart_color_of_length (card_eq_length_dom hw),
      designReadPart_color_of_length (card_eq_length_dom hw)]
    dsimp only [Equiv.refl_apply]
    rw [restrVColorAt_spec hk hl x u,restrVColorAt_spec hk hl x v]
    exact (Y).natVColor_eq_iff u v
  · intro u v
    exact (designReadPart_designRel hw hk hl x hb hab u v).symm

end
end Algo
