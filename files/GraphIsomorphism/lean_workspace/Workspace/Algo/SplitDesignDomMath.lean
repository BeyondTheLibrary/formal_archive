import Workspace.Algo.SplitDesignDominant

/-! # The label bijection in Section 9.7's dominant-class exit

Equal traces are excluded by the first test. Every trace of the common
size occurs because the full symmetric group acts on the large twin class.
These are the same two steps used by `DomHyp.domIsJohnsonColoring`.
-/
namespace Algo
open Babai

section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {X : BlkDesignObj s} {α : ℝ} (hd : X.DomHyp α)
    (hinj : ∀ u ∈ X.domClass α, ∀ v ∈ X.domClass α,
      X.nbhd u ∩ X.bigTwin = X.nbhd v ∩ X.bigTwin → u = v)
    (x₀ : ↥(X.domClass α))
include hd

theorem designDom_localSize (x : ↥(X.domClass α)) :
    X.localSize x.val = X.localSize x₀.val := by
  have hx : x.val ∈ X.localSizeClass x₀.val := by
    rw [← hd.domClass_eq x₀.property]
    exact x.property
  exact hx.2

noncomputable def designDomTraceMap (x : ↥(X.domClass α)) :
    binom ↥X.bigTwin (X.localSize x₀.val) :=
  ⟨X.traceFinset x.val,by rw [X.card_traceFinset,designDom_localSize hd x₀ x]⟩

include hinj in
theorem designDomTraceMap_bijective : Function.Bijective (designDomTraceMap hd x₀) := by
  classical
  constructor
  · intro x y hxy
    exact Subtype.ext (hinj _ x.property _ y.property
      ((X.traceFinset_eq_iff _ _).1 (congrArg Subtype.val hxy)))
  · intro F
    let T : Set (Set ↥s) := Subtype.val '' ((F.val : Finset ↥X.bigTwin) : Set ↥X.bigTwin)
    have hTsub : T ⊆ X.bigTwin := by rintro _ ⟨B,_,rfl⟩; exact B.property
    have hTcard : T.ncard = X.localSize x₀.val := by
      rw [show T = Subtype.val '' ((F.val : Finset ↥X.bigTwin) : Set ↥X.bigTwin) from rfl,
        Set.ncard_image_of_injective _ Subtype.val_injective,Set.ncard_coe_finset]
      exact F.property
    obtain ⟨y,hy,hTy⟩ := X.exists_traceClass hd.twin_pairwise x₀.property.1 hTsub hTcard
    have hyA : y ∈ X.domClass α := hd.traceClass_subset_domClass x₀.property hTcard ⟨hy,hTy⟩
    refine ⟨⟨y,hyA⟩,Subtype.ext ?_⟩
    change X.traceFinset y = F.val
    ext B
    rw [X.mem_traceFinset y B]
    constructor
    · intro hB
      have hm : B.val ∈ T := by rw [← hTy]; exact ⟨hB,B.property⟩
      obtain ⟨D,hD,hDB⟩ := hm
      have : D = B := Subtype.ext hDB
      exact this ▸ hD
    · intro hB
      have hm : B.val ∈ T := ⟨B,hB,rfl⟩
      rw [← hTy] at hm
      exact hm.1

noncomputable def designDomTraceEquiv : ↥(X.domClass α) ≃ binom ↥X.bigTwin (X.localSize x₀.val) :=
  Equiv.ofBijective _ (designDomTraceMap_bijective hd hinj x₀)

include hinj in
theorem designDom_choose : (X.domClass α).ncard = X.bigTwin.ncard.choose (X.localSize x₀.val) := by
  classical
  letI : Fintype ↥X.bigTwin := Fintype.ofFinite _
  have hh := Nat.card_congr (designDomTraceEquiv hd hinj x₀)
  rw [Nat.card_coe_set_eq,Nat.card_eq_fintype_card,Fintype.card_finset_len,
    ← Nat.card_eq_fintype_card,Nat.card_coe_set_eq] at hh
  exact hh

include hinj in
theorem designDom_parameters (hbound : X.bigTwin.ncard ≠ 2 * X.localSize x₀.val) :
    2 ≤ min (X.localSize x₀.val) (X.bigTwin.ncard - X.localSize x₀.val) ∧
    2 * min (X.localSize x₀.val) (X.bigTwin.ncard - X.localSize x₀.val) + 1 ≤
      X.bigTwin.ncard := by
  have hlt : X.bigTwin.ncard < X.bigTwin.ncard.choose (X.localSize x₀.val) := by
    rw [← designDom_choose hd hinj x₀]
    exact hd.bigTwin_ncard_lt
  have hd1 := hd.one_le_localSize x₀.property
  have hdc := hd.localSize_lt x₀.property
  obtain ⟨h1,h2⟩ := two_le_and_add_two_le_of_lt_choose (by omega) hlt
  omega

end
end Algo
