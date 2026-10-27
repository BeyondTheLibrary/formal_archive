import Workspace.Algo.DesignReadFamilyValidity

/-! # Validity at the actual Section 9.7 call

The block-design hypotheses already imply the arity guard and the minimum
domain size. Thus every computed version satisfies the required partition
or dominant-UPCC condition, with no additional read-off assumptions.
-/
namespace Algo
open Babai RAM
open scoped Classical

section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {X : BlkDesignObj s} {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {r : RawUpccCase} (h : DesignNames X name₁ name₂ r)
    (e₁ : ↥X.Pt₁ ≃ Fin r.2.1.length) (he₁ : ∀ x,r.2.1[(e₁ x).val] = name₁ x)
    (e₂ : ↥X.blocks ≃ Fin r.2.2.length) (he₂ : ∀ B,r.2.2[(e₂ B).val] = name₂ B)
include h he₁ he₂

theorem designCallReadFamily_partition_valid (hlt : X.n₂ < X.n₁)
    (h1 : ¬ X.IsCase1) (h2 : ¬ X.IsCase2)
    {xs : List ℕ} {o : RawDesignReadOut} (ho : (xs,o) ∈ designCallReadFamily r)
    {P : RawColPart} (hP : o.1 = some P) :
    (decColPartition r.2.2.length P).IsAlphaPartition ((3:ℝ)/4) := by
  obtain ⟨hk2,hkn,_⟩ := designCall_hypotheses h e₁ he₁ e₂ he₂ hlt h1 h2
  exact ambientDesignReadFamily_partition_valid List.nodup_range
    (fun i => List.mem_range) rfl (designCall_guard h e₁ he₁ e₂ he₂ hlt)
    (by norm_num : 0 < 4) rfl (by norm_num) (by omega) ho hP

theorem designCallReadFamily_upcc_valid (hlt : X.n₂ < X.n₁)
    {xs : List ℕ} {o : RawDesignReadOut} (ho : (xs,o) ∈ designCallReadFamily r)
    {q : RawConfig} (hq : o.2.2 = some q) :
    IsUPCCColoring (designReadNamedColor r.2.2.length o.2.1 q) ∧
      IsDominant ((3:ℝ)/4) (winSet r.2.2.length o.2.1) ∧
      ∃ Z : PartitionStructure (Fin o.2.1.length),Z.IsCoherent ∧ Z.IsUniprimitive ∧
        ∀ u v : Fin o.2.1.length,binColor (q,(u,v)) = Z.natColor u v := by
  exact ambientDesignReadFamily_upcc_valid List.nodup_range
    (fun i => List.mem_range) rfl (designCall_guard h e₁ he₁ e₂ he₂ hlt)
    (by norm_num : 0 < 4) rfl (by norm_num) ho hq

end
end Algo
