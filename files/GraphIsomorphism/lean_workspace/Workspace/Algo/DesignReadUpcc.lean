import Workspace.Algo.DesignReadExit

/-! # Canonical names for the returned UPCC

A raw skeleton can have gaps in its colors. Before returning the UPCC,
the read-off closes these gaps in increasing order. This is exactly the
natural coloring of the structure built from the computed pair table.
-/
namespace Algo
open Babai RAM

/-- The component branch uses exactly the first disconnected-color test. -/
theorem designReadHasComponents_spec (z : DIn) :
    designReadHasComponents z = true ↔ z.1.1.2.length + 2 ≤ z.1.1.1.length ∧
      ∃ k, IsDisconnectedColor (namedBin (designDomPairs z).1.length (designDomPairs z)) k := by
  simp only [designReadHasComponents,designReadHasSkeleton,Bool.and_eq_true,decide_eq_true_eq,
    sbipImprimitive_spec]

theorem designReadUpccTable_names {V : Type*} [Finite V] (z : DIn)
    (e : V ≃ Fin (dominantList z).length) (u v : V) :
    binColor (designReadUpccTable z,(e u,e v)) =
      (PartitionStructure.ofNamedColoring (fun a b : V =>
        binColor (designDomPairs z,(e a,e b)))).natColor u v := by
  apply sbipRecode_spec (designDomPairs z) (fun a => (e a).val)
  intro a
  change a ∈ List.range (dominantList z).length ↔ ∃ u, (e u).val = a
  rw [List.mem_range]
  exact ⟨fun ha => ⟨e.symm ⟨a,ha⟩,congrArg Fin.val (e.apply_symm_apply _)⟩,
    fun ⟨u,hu⟩ => hu ▸ (e u).isLt⟩

/-- Returning tuple families do not lose an output when the object is read. -/
theorem designCallReadFamily_nonempty {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {X : BlkDesignObj s} {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {r : RawUpccCase} (h : DesignNames X name₁ name₂ r)
    (e₁ : ↥X.Pt₁ ≃ Fin r.2.1.length) (he₁ : ∀ x, r.2.1[(e₁ x).val] = name₁ x)
    (e₂ : ↥X.blocks ≃ Fin r.2.2.length) (he₂ : ∀ B, r.2.2[(e₂ B).val] = name₂ B)
    (hlt : X.n₂ < X.n₁) (h1 : ¬ X.IsCase1) (h2 : ¬ X.IsCase2) :
    ∃ o, o ∈ designCallReadFamily r := by
  obtain ⟨xs,hxs⟩ := designCallVersions_nonempty h e₁ he₁ e₂ he₂ hlt h1 h2
  exact ⟨_,List.mem_map.2 ⟨xs,hxs,rfl⟩⟩

end Algo
