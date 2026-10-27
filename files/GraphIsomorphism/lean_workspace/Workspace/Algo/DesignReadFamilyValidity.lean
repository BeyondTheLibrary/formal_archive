import Workspace.Algo.DesignReadNamesValidity

/-! # Validity of every computed Design Lemma version

Each family member comes from a returning tuple. The refinement pipeline
supplies coherence, so the raw read-off validity theorems apply to the
actual computed family without further semantic inputs.
-/
namespace Algo
open Babai RAM
open scoped Classical
set_option quotPrecheck false

/-- The concrete refinement pipeline is coherent on every admitted input. -/
theorem ambientPipeline321_isCoherent {n k c : ℕ} {ks base dom : List ℕ}
    {rels : RawRelStruct} (hnd : dom.Nodup) (hmem : ∀ i,i ∈ dom ↔ i < n)
    (hk : ks.length = k) (hg : ks.length ≤ guardBound c base.length) :
    (decWL n k (ambientPipeline321 c ((ks,base,dom),rels))).IsCoherent := by
  subst k
  apply KAryPartStruct.isCoherent_congr (fun u v => (ambientPipeline321_spec (n := n) (c := c) (a := ((ks,base,dom),rels)) hnd hmem hg u v).symm)
  exact KAryPartStruct.F3_isCoherent _ (KAryPartStruct.F2_isConfiguration _)

theorem ambientDesignReadFamily_mem (c : ℕ) (g : AmbientGIn) (xs : List ℕ) (o : RawDesignReadOut) :
    (xs,o) ∈ ambientDesignReadFamily c g ↔ xs ∈ ambientDesignVersions c g ∧
      o = designReadExit (ambientDesignAt c g xs) := by
  simp only [ambientDesignReadFamily,designReadAt,List.mem_map,Prod.mk.injEq]
  constructor
  · rintro ⟨ys,hy,he,ho⟩; subst ys; exact ⟨hy,ho.symm⟩
  · rintro ⟨hx,rfl⟩; exact ⟨xs,hx,rfl,rfl⟩

section
variable {n k a b c : ℕ} {ks base dom : List ℕ} {rels : RawRelStruct}
    (hnd : dom.Nodup) (hmem : ∀ i,i ∈ dom ↔ i < n) (hk : ks.length = k)
    (hg : ks.length ≤ guardBound c base.length) {α : ℝ} (hb : 0 < b) (hab : α = (a:ℝ)/b)
local notation "g" => (((ks,base,dom),rels),(a,b))
include hnd hmem hk hg hb hab

/-- An actual member supplies its well-typed returning tuple. -/
theorem ambientDesignVersions_witness {ys : List ℕ} (hy : ys ∈ ambientDesignVersions c g) :
    ∃ l,∃ hl : l < k,∃ x : Str (Fin n) l,tupleOf x = ys ∧
      returnsB (ambientDesignAt c g ys) = true := by
  have hs : ∃ xs,ambientDesignProcedure c g = some xs := by
    cases hh : ambientDesignProcedure c g with
    | none => simp [ambientDesignVersions,hh] at hy
    | some xs => exact ⟨xs,rfl⟩
  obtain ⟨xs,hs⟩ := hs
  obtain ⟨l,hl,_,_,hnames,_⟩ := ambientDesignVersions_spec hnd hmem hk hg hb hab hs
  obtain ⟨x,hx⟩ := exists_tupleOf (hnames ys hy).1 (hnames ys hy).2
  refine ⟨l,hl,x,hx,?_⟩
  rw [ambientDesignVersions,hs] at hy
  exact (List.mem_filter.mp hy).2

/-- Every partition in the actual family is an alpha-partition. -/
theorem ambientDesignReadFamily_partition_valid (hα : 1/2 ≤ α) (hn : 4 ≤ n)
    {xs : List ℕ} {o : RawDesignReadOut} (ho : (xs,o) ∈ ambientDesignReadFamily c g)
    {P : RawColPart} (hP : o.1 = some P) : (decColPartition n P).IsAlphaPartition α := by
  obtain ⟨hxs,rfl⟩ := (ambientDesignReadFamily_mem c g xs o).mp ho
  obtain ⟨l,hl,x,hx,hr⟩ := ambientDesignVersions_witness hnd hmem hk hg hb hab hxs
  rw [← hx] at hr hP
  exact designReadExit_partition_valid
    (hk ▸ ambientPipeline321_wf (n := n) (c := c) (a := ((ks,base,dom),rels)) hnd hmem hg) hk hl.le x hb hab hα hn
    (ambientPipeline321_isCoherent (rels := rels) hnd hmem hk hg) hr hP

/-- Every configuration in the actual family is a UPCC on a dominant old-name subset. -/
theorem ambientDesignReadFamily_upcc_valid (hα : 1/2 ≤ α)
    {xs : List ℕ} {o : RawDesignReadOut} (ho : (xs,o) ∈ ambientDesignReadFamily c g)
    {q : RawConfig} (hq : o.2.2 = some q) :
    IsUPCCColoring (designReadNamedColor n o.2.1 q) ∧ IsDominant α (winSet n o.2.1) ∧
      ∃ Z : PartitionStructure (Fin o.2.1.length),Z.IsCoherent ∧ Z.IsUniprimitive ∧
        ∀ u v : Fin o.2.1.length,binColor (q,(u,v)) = Z.natColor u v := by
  obtain ⟨hxs,rfl⟩ := (ambientDesignReadFamily_mem c g xs o).mp ho
  obtain ⟨l,hl,x,hx,_⟩ := ambientDesignVersions_witness hnd hmem hk hg hb hab hxs
  rw [← hx] at hq ⊢
  have hw := hk ▸ ambientPipeline321_wf (n := n) (c := c) (a := ((ks,base,dom),rels)) hnd hmem hg
  have hc := ambientPipeline321_isCoherent (rels := rels) hnd hmem hk hg
  exact ⟨designReadExit_named_upcc hw hk hl.le x hb hab hα hc hq,
    designReadExit_upcc_dominant hw hk hl.le x hb hab hα hc hq,
    designReadExit_position_upcc hw hk hl.le x hb hab hα hc hq⟩

end
end Algo
