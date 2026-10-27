import Workspace.Algo.SplitPartitionTransport
import Workspace.DesignLemma.Reduction
import Workspace.SplitOrJohnson.BlockSystem

/-! # The component family selected by the raw color order

Proposition 3.4.4 applies to any disconnected non-diagonal constituent.
We use the one selected by the raw numeric color order. Its components form
the dominant-class part of the same mathematical colored partition used in
the Design Lemma proof.
-/
namespace Algo
open Babai Equiv
open scoped Classical

noncomputable def designBlockFamily {V : Type*} (D : Set V) (c : D → D → ℕ) : Set (Set V) :=
  (fun A : Set D => Subtype.val '' A) '' blocks c

theorem designBlockFamily_subset {V : Type*} {D : Set V} {c : D → D → ℕ}
    {A : Set V} (hA : A ∈ designBlockFamily D c) : A ⊆ D := by
  obtain ⟨B,_,rfl⟩ := hA
  rintro a ⟨b,_,rfl⟩
  exact b.property

theorem designBlockFamily_rel {V : Type*} (D : Set V) (c : D → D → ℕ) (u v : D) :
    (∀ A ∈ designBlockFamily D c,u.val ∈ A ↔ v.val ∈ A) ↔ v ∈ blockOf c u := by
  constructor
  · intro h
    have hm : u.val ∈ Subtype.val '' blockOf c u := ⟨u,mem_blockOf_self c u,rfl⟩
    obtain ⟨w,hw,he⟩ := (h _ ⟨blockOf c u,blockOf_mem_blocks c u,rfl⟩).mp hm
    have he' : w = v := Subtype.ext he
    exact he' ▸ hw
  · intro hv A hA
    obtain ⟨B,⟨w,rfl⟩,rfl⟩ := hA
    have huv : blockOf c u = blockOf c v :=
      ((colorDigraph c (blockColor c)).weakComponent_eq_of_mem hv).symm
    have hmem (a : D) : a.val ∈ Subtype.val '' blockOf c w ↔ a ∈ blockOf c w := by
      constructor
      · rintro ⟨b,hb,he⟩
        exact (Subtype.ext he : b = a) ▸ hb
      · intro ha
        exact ⟨a,ha,rfl⟩
    change u.val ∈ Subtype.val '' blockOf c w ↔ v.val ∈ Subtype.val '' blockOf c w
    rw [hmem,hmem]
    constructor
    · intro hu
      have huw : blockOf c u = blockOf c w :=
        (colorDigraph c (blockColor c)).weakComponent_eq_of_mem hu
      rw [← huw,huv]
      exact mem_blockOf_self c v
    · intro hvw
      have hvw' : blockOf c v = blockOf c w :=
        (colorDigraph c (blockColor c)).weakComponent_eq_of_mem hvw
      rw [← hvw',← huv]
      exact mem_blockOf_self c u

theorem designBlockFamily_partition {V : Type*} [Finite V] {D : Set V}
    {c : D → D → ℕ} {P : PartitionStructure D}
    (hcoh : P.IsCoherent) (hhom : P.IsHomogeneous) (hker : SameKernel c P.natColor)
    (hdisc : ∃ j,IsDisconnectedColor c j) :
    IsEquipartitionOn (designBlockFamily D c) D ∧ IsNontrivialPartition (designBlockFamily D c) := by
  have he := isEquipartition_blocks_of_sameKernel hcoh hhom hker hdisc
  have h2 := (colorDigraph c (blockColor c)).exists_ne_weakComponents (blockColor_spec hdisc).2.2
  apply isEquipartitionOn_image (blocks c) he h2
  rintro A ⟨u,rfl⟩
  exact blockOf_nontrivial_of_sameKernel hcoh hhom hker hdisc u

end Algo
