import Workspace.Refinement.NamedWL
import Workspace.SplitOrJohnson.NatColor

/-!
# Configurations with ordered integer names

Restriction can leave gaps in the names. Ranking the old names closes those gaps.
For a stable coloring this is also a named WL round: the old name is the first tag
entry and no class splits. Thus restrictions use the same order as refinement.
-/

namespace Babai.WL

variable {V C D : Type*}

/-- Coherence depends on the classes of a coloring. -/
theorem named_coherent_congr {c : V → V → C} {d : V → V → D}
    (hk : ∀ a b x y, c a b = c x y ↔ d a b = d x y)
    (hc : IsCoherentColoring c) : IsCoherentColoring d := by
  have hd : IsConfigColoring d :=
    ⟨fun a b x he => hc.1.1 a b x ((hk a b x x).2 he),
      fun a b x y he => (hk b a y x).1 (hc.1.2 a b x y ((hk a b x y).2 he))⟩
  apply (isStable_iff_isCoherentColoring hd).1
  intro a b x y he
  exact (step_congr hk a b x y).1
    ((isStable_iff_isCoherentColoring hc.1).2 hc a b x y ((hk a b x y).2 he))

variable [Fintype V]

/-- Old integer names, treated as one-entry tags. -/
def namedCodes (c : V → V → ℕ) : Finset (List ℕ) :=
  Finset.univ.image fun p : V × V => [c p.1 p.2]

theorem namedCodes_mem (c : V → V → ℕ) (u v : V) : [c u v] ∈ namedCodes c :=
  Finset.mem_image.2 ⟨(u, v), Finset.mem_univ _, rfl⟩

theorem namedCodes_length (c : V → V → ℕ) (t : List ℕ) (ht : t ∈ namedCodes c) :
    t.length = 1 := by
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.1 ht
  rfl

/-- Close gaps in integer names while keeping their order. -/
def namedRecode (c : V → V → ℕ) (u v : V) : ℕ := namedRank (namedCodes c) [c u v]

theorem namedRecode_eq_iff (c : V → V → ℕ) (a b x y : V) :
    namedRecode c a b = namedRecode c x y ↔ c a b = c x y := by
  rw [namedRecode, namedRecode,
    namedRank_inj (namedCodes_length c) (namedCodes_mem c a b) (namedCodes_mem c x y)]
  simp

theorem namedRecode_image (c : V → V → ℕ) :
    Finset.univ.image (fun p : V × V => namedRecode c p.1 p.2) =
      Finset.range (namedCodes c).card := by
  rw [← namedRank_image (namedCodes_length c), namedCodes, Finset.image_image]
  rfl

/-- On a stable coloring, closing gaps is exactly one named WL round. -/
theorem namedRecode_eq_step {c : V → V → ℕ} [DecidableEq V] (hs : IsStable c) :
    namedRecode c = namedStep c := by
  funext u v
  have htag : ∀ a b x y, c a b = c x y → namedTag c a b = namedTag c x y :=
    fun a b x y h => (namedTag_eq_iff c a b x y).2 (hs a b x y h)
  have hcmp (a b : V) :
      Algo.cmpRec (namedTag c a b) (namedTag c u v) = Algo.cmpRec [c a b] [c u v] := by
    rcases lt_trichotomy (c a b) (c u v) with h | h | h
    · simp [namedTag, Algo.cmpRec_cons, h]
    · rw [htag a b u v h, Algo.cmpRec_self, h, Algo.cmpRec_self]
    · simp [namedTag, Algo.cmpRec_cons, h, Nat.not_lt.2 (Nat.le_of_lt h)]
  symm
  unfold namedStep namedRecode namedRank
  refine Finset.card_bij (fun t _ => [t.headD 0]) ?_ ?_ ?_
  · intro t ht
    obtain ⟨ht, hc⟩ := Finset.mem_filter.1 ht
    obtain ⟨⟨a, b⟩, _, rfl⟩ := Finset.mem_image.1 ht
    exact Finset.mem_filter.2 ⟨namedCodes_mem c a b, by
      change Algo.cmpRec [c a b] [c u v] = 1
      exact (hcmp a b).symm.trans hc⟩
  · intro s hs t ht he
    obtain ⟨⟨a, b⟩, _, rfl⟩ := Finset.mem_image.1 (Finset.mem_filter.1 hs).1
    obtain ⟨⟨x, y⟩, _, rfl⟩ := Finset.mem_image.1 (Finset.mem_filter.1 ht).1
    exact htag a b x y (List.cons.inj he).1
  · intro t ht
    obtain ⟨ht, hc⟩ := Finset.mem_filter.1 ht
    obtain ⟨⟨a, b⟩, _, rfl⟩ := Finset.mem_image.1 ht
    exact ⟨namedTag c a b, Finset.mem_filter.2 ⟨namedTag_mem c a b, by rwa [hcmp]⟩, rfl⟩

end Babai.WL

namespace Babai.PartitionStructure

variable {V W : Type*} [Finite V]

/-- Definition 3.1.1 with ordered integer names. On coherent inputs this is a named
round of Sections 4.1.1 and 4.3, by `WL.namedRecode_eq_step`. -/
noncomputable def ofNamedColoring (c : V → V → ℕ) : PartitionStructure V := by
  classical
  letI : Fintype V := Fintype.ofFinite _
  exact {
    rank := (WL.namedCodes c).card
    color := fun u v => ⟨WL.namedRecode c u v, WL.namedRank_lt (WL.namedCodes_mem c u v)⟩
    color_surjective := fun i => by
      obtain ⟨⟨u, v⟩, _, hi⟩ := Finset.mem_image.1
        ((WL.namedRecode_image c).symm ▸ Finset.mem_range.2 i.isLt)
      exact ⟨u, v, Fin.ext hi⟩ }

theorem natColor_ofNamedColoring (c : V → V → ℕ) (u v : V) :
    (ofNamedColoring c).natColor u v =
      @WL.namedRecode V (Fintype.ofFinite _) c u v := rfl

theorem ofNamedColoring_color_eq_iff (c : V → V → ℕ) (a b x y : V) :
    (ofNamedColoring c).color a b = (ofNamedColoring c).color x y ↔ c a b = c x y := by
  letI : Fintype V := Fintype.ofFinite _
  rw [← (ofNamedColoring c).natColor_eq_iff, natColor_ofNamedColoring,
    natColor_ofNamedColoring, WL.namedRecode_eq_iff]

/-- A partition structure with the classes of a coherent coloring is coherent. -/
theorem named_isCoherent_of_kernel {C : Type*} (X : PartitionStructure V)
    {c : V → V → C} (hc : WL.IsCoherentColoring c)
    (hk : ∀ a b x y, c a b = c x y ↔ X.color a b = X.color x y) : X.IsCoherent := by
  have h := WL.named_coherent_congr hk hc
  exact ⟨⟨h.1.1, h.1.2⟩, h.2⟩

/-- Renaming a coherent coloring keeps it coherent. -/
theorem isCoherent_ofNamedColoring {c : V → V → ℕ} (hc : WL.IsCoherentColoring c) :
    (ofNamedColoring c).IsCoherent :=
  named_isCoherent_of_kernel _ hc fun a b x y => (ofNamedColoring_color_eq_iff c a b x y).symm

/-- A bijection preserving the input names preserves the new names. -/
theorem natColor_ofNamedColoring_map [Finite W]
    {c : V → V → ℕ} {d : W → W → ℕ} (e : V ≃ W)
    (h : ∀ u v, d (e u) (e v) = c u v) (u v : V) :
    (ofNamedColoring d).natColor (e u) (e v) = (ofNamedColoring c).natColor u v := by
  classical
  letI : Fintype V := Fintype.ofFinite _
  letI : Fintype W := Fintype.ofFinite _
  have he : WL.namedCodes d = WL.namedCodes c := by
    ext t
    simp only [WL.namedCodes, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨a, b⟩, rfl⟩
      exact ⟨(e.symm a, e.symm b), by simp only [← h, Equiv.apply_symm_apply]⟩
    · rintro ⟨⟨a, b⟩, rfl⟩
      exact ⟨(e a, e b), by rw [h]⟩
  simp only [natColor_ofNamedColoring, WL.namedRecode, he, h]

end Babai.PartitionStructure
