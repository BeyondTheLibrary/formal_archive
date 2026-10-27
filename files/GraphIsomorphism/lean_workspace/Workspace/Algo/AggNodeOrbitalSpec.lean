import Workspace.Algo.AggNodeOrbitalRows

/-! # Exactness and choice count of the orbital enumeration -/
namespace Algo
open RAM RAM.Targets Babai Equiv MulAction
open scoped Classical

theorem aggnPairRow_length (dom C : List ℕ) :
    (aggnPairRow (dom,C)).length ≤ C.length - 1 := by
  cases C with
  | nil => simp [aggnPairRow]
  | cons a C =>
    simp only [aggnPairRow,List.headD_cons,List.filter_cons,ne_eq,not_true_eq_false,
      decide_false,Bool.false_eq_true,↓reduceIte,List.length_map,List.length_cons,Nat.add_sub_cancel]
    exact List.length_filter_le _ _

theorem aggnOrbitals_length (p : (List ℕ × RawGens) × List ℕ) :
    (aggnOrbitals p).length ≤ p.2.length - 1 := by
  rw [aggnOrbitals,List.length_map]
  exact (length_winOrbits_le _ _).trans (aggnPairRow_length _ _)

theorem aggnPairRow_mem {m : ℕ} {dom C : List ℕ} (hd : dom.length = m)
    (hC : ∀ u ∈ C,u < m) {j : ℕ} (hj : j ∈ aggnPairRow (dom,C)) :
    ∃ a b : Fin m, a.val = C.headD 0 ∧ a.val ∈ C ∧ b.val ∈ C ∧ a ≠ b ∧
      j = aggnPairName (m,(a.val,b.val)) := by
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hj
  obtain ⟨hb,hne⟩ := List.mem_filter.mp hb
  have ha : C.headD 0 ∈ C := by cases C <;> simp_all
  refine ⟨⟨_,hC _ ha⟩,⟨b,hC _ hb⟩,rfl,ha,hb,?_,?_⟩
  · intro he
    exact (of_decide_eq_true hne) (congrArg Fin.val he).symm
  · rw [hd]

theorem aggnPairRow_lt {m : ℕ} {dom C : List ℕ} (hd : dom.length = m)
    (hC : ∀ u ∈ C,u < m) : ∀ j ∈ aggnPairRow (dom,C),j < m*m := by
  intro j hj
  obtain ⟨a,b,_,_,_,_,rfl⟩ := aggnPairRow_mem hd hC hj
  exact (finProdFinEquiv (a,b)).isLt

/-- Every returned relation is a non-diagonal orbital based in the given window. -/
theorem aggnOrbitals_mem {m : ℕ} {dom C : List ℕ} {gs : RawGens}
    (hd : dom.length = m) (hw : RawGens.WF m gs) (hC : ∀ u ∈ C,u < m)
    {R : RawRel} (hR : R ∈ aggnOrbitals ((dom,gs),C)) :
    ∃ a b : Fin m,a.val ∈ C ∧ b.val ∈ C ∧ a ≠ b ∧
      aggnDecodePairRel m R = {uv | ∃ g ∈ decGroup m gs,g a = uv.1 ∧ g b = uv.2} := by
  obtain ⟨orb,ho,rfl⟩ := List.mem_map.mp hR
  obtain ⟨j,hj,rfl⟩ := winOrbits_mem ho
  obtain ⟨a,b,_,ha,hb,hab,rfl⟩ := aggnPairRow_mem hd hC hj
  refine ⟨a,b,ha,hb,hab,?_⟩
  simpa only [aggnPairOrbit,hd] using aggnPairRel_orbit hd hw a b

private theorem aggnPairRel_of_orbit_mem {m : ℕ} {dom C orb : List ℕ} {gs : RawGens}
    (hd : dom.length = m) (hw : RawGens.WF m gs) (hC : ∀ u ∈ C,u < m)
    (ho : orb ∈ winOrbits (aggnPairGens (dom,gs),aggnPairRow (dom,C)))
    (a b : Fin m) (hab : aggnPairName (m,(a.val,b.val)) ∈ orb) :
    aggnDecodePairRel m (aggnPairRel (dom,orb)) =
      {uv | ∃ g ∈ decGroup m gs,g a = uv.1 ∧ g b = uv.2} := by
  obtain ⟨j,hj,rfl⟩ := winOrbits_mem ho
  have hjlt := aggnPairRow_lt hd hC j hj
  have hab' : finProdFinEquiv (a,b) ∈
      winSet (m*m) (rawOrbit (aggnPairGens (dom,gs),j)) := hab
  rw [winSet_rawOrbit (aggnPairGens_wf hd hw) ⟨j,hjlt⟩] at hab'
  have he := orbit_eq_iff.mpr hab'
  rw [← aggnPairRel_orbit hd hw a b]
  ext uv
  rw [aggnPairRel_mem hd,aggnPairRel_mem hd]
  change finProdFinEquiv uv ∈ winSet (m*m) (rawOrbit (aggnPairGens (dom,gs),j)) ↔
    finProdFinEquiv uv ∈ winSet (m*m) (aggnPairOrbit ((dom,gs),(a.val,b.val)))
  rw [winSet_rawOrbit (aggnPairGens_wf hd hw) ⟨j,hjlt⟩]
  change _ ↔ finProdFinEquiv uv ∈ winSet (m*m)
    (rawOrbit (aggnPairGens (dom,gs),aggnPairName (dom.length,(a.val,b.val))))
  rw [hd]
  change _ ↔ finProdFinEquiv uv ∈ winSet (m*m)
    (rawOrbit (aggnPairGens (dom,gs),(finProdFinEquiv (a,b)).val))
  rw [winSet_rawOrbit (aggnPairGens_wf hd hw) (finProdFinEquiv (a,b)),he]

/-- Transitivity makes the chosen row cover every non-diagonal orbital. -/
theorem aggnOrbitals_complete {m : ℕ} {dom C : List ℕ} {gs : RawGens}
    (hd : dom.length = m) (hw : RawGens.WF m gs) (hC : ∀ u ∈ C,u < m)
    (hinv : IsInvariant (decGroup m gs) (winSet m C))
    (htr : ∀ a ∈ winSet m C,∀ b ∈ winSet m C,∃ g ∈ decGroup m gs,g a = b)
    (a b : Fin m) (ha : a.val ∈ C) (hb : b.val ∈ C) (hab : a ≠ b) :
    ∃ R ∈ aggnOrbitals ((dom,gs),C),aggnDecodePairRel m R =
      {uv | ∃ g ∈ decGroup m gs,g a = uv.1 ∧ g b = uv.2} := by
  have hah : C.headD 0 ∈ C := by cases C <;> simp_all
  let a₀ : Fin m := ⟨C.headD 0,hC _ hah⟩
  obtain ⟨g,hg,hga⟩ := htr a ha a₀ hah
  have hgb : (g b).val ∈ C := ((isInvariant_iff_mem _ _).mp hinv g hg b).mp hb
  have hne : (g b).val ≠ C.headD 0 := by
    intro he
    have he' : g b = a₀ := Fin.ext he
    exact hab (g.injective (hga.trans he'.symm))
  have hj : aggnPairName (m,(a₀.val,(g b).val)) ∈ aggnPairRow (dom,C) := by
    apply List.mem_map.mpr
    refine ⟨(g b).val,List.mem_filter.mpr ⟨hgb,by simpa using hne⟩,?_⟩
    rw [hd]
  obtain ⟨orb,ho,hjmem⟩ := List.mem_flatten.mp
    (winOrbits_cover (aggnPairGens_wf hd hw) (aggnPairRow_lt hd hC) hj)
  refine ⟨aggnPairRel (dom,orb),List.mem_map.mpr ⟨orb,ho,rfl⟩,?_⟩
  rw [aggnPairRel_of_orbit_mem hd hw hC ho a₀ (g b) hjmem,← hga]
  ext uv
  constructor
  · rintro ⟨h,hh,ha',hb'⟩
    exact ⟨h*g,(decGroup m gs).mul_mem hh hg,ha',hb'⟩
  · rintro ⟨h,hh,ha',hb'⟩
    refine ⟨h*g⁻¹,(decGroup m gs).mul_mem hh ((decGroup m gs).inv_mem hg),?_,?_⟩
    · simpa using ha'
    · simpa using hb'

end Algo
