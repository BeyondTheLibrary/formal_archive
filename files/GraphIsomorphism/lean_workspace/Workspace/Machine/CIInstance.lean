import Workspace.Machine.TargetsCI
import Mathlib.Logic.Equiv.Fin.Basic

/-! # The numbered CI-to-SI instance and its generators -/

namespace RAM.CIReduction

open Targets Equiv Babai Babai.CosetToString

/-- Number ordered pairs by `j + n * i`. -/
def action (n : ℕ) :
    (Perm (Fin n) × Perm (Fin n)) →* Perm (Fin (n * n)) :=
  finProdFinEquiv.permCongrHom.toMonoidHom.comp productAction

/-- Generators from the first factor, followed by generators from the second. -/
def gens {n : ℕ} (gs hs : List (Perm (Fin n))) : List (Perm (Fin (n * n))) :=
  gs.map (fun g => action n (g, 1)) ++ hs.map (fun h => action n (1, h))

theorem gens_generate {n : ℕ} (gs hs : List (Perm (Fin n))) :
    genGroup (gens gs hs) = ((genGroup gs).prod (genGroup hs)).map (action n) := by
  let K := genGroup (gens gs hs)
  let f : Perm (Fin n) →* Perm (Fin (n * n)) :=
    { toFun := fun g => action n (g, 1)
      map_one' := map_one (action n)
      map_mul' := fun g h => by simpa using (action n).map_mul (g, 1) (h, 1) }
  let k : Perm (Fin n) →* Perm (Fin (n * n)) :=
    { toFun := fun h => action n (1, h)
      map_one' := map_one (action n)
      map_mul' := fun g h => by simpa using (action n).map_mul (1, g) (1, h) }
  have hf : genGroup gs ≤ K.comap f := by
    apply (Subgroup.closure_le _).mpr
    intro g hg
    exact Subgroup.subset_closure (List.mem_append_left _ (List.mem_map.mpr ⟨g, hg, rfl⟩))
  have hk : genGroup hs ≤ K.comap k := by
    apply (Subgroup.closure_le _).mpr
    intro h hh
    exact Subgroup.subset_closure (List.mem_append_right _ (List.mem_map.mpr ⟨h, hh, rfl⟩))
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro π hπ
    rcases List.mem_append.mp hπ with hπ | hπ
    · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hπ
      exact ⟨(g, 1), ⟨Subgroup.subset_closure hg, Subgroup.one_mem _⟩, rfl⟩
    · obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hπ
      exact ⟨(1, h), ⟨Subgroup.one_mem _, Subgroup.subset_closure hh⟩, rfl⟩
  · rintro π ⟨⟨g, h⟩, ⟨hg, hh⟩, rfl⟩
    have hf' : action n (g, 1) ∈ K := hf hg
    have hk' : action n (1, h) ∈ K := hk hh
    have hm := K.mul_mem hf' hk'
    simpa only [← map_mul, Prod.mk_mul_mk, mul_one, one_mul] using hm

/-- The typed CI reduction. Its strings are the diagonal and the permutation graph. -/
noncomputable def instanceSI {n : ℕ} (a : CIInput n) : SIInput (n * n) 2 :=
  (gens a.1 a.2.1,
    graphString (1 : Perm (Fin n)) ∘ finProdFinEquiv.symm,
    graphString (a.2.2.2⁻¹ * a.2.2.1) ∘ finProdFinEquiv.symm)

theorem instanceSI_correct {n : ℕ} (a : CIInput n) :
    (IsoSet (instanceSI a).1 (instanceSI a).2.1 (instanceSI a).2.2).Nonempty ↔ CIYes a := by
  have hmem : ∀ π : Perm (Fin (n * n)),
      π ∈ IsoSet (instanceSI a).1 (instanceSI a).2.1 (instanceSI a).2.2 ↔
      ∃ g ∈ genGroup a.1, ∃ h ∈ genGroup a.2.1,
        action n (g, h) = π ∧ a.2.2.1 * g = a.2.2.2 * h := by
    intro π
    constructor
    · rintro ⟨hπ, hstr⟩
      change π ∈ genGroup (gens a.1 a.2.1) at hπ
      rw [gens_generate] at hπ
      obtain ⟨⟨g, h⟩, ⟨hg, hh⟩, rfl⟩ := hπ
      refine ⟨g, hg, h, hh, rfl, (preserves_iff _ _ _ _).mp fun p => ?_⟩
      have ht := hstr (finProdFinEquiv p)
      change graphString 1 (finProdFinEquiv.symm (finProdFinEquiv p)) =
        graphString (a.2.2.2⁻¹ * a.2.2.1)
          (finProdFinEquiv.symm (finProdFinEquiv
            (productAction (g, h) (finProdFinEquiv.symm (finProdFinEquiv p))))) at ht
      simpa only [Equiv.symm_apply_apply] using ht
    · rintro ⟨g, hg, h, hh, rfl, he⟩
      refine ⟨?_, fun i => ?_⟩
      · change action n (g, h) ∈ genGroup (gens a.1 a.2.1)
        rw [gens_generate]
        exact ⟨(g, h), ⟨hg, hh⟩, rfl⟩
      · change graphString 1 (finProdFinEquiv.symm i) =
          graphString (a.2.2.2⁻¹ * a.2.2.1)
            (finProdFinEquiv.symm (finProdFinEquiv (productAction (g, h) (finProdFinEquiv.symm i))))
        rw [Equiv.symm_apply_apply]
        exact (preserves_iff _ _ _ _).mpr he (finProdFinEquiv.symm i)
  constructor
  · rintro ⟨π, hπ⟩
    obtain ⟨g, hg, h, hh, _, he⟩ := (hmem π).mp hπ
    exact ⟨a.2.2.1 * g, ⟨g, hg, rfl⟩, ⟨h, hh, he⟩⟩
  · rintro ⟨ρ, ⟨g, hg, hρg⟩, ⟨h, hh, hρh⟩⟩
    exact ⟨action n (g, h), (hmem _).mpr ⟨g, hg, h, hh, rfl, hρg.symm.trans hρh⟩⟩

end RAM.CIReduction
