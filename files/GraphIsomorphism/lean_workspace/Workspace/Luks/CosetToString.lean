import Workspace.Luks.Defs

/-!
# Coset Intersection as String Isomorphism

Sec. 1.1 cites Luks [Lu82, Lu93] for the polynomial equivalence of CI and SI.
Here we prove the mathematical CI-to-SI reduction. The two copies of the vertex
set are the coordinates of a Cartesian product. One string marks the diagonal,
and the other marks the graph of `τ⁻¹ * σ`.

The paper's right coset `Gσ` is Lean's set `{σ * g | g ∈ G}`. With this
translation, the two cosets meet exactly when `σ * g = τ * h` for some
`g ∈ G` and `h ∈ H`. Such a pair sends the diagonal onto that permutation graph.
-/

namespace Babai.CosetToString

open Equiv Classical

variable {Ω : Type*}

/-- The paper's right coset, after reversing the multiplication convention. -/
def coset (G : Subgroup (Perm Ω)) (σ : Perm Ω) : Set (Perm Ω) :=
  {ρ | ∃ g ∈ G, ρ = σ * g}

/-- The componentwise action on the Cartesian product. -/
def productAction : (Perm Ω × Perm Ω) →* Perm (Ω × Ω) where
  toFun p := Equiv.prodCongr p.1 p.2
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The SI group is the image of `G × H` in its componentwise action. -/
def productGroup (G H : Subgroup (Perm Ω)) : Subgroup (Perm (Ω × Ω)) :=
  (G.prod H).map productAction

/-- A binary string marking the graph of a permutation. -/
noncomputable def graphString (σ : Perm Ω) (p : Ω × Ω) : Fin 2 :=
  if p.2 = σ p.1 then 1 else 0

theorem graphString_eq_one (σ : Perm Ω) (p : Ω × Ω) :
    graphString σ p = 1 ↔ p.2 = σ p.1 := by
  by_cases h : p.2 = σ p.1 <;> simp [graphString, h]

theorem graphString_eq (σ τ : Perm Ω) (p q : Ω × Ω) :
    graphString σ p = graphString τ q ↔ (p.2 = σ p.1 ↔ q.2 = τ q.1) := by
  by_cases h : p.2 = σ p.1 <;> by_cases h' : q.2 = τ q.1 <;>
    simp [graphString, h, h']

/-- The image of the diagonal is the desired graph precisely when the coset
representatives agree after multiplication by the two group elements. -/
theorem preserves_iff (σ τ g h : Perm Ω) :
    (∀ p, graphString 1 p = graphString (τ⁻¹ * σ) (productAction (g, h) p)) ↔
      σ * g = τ * h := by
  constructor
  · intro hp
    apply Equiv.ext
    intro u
    have he : graphString (τ⁻¹ * σ) (g u, h u) = 1 := by
      simpa [graphString, productAction] using (hp (u, u)).symm
    have he' := congrArg τ ((graphString_eq_one _ _).mp he)
    simpa [Perm.mul_apply] using he'.symm
  · intro he p
    rw [graphString_eq]
    change p.2 = p.1 ↔ h p.2 = τ⁻¹ (σ (g p.1))
    have he' : τ⁻¹ (σ (g p.1)) = h p.1 := by
      have := congrArg (fun π : Perm Ω => τ⁻¹ (π p.1)) he
      simpa [Perm.mul_apply] using this
    rw [he', h.injective.eq_iff]

private theorem strIso_iff {A : Type*} (K : Set (Perm Ω)) (x y : Ω → A) (π : Perm Ω) :
    π ∈ strIso K x y ↔ π ∈ K ∧ ∀ u, x u = y (π u) := by
  constructor
  · rintro ⟨hπ, h⟩
    refine ⟨hπ, fun u => ?_⟩
    simpa [strAct] using congrFun h (π u)
  · rintro ⟨hπ, h⟩
    exact ⟨hπ, funext fun u => by simpa [strAct] using h (π⁻¹ u)⟩

/-- **Corollary 1.1.2, Sec. 1.1, mathematical CI reduction.** The paper's
cosets `Gσ` and `Hτ` meet exactly when the diagonal string and the string marking
`τ⁻¹ * σ` are isomorphic under `G × H` on `Ω × Ω`.
For `Ω = Fin n`, this SI instance has `n²` positions and two letters. -/
theorem decision (G H : Subgroup (Perm Ω)) (σ τ : Perm Ω) :
    (coset G σ ∩ coset H τ).Nonempty ↔
      (strIso (productGroup G H) (graphString 1) (graphString (τ⁻¹ * σ))).Nonempty := by
  constructor
  · rintro ⟨ρ, ⟨g, hg, hρg⟩, ⟨h, hh, hρh⟩⟩
    refine ⟨productAction (g, h), (strIso_iff _ _ _ _).mpr ⟨?_, ?_⟩⟩
    · exact Subgroup.mem_map.mpr ⟨(g, h), ⟨hg, hh⟩, rfl⟩
    · exact (preserves_iff σ τ g h).mpr (hρg.symm.trans hρh)
  · rintro ⟨π, hπ⟩
    obtain ⟨hG, hstr⟩ := (strIso_iff _ _ _ _).mp hπ
    obtain ⟨⟨g, h⟩, ⟨hg, hh⟩, rfl⟩ := hG
    have he := (preserves_iff σ τ g h).mp hstr
    exact ⟨σ * g, ⟨g, hg, rfl⟩, ⟨h, hh, he⟩⟩

end Babai.CosetToString

#print axioms Babai.CosetToString.decision
