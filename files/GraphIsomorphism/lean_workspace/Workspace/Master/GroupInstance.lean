/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 15: the instances the Master Algorithm produces are again instances with respect to
a group, on a window invariant under it.
-/
import Workspace.Master.Line2

/-!
# The group invariant of the Master Algorithm

A `Babai.SIInstance` carries a candidate **set**.  Every instance the paper's algorithm ever
looks at is with respect to a *group*, on a window invariant under it
(`Babai.IsGroupInstance`, `Workspace/Master/Defs.lean`).  This file proves that each of the
named reductions of Secs. 11–14 preserves that invariant, which is what lets Sec. 15 state
the properties of one round for group instances only.

Everything bottoms out in Luks's Chain Rule (`Babai.chainReduction`): its calls are with
respect to the successive groups `M ⊓ Aut^Δ(x)`, and their windows are the members of the
list it is given.  So, as soon as the list consists of `N`-invariant sets and the starting
group is inside `N`, every call is a group instance
(`Babai.calls_chainReduction_isGroupInstance`).  The lift to a window
(`Babai.windowInstance`) turns a group instance on `↥Δ` into one on `Ω`, the group being the
full preimage `Babai.windowPreimSubgroup`.
-/

universe u v

namespace Babai

open MulAction Equiv Equiv.Perm

/-! ### The preimage of a subgroup under a representation of `G` -/

section Preim

variable {α : Type u} {G : Subgroup (Equiv.Perm α)} {H : Type*} [Group H]

/-- `ψ⁻¹(N)`, the full preimage in `G` of a subgroup `N` of the image group, read as a
subgroup of `S(α)`.  For `N = 1` this is `Babai.kerSubgroup`. -/
def preimSubgroup (ψ : G →* H) (N : Subgroup H) : Subgroup (Equiv.Perm α) :=
  (N.comap ψ).map G.subtype

theorem mem_preimSubgroup {ψ : G →* H} {N : Subgroup H} {τ : Equiv.Perm α} :
    τ ∈ preimSubgroup ψ N ↔ ∃ h : τ ∈ G, ψ ⟨τ, h⟩ ∈ N := by
  constructor
  · rintro ⟨⟨g, hg⟩, hmem, rfl⟩
    exact ⟨hg, hmem⟩
  · rintro ⟨h, hmem⟩
    exact ⟨⟨τ, h⟩, hmem, rfl⟩

theorem preimSubgroup_le (ψ : G →* H) (N : Subgroup H) : preimSubgroup ψ N ≤ G :=
  Subgroup.map_subtype_le _

/-- The descent to `ψ⁻¹(N)` has the same multiplicative cost as the descent from the
image group `ψ(G)` to `N`: `|G : ψ⁻¹(N)| = |ψ(G) : N|`. -/
theorem relIndex_preimSubgroup (ψ : G →* H) (N : Subgroup H) :
    (preimSubgroup ψ N).relIndex G = N.relIndex ψ.range := by
  have hinj : Function.Injective G.subtype := Subgroup.subtype_injective G
  have htop : (⊤ : Subgroup G).map G.subtype = G := by
    rw [← MonoidHom.range_eq_map, Subgroup.subtype_range]
  calc (preimSubgroup ψ N).relIndex G
      = ((N.comap ψ).map G.subtype).relIndex ((⊤ : Subgroup G).map G.subtype) := by
        rw [preimSubgroup, htop]
    _ = (N.comap ψ).relIndex ⊤ := Subgroup.relIndex_map_map_of_injective _ _ hinj
    _ = (N.comap ψ).index := Subgroup.relIndex_top_right _
    _ = N.relIndex ψ.range := Subgroup.index_comap _ _

/-- `ψ⁻¹(1) = ker ψ`. -/
theorem preimSubgroup_bot (ψ : G →* H) : preimSubgroup ψ (⊥ : Subgroup H) = kerSubgroup ψ :=
  rfl

end Preim

/-! ### The subgroup of `K` above a subgroup of the window group

The Luks descent of step 6 happens inside the group `G = K^Δ` induced on the window, but
the instances it produces are instances on `Ω` with respect to a subgroup of `K`, namely the
full preimage of `G₁` under the restriction `K → K^Δ`.  This section says that the group
induced on the window by that preimage is `G₁` again, and that the two indices agree. -/

section WindowPreim

variable {Ω : Type u} {K : Subgroup (Equiv.Perm Ω)} {Δ : Set Ω}

/-- The full preimage in `K` of a subgroup `G₁` of the group `K^Δ` induced on the window,
as a subgroup of `S(Ω)`.  Its underlying set is `Babai.windowPreim`. -/
def windowPreimSubgroup (K : Subgroup (Equiv.Perm Ω)) (Δ : Set Ω) (h : IsInvariant K Δ)
    (G₁ : Subgroup (Equiv.Perm Δ)) : Subgroup (Equiv.Perm Ω) :=
  (G₁.comap (restrictHom K Δ h)).map K.subtype

theorem mem_windowPreimSubgroup {h : IsInvariant K Δ} {G₁ : Subgroup (Equiv.Perm Δ)}
    {τ : Equiv.Perm Ω} :
    τ ∈ windowPreimSubgroup K Δ h G₁ ↔ ∃ hτ : τ ∈ K, restrictHom K Δ h ⟨τ, hτ⟩ ∈ G₁ := by
  constructor
  · rintro ⟨⟨g, hg⟩, hmem, rfl⟩
    exact ⟨hg, hmem⟩
  · rintro ⟨hτ, hmem⟩
    exact ⟨⟨τ, hτ⟩, hmem, rfl⟩

theorem coe_windowPreimSubgroup (h : IsInvariant K Δ) (G₁ : Subgroup (Equiv.Perm Δ)) :
    ((windowPreimSubgroup K Δ h G₁ : Subgroup (Equiv.Perm Ω)) : Set (Equiv.Perm Ω)) =
      windowPreim K Δ h (G₁ : Set (Equiv.Perm Δ)) := by
  ext τ
  rw [SetLike.mem_coe, mem_windowPreimSubgroup, mem_windowPreim]
  rfl

theorem windowPreimSubgroup_le (h : IsInvariant K Δ) (G₁ : Subgroup (Equiv.Perm Δ)) :
    windowPreimSubgroup K Δ h G₁ ≤ K := Subgroup.map_subtype_le _

theorem isInvariant_windowPreimSubgroup (h : IsInvariant K Δ)
    (G₁ : Subgroup (Equiv.Perm Δ)) : IsInvariant (windowPreimSubgroup K Δ h G₁) Δ :=
  fun σ hσ => h σ (windowPreimSubgroup_le h G₁ hσ)

/-- The group induced on the window by the preimage of `G₁` is `G₁` itself. -/
theorem restrictTo_windowPreimSubgroup (h : IsInvariant K Δ)
    {G₁ : Subgroup (Equiv.Perm Δ)} (hle : G₁ ≤ restrictTo K Δ h) :
    restrictTo (windowPreimSubgroup K Δ h G₁) Δ
      (isInvariant_windowPreimSubgroup h G₁) = G₁ := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨⟨τ, hτ⟩, rfl⟩
    obtain ⟨hτK, hmem⟩ := mem_windowPreimSubgroup.1 hτ
    exact hmem
  · intro g hg
    obtain ⟨⟨τ, hτ⟩, hτg⟩ := MonoidHom.mem_range.1 (hle hg)
    have hτ₁ : τ ∈ windowPreimSubgroup K Δ h G₁ :=
      mem_windowPreimSubgroup.2 ⟨hτ, by rw [hτg]; exact hg⟩
    exact ⟨⟨τ, hτ₁⟩, hτg⟩

/-- The Luks descent has the same multiplicative cost upstairs and downstairs:
`|K : K₁| = |K^Δ : G₁|`. -/
theorem relIndex_windowPreimSubgroup (h : IsInvariant K Δ)
    (G₁ : Subgroup (Equiv.Perm Δ)) :
    (windowPreimSubgroup K Δ h G₁).relIndex K = G₁.relIndex (restrictTo K Δ h) :=
  relIndex_preimSubgroup (restrictHom K Δ h) G₁

end WindowPreim

/-! ### The lift of a group instance to a window -/

section Lift

variable {Ω : Type u} {A : Type v} {K : Subgroup (Equiv.Perm Ω)} {Δ : Set Ω}

/-- An instance on the window `Δ` with respect to a group, read on `Ω`
(`Babai.windowInstance`), is again an instance with respect to a group: the group is the
full preimage `Babai.windowPreimSubgroup`, and the lifted window `Subtype.val '' J.Δ` is
invariant under it because `J.Δ` is invariant under the group downstairs. -/
theorem isGroupInstance_windowInstance (h : IsInvariant K Δ) (x₀ : Ω → A)
    {J : SIInstance Δ A} (hJ : IsGroupInstance J) :
    IsGroupInstance (windowInstance K Δ h x₀ J) := by
  obtain ⟨M, hMK, hMinv⟩ := hJ
  refine ⟨windowPreimSubgroup K Δ h M, ?_, ?_⟩
  · show windowPreim K Δ h J.K = _
    rw [hMK, coe_windowPreimSubgroup]
  · intro σ hσ
    obtain ⟨hσK, hσM⟩ := mem_windowPreimSubgroup.1 hσ
    have hρ := hMinv _ hσM
    show (σ : Equiv.Perm Ω) '' (Subtype.val '' J.Δ) = Subtype.val '' J.Δ
    rw [← Set.image_comp]
    have hcomp : ((σ : Equiv.Perm Ω) : Ω → Ω) ∘ (Subtype.val : Δ → Ω) =
        (Subtype.val : Δ → Ω) ∘ (restrictHom K Δ h ⟨σ, hσK⟩ : Equiv.Perm Δ) := by
      funext w
      exact (coe_restrictHom_apply h ⟨σ, hσK⟩ w).symm
    rw [hcomp, Set.image_comp, hρ]

end Lift

/-! ### The Chain Rule produces group instances -/

section Chain

variable {Ω : Type u} {A : Type v} [Fintype Ω] [DecidableEq Ω]

/-- Every call of Luks's Chain Rule is with respect to a **group**, a subgroup of the group
the chain starts from, and its window is one of the sets of the list. -/
theorem calls_chainReduction_group (N : Subgroup (Equiv.Perm Ω)) (x y : Ω → A) :
    ∀ (Δs : List (Set Ω)) (σ : Equiv.Perm Ω) (M : Subgroup (Equiv.Perm Ω)),
      ∀ I ∈ (chainReduction N x y Δs σ M).calls,
        ∃ M' : Subgroup (Equiv.Perm Ω),
          I.K = (M' : Set (Equiv.Perm Ω)) ∧ M' ≤ M ∧ I.Δ ∈ Δs := by
  classical
  intro Δs
  induction Δs with
  | nil =>
    intro σ M I hI
    rw [chainReduction, SIReduction.calls_done] at hI
    exact absurd hI (List.not_mem_nil)
  | cons Δ rest ih =>
    intro σ M I hI
    rw [chainReduction, SIReduction.calls_call] at hI
    rcases List.mem_cons.1 hI with rfl | hI
    · exact ⟨M, rfl, le_rfl, List.mem_cons_self⟩
    · by_cases h : (SIInstance.answer
          (⟨(M : Set (Equiv.Perm Ω)), Δ, x, strAct y σ⁻¹⟩ : SIInstance Ω A)).Nonempty
      · rw [dif_pos h] at hI
        obtain ⟨M', hM'K, hM'le, hM'Δ⟩ := ih (σ * h.some) (M ⊓ autWindow N Δ x) I hI
        exact ⟨M', hM'K, le_trans hM'le inf_le_left, List.mem_cons_of_mem _ hM'Δ⟩
      · rw [dif_neg h, SIReduction.calls_done] at hI
        exact absurd hI (List.not_mem_nil)

/-- Every call of the Chain Rule is a **group instance**, provided the sets of the list are
invariant under `N` and the chain starts inside `N`. -/
theorem calls_chainReduction_isGroupInstance {N : Subgroup (Equiv.Perm Ω)} (x y : Ω → A)
    {Δs : List (Set Ω)} (hinv : ∀ Δ ∈ Δs, IsInvariant N Δ) (σ : Equiv.Perm Ω)
    {M : Subgroup (Equiv.Perm Ω)} (hMN : M ≤ N) :
    ∀ I ∈ (chainReduction N x y Δs σ M).calls, IsGroupInstance I := by
  intro I hI
  obtain ⟨M', hM'K, hM'le, hM'Δ⟩ := calls_chainReduction_group N x y Δs σ M I hI
  exact ⟨M', hM'K, fun τ hτ => hinv I.Δ hM'Δ τ (hMN (hM'le hτ))⟩

/-- Every call of the Chain Rule over the orbits of `N` is a group instance: the orbits are
`N`-invariant. -/
theorem calls_chainOverOrbits_isGroupInstance (N : Subgroup (Equiv.Perm Ω))
    (I : SIInstance Ω A) :
    ∀ J ∈ (chainOverOrbits N I).calls, IsGroupInstance J :=
  calls_chainReduction_isGroupInstance I.x I.y
    (fun _ hΔ => isInvariant_of_mem_orbitList hΔ) 1 le_rfl

end Chain

/-! ### Line 2: the imprimitive Luks reduction -/

section Line2

variable {Ω : Type u} {A : Type v} [Fintype Ω] [DecidableEq Ω]
  {G : Subgroup (Equiv.Perm Ω)} {H : Type*} [Group H]

/-- §15, line 2: every call of the imprimitive Luks reduction is a group instance.  Its
calls are those of the Chain Rule over the orbits of `N = ker ϕ`. -/
theorem calls_line2Reduction_isGroupInstance [Fintype H] (ϕ : G →* H) (x y : Ω → A) :
    ∀ J ∈ (line2Reduction ϕ x y).calls, IsGroupInstance J := by
  rw [line2Reduction]
  exact SIReduction.mem_calls_expand_of_calls
    (P := fun I => I.K = ((kerSubgroup ϕ : Subgroup (Equiv.Perm Ω)) : Set (Equiv.Perm Ω))
      ∧ I.Δ = Set.univ)
    (fun I hI => run_chainOverOrbits hI.1 hI.2)
    (fun I _ => calls_chainOverOrbits_isGroupInstance _ I)
    (luksBruteForceReduction ϕ x y) (calls_luksBruteForceReduction_wrt ϕ x y)

end Line2

/-! ### Line 4b: Corollary 12.0.10 -/

section Line4b

variable {Ω : Type u} {A : Type v} [Fintype Ω] [DecidableEq Ω] {m : ℕ}

/-- Every call of the case `G^ϕ = A(Γ)` of Cor. 12.0.6 is a group instance. -/
theorem calls_giantAReduction_isGroupInstance {G' : Subgroup (Equiv.Perm Ω)}
    (ψ : G' →* alternatingGroup (Fin m)) (x y : Ω → A) :
    ∀ J ∈ (giantAReduction ψ x y).calls, IsGroupInstance J := by
  rw [giantAReduction]
  exact SIReduction.mem_calls_expand_of_calls
    (P := fun I => I.K = ((kerSubgroup ψ : Subgroup (Equiv.Perm Ω)) : Set (Equiv.Perm Ω))
      ∧ I.Δ = Set.univ)
    (fun I hI => run_chainOverOrbits hI.1 hI.2)
    (fun I _ => calls_chainOverOrbits_isGroupInstance _ I)
    (TopAction1Reduction ψ x y (altGens m)) (calls_wrt_TopAction1 ψ x y)

/-- Every call of the single `N`-instance expanded by the Chain Rule is a group
instance. -/
theorem calls_nOrbitReduction_isGroupInstance (N : Subgroup (Equiv.Perm Ω)) (x y : Ω → A) :
    ∀ J ∈ (nOrbitReduction N x y).calls, IsGroupInstance J :=
  calls_chainOverOrbits_isGroupInstance N _

open Classical in
/-- §12, Cor. 12.0.8: every call of `Babai.topAction3Reduction` is a group instance. -/
theorem calls_topAction3Reduction_isGroupInstance {G : Subgroup (Equiv.Perm Ω)}
    (ϕ : G →* Equiv.Perm (Fin m)) (x y : Ω → A) :
    ∀ I ∈ (topAction3Reduction ϕ x y).calls, IsGroupInstance I := by
  classical
  have h0 := calls_giantAReduction_isGroupInstance (altHom ϕ) x x
  have h1 := calls_nOrbitReduction_isGroupInstance (kerSubgroup ϕ) x y
  have h2 := calls_nOrbitReduction_isGroupInstance (kerSubgroup ϕ) x
    (strAct y (oddRep ϕ)⁻¹)
  rw [topAction3Reduction, SIReduction.calls_bind]
  intro I hI
  rcases List.mem_append.1 hI with hI | hI
  · exact h0 I hI
  · by_cases hz : (giantAReduction (altHom ϕ) x x).run = none
    · rw [if_pos hz, SIReduction.calls_done] at hI; exact absurd hI (by simp)
    · rw [if_neg hz, SIReduction.calls_bind, run_nOrbitReduction] at hI
      rcases List.mem_append.1 hI with hI | hI
      · exact h1 I hI
      · by_cases hr : ϕ.range ≤ alternatingGroup (Fin m)
        · rw [if_pos hr, SIReduction.calls_done] at hI; exact absurd hI (by simp)
        · rw [if_neg hr, SIReduction.calls_bind, SIReduction.calls_done] at hI
          simp only [List.append_nil] at hI
          exact h2 I hI

/-- §12, Cor. 12.0.8 on a window: every call is a group instance.  The calls are the lifts
(`Babai.windowInstance`) of the calls of `Babai.topAction3Reduction` on the window. -/
theorem calls_windowTopAction3Reduction_isGroupInstance (K : Subgroup (Equiv.Perm Ω))
    (Δ : Set Ω) (hinv : IsInvariant K Δ)
    (ϕ : restrictTo K Δ hinv →* Equiv.Perm (Fin m)) (x y : Ω → A) :
    ∀ I ∈ (windowTopAction3Reduction K Δ hinv ϕ x y).calls, IsGroupInstance I := by
  classical
  rw [windowTopAction3Reduction, SIReduction.calls_bind, SIReduction.calls_done,
    List.append_nil,
    SIReduction.calls_window hinv x _ (calls_topAction3Reduction_K ϕ _ _)]
  intro J hJ
  rw [List.mem_map] at hJ
  obtain ⟨J', hJ', rfl⟩ := hJ
  exact isGroupInstance_windowInstance hinv x
    (calls_topAction3Reduction_isGroupInstance ϕ _ _ J' hJ')

variable {G : Subgroup (Equiv.Perm Ω)}

/-- §12, the body of Procedure TopAction4: every call is a group instance.  The first
family is Cor. 12.0.8 on the window `Ω(C)`, the second the Chain Rule over the remaining
color classes `Ω_j`, which are `G_C`-invariant (`Babai.isInvariant_omegaCut`). -/
theorem calls_topAction4Body_isGroupInstance (hG : IsTransitive G)
    (ϕ : G →* Equiv.Perm (Fin m)) (hϕ : IsGiantRep ϕ)
    (hk : VeryLargeK m (maxOrbitLength G)) (C : Set (Fin m)) (hC : m < 2 * C.ncard)
    (x y' : Ω → A) (t : ℕ) :
    ∀ J ∈ (topAction4Body hG ϕ hϕ hk C hC x y' t).calls, IsGroupInstance J := by
  classical
  have hinvΔ : ∀ Δ ∈ (List.range t).map (omegaCut (Ω := Ω) ϕ C),
      IsInvariant (stabOn ϕ C) Δ := by
    intro Δ hΔ
    rw [List.mem_map] at hΔ
    obtain ⟨j, -, rfl⟩ := hΔ
    refine isInvariant_omegaCut ϕ hϕ hk C j (stabOn ϕ C) (stabOn_le ϕ C) ?_
    intro τ hτ
    exact (mem_stabOn.1 hτ).choose_spec
  rw [topAction4Body, SIReduction.calls_bind]
  intro J hJ
  rcases List.mem_append.1 hJ with h | h
  · exact calls_windowTopAction3Reduction_isGroupInstance _ _ _ _ x y' J h
  · revert h
    generalize (windowTopAction3Reduction (stabOn ϕ C) (omegaOf ϕ C)
      (isInvariant_omegaOf_stabOn ϕ hϕ hk C) (phiCFin hG ϕ hϕ hk C hC) x y').run = r
    cases r with
    | none => intro h; simp [SIReduction.calls_done] at h
    | some S =>
      by_cases hS : S.Nonempty
      · simp only [dif_pos hS]
        intro h
        exact calls_chainReduction_isGroupInstance (N := stabOn ϕ C) x y' hinvΔ _
          inf_le_left J h
      · intro h; simp [dif_neg hS, SIReduction.calls_done] at h

variable {κ : Type*}

/-- §12, **Procedure TopAction4**: every call is a group instance. -/
theorem calls_topAction4Reduction_isGroupInstance (hG : IsTransitive G)
    (ϕ : G →* Equiv.Perm (Fin m)) (hϕ : IsGiantRep ϕ)
    (hk : VeryLargeK m (maxOrbitLength G)) (col : (Ω → A) → Fin m → κ) (c : κ)
    (x y : Ω → A) (hC : m < 2 * (colorClass col x c).ncard) :
    ∀ J ∈ (topAction4Reduction hG ϕ hϕ hk col c x y hC).calls, IsGroupInstance J := by
  classical
  rw [topAction4Reduction]
  by_cases hsize : (colorClass col x c).ncard = (colorClass col y c).ncard
  · rw [if_pos hsize, SIReduction.calls_bind, SIReduction.calls_done, List.append_nil]
    exact calls_topAction4Body_isGroupInstance hG ϕ hϕ hk _ hC x _ (tOf hG ϕ)
  · rw [if_neg hsize, SIReduction.calls_done]
    intro J hJ
    exact absurd hJ (by simp)

end Line4b

end Babai
