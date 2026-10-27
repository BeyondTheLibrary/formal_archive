import Workspace.Algo.TopWindowThree

/-!
# Choices that remain fixed in the top-four coset tree

`Babai.TopAction4Enum` supplies kernel orbits and color windows. The tree
also reads `Babai.altGens`, `Babai.colorEquivFin`, and `Babai.alignColorElt`.
Their specifications do not determine the individual calls.

The examples here concern the exact tree interface, not Corollary 12.0.10.
Two valid generating pairs can give different call lists. Two valid
aligning elements can give different target strings.
-/

namespace Algo

open Equiv (Perm)

section Generators

variable {Ω A H : Type*} [Fintype Ω] [DecidableEq Ω] [Group H]
  {G : Subgroup (Perm Ω)}

omit [Fintype Ω] [DecidableEq Ω] in
/-- A surjective representation has different preimage sets for different
top permutations. -/
theorem top4_preimage_injective (ϕ : G →* H) (hϕ : Function.Surjective ϕ) :
    Function.Injective (Babai.preimageSet ϕ) := by
  intro σ τ he
  obtain ⟨g, hg⟩ := hϕ σ
  have hm : (g : Perm Ω) ∈ Babai.preimageSet ϕ σ := ⟨g.2, hg⟩
  rw [he] at hm
  exact hg.symm.trans hm.2

/-- The lifting call list determines the ordered list of top generators.
Equality of generated groups is not enough to identify these calls. -/
theorem top4_calls_determine_generators (ϕ : G →* H) (hϕ : Function.Surjective ϕ)
    (x y : Ω → A) {S T : List H}
    (he : (Babai.cosetTopAction1 ϕ x y S).calls =
      (Babai.cosetTopAction1 ϕ x y T).calls) : S = T := by
  rw [Babai.calls_cosetTopAction1, Babai.calls_cosetTopAction1] at he
  have hinj : Function.Injective (fun σ : H =>
      (⟨Babai.preimageSet ϕ σ, Set.univ, x, y⟩ : Babai.SIInstance Ω A)) := by
    intro σ τ h
    exact top4_preimage_injective ϕ hϕ (congrArg Babai.SIInstance.K h)
  exact List.cons.inj ((List.map_injective_iff.2 hinj) he) |>.2

omit [Fintype Ω] [DecidableEq Ω] in
/-- Reordering the orbit windows cannot identify distinct lifting
requests: already the first calls have different candidate sets. -/
theorem top4_lifting_chains_differ (ϕ : G →* H) (hϕ : Function.Surjective ϕ)
    (x y : Ω → A) {σ τ : H} (hne : σ ≠ τ)
    (U V : Set Ω) (us vs : List (Set Ω)) :
    (Babai.cosetChain x y (U :: us) (Babai.preimageSet ϕ σ)).calls ≠
      (Babai.cosetChain x y (V :: vs) (Babai.preimageSet ϕ τ)).calls := by
  classical
  have hn : ∀ s : H, Babai.preimageSet ϕ s ≠ ∅ := by
    intro s
    obtain ⟨g, hg⟩ := hϕ s
    exact Set.nonempty_iff_ne_empty.1 ⟨(g : Perm Ω), g.2, hg⟩
  intro he
  rw [Babai.cosetChain, if_neg (hn σ), Babai.cosetChain, if_neg (hn τ),
    Babai.SIReduction.calls_call, Babai.SIReduction.calls_call] at he
  exact hne (top4_preimage_injective ϕ hϕ
    (congrArg Babai.SIInstance.K (List.cons.inj he).1))

end Generators

/-- Two valid witnesses for the specification of `Babai.altGens 20` have
different lifting call lists. Reversing the pair preserves its length and
generated group, but changes the first nonidentity lifting request. -/
theorem top4_generator_choice_changes_calls :
    ∃ S T : List (alternatingGroup (Fin 20)),
      S.length = 2 ∧ T.length = 2 ∧
      Subgroup.closure {σ : alternatingGroup (Fin 20) | σ ∈ S} = ⊤ ∧
      Subgroup.closure {σ : alternatingGroup (Fin 20) | σ ∈ T} = ⊤ ∧
      (Babai.cosetTopAction1 (MonoidHom.id (alternatingGroup (Fin 20)))
        (fun _ => (0 : ℕ)) (fun _ => 0) S).calls ≠
      (Babai.cosetTopAction1 (MonoidHom.id (alternatingGroup (Fin 20)))
        (fun _ => (0 : ℕ)) (fun _ => 0) T).calls := by
  classical
  let a : Perm (Fin 20) := Babai.thr 19 0 1
  let b : Perm (Fin 20) := Fin.cycleRange 18
  have hab : Subgroup.closure ({a, b} : Set (Perm (Fin 20))) =
      alternatingGroup (Fin 20) :=
    Babai.TwoGen.two_generated_even (d := 18) (by omega) (by decide)
  have ha : a ∈ alternatingGroup (Fin 20) := by
    rw [← hab]
    exact Subgroup.subset_closure (by simp)
  have hb : b ∈ alternatingGroup (Fin 20) := by
    rw [← hab]
    exact Subgroup.subset_closure (by simp)
  let a' : alternatingGroup (Fin 20) := ⟨a, ha⟩
  let b' : alternatingGroup (Fin 20) := ⟨b, hb⟩
  have hgen : Subgroup.closure ({a', b'} : Set (alternatingGroup (Fin 20))) = ⊤ := by
    apply Subgroup.map_injective (alternatingGroup (Fin 20)).subtype_injective
    rw [MonoidHom.map_closure]
    have hi : (alternatingGroup (Fin 20)).subtype ''
        ({a', b'} : Set (alternatingGroup (Fin 20))) = {a, b} := by
      ext z
      simp [a', b', eq_comm]
    rw [hi, hab, ← MonoidHom.range_eq_map, Subgroup.subtype_range]
  have hne : a ≠ b := by decide
  refine ⟨[a', b'], [b', a'], rfl, rfl, ?_, ?_, ?_⟩
  · have he : {σ : alternatingGroup (Fin 20) | σ ∈ [a', b']} = {a', b'} := by
      ext σ
      simp
    rw [he]
    exact hgen
  · have he : {σ : alternatingGroup (Fin 20) | σ ∈ [b', a']} = {a', b'} := by
      ext σ
      simp [or_comm]
    rw [he]
    exact hgen
  · intro hc
    have hst := top4_calls_determine_generators (MonoidHom.id (alternatingGroup (Fin 20)))
      (fun σ => ⟨σ, rfl⟩) (fun _ => (0 : ℕ)) (fun _ => 0) hc
    exact hne (congrArg Subtype.val (List.cons.inj hst).1)

/-- Even for a canonical coloring, the specification of an aligning
element does not determine the updated target string. -/
theorem top4_alignment_choice_changes_target :
    ∃ (ϕ : (⊤ : Subgroup (Perm (Fin 20))) →* Perm (Fin 20))
      (col : (Fin 20 → ℕ) → Fin 20 → ℕ) (x y : Fin 20 → ℕ)
      (σ τ : (⊤ : Subgroup (Perm (Fin 20)))),
      Babai.IsTransitive (⊤ : Subgroup (Perm (Fin 20))) ∧
      Babai.HugeM 20 (Nat.card (Fin 20)) ∧
      Babai.IsGiantRep ϕ ∧ Babai.IsCanonicalColoring ϕ col ∧
      20 < 2 * (Babai.colorClass col x 0).ncard ∧
      (∀ α : Perm (Fin 20), α ∈ alternatingGroup (Fin 20) →
        (∀ γ, γ ∉ Babai.colorClass col x 0 → α γ = γ) →
        ∃ β ∈ Babai.homImage ϕ (Babai.strAut (⊤ : Set (Perm (Fin 20))) x),
          ∀ γ ∈ Babai.colorClass col x 0, β γ = α γ) ∧
      (ϕ σ) '' Babai.colorClass col x 0 = Babai.colorClass col y 0 ∧
      (ϕ τ) '' Babai.colorClass col x 0 = Babai.colorClass col y 0 ∧
      Babai.strAct y (σ : Perm (Fin 20))⁻¹ ≠
        Babai.strAct y (τ : Perm (Fin 20))⁻¹ := by
  classical
  let ϕ := (⊤ : Subgroup (Perm (Fin 20))).subtype
  let col : (Fin 20 → ℕ) → Fin 20 → ℕ := fun _ _ => 0
  let x : Fin 20 → ℕ := fun _ => 0
  let y : Fin 20 → ℕ := Fin.val
  let σ : (⊤ : Subgroup (Perm (Fin 20))) := 1
  let τ : (⊤ : Subgroup (Perm (Fin 20))) := ⟨Equiv.swap 0 1, trivial⟩
  have hC : ∀ z, Babai.colorClass col z 0 = Set.univ := fun _ => by
    ext u
    simp [Babai.colorClass, col]
  refine ⟨ϕ, col, x, y, σ, τ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨0, ?_⟩
    ext z
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    exact ⟨⟨Equiv.swap 0 z, trivial⟩, by simp [Subgroup.smul_def]⟩
  · have hlog : Real.logb 2 (20 : ℝ) < 8 := by
      rw [Real.logb_lt_iff_lt_rpow (by norm_num) (by norm_num)]
      norm_num
    rw [Babai.HugeM, Nat.card_eq_fintype_card, Fintype.card_fin]
    change max (16 : ℝ) (4 + 2 * Real.logb 2 (20 : ℝ)) ≤ 20
    exact max_le (by norm_num) (by linarith)
  · show alternatingGroup (Fin 20) ≤ ϕ.range
    rw [Subgroup.subtype_range]
    exact le_top
  · intro z g u
    rfl
  · rw [hC, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
    omega
  · intro α _ _
    refine ⟨α, ?_, fun _ _ => rfl⟩
    exact ⟨α, ⟨trivial, rfl⟩, trivial, rfl⟩
  · rw [hC, hC]
    exact Set.image_univ_of_surjective (ϕ σ).surjective
  · rw [hC, hC]
    exact Set.image_univ_of_surjective (ϕ τ).surjective
  · intro he
    have h0 := congrFun he (0 : Fin 20)
    norm_num [Babai.strAct, σ, τ, y] at h0

end Algo

#print axioms Algo.polyFun_topw3LiftWindow
#print axioms Algo.topw3LiftWindow_spec
#print axioms Algo.topw3LiftWindow_size
#print axioms Algo.topw3_start_ne_preimage
#print axioms Algo.topw3_windowPreim_ne_preimage
#print axioms Algo.top4_calls_determine_generators
#print axioms Algo.top4_lifting_chains_differ
#print axioms Algo.top4_generator_choice_changes_calls
#print axioms Algo.top4_alignment_choice_changes_target
