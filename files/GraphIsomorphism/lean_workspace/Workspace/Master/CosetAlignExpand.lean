import Workspace.Master.CosetAlign
import Workspace.Master.CosetDominant

/-! # Expanding the first color window in coset form

Line 6 puts the dominant window first. It therefore receives the structure
transporter itself. The remaining windows receive the preceding answers.
-/

universe u v

namespace Babai

open Equiv MulAction
open scoped Pointwise Classical

variable {Ω : Type u} {A : Type v} [Fintype Ω] [DecidableEq Ω]
  {Γ 𝒳 : Type*} [MulAction (Perm Γ) 𝒳] {G : Subgroup (Perm Ω)}

/-- Replacing a call by a correct round that makes a call cannot remove all calls. -/
theorem SIReduction.calls_expand_ne_nil_of_mem
    {f : SIInstance Ω A → SIReduction Ω A (Set (Perm Ω))}
    {P : SIInstance Ω A → Prop} (hf : ∀ I, P I → (f I).run = I.answer)
    (R : SIReduction Ω A (Set (Perm Ω))) (hR : ∀ I ∈ R.calls, P I)
    {I : SIInstance Ω A} (hI : I ∈ R.calls) (hi : (f I).calls ≠ []) :
    (R.expand f).calls ≠ [] := by
  induction R with
  | done a => simp at hI
  | call J k ih =>
    rw [SIReduction.expand, SIReduction.calls_bind, hf J (hR J (by simp))]
    rcases List.mem_cons.1 hI with he | ht
    · subst I
      exact fun h => hi (List.append_eq_nil_iff.1 h).1
    · have hk := ih J.answer (fun K hK => hR K (List.mem_cons_of_mem _ hK)) ht
      exact fun h => hk (List.append_eq_nil_iff.1 h).2

/-- The first color window uses a coset of the whole source stabilizer. -/
def CosetAlignCall (G N : Subgroup (Perm Ω)) (head : Set Ω) (tail : List (Set Ω))
    (J : SIInstance Ω A) : Prop :=
  J.Δ ∈ head :: tail ∧ IsCosetInstance G J ∧
    (J.Δ = head → ∃ σ : Perm Ω, σ ∈ G ∧ J.K = σ • (N : Set (Perm Ω)))

theorem calls_cosetDesignAlign_spec (ϕ : G →* Perm Γ) (x y : Ω → A)
    (X : 𝒳) (versions : List 𝒳) (head : Set Ω) (tail : List (Set Ω))
    (hne : head ∉ tail)
    (hinv : ∀ Δ ∈ head :: tail, IsInvariant (preimageSubgroup ϕ (structAut X)) Δ) :
    ∀ J ∈ (cosetDesignAlign ϕ x y X versions (head :: tail)).calls,
      CosetAlignCall G (preimageSubgroup ϕ (structAut X)) head tail J := by
  apply SIReduction.mem_calls_unionOver
  intro Y J hJ
  refine ⟨(calls_cosetChain x y (head :: tail) _).2 J hJ,
    isCosetInstance_calls_cosetAlignChain ϕ x y X Y _ hinv J hJ, ?_⟩
  intro hhead
  by_cases hc : (alignTransporter ϕ X Y).Nonempty
  · obtain ⟨σ, hσ, hXY⟩ := hc
    rcases calls_cosetChain_cons x y head tail (alignTransporter ϕ X Y) J hJ with he | ht
    · exact ⟨σ, hσ, by rw [he]; exact alignTransporter_eq_smul ϕ X Y ⟨σ, hσ⟩ hXY⟩
    · exact False.elim (hne (hhead ▸ ht))
  · have he := Set.not_nonempty_iff_eq_empty.1 hc
    simp [cosetAlignChain, he] at hJ

/-- Sec. 14.1, lines 1–11: expand the first color window by its dominant round. -/
noncomputable def cosetAlignExpand (ϕ : G →* Perm Γ) (x y : Ω → A)
    (X : 𝒳) (versions : List 𝒳) (head : Set Ω) (tail : List (Set Ω))
    (g : SIInstance Ω A → SIReduction Ω A (Set (Perm Ω))) :
    SIReduction Ω A (Set (Perm Ω)) :=
  (cosetDesignAlign ϕ x y X versions (head :: tail)).expand
    (fun J => if J.Δ = head then g J else .call J .done)

variable {ϕ : G →* Perm Γ} {x y : Ω → A} {X : 𝒳} {versions : List 𝒳}
  {head : Set Ω} {tail : List (Set Ω)}
  {g : SIInstance Ω A → SIReduction Ω A (Set (Perm Ω))}

theorem run_cosetAlignExpand {Vers : (Ω → A) → Set 𝒳}
    (hcan : IsCanonicalVersions ϕ Vers) (hX : X ∈ Vers x)
    (hv : ∀ Y, Y ∈ versions ↔ Y ∈ Vers y) (hne : head ∉ tail)
    (hinv : ∀ Δ ∈ head :: tail, IsInvariant (preimageSubgroup ϕ (structAut X)) Δ)
    (hcover : (⋃ Δ ∈ head :: tail, Δ) = Set.univ)
    (hg : ∀ J, CosetAlignCall G (preimageSubgroup ϕ (structAut X)) head tail J →
      J.Δ = head → (g J).run = J.answer) :
    (cosetAlignExpand ϕ x y X versions head tail g).run = strIso (G : Set (Perm Ω)) x y := by
  rw [cosetAlignExpand]
  rw [SIReduction.run_expand_of_calls (P := CosetAlignCall G
    (preimageSubgroup ϕ (structAut X)) head tail)
    (fun J hJ => by
      try dsimp only
      split
      · next h => exact hg J hJ h
      · rfl)
    _ (calls_cosetDesignAlign_spec ϕ x y X versions head tail hne hinv)]
  exact run_cosetDesignAlign ϕ x y hcan X hX versions hv _ hcover

theorem calls_cosetAlignExpand {Q : SIInstance Ω A → Prop} (hne : head ∉ tail)
    (hinv : ∀ Δ ∈ head :: tail, IsInvariant (preimageSubgroup ϕ (structAut X)) Δ)
    (hg : ∀ J, CosetAlignCall G (preimageSubgroup ϕ (structAut X)) head tail J →
      J.Δ = head → (g J).run = J.answer)
    (hqg : ∀ J, CosetAlignCall G (preimageSubgroup ϕ (structAut X)) head tail J →
      J.Δ = head → ∀ K ∈ (g J).calls, Q K)
    (hqt : ∀ J, CosetAlignCall G (preimageSubgroup ϕ (structAut X)) head tail J →
      J.Δ ≠ head → Q J) :
    ∀ J ∈ (cosetAlignExpand ϕ x y X versions head tail g).calls, Q J := by
  unfold cosetAlignExpand
  refine SIReduction.mem_calls_expand_of_calls
    (f := fun J => if J.Δ = head then g J else .call J .done)
    (P := CosetAlignCall G (preimageSubgroup ϕ (structAut X)) head tail)
    (fun J hJ => by
      try dsimp only
      split
      · next h => exact hg J hJ h
      · rfl) ?_ _ (calls_cosetDesignAlign_spec ϕ x y X versions head tail hne hinv)
  intro J hJ K hK
  dsimp only at hK
  split at hK
  · next h => exact hqg J hJ h K hK
  · next h =>
      simp only [SIReduction.calls_call, SIReduction.calls_done, List.mem_singleton] at hK
      subst K
      exact hqt J hJ h

theorem calls_length_cosetAlignExpand {c : ℕ} (hne : head ∉ tail)
    (hinv : ∀ Δ ∈ head :: tail, IsInvariant (preimageSubgroup ϕ (structAut X)) Δ)
    (hg : ∀ J, CosetAlignCall G (preimageSubgroup ϕ (structAut X)) head tail J →
      J.Δ = head → (g J).run = J.answer) (hc : 1 ≤ c)
    (hlen : ∀ J, CosetAlignCall G (preimageSubgroup ϕ (structAut X)) head tail J →
      J.Δ = head → (g J).calls.length ≤ c) :
    (cosetAlignExpand ϕ x y X versions head tail g).calls.length ≤
      versions.length * (head :: tail).length * c := by
  refine (SIReduction.calls_expand_length_le_of_calls
    (P := CosetAlignCall G (preimageSubgroup ϕ (structAut X)) head tail)
    (fun J hJ => by
      try dsimp only
      split
      · next h => exact hg J hJ h
      · rfl)
    (c := c) (fun J hJ => ?_) _
    (calls_cosetDesignAlign_spec ϕ x y X versions head tail hne hinv)).trans ?_
  · split
    · next h => exact hlen J hJ h
    · simpa only [SIReduction.calls_call, SIReduction.calls_done, List.length_singleton]
        using hc
  · exact Nat.mul_le_mul_right c (calls_length_cosetDesignAlign _ _ _ _ _ _)

/-- A comparable version forces a call, provided the replacement of its first
window makes a call. Later empty answers do not affect this first call. -/
theorem calls_cosetAlignExpand_ne_nil (hne : head ∉ tail)
    (hinv : ∀ Δ ∈ head :: tail, IsInvariant (preimageSubgroup ϕ (structAut X)) Δ)
    (hg : ∀ J, CosetAlignCall G (preimageSubgroup ϕ (structAut X)) head tail J →
      J.Δ = head → (g J).run = J.answer)
    (hn : ∀ J, CosetAlignCall G (preimageSubgroup ϕ (structAut X)) head tail J →
      J.Δ = head → (g J).calls ≠ [])
    {Y : 𝒳} (hY : Y ∈ versions) (hσ : ∃ σ : G, (ϕ σ) • X = Y) :
    (cosetAlignExpand ϕ x y X versions head tail g).calls ≠ [] := by
  obtain ⟨σ, hσ⟩ := hσ
  have hc : (alignTransporter ϕ X Y).Nonempty := ⟨σ, σ.2, hσ⟩
  let I : SIInstance Ω A := ⟨alignTransporter ϕ X Y, head, x, y⟩
  have hi : I ∈ (cosetDesignAlign ϕ x y X versions (head :: tail)).calls := by
    rw [cosetDesignAlign, SIReduction.calls_unionOver, List.mem_flatten]
    refine ⟨_, List.mem_map.2 ⟨Y, hY, rfl⟩, ?_⟩
    rw [cosetAlignChain, cosetChain, if_neg hc.ne_empty, SIReduction.calls_call]
    exact List.mem_cons_self
  have hspec := calls_cosetDesignAlign_spec ϕ x y X versions head tail hne hinv
  refine SIReduction.calls_expand_ne_nil_of_mem
    (f := fun J => if J.Δ = head then g J else .call J .done)
    (P := CosetAlignCall G (preimageSubgroup ϕ (structAut X)) head tail)
    (fun J hJ => by
      try dsimp only
      split
      · next h => exact hg J hJ h
      · rfl) _ hspec hi ?_
  change (if I.Δ = head then g I else SIReduction.call I SIReduction.done).calls ≠ []
  rw [if_pos rfl]
  exact hn I (hspec I hi) rfl

end Babai
