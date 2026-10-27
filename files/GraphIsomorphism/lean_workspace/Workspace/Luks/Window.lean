/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 11.1: transport of String Isomorphism instances and reductions along a window.
-/
import Workspace.Luks.Instances

/-!
# Instances and reductions on a window

Several statements of Sections 12–14 are proved for a group acting on **all** of `Ω` and
are then applied to a group acting on a proper invariant subset `Δ ⊆ Ω` (Cor. 12.0.10
applies Cor. 12.0.8 to the window `Ω(C)`; see the corrected paper).  This file provides the
translation, once.

Fix a `K`-invariant window `Δ ⊆ Ω`.  Notation 2.2.1 gives the restriction homomorphism
`res : K → S(Δ)` (`Babai.restrictHom`) with image `K̄ = K^Δ` (`Babai.restrictTo`).

* `Babai.restrictStr`, `Babai.extendStr`: the restriction `x|_Δ : Δ → Σ` of a string and
  the extension of a string on `Δ` to `Ω` (the values outside `Δ` are irrelevant to every
  statement below, and are taken from a reference string).
* `Babai.windowPreim`, `Babai.windowImage`: the full preimage in `K` of a set of
  permutations of `Δ`, and the image in `S(Δ)` of a set of permutations of `Ω`.
* `Babai.wIso_eq_windowPreim`: **`Iso^Δ_K(x,y)` is the full preimage of
  `Iso_{K̄}(x|_Δ, y|_Δ)`**.  This is what makes a statement about `K̄` acting on `Δ` a
  statement about `K` and the window `Δ`.
* `Babai.windowInstance`: an instance on `Δ` becomes an instance on `Ω` with a window of the
  same size; `Babai.answer_windowInstance` says the answers correspond.
* `Babai.SIReduction.window`: a reduction on `Δ` becomes a reduction on `Ω` with the
  *same* number of calls and windows of the *same* sizes
  (`Babai.SIReduction.calls_window`, `Babai.SIReduction.run_window`).
-/

universe u v w

namespace Babai

open MulAction Equiv Equiv.Perm
open scoped Pointwise Classical

variable {Ω : Type u} {A : Type v} {α : Type w}

/-! ### Strings on a window -/

/-- The restriction `x|_Δ : Δ → Σ` of a string to the window. -/
def restrictStr (Δ : Set Ω) (x : Ω → A) : Δ → A := fun w => x (w : Ω)

/-- An extension of a string on the window to all of `Ω`, agreeing with the reference
string `x₀` outside `Δ`.  Only the values on `Δ` ever matter. -/
noncomputable def extendStr (Δ : Set Ω) (x₀ : Ω → A) (z : Δ → A) : Ω → A :=
  fun u => if h : u ∈ Δ then z ⟨u, h⟩ else x₀ u

@[simp] theorem extendStr_coe (Δ : Set Ω) (x₀ : Ω → A) (z : Δ → A) (w : Δ) :
    extendStr Δ x₀ z (w : Ω) = z w := dif_pos w.2

@[simp] theorem extendStr_restrictStr (Δ : Set Ω) (x : Ω → A) :
    extendStr Δ x (restrictStr Δ x) = x := by
  funext u
  by_cases hu : u ∈ Δ
  · exact extendStr_coe Δ x (restrictStr Δ x) ⟨u, hu⟩
  · exact dif_neg hu

/-! ### The restriction homomorphism and its preimages -/

variable {K : Subgroup (Equiv.Perm Ω)} {Δ : Set Ω}

@[simp] theorem coe_restrictHom_apply (h : IsInvariant K Δ) (σ : K) (w : Δ) :
    ((restrictHom K Δ h σ w : Δ) : Ω) = (σ : Equiv.Perm Ω) (w : Ω) := rfl

/-- The full preimage in `K` of a set `L ⊆ S(Δ)` of permutations of the window. -/
def windowPreim (K : Subgroup (Equiv.Perm Ω)) (Δ : Set Ω) (h : IsInvariant K Δ)
    (L : Set (Equiv.Perm Δ)) : Set (Equiv.Perm Ω) :=
  {τ | ∃ hτ : τ ∈ K, restrictHom K Δ h ⟨τ, hτ⟩ ∈ L}

theorem mem_windowPreim {h : IsInvariant K Δ} {L : Set (Equiv.Perm Δ)}
    {τ : Equiv.Perm Ω} :
    τ ∈ windowPreim K Δ h L ↔ ∃ hτ : τ ∈ K, restrictHom K Δ h ⟨τ, hτ⟩ ∈ L := Iff.rfl

/-- The image in `S(Δ)` of a set `S ⊆ S(Ω)` of permutations, through `res : K → S(Δ)`.
(Elements of `S` outside `K` are discarded.) -/
def windowImage (K : Subgroup (Equiv.Perm Ω)) (Δ : Set Ω) (h : IsInvariant K Δ)
    (S : Set (Equiv.Perm Ω)) : Set (Equiv.Perm Δ) :=
  {ρ | ∃ τ ∈ S, ∃ hτ : τ ∈ K, restrictHom K Δ h ⟨τ, hτ⟩ = ρ}

/-- `windowImage` undoes `windowPreim` on sets contained in the image `K̄ = K^Δ`. -/
theorem windowImage_windowPreim (h : IsInvariant K Δ) {L : Set (Equiv.Perm Δ)}
    (hL : L ⊆ (restrictTo K Δ h : Set (Equiv.Perm Δ))) :
    windowImage K Δ h (windowPreim K Δ h L) = L := by
  ext ρ
  constructor
  · rintro ⟨τ, ⟨hτ, hmem⟩, hτ', rfl⟩
    exact hmem
  · intro hρ
    obtain ⟨σ, hσ⟩ := MonoidHom.mem_range.1 (hL hρ)
    have hσ' : restrictHom K Δ h ⟨(σ : Equiv.Perm Ω), σ.2⟩ = ρ := hσ
    exact ⟨(σ : Equiv.Perm Ω), ⟨σ.2, by rw [hσ']; exact hρ⟩, σ.2, hσ'⟩

/-! ### Window isomorphism is a full preimage

This is the identity that turns a statement about the group `K̄ = K^Δ` acting on `Δ` into
a statement about `K` and the window `Δ`. -/

/-- **`Iso^Δ_K(x,y)` is the full preimage, under `res : K → S(Δ)`, of
`Iso_{K̄}(x|_Δ, y|_Δ)`.** -/
theorem wIso_eq_windowPreim (h : IsInvariant K Δ) (x y : Ω → A) :
    wIso Δ (K : Set (Equiv.Perm Ω)) x y =
      windowPreim K Δ h
        (strIso ((restrictTo K Δ h : Subgroup (Equiv.Perm Δ)) : Set (Equiv.Perm Δ))
          (restrictStr Δ x) (restrictStr Δ y)) := by
  ext τ
  constructor
  · rintro ⟨hτ, hcond⟩
    refine ⟨hτ, ⟨⟨⟨τ, hτ⟩, rfl⟩, ?_⟩⟩
    rw [strAct_eq_iff]
    intro w
    exact hcond (w : Ω) w.2
  · rintro ⟨hτ, -, hiso⟩
    refine ⟨hτ, fun u hu => ?_⟩
    have := strAct_eq_iff.1 hiso ⟨u, hu⟩
    exact this

/-- The same identity for a *window* inside the window: `Iso^{Δ'}_K(x,y)` is the full
preimage of `Iso^{Δ''}_{K̄}(x|_Δ, y|_Δ)` when `Δ' = Δ'' ⊆ Δ`. -/
theorem wIso_eq_windowPreim_sub (h : IsInvariant K Δ) (Δ' : Set Δ) (x y : Ω → A) :
    wIso (Subtype.val '' Δ') (K : Set (Equiv.Perm Ω)) x y =
      windowPreim K Δ h
        (wIso Δ' ((restrictTo K Δ h : Subgroup (Equiv.Perm Δ)) : Set (Equiv.Perm Δ))
          (restrictStr Δ x) (restrictStr Δ y)) := by
  ext τ
  constructor
  · rintro ⟨hτ, hcond⟩
    exact ⟨hτ, ⟨⟨⟨τ, hτ⟩, rfl⟩, fun w hw => hcond (w : Ω) ⟨w, hw, rfl⟩⟩⟩
  · rintro ⟨hτ, -, hcond⟩
    refine ⟨hτ, ?_⟩
    rintro u ⟨w, hw, rfl⟩
    exact hcond w hw

/-! ### Transport of instances -/

/-- An instance on the window `Δ` seen as an instance on `Ω`: the candidate set is the
full preimage in `K`, the window is the same set of points, and the strings are extended
by the reference string `x₀` outside `Δ`. -/
noncomputable def windowInstance (K : Subgroup (Equiv.Perm Ω)) (Δ : Set Ω)
    (h : IsInvariant K Δ) (x₀ : Ω → A) (J : SIInstance Δ A) : SIInstance Ω A where
  K := windowPreim K Δ h J.K
  Δ := Subtype.val '' J.Δ
  x := extendStr Δ x₀ J.x
  y := extendStr Δ x₀ J.y

/-- The lifted instance has a window of the same size. -/
theorem windowSize_windowInstance (h : IsInvariant K Δ) (x₀ : Ω → A) (J : SIInstance Δ A) :
    (windowInstance K Δ h x₀ J).windowSize = J.windowSize := by
  rw [SIInstance.windowSize, SIInstance.windowSize, windowInstance]
  exact Set.ncard_image_of_injective _ Subtype.val_injective

/-- The answer to the lifted instance is the full preimage of the answer to the original
instance. -/
theorem answer_windowInstance (h : IsInvariant K Δ) (x₀ : Ω → A) (J : SIInstance Δ A) :
    (windowInstance K Δ h x₀ J).answer = windowPreim K Δ h J.answer := by
  ext τ
  constructor
  · rintro ⟨⟨hτ, hK⟩, hcond⟩
    refine ⟨hτ, hK, fun w hw => ?_⟩
    calc J.x w = extendStr Δ x₀ J.x (w : Ω) := (extendStr_coe Δ x₀ J.x w).symm
      _ = extendStr Δ x₀ J.y ((τ : Equiv.Perm Ω) (w : Ω)) := hcond (w : Ω) ⟨w, hw, rfl⟩
      _ = J.y (restrictHom K Δ h ⟨τ, hτ⟩ w) :=
          extendStr_coe Δ x₀ J.y (restrictHom K Δ h ⟨τ, hτ⟩ w)
  · rintro ⟨hτ, hK, hcond⟩
    refine ⟨⟨hτ, hK⟩, ?_⟩
    rintro u ⟨w, hw, rfl⟩
    calc extendStr Δ x₀ J.x (w : Ω) = J.x w := extendStr_coe Δ x₀ J.x w
      _ = J.y (restrictHom K Δ h ⟨τ, hτ⟩ w) := hcond w hw
      _ = extendStr Δ x₀ J.y ((τ : Equiv.Perm Ω) (w : Ω)) :=
          (extendStr_coe Δ x₀ J.y (restrictHom K Δ h ⟨τ, hτ⟩ w)).symm

/-- On instances whose candidate set lies in `K̄ = K^Δ`, the answer to the lifted instance
determines the answer to the original one. -/
theorem windowImage_answer_windowInstance (h : IsInvariant K Δ) (x₀ : Ω → A)
    (J : SIInstance Δ A) (hJ : J.K ⊆ (restrictTo K Δ h : Set (Equiv.Perm Δ))) :
    windowImage K Δ h (windowInstance K Δ h x₀ J).answer = J.answer := by
  rw [answer_windowInstance]
  exact windowImage_windowPreim h (fun ρ hρ => hJ hρ.1)

/-! ### Transport of reductions -/

namespace SIReduction

/-- A reduction on the window `Δ` seen as a reduction on `Ω`: every call is lifted by
`Babai.windowInstance` and its answer is pushed back by `Babai.windowImage`.  The tree shape
is unchanged, so the number of calls and the window sizes are unchanged. -/
noncomputable def window (K : Subgroup (Equiv.Perm Ω)) (Δ : Set Ω) (h : IsInvariant K Δ)
    (x₀ : Ω → A) : SIReduction Δ A α → SIReduction Ω A α
  | .done a => .done a
  | .call J k =>
      .call (windowInstance K Δ h x₀ J)
        (fun ans => window K Δ h x₀ (k (windowImage K Δ h ans)))

/-- The lifted reduction makes exactly the lifted calls, provided every call of the
original reduction has its candidate set inside `K̄ = K^Δ`. -/
theorem calls_window (h : IsInvariant K Δ) (x₀ : Ω → A) :
    ∀ R : SIReduction Δ A α,
      (∀ J ∈ R.calls, J.K ⊆ (restrictTo K Δ h : Set (Equiv.Perm Δ))) →
      (window K Δ h x₀ R).calls = R.calls.map (windowInstance K Δ h x₀) := by
  intro R
  induction R with
  | done a => intro _; rfl
  | call J k ih =>
    intro hR
    have hJ : J.K ⊆ (restrictTo K Δ h : Set (Equiv.Perm Δ)) := hR J (by simp [calls])
    rw [window, calls_call, calls_call, List.map_cons,
      windowImage_answer_windowInstance h x₀ J hJ]
    exact congrArg _ (ih J.answer (fun J' hJ' => hR J' (by simp [calls, hJ'])))

/-- The lifted reduction computes the same value. -/
theorem run_window (h : IsInvariant K Δ) (x₀ : Ω → A) :
    ∀ R : SIReduction Δ A α,
      (∀ J ∈ R.calls, J.K ⊆ (restrictTo K Δ h : Set (Equiv.Perm Δ))) →
      (window K Δ h x₀ R).run = R.run := by
  intro R
  induction R with
  | done a => intro _; rfl
  | call J k ih =>
    intro hR
    have hJ : J.K ⊆ (restrictTo K Δ h : Set (Equiv.Perm Δ)) := hR J (by simp [calls])
    rw [window, run_call, run_call, windowImage_answer_windowInstance h x₀ J hJ]
    exact ih J.answer (fun J' hJ' => hR J' (by simp [calls, hJ']))

end SIReduction

end Babai
