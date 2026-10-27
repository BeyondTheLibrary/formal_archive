/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 13.1: Procedure LocalCertificates and Procedure Recompute H(W).
-/
import Workspace.LocalCertificates.Defs

/-!
# §13.1 Procedure LocalCertificates

## How the pseudocode is modelled

The paper's procedure is a `while` loop over a growing window `W ⊆ Ω`, carrying the group

> `H(W) := Aut^W_{G_T}(x)`  (to be updated as `W` is updated)

A *stage* of the loop (`Babai.Stage`) is the pair `(W, H(W))` together with the three
invariants that the paper's "Justification" paragraph states and uses:

* `H(W) ≤ G_T` ("An invariant of the while loop will be that `T` is invariant under the
  action of the group `H(W)`, i. e., `H(W) ≤ G_T`"),
* `H(W) = Aut^W_{G_T}(x)` (the "Notation" line of the pseudocode),
* `W ⊆ Aff(H(W), ψ_T)`, which is what makes `W` grow monotonically (`W_new ⊇ W_old`), and
* `W` is `H(W)`-invariant, which is what makes `Aut^W_{G_T}(x)` a group at all.

Line 01 is `Babai.Stage.init`, lines 03–04 are `Babai.Stage.step`, line 02 is
`Babai.Stage.LoopCond`.  The loop runs while `LoopCond` holds; it terminates because `|W|`
strictly increases (`Babai.Stage.ncard_lt_ncard_step`), and the number of iterations is
`Babai.haltIndex`, the first index at which `LoopCond` fails.  Lines 06–11 read off the
outputs `W(T)`, `K(T)`, `M(T)` from the stage reached
(`Babai.windowOut`, `Babai.certK`, `Babai.certM`).

Procedure Recompute `H(W)` (lines 04a–04h) is the *computation* of the group produced by
`Stage.step`; its mathematical content is Eq. (69) and the strong Luks reduction, stated
here as `Babai.eq_69` and `Babai.recompute_eq`.

The running-time claims of §13.1 are covered inside the RAM proof of Theorem 1.1.1
(`Algo.theorem_1_1_1`) and not stated as a separate RAM theorem; see the corrected paper.
-/

namespace Babai

open MulAction Equiv Equiv.Perm
open scoped Pointwise
open scoped Classical

variable {Ω Γ Λ : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ]
  {G H : Subgroup (Equiv.Perm Ω)}

/-! ### `G_T` and `ψ_T` -/

/-- §13.1.  The group `G_T`, the setwise stabilizer of the test set `T` in `G` with
respect to `ϕ` (Notation 13.1.1). -/
abbrev bigGT (ϕ : G →* Equiv.Perm Γ) (T : Set Γ) : Subgroup (Equiv.Perm Ω) :=
  stabIn ϕ (le_refl G) T

/-- §13.1.  The representation `ψ_T` restricted to a subgroup `H ≤ G_T`; the paper writes
`ψ̄_T` for this restriction in the proof of Claim 13.1.6. -/
def psiOn (ϕ : G →* Equiv.Perm Γ) (T : Set Γ) (hH : H ≤ bigGT ϕ T) :
    H →* Equiv.Perm T :=
  (psi ϕ T).comp (Subgroup.inclusion hH)

theorem imgOn_eq_range (ϕ : G →* Equiv.Perm Γ) (T : Set Γ) (hH : H ≤ bigGT ϕ T) :
    imgOn ϕ T hH = (psiOn ϕ T hH).range := rfl

theorem psiOn_comp {H' : Subgroup (Equiv.Perm Ω)} (ϕ : G →* Equiv.Perm Γ) (T : Set Γ)
    (hH : H ≤ bigGT ϕ T) (h : H' ≤ H) :
    psiOn ϕ T (le_trans h hH) = (psiOn ϕ T hH).comp (Subgroup.inclusion h) := rfl

/-! ### The stages of the while loop -/

variable (ϕ : G →* Equiv.Perm Γ) (x : Ω → Λ) (T : Set Γ)

/-- §13.1, Procedure LocalCertificates.  A *stage* of the while loop: the window `W` and
the group `H = H(W) = Aut^W_{G_T}(x)`, together with the invariants of the loop. -/
structure Stage where
  /-- The current window `W ⊆ Ω`. -/
  W : Set Ω
  /-- The current group `H(W)`. -/
  H : Subgroup (Equiv.Perm Ω)
  /-- "An invariant of the while loop will be that `T` is invariant under the action of
  the group `H(W)`, i. e., `H(W) ≤ G_T`." -/
  le : H ≤ bigGT ϕ T
  /-- The Notation line of the pseudocode: `H(W) = Aut^W_{G_T}(x)`. -/
  isAut : (H : Set (Equiv.Perm Ω)) = wAut W (bigGT ϕ T : Set (Equiv.Perm Ω)) x
  /-- `W` is `H(W)`-invariant (this is what makes `Aut^W_{G_T}(x)` a group). -/
  inv : IsInvariant H W
  /-- The window never exceeds the set of points affected by the current group; this is
  what gives `W_new ⊇ W_old` in the paper's Justification. -/
  sub : W ⊆ {u | AffectedIn (psiOn ϕ T le) u}

namespace Stage

variable {ϕ x T}

/-- The set of points affected by `(H(W), ψ_T)`, the new window of line 03. -/
def aff (s : Stage ϕ x T) : Set Ω := {u | AffectedIn (psiOn ϕ T s.le) u}

theorem isInvariant_aff (s : Stage ϕ x T) : IsInvariant s.H s.aff :=
  isInvariant_affectedIn _

theorem sub_aff (s : Stage ϕ x T) : s.W ⊆ s.aff := s.sub

variable (ϕ x T)

/-- Line 01: `W := ∅` (: so `H(W) = G_T` :). -/
def init : Stage ϕ x T where
  W := ∅
  H := bigGT ϕ T
  le := le_rfl
  isAut := by rw [wAut_empty]
  inv := by intro σ _; simp
  sub := by simp

variable {ϕ x T}

/-- Lines 03–04: `W ← Aff(H(W), ψ_T)` and recompute `H(W)`. -/
noncomputable def step (s : Stage ϕ x T) : Stage ϕ x T where
  W := s.aff
  H := wAutSubgroup s.H s.aff s.isInvariant_aff x
  le := le_trans (wAutSubgroup_le _ _ _ _) s.le
  isAut := by
    rw [coe_wAutSubgroup, s.isAut, wAut_wAut s.sub_aff]
  inv := fun σ hσ => s.isInvariant_aff σ ((wAutSubgroup_le s.H s.aff s.isInvariant_aff x) hσ)
  sub := by
    intro u hu
    have h := observation_13_1_5 (H₁ := wAutSubgroup s.H s.aff s.isInvariant_aff x)
      (H₂ := s.H) (wAutSubgroup_le _ _ _ _) (psiOn ϕ T s.le)
    exact h hu

@[simp] theorem step_W (s : Stage ϕ x T) : s.step.W = s.aff := rfl

theorem step_H_le (s : Stage ϕ x T) : s.step.H ≤ s.H :=
  wAutSubgroup_le s.H s.aff s.isInvariant_aff x

/-- The paper's Justification: "on each iteration of the while loop on lines 02–05,
`H(W_new) ≤ H(W_old)` and `W_new ⊇ W_old`." -/
theorem W_subset_step_W (s : Stage ϕ x T) : s.W ⊆ s.step.W := s.sub_aff

/-- Line 02, the while condition:
`H(W)^T ≥ A(T)` and `Aff(H(W), ψ_T) ⊄ W`. -/
def LoopCond (s : Stage ϕ x T) : Prop :=
  alternatingGroup T ≤ imgOn ϕ T s.le ∧ ¬ s.aff ⊆ s.W

/-- "In fact, these inclusions are proper or else we exit on line 02": while the loop
runs, the window strictly grows. -/
theorem ssubset_step_W (s : Stage ϕ x T) (h : s.LoopCond) : s.W ⊂ s.step.W :=
  ⟨s.W_subset_step_W, fun hcon => h.2 hcon⟩

theorem ncard_lt_ncard_step (s : Stage ϕ x T) (h : s.LoopCond) :
    s.W.ncard < s.step.W.ncard :=
  Set.ncard_lt_ncard (s.ssubset_step_W h) (Set.toFinite _)

/-- "It also follows that on line 07 we actually have `Aff(H(W), ψ_T) = W`": when the loop
stops with `H(W)^T ≥ A(T)`, the window is exactly the affected set. -/
theorem aff_eq_of_not_loopCond (s : Stage ϕ x T) (h : ¬ s.LoopCond)
    (hgiant : alternatingGroup T ≤ imgOn ϕ T s.le) : s.aff = s.W := by
  have h2 : s.aff ⊆ s.W := by
    by_contra hcon
    exact h ⟨hgiant, hcon⟩
  exact le_antisymm h2 s.sub_aff

end Stage

/-! ### The while loop -/

/-- The stage reached after `i` iterations of the while loop (lines 01–05). -/
noncomputable def stages : ℕ → Stage ϕ x T
  | 0 => Stage.init ϕ x T
  | (i + 1) => (stages i).step

@[simp] theorem stages_zero : stages ϕ x T 0 = Stage.init ϕ x T := rfl

@[simp] theorem stages_succ (i : ℕ) : stages ϕ x T (i + 1) = (stages ϕ x T i).step := rfl

variable {ϕ x T}

/-- While the loop condition holds, the window has grown at least by one point per
round. -/
theorem le_ncard_stages_W (i : ℕ) (h : ∀ j < i, (stages ϕ x T j).LoopCond) :
    i ≤ (stages ϕ x T i).W.ncard := by
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih =>
      have hi : i ≤ (stages ϕ x T i).W.ncard := ih fun j hj => h j (by omega)
      have := (stages ϕ x T i).ncard_lt_ncard_step (h i (by omega))
      rw [stages_succ]
      omega

/-- The while loop terminates: the window strictly increases in each round and is bounded
by `Ω`. -/
theorem exists_not_loopCond : ∃ i, ¬ (stages ϕ x T i).LoopCond := by
  by_contra hcon
  push_neg at hcon
  have h := le_ncard_stages_W (ϕ := ϕ) (x := x) (T := T) (Fintype.card Ω + 1)
    fun j _ => hcon j
  have hle : (stages ϕ x T (Fintype.card Ω + 1)).W.ncard ≤ Fintype.card Ω := by
    have := Set.ncard_le_ncard (Set.subset_univ (stages ϕ x T (Fintype.card Ω + 1)).W)
      (Set.toFinite _)
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card] at this
  omega

variable (ϕ x T)

/-- The number of iterations of the while loop: the first index at which the loop
condition of line 02 fails. -/
noncomputable def haltIndex : ℕ := Nat.find (exists_not_loopCond (ϕ := ϕ) (x := x) (T := T))

/-- The stage at which the loop exits (line 06). -/
noncomputable def outStage : Stage ϕ x T := stages ϕ x T (haltIndex ϕ x T)

theorem not_loopCond_outStage : ¬ (outStage ϕ x T).LoopCond :=
  Nat.find_spec (exists_not_loopCond (ϕ := ϕ) (x := x) (T := T))

theorem loopCond_of_lt_haltIndex {i : ℕ} (h : i < haltIndex ϕ x T) :
    (stages ϕ x T i).LoopCond := by
  by_contra hcon
  have hle : haltIndex ϕ x T ≤ i := Nat.find_le hcon
  omega

/-! ### The outputs (lines 06–11) -/

/-- Line 06: `W(T) ← W`. -/
noncomputable def windowOut : Set Ω := (outStage ϕ x T).W

/-- Line 07: the test on which the procedure branches, `H(W)^T ≥ A(T)`. -/
def isFullOut : Prop := alternatingGroup T ≤ imgOn ϕ T (outStage ϕ x T).le

/-- Line 08: `K(T) ← H(W)_(W̄)` where `W̄ = Ω ∖ W`, the pointwise stabilizer of the
complement of the window. -/
noncomputable def certK : Subgroup (Equiv.Perm Ω) :=
  pointwiseStabilizer (outStage ϕ x T).H (windowOut ϕ x T)ᶜ

/-- Line 10: `M(T) ← H(W)^T`. -/
noncomputable def certM : Subgroup (Equiv.Perm T) := imgOn ϕ T (outStage ϕ x T).le

/-! ### Procedure Recompute `H(W)` (lines 04a–04h) -/

section Recompute

variable {ϕ x T}

/-- Line 04a: `N ← H(W_old)^T_(T)`, the kernel of the `H(W_old) → S(T)` map. -/
def kerN (s : Stage ϕ x T) : Subgroup (Equiv.Perm Ω) :=
  (psiOn ϕ T s.le).ker.map s.H.subtype

theorem kerN_le (s : Stage ϕ x T) : kerN s ≤ s.H := by
  rintro σ ⟨τ, -, rfl⟩
  exact τ.2

theorem mem_kerN (s : Stage ϕ x T) {σ : Equiv.Perm Ω} :
    σ ∈ kerN s ↔ ∃ h : σ ∈ s.H, psiOn ϕ T s.le ⟨σ, h⟩ = 1 := by
  constructor
  · rintro ⟨⟨τ, hτ⟩, hker, rfl⟩
    exact ⟨hτ, hker⟩
  · rintro ⟨hσ, hker⟩
    exact ⟨⟨σ, hσ⟩, hker, rfl⟩

/-- Eq. (69), §13.1.

> `H(W_old) = ⋃_sb N sb`  (69)
>
> where the union extends over `sb ∈ H(W_old)^T`.

The paper's `N sb` is the coset `N σ` for any lift `σ ∈ H(W_old)` of `sb` (line 04d), which
in Lean's left-action convention is `σ • N` (see the header of `Workspace/Luks/Defs.lean`).
`lift` is the selection made on line 04d. -/
theorem eq_69 (s : Stage ϕ x T) (lift : imgOn ϕ T s.le → Equiv.Perm Ω)
    (hlift : ∀ sb, ∃ h : lift sb ∈ s.H, psiOn ϕ T s.le ⟨lift sb, h⟩ = (sb : Equiv.Perm T)) :
    (s.H : Set (Equiv.Perm Ω)) = ⋃ sb : imgOn ϕ T s.le, (lift sb) • (kerN s : Set (Equiv.Perm Ω)) := by
  ext σ
  constructor
  · intro hσ
    -- `sb := σ^{ψ_T}`, and `σ = (lift sb) · ((lift sb)⁻¹ σ)` with the second factor in `N`
    have hmem : psiOn ϕ T s.le ⟨σ, hσ⟩ ∈ imgOn ϕ T s.le := ⟨⟨σ, hσ⟩, rfl⟩
    set sb : imgOn ϕ T s.le := ⟨psiOn ϕ T s.le ⟨σ, hσ⟩, hmem⟩ with hsb
    obtain ⟨hl, hlval⟩ := hlift sb
    refine Set.mem_iUnion.2 ⟨sb, ?_⟩
    refine (mem_perm_smul_set).2 ?_
    refine (mem_kerN s).2 ⟨s.H.mul_mem (s.H.inv_mem hl) hσ, ?_⟩
    have : psiOn ϕ T s.le ⟨(lift sb)⁻¹ * σ, s.H.mul_mem (s.H.inv_mem hl) hσ⟩
        = (psiOn ϕ T s.le ⟨lift sb, hl⟩)⁻¹ * psiOn ϕ T s.le ⟨σ, hσ⟩ := by
      rw [← map_inv, ← map_mul]
      rfl
    rw [this, hlval, hsb]
    simp
  · intro hσ
    rw [Set.mem_iUnion] at hσ
    obtain ⟨sb, hmem⟩ := hσ
    obtain ⟨hl, -⟩ := hlift sb
    have hker := (mem_perm_smul_set).1 hmem
    have hmul : lift sb * ((lift sb)⁻¹ * σ) ∈ s.H := s.H.mul_mem hl (kerN_le s hker)
    rw [mul_inv_cancel_left] at hmul
    exact hmul

/-- Lines 04b–04h: the group collected by Procedure Recompute `H(W)`,
`L = ⋃_sb Aut^{W_new}_{Nσ}(x)`. -/
noncomputable def recompute (s : Stage ϕ x T) (lift : imgOn ϕ T s.le → Equiv.Perm Ω) :
    Set (Equiv.Perm Ω) :=
  ⋃ sb : imgOn ϕ T s.le, wAut s.aff ((lift sb) • (kerN s : Set (Equiv.Perm Ω))) x

/-- §13.1, the justification of Procedure Recompute `H(W)`.

> This is immediate from the observation `H(W_old) = ⋃_sb N sb` (69) … So we can use strong
> descent (over the orbits of `N` in `W_new`) to compute `Aut^{W_new}_{H(W_old)}(x)`.  But
> this group is `H(W_new)` because `W_new ⊇ W_old`.

The two steps are: the union of Eq. (69) is carried through `Aut^{W_new}`, and
`Aut^{W_new}_{H(W_old)}(x) = Aut^{W_new}_{G_T}(x) = H(W_new)` (`Babai.wAut_wAut`). -/
theorem recompute_eq (s : Stage ϕ x T) (lift : imgOn ϕ T s.le → Equiv.Perm Ω)
    (hlift : ∀ sb, ∃ h : lift sb ∈ s.H, psiOn ϕ T s.le ⟨lift sb, h⟩ = (sb : Equiv.Perm T)) :
    recompute s lift = (s.step.H : Set (Equiv.Perm Ω)) := by
  have h69 := eq_69 s lift hlift
  rw [s.step.isAut, Stage.step_W, ← wAut_wAut (K := (bigGT ϕ T : Set (Equiv.Perm Ω))) (x := x) s.sub_aff,
    ← s.isAut, h69]
  ext σ
  simp only [recompute, Set.mem_iUnion, mem_wAut, Set.mem_iUnion]
  constructor
  · rintro ⟨sb, hσ, hresp⟩
    exact ⟨⟨sb, hσ⟩, hresp⟩
  · rintro ⟨⟨sb, hσ⟩, hresp⟩
    exact ⟨sb, hσ, hresp⟩

end Recompute

end Babai
