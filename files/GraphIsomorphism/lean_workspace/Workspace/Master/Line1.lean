/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 15, line 1: one round of Procedure Reduce-to-Johnson (Sec. 11.3).
-/
import Workspace.Master.JohnsonActionData
import Workspace.Master.CosetForms

/-!
# §15, line 1: Procedure Reduce-to-Johnson

> **Procedure Reduce-to-Johnson**
> Input: group `G ≤ S(Ω)`, strings `x, y : Ω → Σ`
> Output: `Iso_G(x,y)` or updated `Ω, G, x, y`, `G` transitive, with set `ℬ` of blocks on
> which `Ḡ` acts as a Johnson group
> 1. if `G ≤ Aut(x)` then if `x = y` return `G`, else return `∅`, exit
> 2. if `|G| < C₀` for some absolute constant `C₀` then compute `Iso_G(x,y)` by brute
>    force, exit
> 3. if `G` intransitive then apply Chain Rule
> 4. (: `G` transitive :) Find minimal block system `ℬ`.  Let `m = |ℬ|`, `Ḡ ≤ S(ℬ)` the
>    induced `G`-action and `N` the kernel of `G → Ḡ` (: `Ḡ` is primitive :)
> 5. if `|Ḡ| < m^{1+log₂ m}` then reduce `G` to `N` via imprimitive Luks reduction
> 6. else (: `Ḡ` a Cameron group of order `≥ m^{1+log₂ m}` :) reduce `Ḡ` to a Johnson group
>    via Luks descent (: Theorem 11.2.1, multiplicative cost `≤ m` :)
> 7. (: `Ḡ` a Johnson group :) return `Ω, G, ℬ, Ḡ`, `x, y`

The four branches are four named reductions, three of them on the window and carried back
to `Ω` by `Babai.liftWindow`:

| step | branch | progress |
|---|---|---|
| 1, 2 | `Babai.bruteForceBranch` — a leaf, no calls | nothing to prove |
| 3 | `Babai.chainRuleBranch` — the Chain Rule over **all** the orbits of `G` | `Babai.IsChainRuleRound`: every orbit is strictly smaller than the window and the orbits partition it |
| 5 | `Babai.blockLuksBranch` — `Babai.line2Reduction`, brute force over `Ḡ` then the orbits of `N` | `3n' ≤ 2n`: the orbits of `N` lie inside blocks |
| 6 | `Babai.DescentData.branch` — `Babai.descentReduction` to `K₁`, the subgroup of `K` above `G₁ = ψ⁻¹(N̄)` | `2·param J ≤ param I` when `G₁` is transitive, `2n' ≤ n` otherwise |

**Step 6 and step 7.**  Theorem 11.2.1 gives a normal subgroup `N̄ ⊴ Ḡ` of index at most
`m` with a Johnson action on a system `𝒞` of imprimitivity of `ℬ`, and step 6 descends to
`G₁ = ψ⁻¹(N̄)`.  The comment of step 7, *"`Ḡ` a Johnson group"*, then says that the new
instances are Johnson cases.  That is a theorem here — `Babai.isJohnsonCase_preimSubgroup`,
the blocks being the unions `⋃ C` for `C ∈ 𝒞` — but only **when `G₁` is transitive on the
window**, which does not follow from `N̄` being transitive on `ℬ`: see the corrected paper
(Sec. 11.3, steps 6–7) for a group where it fails.  The branch therefore does what the
procedure itself prescribes in that case, namely go back to step 3 and apply the Chain Rule
to the orbits of `G₁`.  Those orbits all have the same length `n/r` with `r ≥ 2`, because
`G₁ ⊴ G` and `G` is transitive (Fact 11.1.8), so that case shrinks the window instead.

In the transitive case step 6 does not shrink the window at all — the paper's own
recurrence (ii) of Sec. 11.4, `T_trans(x) ≤ m(T_Jh(x) + p(x))`, says so — and what it
achieves is that the instance is now a **Johnson case**.  In the measure of
`Workspace/Master/Procedure.lean` that is a drop of the second component, because an
instance outside the Johnson case is given the parameter `2n` (see `Babai.param`), and a
Johnson case on the same window has `m ≤ n`.
-/

universe u v

namespace Babai

open MulAction Equiv Equiv.Perm
open scoped Pointwise

/-! ### Proposition 11.1.6 (Descent) as a reduction -/

section Descent

variable {Ω : Type u} {A : Type v}

/-- §11.1, **Proposition 11.1.6** (Descent) as a reduction: one call of
`Iso^Δ_H(x, y^{σ⁻¹})` for each coset representative `σ` in the list, and the union of the
translates `σ · (that set)`.  This is Eq. (62). -/
noncomputable def descentReduction (H : Subgroup (Equiv.Perm Ω)) (Δ : Set Ω) (x y : Ω → A) :
    List (Equiv.Perm Ω) → SIReduction Ω A (Set (Equiv.Perm Ω))
  | [] => .done ∅
  | σ :: rest =>
      .call ⟨(H : Set (Equiv.Perm Ω)), Δ, x, strAct y σ⁻¹⟩ fun ans =>
        (descentReduction H Δ x y rest).bind fun s => .done (σ • ans ∪ s)

/-- Eq. (62): the value of the descent reduction is the union of the translated answers. -/
theorem run_descentReduction (H : Subgroup (Equiv.Perm Ω)) (Δ : Set Ω) (x y : Ω → A) :
    ∀ L : List (Equiv.Perm Ω), (descentReduction H Δ x y L).run =
      ⋃ σ ∈ L, σ • wIso Δ (H : Set (Equiv.Perm Ω)) x (strAct y σ⁻¹) := by
  intro L
  induction L with
  | nil => rw [descentReduction]; simp
  | cons σ rest ih =>
    rw [descentReduction, SIReduction.run_call, SIReduction.run_bind, SIReduction.run_done,
      ih]
    have hans : (⟨(H : Set (Equiv.Perm Ω)), Δ, x, strAct y σ⁻¹⟩ : SIInstance Ω A).answer =
        wIso Δ (H : Set (Equiv.Perm Ω)) x (strAct y σ⁻¹) := rfl
    rw [hans]
    ext τ
    simp only [Set.mem_union, Set.mem_iUnion, List.mem_cons, exists_prop]
    constructor
    · rintro (h | ⟨ρ, hρ, hτ⟩)
      · exact ⟨σ, Or.inl rfl, h⟩
      · exact ⟨ρ, Or.inr hρ, hτ⟩
    · rintro ⟨ρ, (rfl | hρ), hτ⟩
      · exact Or.inl hτ
      · exact Or.inr ⟨ρ, hρ, hτ⟩

/-- The descent reduction makes exactly one call per coset representative. -/
theorem calls_descentReduction (H : Subgroup (Equiv.Perm Ω)) (Δ : Set Ω) (x y : Ω → A) :
    ∀ L : List (Equiv.Perm Ω), (descentReduction H Δ x y L).calls =
      L.map (fun σ => (⟨(H : Set (Equiv.Perm Ω)), Δ, x, strAct y σ⁻¹⟩ : SIInstance Ω A)) := by
  intro L
  induction L with
  | nil => rw [descentReduction]; simp
  | cons σ rest ih =>
    rw [descentReduction, SIReduction.calls_call, SIReduction.calls_bind,
      SIReduction.calls_done, ih]
    simp

theorem calls_length_descentReduction (H : Subgroup (Equiv.Perm Ω)) (Δ : Set Ω) (x y : Ω → A)
    (L : List (Equiv.Perm Ω)) : (descentReduction H Δ x y L).calls.length = L.length := by
  rw [calls_descentReduction, List.length_map]

/-- Every call of the descent reduction is an instance with respect to `H`, on the same
window. -/
theorem calls_descentReduction_spec (H : Subgroup (Equiv.Perm Ω)) (Δ : Set Ω) (x y : Ω → A)
    (L : List (Equiv.Perm Ω)) :
    ∀ J ∈ (descentReduction H Δ x y L).calls,
      J.K = (H : Set (Equiv.Perm Ω)) ∧ J.Δ = Δ := by
  intro J hJ
  rw [calls_descentReduction, List.mem_map] at hJ
  obtain ⟨σ, -, rfl⟩ := hJ
  exact ⟨rfl, rfl⟩

/-! ### The list of coset representatives -/

variable [Fintype Ω] [DecidableEq Ω]

open scoped Classical in
/-- The canonical right coset representatives of `H` in `G`, as a list: one per element of
`G ⧸ H.subgroupOf G` (`Babai.cosetRep`).  Its length is the index `|G : H|`. -/
noncomputable def cosetRepList (H G : Subgroup (Equiv.Perm Ω)) : List (Equiv.Perm Ω) :=
  letI : Fintype (G ⧸ H.subgroupOf G) := Fintype.ofFinite _
  (Finset.univ : Finset (G ⧸ H.subgroupOf G)).toList.map cosetRep

open scoped Classical in
/-- There is at least one coset representative: the quotient `G/(H ∩ G)` has the trivial
coset in it. -/
theorem cosetRepList_ne_nil (H G : Subgroup (Equiv.Perm Ω)) : cosetRepList H G ≠ [] := by
  classical
  letI : Fintype (G ⧸ H.subgroupOf G) := Fintype.ofFinite _
  have hmem : ((1 : G) : G ⧸ H.subgroupOf G) ∈
      (Finset.univ : Finset (G ⧸ H.subgroupOf G)).toList :=
    Finset.mem_toList.2 (Finset.mem_univ _)
  rw [cosetRepList]
  exact fun h => List.ne_nil_of_mem hmem (List.map_eq_nil_iff.1 h)

open scoped Classical in
/-- Every coset representative lies in `G`. -/
theorem mem_cosetRepList {H G : Subgroup (Equiv.Perm Ω)} {σ : Equiv.Perm Ω}
    (h : σ ∈ cosetRepList H G) : σ ∈ G := by
  classical
  letI : Fintype (G ⧸ H.subgroupOf G) := Fintype.ofFinite _
  rw [cosetRepList, List.mem_map] at h
  obtain ⟨q, -, rfl⟩ := h
  exact cosetRep_mem q

theorem length_cosetRepList (H G : Subgroup (Equiv.Perm Ω)) :
    (cosetRepList H G).length = H.relIndex G := by
  classical
  letI : Fintype (G ⧸ H.subgroupOf G) := Fintype.ofFinite _
  rw [cosetRepList, List.length_map, Finset.length_toList, Finset.card_univ,
    ← Nat.card_eq_fintype_card, card_quotient_subgroupOf]

/-- The cosets of the representatives cover `G` (proof of Prop. 11.1.6). -/
theorem coe_eq_iUnion_cosetRepList {H G : Subgroup (Equiv.Perm Ω)} (hHG : H ≤ G) :
    (G : Set (Equiv.Perm Ω)) =
      ⋃ σ ∈ cosetRepList H G, σ • (H : Set (Equiv.Perm Ω)) := by
  classical
  letI : Fintype (G ⧸ H.subgroupOf G) := Fintype.ofFinite _
  rw [coe_eq_iUnion_cosetRep hHG]
  ext g
  simp only [Set.mem_iUnion, cosetRepList, List.mem_map, Finset.mem_toList,
    Finset.mem_univ, true_and, exists_prop]
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨cosetRep q, ⟨q, rfl⟩, hq⟩
  · rintro ⟨σ, ⟨q, rfl⟩, hσ⟩
    exact ⟨q, hσ⟩

/-- §11.1, Prop. 11.1.6 as a reduction: **the descent to `H ≤ G` is correct**, and it makes
`|G : H|` calls. -/
theorem run_descentReduction_cosetRepList {H G : Subgroup (Equiv.Perm Ω)} (hHG : H ≤ G)
    (Δ : Set Ω) (x y : Ω → A) :
    (descentReduction H Δ x y (cosetRepList H G)).run =
      wIso Δ (G : Set (Equiv.Perm Ω)) x y := by
  rw [run_descentReduction]
  rw [descent_of_cover (H := H) (G := G) (R := {σ | σ ∈ cosetRepList H G})
    (by simpa using coe_eq_iUnion_cosetRepList hHG) Δ x y]
  rfl

/-- §11.1, Prop. 11.1.6 **in coset form**: with the canonical coset representatives the
union of the answers of the `|G : H|` coset calls is `Iso^Δ_G(x,y)`.  This is Eq. (62) as
printed, middle term. -/
theorem run_cosetDescent_cosetRepList {H G : Subgroup (Equiv.Perm Ω)} (hHG : H ≤ G)
    (Δ : Set Ω) (x y : Ω → A) :
    (cosetDescent H Δ x y (cosetRepList H G)).run =
      wIso Δ (G : Set (Equiv.Perm Ω)) x y := by
  rw [run_cosetDescent, descent_of_cover (H := H) (G := G)
    (R := {σ | σ ∈ cosetRepList H G})
    (by simpa using coe_eq_iUnion_cosetRepList hHG) Δ x y]
  refine Set.iUnion_congr fun σ => Set.iUnion_congr fun _ => ?_
  exact wIso_smul Δ (H : Set (Equiv.Perm Ω)) σ x y

/-- A coset cover with the index bound. Representatives themselves need not be canonical. -/
structure CosetRepEnum (H G : Subgroup (Equiv.Perm Ω)) where
  reps : List (Equiv.Perm Ω)
  cover : (G : Set (Equiv.Perm Ω)) = ⋃ σ ∈ reps, σ • (H : Set (Equiv.Perm Ω))
  length : reps.length ≤ H.relIndex G

noncomputable def CosetRepEnum.default {H G : Subgroup (Equiv.Perm Ω)} (h : H ≤ G) :
    CosetRepEnum H G :=
  ⟨cosetRepList H G, coe_eq_iUnion_cosetRepList h, le_of_eq (length_cosetRepList H G)⟩

theorem CosetRepEnum.mem {H G : Subgroup (Equiv.Perm Ω)} (E : CosetRepEnum H G)
    {σ : Equiv.Perm Ω} (hσ : σ ∈ E.reps) : σ ∈ G := by
  change σ ∈ (G : Set (Equiv.Perm Ω))
  rw [E.cover]
  exact Set.mem_iUnion₂.2 ⟨σ, hσ, ⟨1, H.one_mem, by simp⟩⟩

theorem CosetRepEnum.run_descent {H G : Subgroup (Equiv.Perm Ω)} (E : CosetRepEnum H G)
    (Δ : Set Ω) (x y : Ω → A) :
    (cosetDescent H Δ x y E.reps).run = wIso Δ (G : Set (Equiv.Perm Ω)) x y := by
  rw [run_cosetDescent, descent_of_cover (H := H) (G := G)
    (R := {σ | σ ∈ E.reps}) (by simpa using E.cover) Δ x y]
  refine Set.iUnion_congr fun σ => Set.iUnion_congr fun _ => ?_
  exact wIso_smul Δ (H : Set (Equiv.Perm Ω)) σ x y

end Descent

/-! ### The window bookkeeping shared by the branches -/

section Branches

open scoped Classical

variable {Ω : Type u} {A : Type v} [Fintype Ω] [DecidableEq Ω] {I : SIInstance Ω A}

/-- §11.3: what every branch of Procedure Reduce-to-Johnson needs — the group `G ≤ S(Ω)`
the instance is with respect to, and the fact that the window is `G`-invariant, so that the
group `G^Δ` induced on the window (Notation 2.2.1) is defined.  This is the part of
`Babai.JohnsonCaseData` that lines 1–3 of Sec. 15 share. -/
structure WindowData (I : SIInstance Ω A) where
  /-- The group the instance is with respect to. -/
  K : Subgroup (Equiv.Perm Ω)
  /-- The candidate set of the instance is that group. -/
  isGroup : I.K = (K : Set (Equiv.Perm Ω))
  /-- The window is invariant, so `K` acts on it. -/
  invariant : IsInvariant K I.Δ
  /-- The orbit order used by step 3, with the same orbits as the finite default list. -/
  orbits : OrbitEnum (restrictTo K I.Δ invariant) := .default _


/-- The group `G = K^Δ` induced on the window, on which Procedure Reduce-to-Johnson
operates. -/
def WindowData.windowGroup (d : WindowData I) : Subgroup (Equiv.Perm I.Δ) :=
  restrictTo d.K I.Δ d.invariant

/-- The window of the instance, counted in the two ways the statements use. -/
theorem WindowData.card_window (_d : WindowData I) :
    Fintype.card I.Δ = I.windowSize := by
  rw [← Nat.card_eq_fintype_card, SIInstance.windowSize, Nat.card_coe_set_eq]

/-- The total window size of the lifted calls is that of the original calls: lifting a
reduction to `Ω` changes no window size (`Babai.windowSize_windowInstance`). -/
theorem sum_windowSize_calls_liftWindow {K : Subgroup (Equiv.Perm Ω)} {Δ : Set Ω}
    (h : IsInvariant K Δ) (x₀ : Ω → A) (R : SIReduction Δ A (Set (Equiv.Perm Δ)))
    (hK : ∀ J ∈ R.calls, J.K ⊆ (restrictTo K Δ h : Set (Equiv.Perm Δ))) :
    (((liftWindow K Δ h x₀ R).calls).map SIInstance.windowSize).sum =
      ((R.calls).map SIInstance.windowSize).sum := by
  rw [calls_liftWindow h x₀ R hK, List.map_map]
  congr 1
  exact List.map_congr_left fun J _ => windowSize_windowInstance h x₀ J

/-- §11.3, steps 1 and 2: *"if `G ≤ Aut(x)` … return"* and *"if `|G| < C₀` … compute
`Iso_G(x,y)` by brute force, exit"*.  Both exits write the answer down without calling
String Isomorphism again, so at the level of the recursion they are one and the same leaf.

The brute force of step 2 is a *computation*, not a mathematical step: the set
`Iso_G(x,y)` is enumerated by running over the at most `C₀` elements of `G`.  What the
recursion sees is a branch with no calls. -/
def bruteForceBranch (I : SIInstance Ω A) : SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  .done I.answer

@[simp] theorem run_bruteForceBranch (I : SIInstance Ω A) :
    (bruteForceBranch I).run = I.answer := rfl

@[simp] theorem calls_bruteForceBranch (I : SIInstance Ω A) :
    (bruteForceBranch I).calls = [] := rfl

/-! ### Step 3: the Chain Rule for an intransitive group

> 3. if `G` intransitive then apply Chain Rule

The Chain Rule (Prop. 11.1.7) is applied to the orbits of `G`, all of them, in **one**
round.  Every orbit is strictly smaller than the window, because `G` is intransitive, and
the orbits partition the window, so their sizes add up to the window size.

Prop. 11.1.7 is printed for two windows, but the paper iterates it: the proof of
Theorem 11.1.9 says *"consider each `B_i` to be the window in succession, reducing the
group at each round, following the Chain Rule"*, and recurrence (i) of Sec. 11.4 sums over
all the parts of one partition in one round.  That is the cut taken here.  See
`Workspace/Master/DESIGN.md`, Round 25. -/

/-- The two `G`-invariant parts of a binary Chain Rule step: the orbit of `u`, and
everything else.  This is Prop. 11.1.7 as printed, for two windows.

Step 3 of Procedure Reduce-to-Johnson no longer runs on this list: it runs on all the
orbits at once (`Babai.orbitList`), which is the cut recurrence (i) of Sec. 11.4 prints.
The binary list is kept because Prop. 11.1.7 is stated for two windows. -/
def orbitSplit {Δ : Type*} (G : Subgroup (Equiv.Perm Δ)) (u : Δ) : List (Set Δ) :=
  [orbit G u, (orbit G u)ᶜ]

theorem isInvariant_compl {Δ : Type*} {G : Subgroup (Equiv.Perm Δ)} {S : Set Δ}
    (h : IsInvariant G S) : IsInvariant G Sᶜ := by
  intro σ hσ
  have hS := h σ hσ
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    intro hmem
    rw [← hS] at hmem
    obtain ⟨v', hv', hvv⟩ := hmem
    exact hv (by rwa [(σ : Equiv.Perm Δ).injective hvv] at hv')
  · intro hw
    refine ⟨(σ : Equiv.Perm Δ)⁻¹ w, ?_, by simp⟩
    intro hmem
    exact hw (by rw [← hS]; exact ⟨_, hmem, by simp⟩)

theorem isInvariant_mem_orbitSplit {Δ : Type*} {G : Subgroup (Equiv.Perm Δ)} {u : Δ}
    {S : Set Δ} (h : S ∈ orbitSplit G u) : IsInvariant G S := by
  have h' : S = orbit G u ∨ S = (orbit G u)ᶜ := by
    simpa [orbitSplit, or_assoc] using h
  rcases h' with rfl | rfl
  · exact isInvariant_orbit' G u
  · exact isInvariant_compl (isInvariant_orbit' G u)

theorem iUnion_orbitSplit {Δ : Type*} (G : Subgroup (Equiv.Perm Δ)) (u : Δ) :
    (⋃ S ∈ orbitSplit G u, S) = Set.univ := by
  ext w
  simp only [orbitSplit, Set.mem_iUnion, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false, exists_prop, Set.mem_univ, iff_true]
  by_cases hw : w ∈ orbit G u
  · exact ⟨orbit G u, Or.inl rfl, hw⟩
  · exact ⟨(orbit G u)ᶜ, Or.inr rfl, hw⟩

theorem sum_ncard_orbitSplit {Δ : Type*} [Fintype Δ] (G : Subgroup (Equiv.Perm Δ)) (u : Δ) :
    ((orbitSplit G u).map (fun S => S.ncard)).sum = Fintype.card Δ := by
  have h := Set.ncard_add_ncard_compl (orbit G u)
  simp only [orbitSplit, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [Nat.card_eq_fintype_card] at h
  omega

/-- §15, line 1, **step 3** as a branch of the round: the Chain Rule over the orbit of `u`
and its complement, run on the window with the group `G = K^Δ` induced on it, and carried
back to `Ω`. -/
noncomputable def chainRuleBranch (d : WindowData I) (_u : I.Δ) :
    SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  SIReduction.alignRed I
    (liftWindow d.K I.Δ d.invariant I.x
      (cosetChain (restrictStr I.Δ I.x) (restrictStr I.Δ I.y)
        d.orbits.windows (d.windowGroup : Set (Equiv.Perm I.Δ))))

/-- The coset-form round the branch is the alignment of: the Chain Rule over the orbits, on
the window, carried back to `Ω`.  Its calls are the instances the machine holds. -/
noncomputable def chainRuleCoset (d : WindowData I) (_u : I.Δ) :
    SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  liftWindow d.K I.Δ d.invariant I.x
    (cosetChain (restrictStr I.Δ I.x) (restrictStr I.Δ I.y)
      d.orbits.windows (d.windowGroup : Set (Equiv.Perm I.Δ)))

/-- §15, line 1, step 3: **the branch is the alignment of its coset form** (Remark 11.1.4,
Eq. (63)). -/
theorem chainRuleBranch_eq (d : WindowData I) (u : I.Δ) :
    chainRuleBranch d u = SIReduction.alignRed I (chainRuleCoset d u) := rfl

/-- Every call of the Chain Rule stays inside the group induced on the window, which is
what lets the branch be carried back to `Ω`. -/
theorem calls_chainRuleBranch_K (d : WindowData I) (u : I.Δ) :
    ∀ J ∈ (cosetChain (restrictStr I.Δ I.x) (restrictStr I.Δ I.y)
        d.orbits.windows (d.windowGroup : Set (Equiv.Perm I.Δ))).calls,
      J.K ⊆ (restrictTo d.K I.Δ d.invariant : Set (Equiv.Perm I.Δ)) :=
  calls_cosetChain_K _ _ _ _

/-- The identity is in the candidate set of a group instance, so the alignment at the root
of a branch does nothing. -/
theorem one_mem_K_of_windowData (d : WindowData I) : (1 : Equiv.Perm Ω) ∈ I.K := by
  rw [d.isGroup]; exact d.K.one_mem

/-- §15, line 1, step 3, **the coset form is correct**. -/
theorem run_chainRuleCoset (d : WindowData I) (u : I.Δ) :
    (chainRuleCoset d u).run = I.answer := by
  have hrun : (cosetChain (restrictStr I.Δ I.x) (restrictStr I.Δ I.y)
      d.orbits.windows (d.windowGroup : Set (Equiv.Perm I.Δ))).run =
      strIso ((restrictTo d.K I.Δ d.invariant : Subgroup (Equiv.Perm I.Δ)) :
        Set (Equiv.Perm I.Δ)) (restrictStr I.Δ I.x) (restrictStr I.Δ I.y) := by
    rw [run_cosetChain, d.orbits.cover, wIso_univ]
    rfl
  rw [chainRuleCoset,
    run_liftWindow d.invariant I.x I.y _ (calls_chainRuleBranch_K d u) hrun,
    SIInstance.answer, d.isGroup]

/-- §15, line 1, step 3 **is correct**: the branch returns `Iso^Δ_K(x,y)`. -/
theorem run_chainRuleBranch (d : WindowData I) (u : I.Δ) :
    (chainRuleBranch d u).run = I.answer := by
  rw [chainRuleBranch_eq, run_alignRed_of_one_mem (one_mem_K_of_windowData d),
    run_chainRuleCoset d u]

/-- §15, line 1, step 3, **the number of calls**: one per orbit of `G`, hence at most the
window size. -/
theorem calls_length_chainRuleBranch (d : WindowData I) (u : I.Δ) :
    ((chainRuleBranch d u).calls).length ≤ I.windowSize := by
  rw [chainRuleBranch_eq, calls_length_alignRed, chainRuleCoset,
    calls_length_liftWindow d.invariant I.x _ (calls_chainRuleBranch_K d u)]
  refine le_trans (calls_cosetChain _ _ _ _).1 ?_
  rw [← d.card_window, ← Nat.card_eq_fintype_card]
  rw [d.orbits.spec.length_eq]
  exact length_orbitList_le d.windowGroup

/-- A part of the split is strictly smaller than the window: the orbit is not everything
because `G` is intransitive, and its complement is not everything because the orbit is
nonempty. -/
theorem ncard_lt_of_mem_orbitSplit {Δ : Type*} [Fintype Δ] {G : Subgroup (Equiv.Perm Δ)}
    (hG : ¬ IsTransitive G) (u : Δ) {S : Set Δ} (hS : S ∈ orbitSplit G u) :
    S.ncard < Fintype.card Δ := by
  have hcard : (Set.univ : Set Δ).ncard = Fintype.card Δ := by
    rw [Set.ncard_univ, Nat.card_eq_fintype_card]
  have horb : orbit G u ≠ Set.univ := fun hc => hG ⟨u, hc⟩
  have h' : S = orbit G u ∨ S = (orbit G u)ᶜ := by
    simpa [orbitSplit, or_assoc] using hS
  rcases h' with rfl | rfl
  · have : orbit G u ⊂ Set.univ := ⟨Set.subset_univ _, fun hc => horb (Set.univ_subset_iff.1 hc)⟩
    have := Set.ncard_lt_ncard this (Set.toFinite _)
    omega
  · have hu : u ∈ orbit G u := mem_orbit_self u
    have : (orbit G u)ᶜ ⊂ Set.univ :=
      ⟨Set.subset_univ _, fun hc => (hc (Set.mem_univ u)) hu⟩
    have := Set.ncard_lt_ncard this (Set.toFinite _)
    omega

/-- §15, line 1, step 3, **the progress**: the branch is a Chain Rule round (recurrence (i)
of Sec. 11.4).  The two windows are strictly smaller than the window of the instance, and
their sizes add up to it. -/
theorem decreases_chainRuleBranch (d : WindowData I) (u : I.Δ)
    (hG : ¬ IsTransitive d.windowGroup) :
    IsChainRuleRound HintedInstance.win param (⟨I, none⟩ : HintedInstance Ω A)
      (((chainRuleBranch d u).calls).map (fun J => (⟨J, none⟩ : HintedInstance Ω A))) := by
  have hcard : Fintype.card I.Δ = I.windowSize := d.card_window
  have hn1 : 1 ≤ I.windowSize := by
    have : 0 < Fintype.card I.Δ := Fintype.card_pos_iff.2 ⟨u⟩
    omega
  have hsmall : ∀ J ∈ (chainRuleBranch d u).calls, J.windowSize < I.windowSize := by
    intro J hJmem
    rw [chainRuleBranch_eq, calls_alignRed, List.mem_map] at hJmem
    obtain ⟨J₀, hJ₀, rfl⟩ := hJmem
    rw [windowSize_alignInst, chainRuleCoset] at *
    obtain ⟨J', hJ', hsize⟩ :=
      calls_liftWindow_windowSize d.invariant I.x _ (calls_chainRuleBranch_K d u) J₀ hJ₀
    have hmem := (calls_cosetChain (restrictStr I.Δ I.x) (restrictStr I.Δ I.y)
      d.orbits.windows (d.windowGroup : Set (Equiv.Perm I.Δ))).2 J' hJ'
    have hlt : J'.windowSize < Fintype.card I.Δ :=
      ncard_lt_of_mem_orbitList hG (d.orbits.spec.mem_iff.1 hmem)
    omega
  refine ⟨hn1, ?_, ?_⟩
  · intro j hj
    obtain ⟨J, hJmem, rfl⟩ := List.mem_map.1 hj
    have h := hsmall J hJmem
    exact ⟨h, by show 2 * J.windowSize ≤ 2 * I.windowSize; omega⟩
  · rw [List.map_map]
    show (((chainRuleBranch d u).calls).map SIInstance.windowSize).sum ≤ I.windowSize
    rw [chainRuleBranch_eq, sum_windowSize_calls_alignRed, chainRuleCoset,
      sum_windowSize_calls_liftWindow d.invariant I.x _ (calls_chainRuleBranch_K d u)]
    refine le_trans (sum_windowSize_calls_cosetChain _ _ _ _) ?_
    rw [(d.orbits.spec.map Set.ncard).sum_eq, sum_ncard_orbitList, hcard]

/-! ### Step 5: the imprimitive Luks reduction to the kernel

> 5. if `|Ḡ| < m^{1+log₂ m}` then reduce `G` to `N` via imprimitive Luks reduction

This is the same reduction as line 2 of Sec. 15 (`Babai.line2Branch`): brute force over the
small quotient `Ḡ` and the Chain Rule over the orbits of `N = ker(G → Ḡ)`.  The only
difference is the bound on `|Ḡ|`: at line 2 it is `m! ≤ ℓ!`, here it is the test of step 5,
`m^{1+log₂ m}`, which is quasipolynomial in `n` because `m ≤ n`. -/

/-- §11.3, step 4: the minimal block system found at step 4, with the two facts about it
that steps 4 and 5 use — `Ḡ` is transitive, so the blocks are permuted, and there are at
least two of them, which is what makes the Luks reduction *imprimitive*. -/
structure BlockData (I : SIInstance Ω A) extends WindowData I where
  /-- Step 4: *"Find minimal block system `ℬ`"*. -/
  ℬ : Set (Set I.Δ)
  /-- `G` is transitive on the window (steps 3–4 have been passed). -/
  transitive : IsTransitive toWindowData.windowGroup
  /-- `ℬ` is a system of imprimitivity for `G`. -/
  system : IsSystemOfImprimitivity toWindowData.windowGroup Set.univ ℬ
  /-- There are at least two blocks. -/
  two_blocks : ∃ B₁ ∈ ℬ, ∃ B₂ ∈ ℬ, B₁ ≠ B₂

  /-- The image elements and kernel-orbit order used by step 5. -/
  enum : Line2Enum (blockHom toWindowData.windowGroup ℬ system.permutes).rangeRestrict :=
    .default _

namespace BlockData

variable (b : BlockData I)

/-- Step 4: the action `ψ : G → Ḡ` of the window group on the blocks, with `Ḡ` its image. -/
noncomputable def blockAction :
    b.windowGroup →* (blockHom b.windowGroup b.ℬ b.system.permutes).range :=
  (blockHom b.windowGroup b.ℬ b.system.permutes).rangeRestrict

theorem kerSubgroup_blockAction :
    kerSubgroup b.blockAction = blockKernel b.windowGroup b.ℬ b.system.permutes := by
  rw [kerSubgroup, blockKernel, blockAction, MonoidHom.ker_rangeRestrict]

end BlockData

/-- §15, line 1, **step 5** as a branch of the round: the imprimitive Luks reduction of
`Babai.line2Reduction`, run on the window and carried back to `Ω`. -/
noncomputable def blockLuksCoset (b : BlockData I) :
    SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  liftWindow b.K I.Δ b.invariant I.x
    (cosetLine2ReductionWith b.blockAction (restrictStr I.Δ I.x) (restrictStr I.Δ I.y) b.enum)

/-- §15, line 1, **step 5** as a branch of the round: the alignment (Remark 11.1.4) of the
coset form `Babai.blockLuksCoset`. -/
noncomputable def blockLuksBranch (b : BlockData I) :
    SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  SIReduction.alignRed I (blockLuksCoset b)

theorem blockLuksBranch_eq (b : BlockData I) :
    blockLuksBranch b = SIReduction.alignRed I (blockLuksCoset b) := rfl

theorem calls_blockLuksBranch_K (b : BlockData I) :
    ∀ J ∈ (cosetLine2ReductionWith b.blockAction (restrictStr I.Δ I.x)
      (restrictStr I.Δ I.y) b.enum).calls,
      J.K ⊆ (restrictTo b.K I.Δ b.invariant : Set (Equiv.Perm I.Δ)) :=
  calls_cosetLine2ReductionWith_K b.blockAction _ _ b.enum

/-- §15, line 1, step 5, the coset form **is correct**. -/
theorem run_blockLuksCoset (b : BlockData I) : (blockLuksCoset b).run = I.answer := by
  rw [blockLuksCoset,
    run_liftWindow b.invariant I.x I.y _ (calls_blockLuksBranch_K b)
      (run_cosetLine2ReductionWith b.blockAction _ _ b.enum),
    SIInstance.answer, b.isGroup]

/-- §15, line 1, step 5 **is correct**: the branch returns `Iso^Δ_K(x,y)`. -/
theorem run_blockLuksBranch (b : BlockData I) : (blockLuksBranch b).run = I.answer := by
  rw [blockLuksBranch_eq,
    run_alignRed_of_one_mem (one_mem_K_of_windowData b.toWindowData), run_blockLuksCoset b]

/-- §15, line 1, step 5, **the number of calls**: `|Ḡ|` (the test of step 5 bounds it by
`m^{1+log₂ m}`) times the number of orbits of `N`, which is at most `n`. -/
theorem calls_length_blockLuksBranch (b : BlockData I) :
    ((blockLuksBranch b).calls).length ≤
      Nat.card (onBlocks b.windowGroup b.ℬ b.system.permutes) * I.windowSize := by
  classical
  rw [blockLuksBranch_eq, calls_length_alignRed, blockLuksCoset,
    calls_length_liftWindow b.invariant I.x _ (calls_blockLuksBranch_K b)]
  refine le_trans (calls_length_cosetLine2ReductionWith b.blockAction _ _ b.enum) ?_
  have hcard : Fintype.card (blockHom b.windowGroup b.ℬ b.system.permutes).range =
      Nat.card (onBlocks b.windowGroup b.ℬ b.system.permutes) := by
    rw [← Nat.card_eq_fintype_card, onBlocks]
  have horb : (orbitList (kerSubgroup b.blockAction)).length ≤ I.windowSize := by
    refine le_trans (length_orbitList_le _) ?_
    rw [SIInstance.windowSize, Nat.card_coe_set_eq]
  rw [hcard] at *
  exact Nat.mul_le_mul le_rfl horb

/-- §15, line 1, step 5, **the progress**: every call has a window of at most half the
size, because the orbits of `N` lie inside blocks and there are at least two blocks. -/
theorem decreases_blockLuksBranch (b : BlockData I) :
    ∀ J ∈ (blockLuksBranch b).calls, 2 * J.windowSize ≤ I.windowSize := by
  classical
  intro J hJ
  rw [blockLuksBranch_eq, calls_alignRed, List.mem_map] at hJ
  obtain ⟨J₀, hJ₀, rfl⟩ := hJ
  rw [windowSize_alignInst, blockLuksCoset] at *
  obtain ⟨J', hJ', hsize⟩ :=
    calls_liftWindow_windowSize b.invariant I.x _ (calls_blockLuksBranch_K b) J₀ hJ₀
  have hwin : J'.Δ ∈ orbitList (kerSubgroup b.blockAction) :=
    calls_cosetLine2ReductionWith_window b.blockAction _ _ b.enum J' hJ'
  obtain ⟨u, hu⟩ := mem_orbitList hwin
  obtain ⟨B₁, hB₁, B₂, hB₂, hne⟩ := b.two_blocks
  have hbound := two_mul_ncard_orbit_le b.transitive
    b.system.isInvariantPartitionOn hB₁ hB₂ hne u
  rw [hsize, SIInstance.windowSize, hu, b.kerSubgroup_blockAction, ← b.card_window]
  exact hbound

/-! ### Step 6: Luks descent to the preimage of the Johnson normal subgroup

> 6. else (: `Ḡ` a Cameron group of order `≥ m^{1+log₂ m}` :) reduce `Ḡ` to a Johnson group
>    via Luks descent (: Theorem 11.2.1, multiplicative cost `≤ m` :)
> 7. (: `Ḡ` a Johnson group :) return `Ω, G, ℬ, Ḡ`, `x, y`

Theorem 11.2.1, applied to the primitive group `Ḡ = G^ℬ`, gives a normal subgroup `N̄ ⊴ Ḡ`
of index at most `m` together with a system `𝒞` of imprimitivity of `N̄` on `ℬ` on which
`N̄` acts as the Johnson group `A_k^{(t)}`.  Step 6 replaces `G` by `G₁ = ψ⁻¹(N̄)`, of the
same index, and Prop. 11.1.6 reduces `Iso_G(x,y)` to `|G : G₁|` instances with respect to
`G₁` **on the same window**.

The branch splits on the transitivity of `G₁`, which is step 3 of the procedure applied to
the new group (see the corrected paper. 11.3, steps 6–7):

* `G₁` **transitive**: the output of step 7.  Every call is with respect to `G₁` on the
  whole window, and it is a Johnson case: the unions `⋃ C`, `C ∈ 𝒞`, are a system of
  imprimitivity of `G₁` on which `G₁` acts as the same Johnson group
  (`Babai.isJohnsonCase_preimSubgroup`).  The window does not shrink, and the progress is
  that the Johnson parameter drops from `2n` to `k ≤ n` — the paper's recurrence (ii) of
  Sec. 11.4, `T_trans(x) ≤ m(T_Jh(x) + p(x))`.
* `G₁` **intransitive**: the procedure goes back to step 3 and applies the Chain Rule to
  the orbits of `G₁`.  Since `N̄ ⊴ Ḡ` we have `G₁ ⊴ G`, and `G` is transitive, so all the
  orbits of `G₁` have the same length `n/r` with `r ≥ 2` (Fact 11.1.8): every call has a
  window of at most `n/2`.
-/

/-- §11.3, step 6: what Theorem 11.2.1 supplies at an instance that has reached step 6 —
the minimal block system of step 4, a normal subgroup `N̄` of `Ḡ = G^ℬ`, and a system `𝒞`
of imprimitivity of `N̄` on `ℬ` on which `N̄` acts as `A_k^{(t)}`.

The field `window_large` is the exit of step 2 (*"if `|G| < C₀` for some absolute constant
`C₀` then compute `Iso_G(x,y)` by brute force, exit"*): an instance that reaches step 6 has
a window above any fixed absolute size.  It is recorded here for the same reason as
`Babai.JohnsonCaseData.window_large`, which it supplies. -/
structure DescentData (I : SIInstance Ω A) where
  /-- Step 4: the minimal block system `ℬ` and the transitive group `G = K^Δ`. -/
  blocks : BlockData I
  /-- Theorem 11.2.1: the normal subgroup `N̄` of `Ḡ = G^ℬ`. -/
  N : Subgroup (Equiv.Perm blocks.ℬ)
  /-- Theorem 11.2.1: `N̄ ⊴ Ḡ`. -/
  N_normal : IsNormalIn N (onBlocks blocks.windowGroup blocks.ℬ blocks.system.permutes)
  /-- Theorem 11.2.1: the system of imprimitivity of `N̄` on `ℬ`. -/
  𝒞 : Set (Set blocks.ℬ)
  /-- It is a system of imprimitivity of `N̄`. -/
  𝒞_system : IsSystemOfImprimitivity N Set.univ 𝒞
  /-- The Johnson parameter `k` of Theorem 11.2.1. -/
  k : ℕ
  /-- The parameter `t` of Theorem 11.2.1. -/
  t : ℕ
  /-- Theorem 11.2.1: `N̄` acts on `𝒞` as the Johnson group `A_k^{(t)}`. -/
  acts : ActsAsJohnsonA N 𝒞 𝒞_system.permutes k t
  /-- §2.2.1: the parameters of a Johnson group satisfy `1 ≤ t`. -/
  t_pos : 1 ≤ t
  /-- §2.2.1: the parameters of a Johnson group satisfy `2t < k`. -/
  k_gt : 2 * t < k
  /-- Step 2: the window is above the absolute constant of the brute-force exit. -/
  window_large : 64 ≤ I.windowSize

  /-- The coset cover on the ambient domain, used in the transitive case. -/
  ambientReps : CosetRepEnum
    (windowPreimSubgroup blocks.K I.Δ blocks.invariant
      (preimSubgroup (blockHom blocks.windowGroup blocks.ℬ blocks.system.permutes) N))
    blocks.K := .default (windowPreimSubgroup_le _ _)
  /-- The coset cover on the window, used before the orbit chain. -/
  windowReps : CosetRepEnum
    (preimSubgroup (blockHom blocks.windowGroup blocks.ℬ blocks.system.permutes) N)
    blocks.windowGroup := .default (preimSubgroup_le _ _)
  /-- The orbit order after descent. -/
  orbits : OrbitEnum
    (preimSubgroup (blockHom blocks.windowGroup blocks.ℬ blocks.system.permutes) N) := .default _

  /-- The inferred giant action, with the actual labels of the union blocks.
  The default retains the original existential choice. -/
  representation : JohnsonActionData
    (isSystemOfImprimitivity_descentBlocks blocks.system N_normal.le 𝒞_system).permutes k t :=
    .default t_pos k_gt
      (actsAsJohnsonA_descentBlocks blocks.system N_normal.le 𝒞_system acts)

namespace DescentData

variable (d : DescentData I)

/-- `G₁ = ψ⁻¹(N̄) ≤ G = K^Δ`, the group step 6 descends to. -/
noncomputable def G₁ : Subgroup (Equiv.Perm I.Δ) :=
  preimSubgroup (blockHom d.blocks.windowGroup d.blocks.ℬ d.blocks.system.permutes) d.N

theorem G₁_le : d.G₁ ≤ d.blocks.windowGroup := preimSubgroup_le _ _

/-- `G₁ ⊴ G`, because `N̄ ⊴ Ḡ`. -/
theorem G₁_normal : IsNormalIn d.G₁ d.blocks.windowGroup :=
  isNormalIn_preimSubgroup d.blocks.system d.N_normal

/-- `K₁ ≤ K`, the subgroup of `K` above `G₁`: the group the instances of step 6 are with
respect to. -/
noncomputable def K₁ : Subgroup (Equiv.Perm Ω) :=
  windowPreimSubgroup d.blocks.K I.Δ d.blocks.invariant d.G₁

theorem K₁_le : d.K₁ ≤ d.blocks.K := windowPreimSubgroup_le _ _

theorem K₁_invariant : IsInvariant d.K₁ I.Δ := isInvariant_windowPreimSubgroup _ _

/-- The group induced on the window by `K₁` is `G₁`. -/
theorem restrictTo_K₁ : restrictTo d.K₁ I.Δ d.K₁_invariant = d.G₁ :=
  restrictTo_windowPreimSubgroup _ d.G₁_le

/-- The Luks descent costs the same upstairs and downstairs: `|K : K₁| = |G : G₁|`. -/
theorem relIndex_K₁ : d.K₁.relIndex d.blocks.K = d.G₁.relIndex d.blocks.windowGroup :=
  relIndex_windowPreimSubgroup _ _

/-! #### The case `G₁` transitive: the output of step 7 -/

/-- §11.3, step 7: **the instances produced by the descent are Johnson cases**, when `G₁`
is transitive.  The block system is `{⋃ C | C ∈ 𝒞}` and the giant representation is the
one the Johnson action carries (`Babai.johnsonGiantRep`). -/
noncomputable def johnsonCaseDataDefault (htr : IsTransitive d.G₁) (y' : Ω → A) :
    JohnsonCaseData (⟨(d.K₁ : Set (Equiv.Perm Ω)), I.Δ, I.x, y'⟩ : SIInstance Ω A) where
  K := d.K₁
  isGroup := rfl
  invariant := d.K₁_invariant
  ℬ := descentBlocks d.𝒞
  m := d.k
  t := d.t
  johnson := by
    rw [d.restrictTo_K₁]
    exact isJohnsonCase_preimSubgroup d.blocks.system d.N_normal.le d.𝒞_system
      d.t_pos d.k_gt.le d.acts htr
  two_blocks :=
    two_blocks_of_actsAsJohnsonA d.t_pos d.k_gt
      (isSystemOfImprimitivity_descentBlocks d.blocks.system d.N_normal.le d.𝒞_system)
      (actsAsJohnsonA_descentBlocks d.blocks.system d.N_normal.le d.𝒞_system d.acts)
  ϕ := (johnsonGiantRep d.t_pos d.k_gt
      (actsAsJohnsonA_descentBlocks d.blocks.system d.N_normal.le d.𝒞_system d.acts)).comp
    (Subgroup.inclusion (le_of_eq d.restrictTo_K₁))
  giant := by
    intro α hα
    obtain ⟨g, hg⟩ := isGiantRep_johnsonGiantRep d.t_pos d.k_gt
      (actsAsJohnsonA_descentBlocks d.blocks.system d.N_normal.le d.𝒞_system d.acts) hα
    refine ⟨⟨(g : Equiv.Perm I.Δ), by rw [d.restrictTo_K₁]; exact g.2⟩, ?_⟩
    rw [MonoidHom.comp_apply]
    convert hg using 2
  param_le := by
    have h1 := johnson_param_le (β := I.Δ) d.t_pos d.k_gt
      (isSystemOfImprimitivity_descentBlocks d.blocks.system d.N_normal.le d.𝒞_system)
      (actsAsJohnsonA_descentBlocks d.blocks.system d.N_normal.le d.𝒞_system d.acts)
    have h2 : Fintype.card I.Δ = I.windowSize := d.blocks.card_window
    show d.k ≤ I.Δ.ncard
    have h3 : I.windowSize = I.Δ.ncard := rfl
    omega
  window_large := d.window_large

/-- The live constructor uses the representation retained by the descent record. -/
noncomputable def johnsonCaseData (htr : IsTransitive d.G₁) (y' : Ω → A) :
    JohnsonCaseData (⟨(d.K₁ : Set (Equiv.Perm Ω)), I.Δ, I.x, y'⟩ : SIInstance Ω A) :=
  { d.johnsonCaseDataDefault htr y' with
    ϕ := d.representation.φ.comp (Subgroup.inclusion (le_of_eq d.restrictTo_K₁))
    giant := by
      intro α hα
      obtain ⟨g, hg⟩ := d.representation.giant hα
      exact ⟨⟨g, d.restrictTo_K₁.symm ▸ g.property⟩, hg⟩ }

/-- With the default labels the complete Johnson record is the original one. -/
theorem johnsonCaseData_default (htr : IsTransitive d.G₁) (y' : Ω → A)
    (hr : d.representation = JohnsonActionData.default d.t_pos d.k_gt
      (actsAsJohnsonA_descentBlocks d.blocks.system d.N_normal.le d.𝒞_system d.acts)) :
    d.johnsonCaseData htr y' = d.johnsonCaseDataDefault htr y' := by
  have hf := congrArg JohnsonActionData.φ hr
  unfold johnsonCaseData johnsonCaseDataDefault
  dsimp only [JohnsonActionData.default] at hf
  dsimp only
  congr 1
  exact congrArg (fun φ => φ.comp (Subgroup.inclusion (le_of_eq d.restrictTo_K₁))) hf

/-! #### The branch -/

open scoped Classical in
/-- §15, line 1, **step 6** as a branch of the round: the Luks descent from `K` to `K₁`,
on the window `Δ` of the instance, followed — when `G₁` is intransitive — by the Chain Rule
over the orbits of `G₁` (step 3 applied to the new group). -/
noncomputable def cosetBranch : SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  if IsTransitive d.G₁ then
    cosetDescent d.K₁ I.Δ I.x I.y d.ambientReps.reps
  else
    liftWindow d.blocks.K I.Δ d.blocks.invariant I.x
      ((cosetDescent d.G₁ Set.univ (restrictStr I.Δ I.x) (restrictStr I.Δ I.y)
          d.windowReps.reps).expand d.orbits.chain)

/-- §15, line 1, **step 6** as a branch of the round: the alignment (Remark 11.1.4) of the
coset form `Babai.DescentData.cosetBranch`. -/
noncomputable def branch : SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  SIReduction.alignRed I d.cosetBranch

theorem branch_eq : d.branch = SIReduction.alignRed I d.cosetBranch := rfl

/-- The reduction that the intransitive case runs on the window: the descent to `G₁` in
coset form, expanded by the coset Chain Rule over the orbits of `G₁`. -/
noncomputable def innerChain : SIReduction I.Δ A (Set (Equiv.Perm I.Δ)) :=
  (cosetDescent d.G₁ Set.univ (restrictStr I.Δ I.x) (restrictStr I.Δ I.y)
    d.windowReps.reps).expand d.orbits.chain

theorem calls_descent_wrt :
    ∀ J ∈ (cosetDescent d.G₁ Set.univ (restrictStr I.Δ I.x) (restrictStr I.Δ I.y)
        d.windowReps.reps).calls,
      (∃ σ ∈ d.windowReps.reps,
        J.K = σ • (d.G₁ : Set (Equiv.Perm I.Δ))) ∧ J.Δ = Set.univ :=
  calls_cosetDescent_spec _ _ _ _ _

theorem run_innerChain :
    (d.innerChain).run =
      strIso ((d.blocks.windowGroup : Subgroup (Equiv.Perm I.Δ)) : Set (Equiv.Perm I.Δ))
        (restrictStr I.Δ I.x) (restrictStr I.Δ I.y) := by
  rw [innerChain, SIReduction.run_expand_of_calls
    (P := fun J => (∃ σ ∈ d.windowReps.reps,
        J.K = σ • (d.G₁ : Set (Equiv.Perm I.Δ))) ∧ J.Δ = Set.univ)
    (fun J hJ => d.orbits.run_chain_eq _ hJ.2) _ d.calls_descent_wrt]
  have h := d.windowReps.run_descent (Set.univ : Set I.Δ)
    (restrictStr I.Δ I.x) (restrictStr I.Δ I.y)
  change (cosetDescent _ _ _ _ _).run = _
  simpa only [wIso_univ] using h

theorem calls_innerChain_K :
    ∀ J ∈ (d.innerChain).calls,
      J.K ⊆ ((restrictTo d.blocks.K I.Δ d.blocks.invariant : Subgroup (Equiv.Perm I.Δ)) :
        Set (Equiv.Perm I.Δ)) := by
  rw [innerChain]
  refine SIReduction.mem_calls_expand_of_calls
    (P := fun J => (∃ σ ∈ d.windowReps.reps,
        J.K = σ • (d.G₁ : Set (Equiv.Perm I.Δ))) ∧ J.Δ = Set.univ)
    (fun J hJ => d.orbits.run_chain_eq _ hJ.2)
    (fun J hJ J' hJ' => ?_) _ d.calls_descent_wrt
  obtain ⟨⟨σ, hσ, hK⟩, -⟩ := hJ
  refine subset_trans (d.orbits.calls_chain_K J J' hJ') ?_
  rw [hK]
  rintro _ ⟨ν, hν, rfl⟩
  exact mul_mem (d.windowReps.mem hσ) (d.G₁_le hν)

theorem calls_innerChain_window :
    ∀ J ∈ (d.innerChain).calls, J.Δ ∈ orbitList d.G₁ := by
  rw [innerChain]
  exact SIReduction.mem_calls_expand_of_calls
    (P := fun J => (∃ σ ∈ d.windowReps.reps,
        J.K = σ • (d.G₁ : Set (Equiv.Perm I.Δ))) ∧ J.Δ = Set.univ)
    (fun J hJ => d.orbits.run_chain_eq _ hJ.2)
    (fun J _ => d.orbits.calls_chain_window J) _ d.calls_descent_wrt

/-- Every call of the intransitive case is a coset instance with respect to the group
induced on the window. -/
theorem calls_innerChain_isCosetInstance :
    ∀ J ∈ (d.innerChain).calls,
      IsCosetInstance (restrictTo d.blocks.K I.Δ d.blocks.invariant) J := by
  rw [innerChain]
  refine SIReduction.mem_calls_expand_of_calls
    (P := fun J => (∃ σ ∈ d.windowReps.reps,
        J.K = σ • (d.G₁ : Set (Equiv.Perm I.Δ))) ∧ J.Δ = Set.univ)
    (fun J hJ => d.orbits.run_chain_eq _ hJ.2)
    (fun J hJ J' hJ' => ?_) _ d.calls_descent_wrt
  obtain ⟨⟨σ, hσ, hK⟩, -⟩ := hJ
  exact d.orbits.calls_chain_coset d.G₁_le J
    ⟨d.G₁, σ, le_rfl, d.windowReps.mem hσ, hK⟩ J' hJ'

theorem calls_length_innerChain :
    (d.innerChain).calls.length ≤
      d.G₁.relIndex d.blocks.windowGroup * (orbitList d.G₁).length := by
  have h := SIReduction.calls_expand_length_le_of_calls
    (P := fun J => (∃ σ ∈ d.windowReps.reps,
        J.K = σ • (d.G₁ : Set (Equiv.Perm I.Δ))) ∧ J.Δ = Set.univ)
    (fun J hJ => d.orbits.run_chain_eq _ hJ.2)
    (c := (orbitList d.G₁).length)
    (fun J _ => d.orbits.calls_length_chain J) _ d.calls_descent_wrt
  rw [innerChain]
  rw [calls_length_cosetDescent] at h
  exact h.trans (Nat.mul_le_mul_right _ d.windowReps.length)

/-- §15, line 1, step 6 **is correct**: the branch returns `Iso^Δ_K(x,y)`.  This is
Eq. (62), in the transitive case directly and in the intransitive case followed by the
Chain Rule. -/
theorem run_cosetBranch : (d.cosetBranch).run = I.answer := by
  classical
  rw [cosetBranch]
  by_cases htr : IsTransitive d.G₁
  · rw [if_pos htr]
    have hr : (cosetDescent d.K₁ I.Δ I.x I.y d.ambientReps.reps).run =
        wIso I.Δ (d.blocks.K : Set (Equiv.Perm Ω)) I.x I.y :=
      d.ambientReps.run_descent I.Δ I.x I.y
    rw [hr, SIInstance.answer, d.blocks.isGroup]
  · rw [if_neg htr]
    have := run_liftWindow d.blocks.invariant I.x I.y d.innerChain d.calls_innerChain_K
      d.run_innerChain
    rw [show liftWindow d.blocks.K I.Δ d.blocks.invariant I.x
        ((cosetDescent d.G₁ Set.univ (restrictStr I.Δ I.x) (restrictStr I.Δ I.y)
          d.windowReps.reps).expand d.orbits.chain) =
        liftWindow d.blocks.K I.Δ d.blocks.invariant I.x d.innerChain from rfl, this,
      SIInstance.answer, d.blocks.isGroup]

/-- §15, line 1, step 6 **is correct**: the branch returns `Iso^Δ_K(x,y)`. -/
theorem run_branch : (d.branch).run = I.answer := by
  rw [branch_eq, run_alignRed_of_one_mem (one_mem_K_of_windowData d.blocks.toWindowData),
    run_cosetBranch]

/-- §15, line 1, step 6, **the number of calls**: the index `|G : G₁|`, which
Theorem 11.2.1 bounds by `m ≤ n`, times the number of orbits of `G₁`, which is at most `n`
(and is `1` in the transitive case). -/
theorem calls_length_branch :
    (d.branch).calls.length ≤
      d.K₁.relIndex d.blocks.K * I.windowSize + d.K₁.relIndex d.blocks.K := by
  classical
  rw [branch_eq, calls_length_alignRed, cosetBranch]
  by_cases htr : IsTransitive d.G₁
  · rw [if_pos htr, calls_length_cosetDescent]
    have : d.ambientReps.reps.length ≤ d.K₁.relIndex d.blocks.K := d.ambientReps.length
    omega
  · rw [if_neg htr]
    have hlift : (liftWindow d.blocks.K I.Δ d.blocks.invariant I.x d.innerChain).calls.length
        = d.innerChain.calls.length :=
      calls_length_liftWindow d.blocks.invariant I.x _ d.calls_innerChain_K
    have horb : (orbitList d.G₁).length ≤ I.windowSize := by
      refine le_trans (length_orbitList_le _) ?_
      rw [SIInstance.windowSize, Nat.card_coe_set_eq]
    have h1 := d.calls_length_innerChain
    have h2 : d.G₁.relIndex d.blocks.windowGroup * (orbitList d.G₁).length ≤
        d.K₁.relIndex d.blocks.K * I.windowSize := by
      rw [d.relIndex_K₁]
      exact Nat.mul_le_mul_left _ horb
    show (liftWindow d.blocks.K I.Δ d.blocks.invariant I.x d.innerChain).calls.length ≤ _
    omega

open scoped Classical in
/-- §15, line 1, step 7: **the hint the descent attaches to each of its calls**.

In the transitive case every call is the instance with respect to `K₁` on the unchanged
window, with the second string shifted (Eq. (62)); `Babai.DescentData.johnsonCaseData` is
the Johnson case data of such a call, and it is what line 7 of Procedure Reduce-to-Johnson
hands on.  In the intransitive case the calls are not Johnson cases and get no hint. -/
noncomputable def hint (J : SIInstance Ω A) : Option (JohnsonCaseData J) :=
  if htr : IsTransitive d.G₁ then
    if h : (⟨(d.K₁ : Set (Equiv.Perm Ω)), I.Δ, I.x, J.y⟩ : SIInstance Ω A) = J then
      some (h ▸ d.johnsonCaseData htr J.y)
    else none
  else none

/-- §15, line 1, step 6, **the calls in the transitive case**: they are the instances with
respect to `K₁` on the window of the instance, so they are Johnson cases, and the descent
really attaches the data of step 7 to them. -/
theorem hint_isSome (htr : IsTransitive d.G₁) :
    ∀ J ∈ (d.branch).calls, (d.hint J).isSome = true := by
  classical
  intro J hJ
  rw [branch_eq, calls_alignRed, List.mem_map, cosetBranch, if_pos htr,
    calls_cosetDescent] at hJ
  obtain ⟨J₀, hJ₀, rfl⟩ := hJ
  rw [List.mem_map] at hJ₀
  obtain ⟨σ, -, rfl⟩ := hJ₀
  have hEq : (⟨(d.K₁ : Set (Equiv.Perm Ω)), I.Δ, I.x,
      (alignInst (⟨σ • (d.K₁ : Set (Equiv.Perm Ω)), I.Δ, I.x, I.y⟩ :
        SIInstance Ω A)).y⟩ : SIInstance Ω A)
      = alignInst (⟨σ • (d.K₁ : Set (Equiv.Perm Ω)), I.Δ, I.x, I.y⟩ : SIInstance Ω A) := by
    rw [alignInst]
    exact congrArg (fun C => (⟨C, I.Δ, I.x, _⟩ : SIInstance Ω A))
      (K_alignInst_smul_coe d.K₁ I.Δ I.x I.y σ).symm
  rw [hint, dif_pos htr, dif_pos hEq]
  rfl

/-- §15, line 1, step 6, **the window in the transitive case**: it is the window of the
instance, unchanged. -/
theorem calls_windowSize_branch (htr : IsTransitive d.G₁) :
    ∀ J ∈ (d.branch).calls, J.windowSize = I.windowSize := by
  classical
  intro J hJ
  rw [branch_eq, calls_alignRed, List.mem_map, cosetBranch, if_pos htr,
    calls_cosetDescent] at hJ
  obtain ⟨J₀, hJ₀, rfl⟩ := hJ
  rw [List.mem_map] at hJ₀
  obtain ⟨σ, -, rfl⟩ := hJ₀
  rfl

/-- §15, line 1, step 6, **the window in the intransitive case**: the orbits of `G₁` all
have the same length `n/r` with `r ≥ 2`, because `G₁ ⊴ G` and `G` is transitive
(Fact 11.1.8). -/
theorem calls_windowSize_branch_of_not (htr : ¬ IsTransitive d.G₁) :
    ∀ J ∈ (d.branch).calls, 2 * J.windowSize ≤ I.windowSize := by
  classical
  intro J hJ
  rw [branch_eq, calls_alignRed, List.mem_map, cosetBranch, if_neg htr] at hJ
  obtain ⟨J₀, hJ₀, rfl⟩ := hJ
  rw [windowSize_alignInst]
  obtain ⟨J', hJ', hsize⟩ :=
    calls_liftWindow_windowSize d.blocks.invariant I.x d.innerChain d.calls_innerChain_K
      J₀ hJ₀
  obtain ⟨u, hu⟩ := mem_orbitList (d.calls_innerChain_window J' hJ')
  obtain ⟨r, hr, hall⟩ := orbit_ncard_mul_eq_card d.blocks.transitive d.G₁_normal htr
  have h := hall u
  have hcard : Fintype.card I.Δ = I.windowSize := d.blocks.card_window
  have hw : J'.windowSize = (orbit d.G₁ u).ncard := by rw [SIInstance.windowSize, hu]
  have : 2 * (orbit d.G₁ u).ncard ≤ Fintype.card I.Δ := by
    calc 2 * (orbit d.G₁ u).ncard ≤ r * (orbit d.G₁ u).ncard :=
          Nat.mul_le_mul_right _ hr
      _ = Fintype.card I.Δ := by rw [mul_comm]; exact h
  omega

/-- §15, line 1, step 6, **the progress**.

If `G₁` is transitive the window is unchanged and the instances produced are Johnson cases,
carrying the data of step 7, so the Johnson parameter drops from `2n` to at most `n`: this
is the second form of `Babai.MakesProgress`, the paper's recurrence (ii).  If `G₁` is
intransitive every call has a window of at most `n/2`: this is the first form. -/
theorem decreases_branch :
    ∀ J ∈ (d.branch).calls,
      MakesProgress HintedInstance.win param (⟨I, none⟩ : HintedInstance Ω A)
        ⟨J, d.hint J⟩ := by
  classical
  intro J hJmem
  have hn : 1 ≤ I.windowSize := by have := d.window_large; omega
  by_cases htr : IsTransitive d.G₁
  · have hsize := d.calls_windowSize_branch htr J hJmem
    have hpJ : param (⟨J, d.hint J⟩ : HintedInstance Ω A) ≤ J.windowSize :=
      param_le_windowSize_of_isSome (d.hint_isSome htr J hJmem)
    refine Or.inr ⟨by show J.windowSize ≤ I.windowSize; omega, ?_, ?_⟩
    · show 1 ≤ 2 * I.windowSize
      omega
    · show 2 * param (⟨J, d.hint J⟩ : HintedInstance Ω A) ≤ 2 * I.windowSize
      omega
  · have h2 := d.calls_windowSize_branch_of_not htr J hJmem
    exact Or.inl ⟨hn, by show 5 * J.windowSize ≤ 4 * I.windowSize; omega⟩

end DescentData

/-- §11.3, step 6: **the absolute constant of Theorem 11.2.1**, chosen once and for all.

It is the *"`n` greater than some absolute constant"* of Theorem 11.2.1; here it is a
threshold on the number `m` of blocks, which is the size of the permutation domain the
theorem is applied to.

**One constant for all ground sets.**  The binder of the ground set is *inside*
`Babai.Theorem_11_2_1`, which is applied at the type `↥b.ℬ` of blocks, so the constant does
not change with the ground set; see the corrected paper entry on Sec. 11.3 step 6.  It
does carry the universe level of the ground set, as `Babai.c923` and the `c₁` of
`Babai.Theorem_1_1_1_math` do, and for the same reason: the cited result is stated for one
universe level.  What matters for *"absolute"* is the binder order, and the constant is
fixed before the ground set, the alphabet, the group and the strings.

The constant is the maximum of the threshold of Theorem 11.2.1 and of the threshold
`max 25 n₁` under which the machine recognizes a Cameron group (`n₁` from
Prop. 11.2.5). Both are absolute constants, and the paper's *"`n₀`"* only has to be large
enough. With one constant, the instances where step 6 applies are the same for the
mathematical round and for the machine (`Babai.cameronThreshold_le_descentThreshold`). -/
noncomputable def descentThreshold : ℕ :=
  max Theorem_11_2_1.{u}.choose (max 25 Proposition_11_2_5.{u}.choose)

/-- The threshold of Theorem 11.2.1 is below `Babai.descentThreshold`. -/
theorem theorem_11_2_1_threshold_le_descentThreshold :
    Theorem_11_2_1.{u}.choose ≤ descentThreshold.{u} := le_max_left _ _

/-- The threshold `max 25 n₁` of the Cameron recognition step, with `n₁` from Prop. 11.2.5,
is below `Babai.descentThreshold`. -/
theorem cameronThreshold_le_descentThreshold :
    max 25 Proposition_11_2_5.{u}.choose ≤ descentThreshold.{u} := le_max_right _ _

/-- §11.3, steps 1–2: **the absolute constant `C₀` of the brute-force exit**, read as a
bound on the window.

Step 2 of Procedure Reduce-to-Johnson exits when `|G| < C₀` for an absolute constant `C₀`.
A window of fewer than

> `N₀ = max{64, n₀!}`

points has `|G^Δ| ≤ N₀!`, which is such a constant, so the test of step 2 succeeds there.
The two parts of the maximum are the two places where a constant is needed: `64` is the
threshold of `Babai.JohnsonCaseData.window_large`, and `n₀!` bounds `|Ḡ|` on a block system
with fewer than `n₀` blocks, which is where Theorem 11.2.1 does not apply
(`Babai.descentThreshold`).

`N₀` is fixed **before** the instance, the group and the strings, which is what
*"absolute constant"* means. -/
noncomputable def bruteForceThreshold : ℕ := max 64 (Nat.factorial descentThreshold.{u})

theorem sixtyFour_le_bruteForceThreshold : 64 ≤ bruteForceThreshold.{u} := le_max_left _ _

/-- Section 11.3, step 2: one fixed small-group cutoff, before all instances.
It includes every small-window exit already represented by `Line1Case.leaf`. -/
noncomputable def bruteForceOrderThreshold : ℕ := bruteForceThreshold.{u}.factorial + 1

/-- §11.3, steps 4–6: **Theorem 11.2.1 supplies the data of step 6**.

At an instance that has passed steps 1–3 (so `G = K^Δ` is transitive) with the minimal
block system `ℬ` of step 4 — on which `Ḡ` is primitive, `Babai.isPrimitive_onBlocks` — and
whose `Ḡ` fails the test of step 5, `|Ḡ| ≥ m^{1+log₂ m}`, Theorem 11.2.1 gives the
`Babai.DescentData` that step 6 runs on, and its multiplicative cost is
`|K : K₁| = |Ḡ : N̄| ≤ m`, the paper's *"multiplicative cost `≤ m`"*.

The threshold is named (`Babai.descentThreshold`) rather than hidden in an existential, so
that the brute-force exit of steps 1–2 can be stated against it. -/
theorem descentData_spec (Ω : Type u) [Fintype Ω] [DecidableEq Ω] (A : Type v)
    (I : SIInstance Ω A) (b : BlockData I)
    (hwin : 64 ≤ I.windowSize) (hn : descentThreshold.{u} ≤ Nat.card b.ℬ)
    (hprim : IsPrimitive (onBlocks b.windowGroup b.ℬ b.system.permutes))
    (hbig : ((Nat.card b.ℬ : ℝ) ^ (1 + Real.logb 2 (Nat.card b.ℬ)) ≤
      (Nat.card (onBlocks b.windowGroup b.ℬ b.system.permutes) : ℝ))) :
    ∃ d : DescentData I, d.blocks = b ∧ d.K₁.relIndex d.blocks.K ≤ Nat.card b.ℬ := by
  classical
  have h := Theorem_11_2_1.{u}.choose_spec
  haveI : Finite b.ℬ := Set.Finite.to_subtype (Set.toFinite _)
  letI : Fintype b.ℬ := Fintype.ofFinite _
  have hcard : Fintype.card b.ℬ = Nat.card b.ℬ := Nat.card_eq_fintype_card.symm
  obtain ⟨N, hNnorm, hidx, 𝒞, hsys, k, t, ht, hk, hacts, -⟩ :=
    h b.ℬ (onBlocks b.windowGroup b.ℬ b.system.permutes)
      (by rw [hcard]; exact le_trans theorem_11_2_1_threshold_le_descentThreshold hn) hprim
      (by rw [hcard]; exact hbig)
  refine ⟨{ blocks := b, N := N, N_normal := hNnorm, 𝒞 := 𝒞, 𝒞_system := hsys,
            k := k, t := t, acts := hacts, t_pos := ht, k_gt := hk,
            window_large := hwin }, rfl, ?_⟩
  show (windowPreimSubgroup b.K I.Δ b.invariant
      (preimSubgroup (blockHom b.windowGroup b.ℬ b.system.permutes) N)).relIndex b.K ≤
      Nat.card b.ℬ
  rw [relIndex_windowPreimSubgroup]
  calc (preimSubgroup (blockHom b.windowGroup b.ℬ b.system.permutes) N).relIndex
        (restrictTo b.K I.Δ b.invariant)
      = N.relIndex (blockHom b.windowGroup b.ℬ b.system.permutes).range :=
        relIndex_preimSubgroup _ _
    _ ≤ Nat.card b.ℬ := by rw [← hcard]; exact hidx

/-- §11.3, steps 4–6: `Babai.descentData_spec` with the threshold read back as an
existential. -/
theorem exists_descentData :
    ∃ n₀ : ℕ, ∀ (Ω : Type u) [Fintype Ω] [DecidableEq Ω] (A : Type v)
      (I : SIInstance Ω A) (b : BlockData I),
      64 ≤ I.windowSize → n₀ ≤ Nat.card b.ℬ →
      IsPrimitive (onBlocks b.windowGroup b.ℬ b.system.permutes) →
      ((Nat.card b.ℬ : ℝ) ^ (1 + Real.logb 2 (Nat.card b.ℬ)) ≤
        (Nat.card (onBlocks b.windowGroup b.ℬ b.system.permutes) : ℝ)) →
      ∃ d : DescentData I, d.blocks = b ∧ d.K₁.relIndex d.blocks.K ≤ Nat.card b.ℬ :=
  ⟨descentThreshold.{u}, fun Ω _ _ A I b h1 h2 h3 h4 => descentData_spec Ω A I b h1 h2 h3 h4⟩

/-! ### The round of line 1

The leaf and recursive branches, assembled into the round of Sec. 15, line 1.  Which branch is taken is
the case distinction of Procedure Reduce-to-Johnson itself: steps 1–2 exit, step 3 tests
transitivity, step 5 tests `|Ḡ| < m^{1+log₂ m}` and step 6 is the remaining case.  The
parameter `q` is the multiplicative cost the round is allowed: at step 5 it bounds `|Ḡ|`
(the test of that step), at step 6 it bounds the index `|Ḡ : N̄| ≤ m` of Theorem 11.2.1. -/

/-- §11.3: which branch of Procedure Reduce-to-Johnson applies to the instance, with the
data that branch needs.  `q` is the multiplicative cost allowed. -/
inductive Line1Case (I : SIInstance Ω A) (q : ℕ) where
  /-- Steps 1 and 2: the window is below the absolute constant `N₀` of
  `Babai.bruteForceThreshold`, so `|G^Δ| ≤ N₀!` is below an absolute constant, the test of
  step 2 succeeds, and the answer is computed by brute force. -/
  | leaf (hsmall : I.windowSize < bruteForceThreshold.{u})
  /-- Step 1: the current group fixes the source on the window. The machine compares
  the source and target and returns the candidate group or the empty set. -/
  | fixedString (d : WindowData I)
      (hfix : d.K ≤ wAutSubgroup d.K I.Δ d.invariant I.x)
  /-- Step 2: the induced group is small, even when the window is large. The
  cutoff is fixed before the instance, rather than chosen from its group order. -/
  | smallGroup (d : WindowData I)
      (hsmall : Nat.card d.windowGroup < bruteForceOrderThreshold.{u})
  /-- Not a branch of Procedure Reduce-to-Johnson: the instance is not with respect to a
  group, so it is not one the Master Algorithm ever produces.  It is answered by brute
  force as well; the escape is kept separate so that it is visible. -/
  | offGroup (hg : ¬ IsGroupInstance I)
  /-- Step 3: `G` is intransitive, so the Chain Rule applies. -/
  | chain (d : WindowData I) (u : I.Δ) (hG : ¬ IsTransitive d.windowGroup)
  /-- Step 5: `G` is transitive with a minimal block system on which it acts as a small
  primitive group `Ḡ`, `|Ḡ| ≤ q`. -/
  | block (b : BlockData I)
      (hcost : Nat.card (onBlocks b.windowGroup b.ℬ b.system.permutes) ≤ q)
  /-- Step 6: `Ḡ` is large, and Theorem 11.2.1 supplies the normal subgroup `N̄ ⊴ Ḡ` of
  index at most `q` with its Johnson action (`Babai.DescentData`). -/
  | descent (d : DescentData I) (hcost : d.K₁.relIndex d.blocks.K ≤ q)

/-- §15, **line 1**: one round of Procedure Reduce-to-Johnson. -/
noncomputable def Line1Case.branch {q : ℕ} :
    Line1Case I q → SIReduction Ω A (Set (Equiv.Perm Ω))
  | .leaf _ => bruteForceBranch I
  | .fixedString _ _ => bruteForceBranch I
  | .smallGroup _ _ => bruteForceBranch I
  | .offGroup _ => bruteForceBranch I
  | .chain d u _ => chainRuleBranch d u
  | .block b _ => blockLuksBranch b
  | .descent d _ => d.branch

/-- §15, **line 1 in coset form**: one round of Procedure Reduce-to-Johnson written in the
middle form of Eqs. (62)–(63), before the alignment step of Remark 11.1.4.  Each branch is
the coset form of the branch of `Babai.Line1Case.branch`, and every leaf returns the
answer in the shifted frame (`Babai.cosetLeaf`). -/
noncomputable def Line1Case.cosetBranch {q : ℕ} :
    Line1Case I q → SIReduction Ω A (Set (Equiv.Perm Ω))
  | .leaf _ => cosetLeaf I I.answer
  | .fixedString _ _ => cosetLeaf I I.answer
  | .smallGroup _ _ => cosetLeaf I I.answer
  | .offGroup _ => cosetLeaf I I.answer
  | .chain d u _ => chainRuleCoset d u
  | .block b _ => blockLuksCoset b
  | .descent d _ => d.cosetBranch

/-- §15, line 1: **the round is the alignment of its coset form** (Remark 11.1.4). -/
theorem Line1Case.branch_eq_alignRed {q : ℕ} (c : Line1Case I q) :
    c.branch = SIReduction.alignRed I c.cosetBranch := by
  cases c with
  | leaf h => rw [branch, cosetBranch, alignRed_cosetLeaf]; rfl
  | fixedString d h => rw [branch, cosetBranch, alignRed_cosetLeaf]; rfl
  | smallGroup d h => rw [branch, cosetBranch, alignRed_cosetLeaf]; rfl
  | offGroup h => rw [branch, cosetBranch, alignRed_cosetLeaf]; rfl
  | chain d u h => rfl
  | block b h => rfl
  | descent d h => rfl

/-- §15, line 1 **is correct**: whichever branch of Procedure Reduce-to-Johnson is taken,
the round returns `Iso^Δ_K(x,y)`. -/
theorem Line1Case.run_branch {q : ℕ} (c : Line1Case I q) : c.branch.run = I.answer := by
  cases c with
  | leaf _ => rfl
  | fixedString _ _ => rfl
  | smallGroup _ _ => rfl
  | offGroup _ => rfl
  | chain d u _ => exact run_chainRuleBranch d u
  | block b _ => exact run_blockLuksBranch b
  | descent d _ => exact d.run_branch

/-- §15, line 1, **the number of calls**: at most `q·n + q + n + 2`.  The three nonempty
branches contribute the number of orbits of `G`, which is at most `n` (the Chain Rule of
step 3), `|Ḡ|` times the number of orbits of `N` (step 5) and the index `|Ḡ : N̄|`
(step 6). -/
theorem Line1Case.calls_length_branch {q : ℕ} (c : Line1Case I q) :
    (c.branch.calls).length ≤ q * I.windowSize + q + I.windowSize + 2 := by
  cases c with
  | leaf _ => simp [Line1Case.branch, bruteForceBranch]
  | fixedString _ _ => simp [Line1Case.branch, bruteForceBranch]
  | smallGroup _ _ => simp [Line1Case.branch, bruteForceBranch]
  | offGroup _ => simp [Line1Case.branch, bruteForceBranch]
  | chain d u _ =>
    have := calls_length_chainRuleBranch d u
    show (chainRuleBranch d u).calls.length ≤ _
    omega
  | block b hcost =>
    show (blockLuksBranch b).calls.length ≤ _
    have h1 := calls_length_blockLuksBranch b
    have h2 : Nat.card (onBlocks b.windowGroup b.ℬ b.system.permutes) * I.windowSize
        ≤ q * I.windowSize := Nat.mul_le_mul_right _ hcost
    omega
  | descent d hcost =>
    show (d.branch).calls.length ≤ _
    have h1 := d.calls_length_branch
    have h2 : d.K₁.relIndex d.blocks.K * I.windowSize ≤ q * I.windowSize :=
      Nat.mul_le_mul_right _ hcost
    omega

/-- §15, line 1, **the hint each branch attaches to its calls**.  Only step 6 has one to
attach: the Johnson case data of step 7 (`Babai.DescentData.hint`).  The calls of steps 3
and 5 shrink the window and start again at line 1, so they carry none. -/
noncomputable def Line1Case.hint {q : ℕ} :
    Line1Case I q → ∀ J : SIInstance Ω A, Option (JohnsonCaseData J)
  | .leaf _, _ => none
  | .fixedString _ _, _ => none
  | .smallGroup _ _, _ => none
  | .offGroup _, _ => none
  | .chain _ _ _, _ => none
  | .block _ _, _ => none
  | .descent d _, J => d.hint J

/-- §15, line 1, **the progress**.  Steps 1–2 and 5 shrink the window (to nothing and to
`n/2` respectively), step 6 keeps the window and halves the Johnson parameter, and step 3
is a Chain Rule round.  These are the two forms of `Babai.MasterStep.decreases`. -/
theorem Line1Case.decreases_branch {q : ℕ} (c : Line1Case I q) :
    (∀ J ∈ c.branch.calls,
        MakesProgress HintedInstance.win param (⟨I, none⟩ : HintedInstance Ω A)
          ⟨J, c.hint J⟩) ∨
      IsChainRuleRound HintedInstance.win param (⟨I, none⟩ : HintedInstance Ω A)
        (c.branch.calls.map (fun J => (⟨J, c.hint J⟩ : HintedInstance Ω A))) := by
  cases c with
  | leaf _ =>
    refine Or.inl ?_
    intro J hJmem
    exact absurd hJmem (by simp [Line1Case.branch, bruteForceBranch])
  | fixedString _ _ =>
    refine Or.inl ?_
    intro J hJmem
    exact absurd hJmem (by simp [Line1Case.branch, bruteForceBranch])
  | smallGroup _ _ =>
    refine Or.inl ?_
    intro J hJmem
    exact absurd hJmem (by simp [Line1Case.branch, bruteForceBranch])
  | offGroup _ =>
    refine Or.inl ?_
    intro J hJmem
    exact absurd hJmem (by simp [Line1Case.branch, bruteForceBranch])
  | chain d u hG =>
    refine Or.inr ?_
    exact decreases_chainRuleBranch d u hG
  | block b hcost =>
    refine Or.inl fun J hJmem => ?_
    have hn : 1 ≤ I.windowSize := by
      obtain ⟨w⟩ := b.transitive.nonempty
      have : 0 < Fintype.card I.Δ := Fintype.card_pos_iff.2 ⟨w⟩
      have := b.card_window
      omega
    have h2 := decreases_blockLuksBranch b J hJmem
    exact Or.inl ⟨hn, by show 5 * J.windowSize ≤ 4 * I.windowSize; omega⟩
  | descent d _ => exact Or.inl d.decreases_branch

/-- §15, **line 1** as a function of the instance: one round of Procedure
Reduce-to-Johnson, given a choice of branch for every instance. -/
noncomputable def line1Fun {q : ℕ} (c : ∀ I : SIInstance Ω A, Line1Case I q)
    (I : SIInstance Ω A) : SIReduction Ω A (Set (Equiv.Perm Ω)) := (c I).branch

theorem run_line1Fun {q : ℕ} (c : ∀ I : SIInstance Ω A, Line1Case I q)
    (I : SIInstance Ω A) : (line1Fun c I).run = I.answer := (c I).run_branch

theorem calls_length_line1Fun {q : ℕ} (c : ∀ I : SIInstance Ω A, Line1Case I q)
    (I : SIInstance Ω A) :
    ((line1Fun c I).calls).length ≤ q * I.windowSize + q + I.windowSize + 2 :=
  (c I).calls_length_branch

/-- The three facts in the shape a caller of `Babai.Line1Case` asks for, given a round cost
that covers `q·n + q + n + 2`. -/
theorem calls_length_line1Fun_le {q : ℕ} (c : ∀ I : SIInstance Ω A, Line1Case I q)
    (roundCost : ℕ → ℕ) (hcost : ∀ n, q * n + q + n + 2 ≤ roundCost n) (I : SIInstance Ω A) :
    ((line1Fun c I).calls).length ≤ roundCost I.windowSize :=
  le_trans (calls_length_line1Fun c I) (hcost I.windowSize)

/-! ### Every branch of line 1 produces group instances

`Babai.IsGroupInstance` (`Workspace/Master/Defs.lean`) is the invariant the Master Algorithm
carries: the candidate set is a group and the window is invariant under it.  Each of the
four branches of Procedure Reduce-to-Johnson preserves it. -/

/-- Every call of the coset form of step 3 is a coset instance with respect to `K`: the
chain starts from the group induced on the window and each answer is a coset again
(`Babai.isCosetInstance_calls_cosetChain`), and the lift of a coset instance is a coset
instance (`Babai.isCosetInstance_windowInstance`). -/
theorem calls_chainRuleCoset_isCosetInstance (d : WindowData I) (u : I.Δ) :
    ∀ J ∈ (chainRuleCoset d u).calls, IsCosetInstance d.K J := by
  refine calls_liftWindow_isCosetInstance d.invariant I.x _ (calls_chainRuleBranch_K d u) ?_
  refine isCosetInstance_calls_cosetChain (G := restrictTo d.K I.Δ d.invariant)
    (N := restrictTo d.K I.Δ d.invariant) le_rfl _ _ _ _
    d.orbits.invariant
    ⟨restrictTo d.K I.Δ d.invariant, 1, le_rfl, one_mem _, by rw [one_smul]; rfl⟩

theorem calls_chainRuleBranch_isGroupInstance (d : WindowData I) (u : I.Δ) :
    ∀ J ∈ (chainRuleBranch d u).calls, IsGroupInstance J := by
  intro J hJ
  rw [chainRuleBranch_eq, calls_alignRed, List.mem_map] at hJ
  obtain ⟨J₀, hJ₀, rfl⟩ := hJ
  exact isGroupInstance_alignInst (calls_chainRuleCoset_isCosetInstance d u J₀ hJ₀)

theorem calls_blockLuksCoset_isCosetInstance (b : BlockData I) :
    ∀ J ∈ (blockLuksCoset b).calls, IsCosetInstance b.K J :=
  calls_liftWindow_isCosetInstance b.invariant I.x _ (calls_blockLuksBranch_K b)
    (isCosetInstance_calls_cosetLine2ReductionWith b.blockAction _ _ b.enum)

theorem calls_blockLuksBranch_isGroupInstance (b : BlockData I) :
    ∀ J ∈ (blockLuksBranch b).calls, IsGroupInstance J := by
  intro J hJ
  rw [blockLuksBranch_eq, calls_alignRed, List.mem_map] at hJ
  obtain ⟨J₀, hJ₀, rfl⟩ := hJ
  exact isGroupInstance_alignInst (calls_blockLuksCoset_isCosetInstance b J₀ hJ₀)

namespace DescentData

variable (d : DescentData I)

/-- §15, line 1, step 6: **every call of the coset form is a coset instance** with respect
to `K`.  In the transitive case the calls are the cosets `σK₁` on the window of the
instance; in the intransitive case they are the lifted calls of the coset Chain Rule over
the orbits of `G₁`. -/
theorem calls_cosetBranch_isCosetInstance :
    ∀ J ∈ (d.cosetBranch).calls, IsCosetInstance d.blocks.K J := by
  classical
  rw [cosetBranch]
  by_cases htr : IsTransitive d.G₁
  · rw [if_pos htr]
    intro J hJ
    rw [calls_cosetDescent, List.mem_map] at hJ
    obtain ⟨σ, hσ, rfl⟩ := hJ
    exact ⟨d.K₁, σ, d.K₁_le, d.ambientReps.mem hσ, rfl, d.K₁_invariant⟩
  · rw [if_neg htr]
    exact calls_liftWindow_isCosetInstance d.blocks.invariant I.x d.innerChain
      d.calls_innerChain_K d.calls_innerChain_isCosetInstance

/-- §15, line 1, step 6: **every call is a group instance**. -/
theorem calls_branch_isGroupInstance : ∀ J ∈ (d.branch).calls, IsGroupInstance J := by
  intro J hJ
  rw [branch_eq, calls_alignRed, List.mem_map] at hJ
  obtain ⟨J₀, hJ₀, rfl⟩ := hJ
  exact isGroupInstance_alignInst (d.calls_cosetBranch_isCosetInstance J₀ hJ₀)

end DescentData

/-- §15, line 1: **every call of the round is a group instance**, whichever branch of
Procedure Reduce-to-Johnson is taken. -/
theorem Line1Case.calls_isGroupInstance {q : ℕ} (c : Line1Case I q) :
    ∀ J ∈ c.branch.calls, IsGroupInstance J := by
  cases c with
  | leaf _ => intro J hJ; exact absurd hJ (by simp [Line1Case.branch, bruteForceBranch])
  | fixedString _ _ => intro J hJ; exact absurd hJ (by simp [Line1Case.branch, bruteForceBranch])
  | smallGroup _ _ => intro J hJ; exact absurd hJ (by simp [Line1Case.branch, bruteForceBranch])
  | offGroup _ => intro J hJ; exact absurd hJ (by simp [Line1Case.branch, bruteForceBranch])
  | chain d u _ => exact calls_chainRuleBranch_isGroupInstance d u
  | block b _ => exact calls_blockLuksBranch_isGroupInstance b
  | descent d _ => exact d.calls_branch_isGroupInstance

/-! ### The multiplicative cost of line 1

Step 5 of Procedure Reduce-to-Johnson is taken when `|Ḡ| < m^{1 + log₂ m}`, and its
multiplicative cost is that bound; step 6 has multiplicative cost `|Ḡ : N̄| ≤ m`
(Theorem 11.2.1).  Both are dominated by

> `q(n) = n^{2 + ⌊log₂ n⌋}`,

because `m ≤ n` and `1 + log₂ m < 2 + ⌊log₂ n⌋`.  The function `q` is quasipolynomial:
`q(n) ≤ exp(2 (log₂ n + 1)²)`. -/

section Cost

/-- §11.3, the multiplicative cost one round of Procedure Reduce-to-Johnson is allowed, as
a function of the window size `n`. -/
def line1Cost (n : ℕ) : ℕ := n ^ (2 + Nat.log 2 n)

theorem self_le_line1Cost {n : ℕ} (hn : 1 ≤ n) : n ≤ line1Cost n := by
  have h : n ^ 1 ≤ n ^ (2 + Nat.log 2 n) := Nat.pow_le_pow_right hn (by omega)
  simpa using h

theorem line1Cost_mono : Monotone line1Cost := by
  intro a b hab
  rcases Nat.eq_zero_or_pos b with hb | hb
  · have ha : a = 0 := by omega
    rw [ha, hb]
  · calc line1Cost a = a ^ (2 + Nat.log 2 a) := rfl
      _ ≤ b ^ (2 + Nat.log 2 a) := Nat.pow_le_pow_left hab _
      _ ≤ b ^ (2 + Nat.log 2 b) :=
          Nat.pow_le_pow_right hb (by
            have : Nat.log 2 a ≤ Nat.log 2 b := Nat.log_mono_right hab
            omega)

/-- `q` is quasipolynomial: `q(n) ≤ exp(2 (log₂ n + 1)²)`. -/
theorem line1Cost_le (n : ℕ) : line1Cost n ≤ 2 ^ (2 * (Nat.log 2 n + 1) ^ 2) := by
  set L := Nat.log 2 n + 1 with hL
  have h1 : n < 2 ^ L := Nat.lt_pow_succ_log_self one_lt_two n
  have hexp : 2 + Nat.log 2 n = L + 1 := by omega
  calc line1Cost n = n ^ (L + 1) := by rw [line1Cost, hexp]
    _ ≤ (2 ^ L) ^ (L + 1) := Nat.pow_le_pow_left (le_of_lt h1) _
    _ = 2 ^ (L * (L + 1)) := by rw [← pow_mul]
    _ ≤ 2 ^ (2 * L ^ 2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)

/-- §11.3, step 5: **the test of step 5 is below `q(n)`**, for `2 ≤ m ≤ n`.  This is the
monotonicity `m^{1 + log₂ m} ≤ n^{2 + ⌊log₂ n⌋}` with real exponents. -/
theorem rpow_le_line1Cost {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n) :
    (m : ℝ) ^ (1 + Real.logb 2 m) ≤ (line1Cost n : ℝ) := by
  have hn1 : 1 ≤ n := by omega
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
  have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hmn' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  have hlognn : 0 ≤ Real.logb 2 (m : ℝ) := Real.logb_nonneg one_lt_two hm1
  have hstep1 : (m : ℝ) ^ (1 + Real.logb 2 m) ≤ (n : ℝ) ^ (1 + Real.logb 2 m) :=
    Real.rpow_le_rpow (by linarith) hmn' (by linarith)
  have hlogle : Real.logb 2 (m : ℝ) ≤ Real.logb 2 (n : ℝ) :=
    Real.logb_le_logb_of_le one_lt_two (by linarith) hmn'
  have hlt := logb_lt_natLog_succ hn1
  have hE : 1 + Real.logb 2 (m : ℝ) ≤ ((2 + Nat.log 2 n : ℕ) : ℝ) := by
    push_cast
    linarith
  have hstep2 : (n : ℝ) ^ (1 + Real.logb 2 m) ≤ (n : ℝ) ^ (((2 + Nat.log 2 n : ℕ) : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hn1' hE
  have hpow : (n : ℝ) ^ (((2 + Nat.log 2 n : ℕ) : ℝ)) = (line1Cost n : ℝ) := by
    rw [Real.rpow_natCast, line1Cost]
    push_cast
    ring
  rw [← hpow]
  linarith

end Cost

/-! ### Line 1 as a total function of the instance

The tests of Procedure Reduce-to-Johnson, run on an arbitrary group instance.

* Steps 1 and 2 exit by brute force whenever the window is below the absolute constant
  `N₀ = max{64, n₀!}`, where `n₀` is the threshold of Theorem 11.2.1 (*"`n` greater than
  some absolute constant"*).  There `|G^Δ| ≤ n!` is bounded by an absolute constant, which
  is the exit condition of step 2 verbatim.
* Step 3 tests transitivity of `G = K^Δ`.
* Step 4 finds a minimal block system — for a transitive group on at least two points one
  exists (`Babai.exists_minimalSystemOfImprimitivity_mem`), and `Ḡ` is primitive on it
  (`Babai.isPrimitive_onBlocks`).
* Step 5 tests `|Ḡ| < m^{1 + log₂ m}`.  It is also taken when `m < n₀`, where `|Ḡ| ≤ m!`
  is again below the absolute constant `n₀! ≤ N₀ ≤ n ≤ q(n)`; this is the one place where
  the threshold of Theorem 11.2.1 shows, and the brute-force exit of step 2 pays for it.
* Step 6 is the remaining case, and Theorem 11.2.1 supplies its data
  (`Babai.exists_descentData`). -/

section Total

open scoped Classical in
/-- §11.3, **Procedure Reduce-to-Johnson always has a branch**: every instance with respect
to a group falls under one of the four branches, with multiplicative cost `q(n)`. -/
theorem nonempty_line1Case (I : SIInstance Ω A) (hg : IsGroupInstance I) :
    Nonempty (Line1Case I (line1Cost I.windowSize)) := by
  classical
  obtain ⟨K, hK, hKinv⟩ := hg
  let d : WindowData I := { K := K, isGroup := hK, invariant := hKinv }
  by_cases hsmall : I.windowSize < bruteForceThreshold.{u}
  · -- steps 1 and 2: the brute-force exit
    exact ⟨.leaf hsmall⟩
  push_neg at hsmall
  rw [bruteForceThreshold] at hsmall
  have h64 : 64 ≤ I.windowSize := le_trans (le_max_left _ _) hsmall
  have hfac : Nat.factorial descentThreshold.{u} ≤ I.windowSize :=
    le_trans (le_max_right _ _) hsmall
  have hcardΔ : Fintype.card I.Δ = I.windowSize := d.card_window
  obtain ⟨u⟩ : Nonempty I.Δ := Fintype.card_pos_iff.1 (by omega)
  have hn1 : 1 ≤ I.windowSize := by omega
  have hcost_n : I.windowSize ≤ line1Cost I.windowSize := self_le_line1Cost hn1
  by_cases htr : IsTransitive d.windowGroup
  · -- steps 4, 5, 6
    obtain ⟨ℬ, B, hℬ, hB, huB, hBne⟩ :=
      exists_minimalSystemOfImprimitivity_mem htr (by omega) u
    obtain ⟨B₁, hB₁, B₂, hB₂, hne⟩ := (Set.one_lt_ncard (Set.toFinite _)).1 hℬ.two_blocks
    let b : BlockData I :=
      { toWindowData := d, ℬ := ℬ, transitive := htr,
        system := hℬ.toIsSystemOfImprimitivity,
        two_blocks := ⟨B₁, hB₁, B₂, hB₂, hne⟩ }
    have hcardℬ : Nat.card b.ℬ = ℬ.ncard := Nat.card_coe_set_eq ℬ
    have hm2 : 2 ≤ Nat.card b.ℬ := by rw [hcardℬ]; exact hℬ.two_blocks
    have hmn : Nat.card b.ℬ ≤ I.windowSize := by
      have h := card_blocks_le (β := I.Δ) (G := d.windowGroup) (Δ := Set.univ) (ℬ := ℬ)
        hℬ.toIsSystemOfImprimitivity
      have : Nat.card b.ℬ = Nat.card ℬ := rfl
      omega
    by_cases hbig : ((Nat.card b.ℬ : ℝ) ^ (1 + Real.logb 2 (Nat.card b.ℬ)) ≤
        (Nat.card (onBlocks b.windowGroup b.ℬ b.system.permutes) : ℝ))
    · by_cases hlarge : descentThreshold.{u} ≤ Nat.card b.ℬ
      · -- step 6
        obtain ⟨dd, -, hcost⟩ := descentData_spec Ω A I b h64 hlarge (isPrimitive_onBlocks hℬ) hbig
        exact ⟨.descent dd (le_trans hcost (le_trans hmn hcost_n))⟩
      · -- `m < n₀`: `|Ḡ| ≤ m! ≤ n₀!` is an absolute constant, and step 5 applies
        push_neg at hlarge
        refine ⟨.block b ?_⟩
        haveI : Fintype ℬ := Fintype.ofFinite _
        have h1 : Nat.card (onBlocks b.windowGroup b.ℬ b.system.permutes) ≤
            Nat.factorial (Fintype.card ℬ) := card_onBlocks_le_factorial b.system.permutes
        have h2 : Fintype.card ℬ = Nat.card b.ℬ := Nat.card_eq_fintype_card.symm
        have h3 : Nat.factorial (Fintype.card ℬ) ≤ Nat.factorial descentThreshold.{u} :=
          Nat.factorial_le (by omega)
        omega
    · -- step 5: the test `|Ḡ| < m^{1+log₂ m}` succeeds
      refine ⟨.block b ?_⟩
      push_neg at hbig
      have hle := rpow_le_line1Cost (m := Nat.card b.ℬ) (n := I.windowSize) hm2 hmn
      have : (Nat.card (onBlocks b.windowGroup b.ℬ b.system.permutes) : ℝ) <
          (line1Cost I.windowSize : ℝ) := lt_of_lt_of_le hbig hle
      exact_mod_cast le_of_lt this
  · -- step 3
    exact ⟨.chain d u htr⟩

open scoped Classical in
/-- §15, **line 1** as a function of the instance: the branch of Procedure
Reduce-to-Johnson that applies (`Babai.nonempty_line1Case`), and the brute-force leaf of
steps 1–2 on the instances the Master Algorithm never produces. -/
noncomputable def line1Case (I : SIInstance Ω A) : Line1Case I (line1Cost I.windowSize) :=
  if h : IsGroupInstance I then Classical.choice (nonempty_line1Case I h) else .offGroup h

/-- §11.3 and §15, line 1: **a choice of branch of Procedure Reduce-to-Johnson for every
instance**.

Which branch applies is a theorem (`Babai.nonempty_line1Case`), and the data the branch runs
on is chosen — the minimal block system of step 4, the normal subgroup Theorem 11.2.1 gives
at step 6.  That is what the procedure itself says: *"find a minimal block system"*.  The
Master Algorithm is stated for **every** such choice, so a choice cannot smuggle in a
program: each branch of `Babai.Line1Case` is a named reduction
(`Babai.Line1Case.branch`), and each leaf carries the exit test of steps 1–2. -/
def Line1Choice (Ω : Type u) (A : Type v) [Fintype Ω] [DecidableEq Ω] :=
  ∀ I : SIInstance Ω A, Line1Case I (line1Cost I.windowSize)

/-- §15, line 1: **`Babai.Line1Choice` is inhabited** — one branch per instance,
`Babai.line1Case`.  This is the only place where `Classical.choice` enters line 1. -/
noncomputable def line1ChoiceOfCases : Line1Choice Ω A := fun I => line1Case I

/-- §15, **line 1** as a reduction, on a hinted instance.  Line 1 is taken only where the
instance carries no hint, so the hint plays no part in choosing the branch. -/
noncomputable def line1Round (c : Line1Choice Ω A) (i : HintedInstance Ω A) :
    SIReduction Ω A (Set (Equiv.Perm Ω)) := (c i.inst).branch

/-- §15, **line 1 in coset form**: the round of Procedure Reduce-to-Johnson before the
alignment step of Remark 11.1.4 (`Babai.Line1Case.cosetBranch`). -/
noncomputable def line1RoundCoset (c : Line1Choice Ω A) (i : HintedInstance Ω A) :
    SIReduction Ω A (Set (Equiv.Perm Ω)) := (c i.inst).cosetBranch

/-- §15, line 1: **the round is the alignment of its coset form** (Remark 11.1.4). -/
theorem line1Round_eq_alignRed (c : Line1Choice Ω A) (i : HintedInstance Ω A) :
    line1Round c i = SIReduction.alignRed i.inst (line1RoundCoset c i) :=
  (c i.inst).branch_eq_alignRed

/-- §15, **line 1**, the hint it attaches to each of its calls: the Johnson case data of
step 7 after the Luks descent, and nothing otherwise
(`Babai.Line1Case.hint`). -/
noncomputable def line1Lift (c : Line1Choice Ω A) (i : HintedInstance Ω A)
    (J : SIInstance Ω A) : HintedInstance Ω A := ⟨J, (c i.inst).hint J⟩

@[simp] theorem inst_line1Lift (c : Line1Choice Ω A) (i : HintedInstance Ω A)
    (J : SIInstance Ω A) : (line1Lift c i J).inst = J := rfl

/-- §15, line 1 **is correct**. -/
theorem run_line1Round (c : Line1Choice Ω A) (i : HintedInstance Ω A) :
    (line1Round c i).run = i.inst.answer := (c i.inst).run_branch

/-- §15, line 1, **the progress**. -/
theorem decreases_line1Round (c : Line1Choice Ω A) (i : HintedInstance Ω A)
    (hJ : ¬ IsJohnson i) :
    (∀ J ∈ (line1Round c i).calls,
        MakesProgress HintedInstance.win param i (line1Lift c i J)) ∨
      IsChainRuleRound HintedInstance.win param i
        ((line1Round c i).calls.map (line1Lift c i)) := by
  obtain ⟨I, hnt⟩ := i
  cases hnt with
  | some d => exact absurd rfl hJ
  | none => exact (c I).decreases_branch

/-- §15, line 1: **every call is a group instance**. -/
theorem calls_line1Round_isGroupInstance (c : Line1Choice Ω A) (i : HintedInstance Ω A) :
    ∀ J ∈ (line1Round c i).calls, IsGroupInstance J :=
  (c i.inst).calls_isGroupInstance

/-- The number of instances one round of line 1 produces, as a function of the window
size. -/
def line1RoundCost (n : ℕ) : ℕ := line1Cost n * n + line1Cost n + n + 2

theorem line1RoundCost_mono : Monotone line1RoundCost := by
  intro a b hab
  have h := line1Cost_mono hab
  have : line1Cost a * a ≤ line1Cost b * b := Nat.mul_le_mul h hab
  rw [line1RoundCost, line1RoundCost]
  omega

/-- §15, line 1, **the number of calls**. -/
theorem calls_length_line1Round (c : Line1Choice Ω A) (i : HintedInstance Ω A) :
    ((line1Round c i).calls).length ≤ line1RoundCost i.inst.windowSize :=
  (c i.inst).calls_length_branch

end Total

end Branches


end Babai
