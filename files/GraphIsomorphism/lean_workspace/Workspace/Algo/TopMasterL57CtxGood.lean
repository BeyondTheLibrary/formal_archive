import Workspace.Algo.TopMasterL57Node
import Workspace.Algo.TopMasterRecursionCameron

/-! # The context of lines 5–7 at a good node

Section 15, lines 5–7. At a good hinted node (`Algo.MasterNodeGood`), the context of the round
of lines 5–7 (`Algo.masterL57Ctx`: the window's action in the window's own size, and the two
strings on the window with their letters renamed) is normalized:

* `Algo.masterL57Ctx_hintFacts`: the hint's meaning (`Algo.MasterHintGoodAt`) holds for the
  context's action, with the representation `ϕ` read on the shortened generators; in particular
  the action is well formed (`Algo.RawAction.WF`), with the images of the generators recomputed
  by `Algo.rawImgOf`;
* `Algo.masterL57Ctx_normal`: the context's generators are at most `|Δ|²`, and every number
  it stores is below `2|Δ| + 1`;
* `Algo.masterL57Guard_of_good`: hence the node of lines 5–7 passes its test (the size bound
  `Algo.AggnCheckedWF` of the round), so the carrier runs the round at every good node.
-/
set_option synthInstance.maxSize 2048
namespace Algo
open RAM RAM.Targets Babai Equiv

/-- Moving a representation along an equality of groups keeps transitivity, the giant
property, and a labelling of a block system compatible with the representation. -/
theorem hintFacts_congr {Ω : Type} [Fintype Ω] [DecidableEq Ω] {H H' : Subgroup (Perm Ω)}
    (e : H' = H) {m t : ℕ} (ϕ : H →* Perm (Fin m)) {B : Set (Set Ω)}
    (hB : IsSystemOfImprimitivity H Set.univ B) (htr : IsTransitive H) (hgi : IsGiantRep ϕ)
    (hL : Nonempty (MasterHintBlockLink (t := t) hB.permutes ϕ)) :
    ∃ hB' : IsSystemOfImprimitivity H' Set.univ B, IsTransitive H' ∧
      IsGiantRep (ϕ.comp (MulEquiv.subgroupCongr e).toMonoidHom) ∧
      Nonempty (MasterHintBlockLink (t := t) hB'.permutes
        (ϕ.comp (MulEquiv.subgroupCongr e).toMonoidHom)) := by
  subst e
  have h : ϕ.comp (MulEquiv.subgroupCongr (rfl : H' = H')).toMonoidHom = ϕ :=
    MonoidHom.ext fun _ => rfl
  rw [h]
  exact ⟨hB, htr, hgi, hL⟩

/-- **The image routine on a well-formed action**: `Algo.rawImgOf` computes `ϕ(σ)` for every
element `σ` of the group. -/
theorem rawImgOf_of_wf {N m : ℕ} {A : RawAction} {ϕ : decGroup N A.1.2 →* Perm (Fin m)}
    (hA : RawAction.WF N m A ϕ) {g : RawPerm} (hg : RawPerm.WF N g)
    (hσ : decPerm N g ∈ decGroup N A.1.2) :
    rawImgOf (A, g) = encPerm m (ϕ ⟨decPerm N g, hσ⟩) := by
  obtain ⟨⟨d, gs⟩, ⟨gd, is⟩⟩ := A
  have h := rawImgOf_spec (dom := d) (gdom := gd) (gens := gs.map (decPerm N))
    (imgs := is.map (decPerm m)) (ϕ := ϕ) hA.1 hA.2.1 hA.2.2.2.2 hσ
  rw [map_encPerm_decPerm hA.2.2.1, map_encPerm_decPerm hA.2.2.2.1, encPerm_decPerm hg] at h
  exact h

section Good
variable {W : RawWinSI} {h : RawMasterHint}

/-- The group of the context equals the group of the node's top action. -/
theorem masterL57Ctx_group' (W : RawWinSI) (h : RawMasterHint) :
    decGroup W.1.length (masterL57Ctx (W, some h)).1.1.2 =
      decGroup W.1.length (masterHintTop (W, h)).1.1.2 :=
  masterL57Ctx_group (W, some h)

/-- `Algo.masterL57Ctx_strIso` at a hinted node. -/
theorem masterL57Ctx_strIso' (W : RawWinSI) (h : RawMasterHint)
    (K : Set (Perm (Fin W.1.length))) :
    strIso K (decStrN W.1.length (masterL57Ctx (W, some h)).2.1)
        (decStrN W.1.length (masterL57Ctx (W, some h)).2.2.1) =
      strIso K (decStrN W.1.length (masterHintTop (W, h)).2.1)
        (decStrN W.1.length (masterHintTop (W, h)).2.2) :=
  masterL57Ctx_strIso (W, some h) K

/-- **The context's action is well formed**, for the representation `ϕ` of the node's top
action read on the context's (shortened) generators. -/
theorem masterL57Action_wf {m : ℕ}
    {ϕ : decGroup W.1.length (masterHintTop (W, h)).1.1.2 →* Perm (Fin m)}
    (hA : RawAction.WF W.1.length m (masterHintTop (W, h)).1 ϕ) :
    RawAction.WF W.1.length m (masterL57Ctx (W, some h)).1
      (ϕ.comp (MulEquiv.subgroupCongr (masterL57Ctx_group' W h)).toMonoidHom) := by
  have hxw : (masterL57XW ((W, some h) : RawMasterSI)).length = W.1.length :=
    length_masterL57XW _
  have hgw : RawGens.WF W.1.length (masterL57Gens ((W, some h) : RawMasterSI)) :=
    wf_tidyGens hxw _
  have hmem : ∀ g ∈ masterL57Gens ((W, some h) : RawMasterSI),
      decPerm W.1.length g ∈ decGroup W.1.length (masterHintTop (W, h)).1.1.2 := by
    intro g hg
    rw [← masterL57Ctx_group' W h]
    exact Subgroup.subset_closure (List.mem_map.2 ⟨g, hg, rfl⟩)
  have himg : ∀ g (hg : g ∈ masterL57Gens ((W, some h) : RawMasterSI)),
      rawImgOf ((masterHintTop (W, h)).1, g) = encPerm m (ϕ ⟨decPerm W.1.length g, hmem g hg⟩) :=
    fun g hg => rawImgOf_of_wf hA (hgw g hg) (hmem g hg)
  refine ⟨List.length_range, ?_, hgw, ?_, ?_⟩
  · change (List.range (masterHintTop (W, h)).1.2.1.length).length = m
    rw [List.length_range]
    exact hA.2.1
  · intro g hg
    change g ∈ (masterL57Gens ((W, some h) : RawMasterSI)).map (fun g => rawImgOf ((masterHintTop (W, h)).1, g)) at hg
    obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.1 hg
    rw [himg g₀ hg₀]
    exact wf_encPerm m _
  · refine ⟨by simp [masterL57Ctx, masterL57Action], fun i hi hi' => ?_⟩
    simp only [masterL57Ctx, masterL57Action, List.getElem_map]
    have hi₀ : i < (masterL57Gens ((W, some h) : RawMasterSI)).length := by simpa using hi
    have e := himg _ (List.getElem_mem hi₀)
    change decPerm m (rawImgOf ((masterHintTop (W, h)).1, _)) = _
    rw [e, decPerm_encPerm]
    rfl

/-- **The hint's meaning for the context's action.** At a good hinted node, the facts of
`Algo.MasterHintGoodAt` hold for the context of lines 5–7 on the window's own points: the
representation `ϕ` of the hint, read on the context's generators, makes the context's action
well formed, the group is transitive, `ϕ` is a giant representation, a block system is
labelled by the `t`-subsets of `[m]` compatibly with `ϕ`, and the bounds on `t` and `m`. -/
theorem masterL57Ctx_hintFacts (hg : MasterHintGood (W, h)) :
    ∃ (m : ℕ) (ϕ : decGroup W.1.length (masterL57Ctx (W, some h)).1.1.2 →* Perm (Fin m))
      (B : Set (Set (Fin W.1.length)))
      (hB : IsSystemOfImprimitivity (decGroup W.1.length (masterL57Ctx (W, some h)).1.1.2)
        Set.univ B),
      RawAction.WF W.1.length m (masterL57Ctx (W, some h)).1 ϕ ∧
        IsTransitive (decGroup W.1.length (masterL57Ctx (W, some h)).1.1.2) ∧ IsGiantRep ϕ ∧
        Nonempty (MasterHintBlockLink (t := h.2) hB.permutes ϕ) ∧
        (∃ U ∈ B, ∃ V ∈ B, U ≠ V) ∧ 1 ≤ h.2 ∧ 2 * h.2 < m ∧ m ≤ W.1.length ∧
        64 ≤ W.1.length := by
  obtain ⟨m, ϕ, B, hB, hwf, htr, hgi, hL, h2, h1, ht, hm, h64⟩ := hg
  obtain ⟨hB', htr', hgi', hL'⟩ := hintFacts_congr (masterL57Ctx_group' W h) ϕ hB htr hgi hL
  exact ⟨m, _, B, hB', masterL57Action_wf hwf, htr', hgi', hL', h2, h1, ht, hm, h64⟩

/-- **The context is normalized**: at a good hinted node, the context's generators number at
most `|Δ|²`, and every number it stores (the two domains, the two strings, the list fixing the
test-set size) is below `2|Δ| + 1`. -/
theorem masterL57Ctx_normal (hg : MasterHintGood (W, h)) :
    (masterL57Ctx (W, some h)).1.1.2.length ≤ W.1.length * W.1.length ∧
      ∀ xs ∈ [(masterL57Ctx (W, some h)).1.1.1, (masterL57Ctx (W, some h)).1.2.1,
        (masterL57Ctx (W, some h)).2.1, (masterL57Ctx (W, some h)).2.2.1,
        (masterL57Ctx (W, some h)).2.2.2], ∀ a ∈ xs, a < 2 * W.1.length + 1 := by
  obtain ⟨m, ϕ, B, hB, hwf, -, -, -, -, -, -, hm, -⟩ := hg
  refine ⟨length_tidyGens (length_masterL57XW _) _, ?_⟩
  have hL : (masterL57Letters ((W, some h) : RawMasterSI)).length ≤ 2 * W.1.length :=
    length_masterL57Letters_le ((W, some h) : RawMasterSI)
  have hrel : ∀ zs : RawStr, (∀ b ∈ zs, b ∈ masterL57Letters ((W, some h) : RawMasterSI)) →
      ∀ a ∈ masterL57Relabel (masterL57Order ((W, some h) : RawMasterSI), zs),
        a < 2 * W.1.length + 1 := by
    intro zs hz a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
    have := (masterL57Rank_letter (hz b hb)).1
    change masterL57Rank (masterL57Order ((W, some h) : RawMasterSI), b) < _
    omega
  intro xs hxs a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl
  · have := List.mem_range.1 ha
    change a < W.1.length at this
    omega
  · have := List.mem_range.1 ha
    have hmA : (masterHintTop (W, h)).1.2.1.length = m := hwf.2.1
    have hb : (masterHintTop (W, h)).1.1.1.length = W.1.length := rfl
    change a < (masterHintTop (W, h)).1.2.1.length at this
    omega
  · exact hrel _ (masterL57XW_letters _) a ha
  · exact hrel _ (masterL57YW_letters _) a ha
  · have := List.mem_range.1 ha
    have := min_le_right (10 + Nat.log 2 W.1.length) W.1.length
    change a < min (10 + Nat.log 2 W.1.length) W.1.length at *
    omega

/-- The list fixing the test-set size meets the guard bound for the exponent
`10 + log |Δ|`. -/
theorem masterL57_testSize_guard (N : ℕ) :
    min (10 + Nat.log 2 N) N ≤ guardBound (10 + Nat.log 2 N) N := by
  unfold guardBound
  rcases Nat.eq_zero_or_pos (Nat.log 2 N) with h0 | hpos
  · rw [h0]
    have hN : N < 2 := by
      by_contra hN
      have := Nat.log_pos (by norm_num : 1 < 2) (by omega : 2 ≤ N)
      omega
    simp only [zero_add, one_pow]
    omega
  · calc min (10 + Nat.log 2 N) N ≤ 10 + Nat.log 2 N := min_le_left _ _
      _ ≤ 2 ^ (10 + Nat.log 2 N) := (Nat.lt_two_pow_self).le
      _ ≤ (Nat.log 2 N + 1) ^ (10 + Nat.log 2 N) := Nat.pow_le_pow_left (by omega) _

/-- **At a good hinted node, the node of lines 5–7 passes its test**: its context is bounded
by the size bound of the round (`Algo.AggnCheckedWF`), so the carrier runs the round. -/
theorem masterL57Guard_of_good (hg : MasterHintGood (W, h)) :
    masterL57Guard ((W, some h) : RawMasterSI) = true := by
  obtain ⟨m, ϕ, B, hB, hwf, -, -, -, -, -, -, hm, -⟩ := masterL57Ctx_hintFacts hg
  obtain ⟨hshort, hletters⟩ := masterL57Ctx_normal hg
  have hC : AggnPhaseCtxWF (10 + Nat.log 2 W.1.length) W.1.length m
      (masterL57Ctx (W, some h)) ϕ :=
    { action := hwf
      source := masterL57Ctx_length _
      target := masterL57Ctx_length_y _
      degree := hm
      arity := by
        change (List.range (min (10 + Nat.log 2 W.1.length) W.1.length)).length ≤ _
        rw [List.length_range]
        exact min_le_right _ _
      guard := by
        change (List.range (min (10 + Nat.log 2 W.1.length) W.1.length)).length ≤
          guardBound _ (masterL57Ctx (W, some h)).2.1.length
        rw [List.length_range, masterL57Ctx_length]
        exact masterL57_testSize_guard _ }
  have hwf' := aggnCheckedWF_of_context hC hshort hletters
  apply (aggnUniformWfCheck_spec 0 0 _).2
  change AggnCheckedWF (masterL57Ctx (W, some h)).2.1.length (masterL57Ctx (W, some h), none)
  rw [masterL57Ctx_length]
  exact hwf'

end Good

end Algo
