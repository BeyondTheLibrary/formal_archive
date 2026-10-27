import Workspace.Algo.TopMasterCameronWindowRows

/-! # Retained labels for the actual ambient Cameron child
The child uses the ambient subgroup's restricted generators. The preceding
module proves their exact numbered action, so the same union blocks and
labels as the computed minimal-block descent apply to that child.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Classical

 theorem MasterHintBlockLink.two_blocks {Ω : Type*} [Fintype Ω]
    {G : Subgroup (Perm Ω)} {B : Set (Set Ω)}
    {hB : ∀ g ∈ G, ∀ U ∈ B, (g : Perm Ω) '' U ∈ B}
    {m t : ℕ} {φ : G →* Perm (Fin m)} (L : MasterHintBlockLink (t := t) hB φ)
    (ht : 1 ≤ t) (hm : 2 * t < m) : ∃ U ∈ B, ∃ V ∈ B, U ≠ V := by
  have hc : Nat.card B = m.choose t := by
    rw [Nat.card_congr L.label, Nat.card_eq_fintype_card,
      Fintype.card_finset_len, Fintype.card_fin]
  have hb : 1 < Nat.card B := by
    rw [hc]
    have := self_le_choose ht hm
    omega
  have : Finite B := Set.Finite.to_subtype (Set.toFinite B)
  have : Nontrivial B := Finite.one_lt_card_iff_nontrivial.mp hb
  obtain ⟨U, V, hUV⟩ := exists_pair_ne B
  exact ⟨U.val, U.property, V.val, V.property, fun he => hUV (Subtype.ext he)⟩

noncomputable def masterCameronUnionBlocks (W : RawWinSI) (c : RawCameron) :
    Set (Set (Fin W.1.length)) :=
  descentBlocks (blockImage
    (blockEquiv W.1.length (rawMinBlocks ((primitiveWindowInput W).1, W.1))
      (blocksWF_rawMinBlocks rfl (primitiveWindowInput W).1))
    (blockSets (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length (camBlocks c)))

section Window
variable {n : ℕ} {W : RawWinSI}
    (hx : W.2.2.2.1.length = n) (hw : RawGens.WF n W.2.1)
    (hnd : W.1.Nodup) (hlt : ∀ u ∈ W.1, u < n)
    (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1))
    (htr : IsTransitive (decGroup W.1.length (primitiveWindowInput W).1)) (hn : 2 ≤ W.1.length)
    {c : RawCameron} (h : c.WF (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length)
    (hhi : (decGroup (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length
      (masterWindowBlockAction W).2.2).map (permCongrHom (decCameron c h)).toMonoidHom ≤
        wreathProduct (JohnsonS c.k c.t) c.s)
    (hlo : basePower (JohnsonA c.k c.t) c.s ≤
      (decGroup (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length
        (masterWindowBlockAction W).2.2).map (permCongrHom (decCameron c h)).toMonoidHom)

noncomputable def masterCameronChildSystem (j : ℕ) :
    IsSystemOfImprimitivity
      (decGroup W.1.length (masterHintTop (masterCameronChildInput ((c, masterWindowBlockInput W), j))).1.1.2)
      Set.univ (masterCameronUnionBlocks W c) := by
  rw [masterCameronChild_minimal_group hx hw hnd hlt hinv htr hn h hhi j]
  exact camMinimalUnionSystem (rawRestrictGens_wf_of_raw (dom := W.2.2.2.1) hw hnd hlt hinv)
    rfl htr hn h hhi hlo

noncomputable def masterCameronChildLink (j : ℕ) :
    MasterHintBlockLink (t := c.t) (masterCameronChildSystem hx hw hnd hlt hinv htr hn h hhi hlo j).permutes
      (masterCameronChildHom hx hw hnd hlt hinv htr hn h hhi j) :=
  (camMinimalRowsHintLink (rawRestrictGens_wf_of_raw (dom := W.2.2.2.1) hw hnd hlt hinv)
    rfl htr hn h hhi hlo).changeGroup
      (masterCameronChild_minimal_group hx hw hnd hlt hinv htr hn h hhi j) (fun _ => rfl)

include hlo in
 theorem masterCameronChildHom_giant (j : ℕ) :
    IsGiantRep (masterCameronChildHom hx hw hnd hlt hinv htr hn h hhi j) :=
  isGiantRep_comp_mulEquiv _
    (camLiftGiantHom_giant (camMinimalAction_wf (dom := W.1)
      (rawRestrictGens_wf_of_raw (dom := W.2.2.2.1) hw hnd hlt hinv) rfl htr hn) h hhi hlo)

include hx hw hnd hlt hinv htr hn h hhi hlo in
 theorem masterCameronChild_two (j : ℕ) :
    ∃ U ∈ masterCameronUnionBlocks W c, ∃ V ∈ masterCameronUnionBlocks W c, U ≠ V :=
  (masterCameronChildLink hx hw hnd hlt hinv htr hn h hhi hlo j).two_blocks h.t_pos h.k_gt

 theorem masterCameronChild_linked (j : ℕ) :
    RawAction.WF W.1.length c.k
      (masterHintTop (masterCameronChildInput ((c, masterWindowBlockInput W), j))).1
      (masterCameronChildHom hx hw hnd hlt hinv htr hn h hhi j) ∧
    IsGiantRep (masterCameronChildHom hx hw hnd hlt hinv htr hn h hhi j) ∧
    Nonempty (MasterHintBlockLink (t := c.t)
      (masterCameronChildSystem hx hw hnd hlt hinv htr hn h hhi hlo j).permutes
      (masterCameronChildHom hx hw hnd hlt hinv htr hn h hhi j)) :=
  ⟨masterCameronChild_rows_wf hx hw hnd hlt hinv htr hn h hhi j,
    masterCameronChildHom_giant hx hw hnd hlt hinv htr hn h hhi hlo j,
    ⟨masterCameronChildLink hx hw hnd hlt hinv htr hn h hhi hlo j⟩⟩
end Window
end Algo
