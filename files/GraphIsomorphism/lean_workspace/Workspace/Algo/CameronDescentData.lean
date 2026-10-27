import Workspace.Algo.CameronJohnson
import Workspace.Master.HintTransport
import Workspace.Master.Line1

/-!
# Step 6 data from numbered blocks

The raw algorithms number the blocks. The master algorithm uses the blocks
as a subtype of sets. We transport the computed subgroup and its coordinate
blocks along the explicit numbering. The calling instance supplies its window
bound. The index estimate travels with the resulting descent data.
-/

namespace Algo

open RAM RAM.Targets
open Equiv (Perm)

/-- Normality inside a group is preserved by a change of point names. -/
theorem camNormal_map {α β : Type*} (e : α ≃ β) {N G : Subgroup (Perm α)}
    (hN : Babai.IsNormalIn N G) :
    Babai.IsNormalIn (N.map (Equiv.permCongrHom e).toMonoidHom)
      (G.map (Equiv.permCongrHom e).toMonoidHom) where
  le := Subgroup.map_mono hN.le
  conj_mem := by
    rintro _ ⟨g, hg, rfl⟩ _ ⟨a, ha, rfl⟩
    exact ⟨g * a * g⁻¹, hN.conj_mem g hg a ha, by simp only [map_mul, map_inv]⟩

section Transport

variable {Ω A : Type*} [Fintype Ω] [DecidableEq Ω] {I : Babai.SIInstance Ω A}

/-- Step 6 of Reduce-to-Johnson: turn the computed Cameron data into the master record. -/
noncomputable def camDescentData (b : Babai.BlockData I) {m : ℕ}
    (e : Fin m ≃ b.ℬ) {c : RawCameron} (h : c.WF m) (gs : RawGens)
    (hG : (decGroup m gs).map (Equiv.permCongrHom e).toMonoidHom =
      Babai.onBlocks b.windowGroup b.ℬ b.system.permutes)
    (hlo : Babai.basePower (Babai.JohnsonA c.k c.t) c.s ≤
      (decGroup m gs).map (Equiv.permCongrHom (decCameron c h)).toMonoidHom)
    (hhi : (decGroup m gs).map (Equiv.permCongrHom (decCameron c h)).toMonoidHom ≤
      Babai.wreathProduct (Babai.JohnsonS c.k c.t) c.s)
    (hwindow : 64 ≤ I.windowSize) : Babai.DescentData I where
  blocks := b
  N := (camNbar c h).map (Equiv.permCongrHom e).toMonoidHom
  N_normal := by
    have hn := camNormal_map e (camNbar_normal h (decGroup m gs) hlo hhi)
    rwa [hG] at hn
  𝒞 := Babai.blockImage e (blockSets m (camBlocks c))
  𝒞_system := Babai.isSystemOfImprimitivity_map_permCongrHom e (camBlocks_system h)
  k := c.k
  t := c.t
  acts := Babai.actsAsJohnsonA_map_permCongrHom e (camBlocks_acts h)
  t_pos := h.t_pos
  k_gt := h.k_gt
  window_large := hwindow

/-- The `N` field is the transported raw output, through the supplied block numbering. -/
theorem camDescentData_raw (b : Babai.BlockData I) {m : ℕ}
    (e : Fin m ≃ b.ℬ) {c : RawCameron} (h : c.WF m) {gs : RawGens}
    (hw : RawGens.WF m gs)
    (hG : (decGroup m gs).map (Equiv.permCongrHom e).toMonoidHom =
      Babai.onBlocks b.windowGroup b.ℬ b.system.permutes)
    (hlo : Babai.basePower (Babai.JohnsonA c.k c.t) c.s ≤
      (decGroup m gs).map (Equiv.permCongrHom (decCameron c h)).toMonoidHom)
    (hhi : (decGroup m gs).map (Equiv.permCongrHom (decCameron c h)).toMonoidHom ≤
      Babai.wreathProduct (Babai.JohnsonS c.k c.t) c.s)
    (hwindow : 64 ≤ I.windowSize) :
    (camDescentData b e h gs hG hlo hhi hwindow).N =
      (decGroup m (rawNbar (c, gs))).map (Equiv.permCongrHom e).toMonoidHom := by
  rw [rawNbar_spec h hw hlo hhi]
  rfl

/-- Step 6, above the absolute threshold, with raw generators and the index bound bundled. -/
theorem camStepSix_data
    (cameron : RawGens × List ℕ → Option RawCameron)
    (hpoly : PolyFun cameron) (hspec : CameronSpec cameron)
    (b : Babai.BlockData I) {m : ℕ} (e : Fin m ≃ b.ℬ)
    (gs : RawGens) (dom : List ℕ) (hd : dom.length = m) (hw : RawGens.WF m gs)
    (hG : (decGroup m gs).map (Equiv.permCongrHom e).toMonoidHom =
      Babai.onBlocks b.windowGroup b.ℬ b.system.permutes)
    (hp : Babai.IsPrimitive (decGroup m gs))
    (hb : (m : ℝ) ^ (1 + Real.logb 2 m) ≤ Nat.card (decGroup m gs))
    (hm : max 25 camDescentThreshold ≤ m) (hwindow : 64 ≤ I.windowSize) :
    ∃ (c : RawCameron) (h : c.WF m) (D : Babai.DescentData I),
      cameron (gs, dom) = some c ∧ D.blocks = b ∧ D.k = c.k ∧ D.t = c.t ∧
      HEq D.N ((decGroup m (rawNbar (c, gs))).map (Equiv.permCongrHom e).toMonoidHom) ∧
      HEq D.𝒞 (Babai.blockImage e (blockSets m (camBlocks c))) ∧
      D.N.relIndex (Babai.onBlocks D.blocks.windowGroup D.blocks.ℬ D.blocks.system.permutes) ≤ m ∧
      Real.logb 2 m ≤ (c.k : ℝ) := by
  obtain ⟨c, h, he, _, hlo, hhi⟩ := hspec m gs dom hd hw ((le_max_left _ _).trans hm) hp hb
  obtain ⟨c', h', he', hidx, hlog⟩ := camRecognize_index cameron hpoly hspec m gs dom hd hw
    ((le_max_left _ _).trans hm) ((le_max_right _ _).trans hm) hp hb
  have hc : c' = c := Option.some.inj (he'.symm.trans he)
  subst c'
  let D := camDescentData b e h gs hG hlo hhi hwindow
  refine ⟨c, h, D, he, rfl, rfl, rfl, heq_of_eq (camDescentData_raw b e h hw hG hlo hhi hwindow), HEq.rfl,
    ?_, hlog⟩
  change ((camNbar c h).map (Equiv.permCongrHom e).toMonoidHom).relIndex
    (Babai.onBlocks b.windowGroup b.ℬ b.system.permutes) ≤ m
  rw [← hG, Subgroup.relIndex_map_map_of_injective _ _ (Equiv.permCongrHom e).injective]
  exact hidx

/-- The raw block images generate the actual action, through `blockEquiv`. -/
theorem camBlockImgs_group {n : ℕ} {bl : RawBlocks} (hb : BlocksWF n bl)
    {gs : RawGens} (hw : RawGens.WF n gs)
    (hp : ∀ g ∈ decGroup n gs, ∀ B ∈ blockSets n bl,
      (g : Perm (Fin n)) '' B ∈ blockSets n bl) :
    (decGroup bl.length (rawBlockImgs (bl, gs))).map
      (Equiv.permCongrHom (blockEquiv n bl hb)).toMonoidHom =
      Babai.onBlocks (decGroup n gs) (blockSets n bl) hp := by
  have hI : ImgsOf (gs.map (decPerm n))
      ((rawBlockImgs (bl, gs)).map (decPerm bl.length))
      (blockPhi n bl hb (gs.map (decPerm n)) hp) := by
    simpa only [blockImgsOf, map_encPerm_decPerm hw] using imgsOf_blockPhi hb hp
  rw [decGroup, ← hI.range_eq_genGroup]
  ext q
  constructor
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    refine ⟨g, ?_⟩
    apply Equiv.ext
    intro B
    change _ = blockEquiv n bl hb
      ((blockEquiv n bl hb).symm (Babai.blockHom (decGroup n gs) (blockSets n bl) hp g
        (blockEquiv n bl hb ((blockEquiv n bl hb).symm B))))
    simp
  · rintro ⟨g, rfl⟩
    refine ⟨blockPhi n bl hb (gs.map (decPerm n)) hp g, ⟨g, rfl⟩, ?_⟩
    apply Equiv.ext
    intro B
    change blockEquiv n bl hb
      ((blockEquiv n bl hb).symm (Babai.blockHom (decGroup n gs) (blockSets n bl) hp g
        (blockEquiv n bl hb ((blockEquiv n bl hb).symm B)))) = _
    simp

/-- Step 4 on a numbered window, transported to the calling instance. -/
noncomputable def camMinBlockData {n : ℕ} {gs : RawGens} {dom : List ℕ}
    (hw : RawGens.WF n gs) (hd : dom.length = n)
    (htr : Babai.IsTransitive (decGroup n gs)) (hn : 2 ≤ n)
    (d : Babai.WindowData I) (e : Fin n ≃ I.Δ)
    (hG : (decGroup n gs).map (Equiv.permCongrHom e).toMonoidHom = d.windowGroup) :
    Babai.BlockData I where
  toWindowData := d
  ℬ := Babai.blockImage e (blockSets n (rawMinBlocks (gs, dom)))
  transitive := by simpa only [hG] using Babai.isTransitive_map_permCongrHom e htr
  system := by
    simpa only [hG] using Babai.isSystemOfImprimitivity_map_permCongrHom e
      (isMinimalSystemOfImprimitivity_rawMinBlocks hw hd htr hn).toIsSystemOfImprimitivity
  two_blocks := by
    have htwo := (isMinimalSystemOfImprimitivity_rawMinBlocks hw hd htr hn).two_blocks
    obtain ⟨B, hB, C, hC, hne⟩ := (Set.one_lt_ncard (Set.toFinite _)).1
      (lt_of_lt_of_le (by decide : 1 < 2) htwo)
    exact ⟨e '' B, Babai.image_mem_blockImage e hB,
      e '' C, Babai.image_mem_blockImage e hC,
      fun he => hne ((Set.image_injective.2 e.injective) he)⟩

/-- The numbering of the computed minimal blocks as blocks in the calling instance. -/
noncomputable def camMinBlockEquiv {n : ℕ} {gs : RawGens} {dom : List ℕ}
    (hw : RawGens.WF n gs) (hd : dom.length = n)
    (htr : Babai.IsTransitive (decGroup n gs)) (hn : 2 ≤ n)
    (d : Babai.WindowData I) (e : Fin n ≃ I.Δ)
    (hG : (decGroup n gs).map (Equiv.permCongrHom e).toMonoidHom = d.windowGroup) :
    Fin (rawMinBlocks (gs, dom)).length ≃ (camMinBlockData hw hd htr hn d e hG).ℬ :=
  (blockEquiv n (rawMinBlocks (gs, dom)) (blocksWF_rawMinBlocks hd gs)).trans
    (Babai.blockImageEquiv e (blockSets n (rawMinBlocks (gs, dom))))

set_option backward.isDefEq.respectTransparency false in
/-- The numbering transports exactly the raw minimal-block group to the master action. -/
theorem camMinBlockEquiv_group {n : ℕ} {gs : RawGens} {dom : List ℕ}
    (hw : RawGens.WF n gs) (hd : dom.length = n)
    (htr : Babai.IsTransitive (decGroup n gs)) (hn : 2 ≤ n)
    (d : Babai.WindowData I) (e : Fin n ≃ I.Δ)
    (hG : (decGroup n gs).map (Equiv.permCongrHom e).toMonoidHom = d.windowGroup) :
    (decGroup (rawMinBlocks (gs, dom)).length
      (rawBlockImgs (rawMinBlocks (gs, dom), gs))).map
        (Equiv.permCongrHom (camMinBlockEquiv hw hd htr hn d e hG)).toMonoidHom =
      Babai.onBlocks (camMinBlockData hw hd htr hn d e hG).windowGroup
        (camMinBlockData hw hd htr hn d e hG).ℬ
        (camMinBlockData hw hd htr hn d e hG).system.permutes := by
  let bl := rawMinBlocks (gs, dom)
  let hmin := isMinimalSystemOfImprimitivity_rawMinBlocks hw hd htr hn
  have hcomp : (Equiv.permCongrHom (camMinBlockEquiv hw hd htr hn d e hG)).toMonoidHom =
      (Equiv.permCongrHom (Babai.blockImageEquiv e (blockSets n bl))).toMonoidHom.comp
        (Equiv.permCongrHom (blockEquiv n bl (blocksWF_rawMinBlocks hd gs))).toMonoidHom := by
    apply MonoidHom.ext
    intro g
    rfl
  rw [hcomp]
  rw [← Subgroup.map_map (K := decGroup bl.length (rawBlockImgs (bl, gs)))
    (Equiv.permCongrHom (Babai.blockImageEquiv e (blockSets n bl))).toMonoidHom
    (Equiv.permCongrHom (blockEquiv n bl (blocksWF_rawMinBlocks hd gs))).toMonoidHom]
  rw [camBlockImgs_group (blocksWF_rawMinBlocks hd gs) hw hmin.permutes]
  have hh := Babai.map_onBlocks_permCongrHom e hmin.permutes
    (Babai.isSystemOfImprimitivity_map_permCongrHom e hmin.toIsSystemOfImprimitivity).permutes
  simpa only [hG] using hh

/-- Step 6 for a well-formed raw window action on computed minimal blocks.
The bijection `e` states how the raw window is encoded in the calling instance. -/
theorem camRawStepSix_data
    (cameron : RawGens × List ℕ → Option RawCameron)
    (hpoly : PolyFun cameron) (hspec : CameronSpec cameron)
    {n : ℕ} {gs : RawGens} {dom : List ℕ}
    (hw : RawGens.WF n gs) (hd : dom.length = n)
    (htr : Babai.IsTransitive (decGroup n gs)) (hn : 2 ≤ n)
    (d : Babai.WindowData I) (e : Fin n ≃ I.Δ)
    (hG : (decGroup n gs).map (Equiv.permCongrHom e).toMonoidHom = d.windowGroup)
    (hp : Babai.IsPrimitive
      (decGroup (rawMinBlocks (gs, dom)).length (rawBlockImgs (rawMinBlocks (gs, dom), gs))))
    (hb : ((rawMinBlocks (gs, dom)).length : ℝ) ^
        (1 + Real.logb 2 (rawMinBlocks (gs, dom)).length) ≤
      Nat.card (decGroup (rawMinBlocks (gs, dom)).length (rawBlockImgs (rawMinBlocks (gs, dom), gs))))
    (hm : max 25 camDescentThreshold ≤ (rawMinBlocks (gs, dom)).length)
    (hwindow : 64 ≤ I.windowSize) :
    ∃ (c : RawCameron) (h : c.WF (rawMinBlocks (gs, dom)).length)
        (D : Babai.DescentData I),
      camRecognizeBlocks cameron (gs, dom) = some c ∧
      D.blocks = camMinBlockData hw hd htr hn d e hG ∧ D.k = c.k ∧ D.t = c.t ∧
      HEq D.N ((decGroup (rawMinBlocks (gs, dom)).length
        (rawNbar (c, (rawBlockImgs (rawMinBlocks (gs, dom), gs))))).map
          (Equiv.permCongrHom (camMinBlockEquiv hw hd htr hn d e hG)).toMonoidHom) ∧
      HEq D.𝒞 (Babai.blockImage (camMinBlockEquiv hw hd htr hn d e hG)
        (blockSets (rawMinBlocks (gs, dom)).length (camBlocks c))) ∧
      D.N.relIndex (Babai.onBlocks D.blocks.windowGroup D.blocks.ℬ D.blocks.system.permutes) ≤
        (rawMinBlocks (gs, dom)).length ∧
      Real.logb 2 (rawMinBlocks (gs, dom)).length ≤ (c.k : ℝ) := by
  have hgw : RawGens.WF (rawMinBlocks (gs, dom)).length
      (rawBlockImgs (rawMinBlocks (gs, dom), gs)) := by
    have hh := camBlockInput_wf hw hd htr hn
    change RawGens.WF (blkDom (rawMinBlocks (gs, dom))).length _ at hh
    simpa only [length_blkDom] using hh
  exact camStepSix_data cameron hpoly hspec (camMinBlockData hw hd htr hn d e hG)
    (camMinBlockEquiv hw hd htr hn d e hG) _ _ (length_blkDom _) hgw
    (camMinBlockEquiv_group hw hd htr hn d e hG) hp hb hm hwindow

end Transport

/-- The step 6 contract is uniform in the raw instance and its window numbering. -/
def CameronDescentSpec (cameron : RawGens × List ℕ → Option RawCameron) : Prop :=
  ∀ {Ω A : Type} [Fintype Ω] [DecidableEq Ω] {I : Babai.SIInstance Ω A}
    {n : ℕ} {gs : RawGens} {dom : List ℕ}
    (hw : RawGens.WF n gs) (hd : dom.length = n)
    (htr : Babai.IsTransitive (decGroup n gs)) (hn : 2 ≤ n)
    (d : Babai.WindowData I) (e : Fin n ≃ I.Δ)
    (hG : (decGroup n gs).map (Equiv.permCongrHom e).toMonoidHom = d.windowGroup)
    (hp : Babai.IsPrimitive
      (decGroup (rawMinBlocks (gs, dom)).length (rawBlockImgs (rawMinBlocks (gs, dom), gs))))
    (hb : ((rawMinBlocks (gs, dom)).length : ℝ) ^
        (1 + Real.logb 2 (rawMinBlocks (gs, dom)).length) ≤
      Nat.card (decGroup (rawMinBlocks (gs, dom)).length (rawBlockImgs (rawMinBlocks (gs, dom), gs))))
    (hm : max 25 camDescentThreshold ≤ (rawMinBlocks (gs, dom)).length)
    (hwindow : 64 ≤ I.windowSize),
    ∃ (c : RawCameron) (h : c.WF (rawMinBlocks (gs, dom)).length)
        (D : Babai.DescentData I),
      camRecognizeBlocks cameron (gs, dom) = some c ∧
      D.blocks = camMinBlockData hw hd htr hn d e hG ∧ D.k = c.k ∧ D.t = c.t ∧
      HEq D.N ((decGroup (rawMinBlocks (gs, dom)).length
        (rawNbar (c, (rawBlockImgs (rawMinBlocks (gs, dom), gs))))).map
          (Equiv.permCongrHom (camMinBlockEquiv hw hd htr hn d e hG)).toMonoidHom) ∧
      HEq D.𝒞 (Babai.blockImage (camMinBlockEquiv hw hd htr hn d e hG)
        (blockSets (rawMinBlocks (gs, dom)).length (camBlocks c))) ∧
      D.N.relIndex (Babai.onBlocks D.blocks.windowGroup D.blocks.ℬ D.blocks.system.permutes) ≤
        (rawMinBlocks (gs, dom)).length ∧
      Real.logb 2 (rawMinBlocks (gs, dom)).length ≤ (c.k : ℝ)

/-- The parameterized recognition routine supplies the complete step 6 data contract. -/
theorem cameronDescentSpec_of
    (cameron : RawGens × List ℕ → Option RawCameron)
    (hpoly : PolyFun cameron) (hspec : CameronSpec cameron) : CameronDescentSpec cameron := by
  intro Ω A _ _ I n gs dom hw hd htr hn d e hG hp hb hm hwindow
  exact camRawStepSix_data cameron hpoly hspec hw hd htr hn d e hG hp hb hm hwindow

/-- Closed form: one polynomial recognition routine works for every step 6 instance. -/
theorem exists_polyFun_cameronDescentSpec :
    ∃ cameron : RawGens × List ℕ → Option RawCameron,
      PolyFun cameron ∧ CameronSpec cameron ∧ CameronDescentSpec cameron := by
  obtain ⟨cameron, hpoly, hspec⟩ := exists_polyFun_cameronSpec
  exact ⟨cameron, hpoly, hspec, cameronDescentSpec_of cameron hpoly hspec⟩

end Algo

#print axioms Algo.camRawStepSix_data
#print axioms Algo.exists_polyFun_cameronDescentSpec
