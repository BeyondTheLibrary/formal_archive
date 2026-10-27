import Workspace.Algo.SplitBipLinkTransport
import Workspace.Algo.SplitUpccCaseOutcome
import Workspace.Algo.SplitUpccCaseTransport
import Workspace.SplitOrJohnson.Step9Func

/-!
# Section 9.4, step 9: the three cases

Test imprimitivity first. Otherwise test whether all off-diagonal pairs have
one color. The remaining case is UPCC. The design branch is a named parameter.
The imprimitive branch has the same interface, to be filled by Section 9.6.
The UPCC branch calls the implementation of Section 9.8.
-/

namespace Algo
open Babai RAM

/-- Off-diagonal pair colors on positions in a supplied domain. -/
def sbipOffColors (p : RawConfig) : List ℕ :=
  ((labPairsList p.1).filter (fun q => decide (q.1 ≠ q.2))).map (fun q => binColor (p,q))

theorem sbipPoly_offColors : PolyFun sbipOffColors :=
  (polyFun_id.pair ((polyFun_fst.comp polyFun_labPairsList).comp
    (PolyFun.filter polyFun_upccNatNe))).comp (PolyFun.mapParam polyFun_binColor)

theorem sbipOffColors_mem (p : RawConfig) (k : ℕ) :
    k ∈ sbipOffColors p ↔ ∃ u v : Fin p.1.length, u ≠ v ∧ namedBin p.1.length p u v = k := by
  simp only [sbipOffColors,List.mem_map,Prod.exists,List.mem_filter,mem_labPairsList,decide_eq_true_eq]
  constructor
  · rintro ⟨u,v,⟨⟨hu,hv⟩,hne⟩,hc⟩
    exact ⟨⟨u,hu⟩,⟨v,hv⟩,fun h => hne (congrArg Fin.val h),hc⟩
  · rintro ⟨u,v,hne,hc⟩
    exact ⟨u,v,⟨⟨u.isLt,v.isLt⟩,fun h => hne (Fin.ext h)⟩,hc⟩

/-- Section 9.4, step 9(ii): all off-diagonal pairs have the same color. -/
def sbipClique (p : RawConfig) : Bool := sbipUniform (sbipOffColors p)

theorem sbipPoly_clique : PolyFun sbipClique := sbipPoly_offColors.comp sbipPoly_uniform

theorem sbipClique_spec (p : RawConfig) :
    sbipClique p = true ↔ ∀ u v a b : Fin p.1.length, u ≠ v → a ≠ b →
      namedBin p.1.length p u v = namedBin p.1.length p a b := by
  rw [sbipClique,sbipUniform_spec]
  constructor
  · intro h u v a b huv hab
    exact h _ ((sbipOffColors_mem _ _).2 ⟨u,v,huv,rfl⟩)
      _ ((sbipOffColors_mem _ _).2 ⟨a,b,hab,rfl⟩)
  · intro h k hk j hj
    obtain ⟨u,v,huv,rfl⟩ := (sbipOffColors_mem _ _).1 hk
    obtain ⟨a,b,hab,rfl⟩ := (sbipOffColors_mem _ _).1 hj
    exact h u v a b huv hab

/-- Section 9.4, step 9: tags zero, one, two mean imprimitive, design, UPCC. -/
def sbipCase (p : RawConfig) : ℕ :=
  if sbipImprimitive p then 0 else if sbipClique p then 1 else 2

theorem sbipPoly_case : PolyFun sbipCase :=
  PolyFun.ite sbipPoly_imprimitive (polyFun_const 0)
    (PolyFun.ite sbipPoly_clique (polyFun_const 1) (polyFun_const 2))

/-- The case test reads `X₂` by its second-part positions. -/
def sbipStep9Case (r : RawUpccCase) : ℕ := sbipCase (sbipIndexed (r.1,r.2.2))

theorem sbipPoly_step9Case : PolyFun sbipStep9Case :=
  ((polyFun_fst.pair (polyFun_snd.comp polyFun_snd)).comp sbipPoly_indexed).comp sbipPoly_case

/-- The three tags agree with the conditions of `step9ImpFunc`, `step9DesignFunc`,
and `step9UPCCFunc`. The common conditions of reaching step 9 are kept by the caller. -/
theorem sbipCase_spec {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (X : Pt (BipBlockInputs Ω)) (p : RawConfig) {n : ℕ} (hlen : p.1.length = n)
    (e : ↥(step8Blks X) ≃ Fin n)
    (hn : ∀ u v, binColor (p,(e u,e v)) = step9BlkColor X u v) :
    (sbipCase p = 0 ↔ Step9Imprimitive X) ∧
    (sbipCase p = 1 ↔ ¬ Step9Imprimitive X ∧ Step9Clique X) ∧
    (sbipCase p = 2 ↔ ¬ Step9Imprimitive X ∧ ¬ Step9Clique X) := by
  subst n
  have hi : sbipImprimitive p = true ↔ Step9Imprimitive X := by
    rw [sbipImprimitive_spec,Step9Imprimitive]
    exact exists_congr (fun k => isDisconnectedColor_map e hn k)
  have hc : sbipClique p = true ↔ Step9Clique X := by
    rw [sbipClique_spec]
    constructor
    · intro h u v a b huv hab
      simpa only [namedBin,hn] using h (e u) (e v) (e a) (e b)
        (fun he => huv (e.injective he)) (fun he => hab (e.injective he))
    · intro h u v a b huv hab
      have hh := h (e.symm u) (e.symm v) (e.symm a) (e.symm b)
        (fun he => huv (e.symm.injective he)) (fun he => hab (e.symm.injective he))
      simpa only [← hn,Equiv.apply_symm_apply] using hh
  cases he : sbipImprimitive p <;> cases hf : sbipClique p <;>
    simp_all [sbipCase]

/-- Section 9.4, step 9: specification on a whole named bipartite table. -/
theorem sbipStep9Case_spec {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (X : Pt (BipBlockInputs Ω)) (r : RawUpccCase)
    (e : ↥(step8Blks X) ≃ Fin r.2.2.length)
    (hn : ∀ u v, binColor (r.1,(r.2.2[(e u).val],r.2.2[(e v).val])) = step9BlkColor X u v) :
    (sbipStep9Case r = 0 ↔ Step9Imprimitive X) ∧
    (sbipStep9Case r = 1 ↔ ¬ Step9Imprimitive X ∧ Step9Clique X) ∧
    (sbipStep9Case r = 2 ↔ ¬ Step9Imprimitive X ∧ ¬ Step9Clique X) := by
  apply sbipCase_spec X _ (sbipIndexed_length _ _) e
  intro u v
  rw [sbipIndexed_get]
  exact hn u v

/-- Dispatch a width. The design and imprimitive cases remain named parameters. -/
def sbipStep9Width (imprimitiveWidth designWidth : RawUpccCase → ℕ) (r : RawUpccCase) : ℕ :=
  if sbipStep9Case r = 0 then imprimitiveWidth r
  else if sbipStep9Case r = 1 then designWidth r else UpccCase.widthF r

/-- Dispatch one version. The packaging map embeds a Section 9.8 raw outcome
in the common outcome type chosen by the caller. -/
def sbipStep9Version {β : Type*} (imprimitiveVersion designVersion : RawUpccCase × ℕ → β)
    (packageUPCC : RawUpccCaseOutcome → β) (z : RawUpccCase × ℕ) : β :=
  if sbipStep9Case z.1 = 0 then imprimitiveVersion z
  else if sbipStep9Case z.1 = 1 then designVersion z else packageUPCC (UpccCase.versionF z)

theorem sbipPoly_step9Width {imprimitiveWidth designWidth : RawUpccCase → ℕ}
    (hi : PolyFun imprimitiveWidth) (hd : PolyFun designWidth) :
    PolyFun (sbipStep9Width imprimitiveWidth designWidth) := by
  exact (PolyFun.ite (sbipPoly_step9Case.natEq (polyFun_const 0)) hi
    (PolyFun.ite (sbipPoly_step9Case.natEq (polyFun_const 1)) hd UpccCase.polyFun_widthF)).of_eq
      (fun r => by simp [sbipStep9Width])

theorem sbipPoly_step9Version {β : Type*} [Enc β]
    {imprimitiveVersion designVersion : RawUpccCase × ℕ → β} {packageUPCC : RawUpccCaseOutcome → β}
    (hi : PolyFun imprimitiveVersion) (hd : PolyFun designVersion) (hu : PolyFun packageUPCC) :
    PolyFun (sbipStep9Version imprimitiveVersion designVersion packageUPCC) := by
  have hc : PolyFun (fun z : RawUpccCase × ℕ => sbipStep9Case z.1) :=
    polyFun_fst.comp sbipPoly_step9Case
  exact (PolyFun.ite (hc.natEq (polyFun_const 0)) hi
    (PolyFun.ite (hc.natEq (polyFun_const 1)) hd (UpccCase.polyFun_versionF.comp hu))).of_eq
      (fun r => by simp [sbipStep9Version])

/-- Section 9.4, step 9(iii): the width is the width of the Section 9.8 routine. -/
theorem sbipStep9Width_upcc (iw dw : RawUpccCase → ℕ) {r : RawUpccCase}
    (h : sbipStep9Case r = 2) : sbipStep9Width iw dw r = UpccCase.widthF r := by
  simp [sbipStep9Width,h]

/-- Section 9.4, step 9(iii): every indexed version is the implemented UPCC version. -/
theorem sbipStep9Version_upcc {β : Type*} (iv dv : RawUpccCase × ℕ → β)
    (pack : RawUpccCaseOutcome → β) {r : RawUpccCase} (h : sbipStep9Case r = 2) (i : ℕ) :
    sbipStep9Version iv dv pack (r,i) = pack (UpccCase.versionF (r,i)) := by
  simp [sbipStep9Version,h]

/-- The UPCC branch has the full valid-outcome specification from Section 9.8.
Its mathematical input is precisely the object of `step9UPCCFunc`. -/
theorem sbipStep9_upcc_spec_index {Ω : Type} [Fintype Ω] [DecidableEq Ω] {N : ℕ}
    (X : Pt (Step9UPCCInputs Ω N)) {n : ℕ}
    (e : ↥((step9UPCCFunc N).obj X).obj.vtxSet ≃ Fin n)
    {r : RawUpccCase} (hw : r.WF) (hn : UpccCaseNames ((step9UPCCFunc N).obj X).obj e r)
    (hcase : sbipStep9Case r = 2) (iw dw : RawUpccCase → ℕ) {i : ℕ}
    (hi : i < sbipStep9Width iw dw r) :
    ∃ Z : Pt (Cat.sum (ColoredPartitions Ω ℕ) (VColBlkGraphs Ω ℕ)),
      UpccCaseOutcomeRep ((step9UPCCFunc N).obj X).obj e (UpccCase.versionF (r,i)) Z ∧
        IsBlkImprimitiveOutcome (BlkCases.V₁ ((step9UPCCFunc N).obj X))
          (BlkCases.numBlocks ((step9UPCCFunc N).obj X)) Z := by
  rw [sbipStep9Width_upcc iw dw hcase] at hi
  exact UpccCase.versionF_spec_index ((step9UPCCFunc N).obj X) e hw hn hi

end Algo
