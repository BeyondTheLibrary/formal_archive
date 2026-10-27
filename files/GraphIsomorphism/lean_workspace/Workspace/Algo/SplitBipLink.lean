import Workspace.Algo.SplitBipIndex
import Workspace.SplitOrJohnson.Step78
import Workspace.SplitOrJohnson.Step8

/-!
# Section 9.4, steps 7 and 8: the first useful link colors

Step 7 compares every pair color in a second-part class. The class is useful
exactly when its link has more than one color. Step 8 chooses the least color
occurring on the retained link. Both minima scan realized colors only.
-/

namespace Algo
open Babai RAM

/-- At most one value occurs in this list. -/
def sbipUniform (l : List ℕ) : Bool :=
  upccCaseAllB (fun z : ℕ × ℕ => decide (z.1 = z.2)) (l.headD 0,l)

theorem sbipPoly_uniform : PolyFun sbipUniform := by
  have hh : PolyFun (fun l : List ℕ => l.headD 0) :=
    (((polyFun_headOption.pair (polyFun_const 0)).comp polyFun_optionGetD)).of_eq
      (fun _ => List.headD_eq_head?_getD.symm)
  exact (hh.pair polyFun_id).comp (upccCasePoly_all polyFun_natEq)

theorem sbipUniform_spec (l : List ℕ) :
    sbipUniform l = true ↔ ∀ a ∈ l, ∀ b ∈ l, a = b := by
  simp only [sbipUniform,upccCaseAllB_spec,decide_eq_true_eq]
  constructor
  · intro h a ha b hb; exact (h a ha).symm.trans (h b hb)
  · intro h b hb
    cases l with
    | nil => simp at hb
    | cons a l => exact h a (List.mem_cons_self) b hb

/-- Pair colors on the two supplied parts. -/
def sbipLinkColors (r : RawUpccCase) : List ℕ :=
  (r.2.1.product r.2.2).map (fun q => binColor (r.1,q))

theorem sbipPoly_linkColors : PolyFun sbipLinkColors :=
  (polyFun_fst.pair (polyFun_snd.comp GIReduction.polyFun_product)).comp
    (PolyFun.mapParam polyFun_binColor)

theorem sbipLinkColors_mem (r : RawUpccCase) (k : ℕ) :
    k ∈ sbipLinkColors r ↔ ∃ u ∈ r.2.1, ∃ v ∈ r.2.2, binColor (r.1,(u,v)) = k := by
  simp only [sbipLinkColors,List.mem_map,Prod.exists]
  constructor
  · rintro ⟨u,v,huv,hc⟩
    exact ⟨u,(List.mem_product.mp huv).1,v,(List.mem_product.mp huv).2,hc⟩
  · rintro ⟨u,hu,v,hv,hc⟩
    exact ⟨u,v,List.mem_product.mpr ⟨hu,hv⟩,hc⟩

/-- A second-part class, using the unshifted diagonal names of step 7. -/
def sbipSecondClass (z : RawUpccCase × ℕ) : List ℕ :=
  sbipClass ((z.1.1,z.1.2.2),z.2 + 1)

theorem sbipPoly_secondClass : PolyFun sbipSecondClass :=
  (((polyFun_fst.comp polyFun_fst).pair
    ((polyFun_fst.comp polyFun_snd).comp polyFun_snd)).pair
      (polyFun_snd.add (polyFun_const 1))).comp sbipPoly_class

theorem sbipSecondClass_mem (r : RawUpccCase) (k u : ℕ) :
    u ∈ sbipSecondClass (r,k) ↔ u ∈ r.2.2 ∧ binColor (r.1,(u,u)) = k := by
  simp [sbipSecondClass,sbipClass_mem,sbipDiag]

/-- A class passes when its link has two distinct pair colors. -/
def sbipUseful (z : RawUpccCase × ℕ) : Bool :=
  !sbipUniform (sbipLinkColors (z.1.1,(z.1.2.1,sbipSecondClass z)))

theorem sbipPoly_useful : PolyFun sbipUseful :=
  polyFun_rawJNot (((((polyFun_fst.comp polyFun_fst).pair
    (((polyFun_fst.comp polyFun_snd).comp polyFun_fst).pair sbipPoly_secondClass)).comp
      sbipPoly_linkColors).comp sbipPoly_uniform))

/-- Second-part diagonal colors, keeping repetitions. -/
def sbipSecondColors (r : RawUpccCase) : List ℕ :=
  r.2.2.map (fun v => binColor (r.1,(v,v)))

theorem sbipPoly_secondColors : PolyFun sbipSecondColors :=
  (polyFun_fst.pair (polyFun_snd.comp polyFun_snd)).comp
    (PolyFun.mapParam ((polyFun_fst.pair (polyFun_snd.pair polyFun_snd)).comp polyFun_binColor))

/-- Section 9.4, step 7: all nontrivial second-part classes. -/
def sbipUsefulColors (r : RawUpccCase) : List ℕ :=
  (sbipSecondColors r).filter (fun k => sbipUseful (r,k))

theorem sbipPoly_usefulColors : PolyFun sbipUsefulColors :=
  (polyFun_id.pair sbipPoly_secondColors).comp (PolyFun.filterParam sbipPoly_useful)

/-- Section 9.4, step 7: the first nontrivial class. -/
def sbipFirstNontrivial (r : RawUpccCase) : ℕ := upccCaseLeast (sbipUsefulColors r)

theorem sbipPoly_firstNontrivial : PolyFun sbipFirstNontrivial :=
  sbipPoly_usefulColors.comp upccCasePoly_least

/-- Section 9.4, step 7: retain the selected second-part class. -/
def sbipStep7Right (r : RawUpccCase) : List ℕ := sbipSecondClass (r,sbipFirstNontrivial r)

theorem sbipPoly_step7Right : PolyFun sbipStep7Right :=
  (polyFun_id.pair sbipPoly_firstNontrivial).comp sbipPoly_secondClass

/-- Section 9.4, step 7: the induced table and its parts. -/
def sbipStep7 (r : RawUpccCase) : RawUpccCase :=
  (sbipInduced (r.1,r.2.1 ++ sbipStep7Right r),(r.2.1,sbipStep7Right r))

theorem sbipPoly_step7 : PolyFun sbipStep7 := by
  have hl : PolyFun (fun r : RawUpccCase => r.2.1) := polyFun_snd.comp polyFun_fst
  exact ((polyFun_fst.pair ((hl.pair sbipPoly_step7Right).comp polyFun_append)).comp
    sbipPoly_induced).pair (hl.pair sbipPoly_step7Right)

/-- Section 9.4, step 8: the first color involved in the link. -/
def sbipFirstInvolved (r : RawUpccCase) : ℕ := upccCaseLeast (sbipLinkColors r)

theorem sbipPoly_firstInvolved : PolyFun sbipFirstInvolved :=
  sbipPoly_linkColors.comp upccCasePoly_least

/-- A least-list scan agrees with the mathematical infimum. -/
theorem sbipLeast_sInf (l : List ℕ) (S : Set ℕ) (hs : S.Nonempty)
    (hm : ∀ k, k ∈ l ↔ k ∈ S) : upccCaseLeast l = sInf S := by
  have hne : l ≠ [] := by
    obtain ⟨k,hk⟩ := hs
    intro he
    have := (hm k).2 hk
    simpa [he] using this
  obtain ⟨hc,hmin⟩ := upccCaseLeast_spec l hne
  exact le_antisymm (hmin _ ((hm _).2 (Nat.sInf_mem hs))) (Nat.sInf_le ((hm _).1 hc))

section Specification
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (X : Pt (BipBlockInputs Ω)) (name₁ : ↥(dominantClass X) → ℕ)
    (name₂ : ↥X.obj.1.1.blocks → ℕ) (r : RawUpccCase)

/-- The named link after step 5. Pair names and diagonal names are from the
original step-3 coloring, as `step7BlkColor` and `step8Colors` require. -/
structure SbipLinkNames : Prop where
  left : ∀ a, a ∈ r.2.1 ↔ ∃ x, name₁ x = a
  right : ∀ b, b ∈ r.2.2 ↔ ∃ B, name₂ B = b
  diagonal : ∀ B, binColor (r.1,(name₂ B,name₂ B)) = step7BlkColor X B.val
  link : ∀ x B, binColor (r.1,(name₁ x,name₂ B)) =
    VColBipBlk.wlCaseColor X.obj.1.1 {x.val} B.val

variable {X name₁ name₂ r} (h : SbipLinkNames X name₁ name₂ r)
include h

/-- Section 9.4, step 7: the class scan lists precisely the class with color `k`. -/
theorem sbipSecondClass_spec (k : ℕ) (B : ↥X.obj.1.1.blocks) :
    name₂ B ∈ sbipSecondClass (r,k) ↔ step7BlkColor X B.val = k := by
  rw [sbipSecondClass_mem,h.diagonal]
  exact and_iff_right ((h.right _).2 ⟨B,rfl⟩)

/-- Section 9.4, step 7: the Boolean link test is exactly `LinkTrivialOn`. -/
theorem sbipUseful_spec (k : ℕ) : sbipUseful (r,k) = true ↔ ¬ LinkTrivialOn X k := by
  have ht : sbipUniform (sbipLinkColors (r.1,(r.2.1,sbipSecondClass (r,k)))) = true ↔
      LinkTrivialOn X k := by
    rw [sbipUniform_spec]
    constructor
    · intro hh x hx y hy B hB C hC hBk hCk
      have hraw := hh _ ((sbipLinkColors_mem _ _).2 ⟨name₁ ⟨x,hx⟩,(h.left _).2 ⟨_,rfl⟩,
        name₂ ⟨B,hB⟩,(sbipSecondClass_spec h k _).2 hBk,rfl⟩)
        _ ((sbipLinkColors_mem _ _).2 ⟨name₁ ⟨y,hy⟩,(h.left _).2 ⟨_,rfl⟩,
          name₂ ⟨C,hC⟩,(sbipSecondClass_spec h k _).2 hCk,rfl⟩)
      rw [h.link,h.link] at hraw
      exact (VColBipBlk.wlCaseColor_eq_iff_raw X.obj.1.1
        ⟨Or.inl ⟨x,hx.1,rfl⟩,Or.inr hB⟩ ⟨Or.inl ⟨y,hy.1,rfl⟩,Or.inr hC⟩).1 hraw
    · intro hh a ha b hb
      obtain ⟨u,hu,v,hv,rfl⟩ := (sbipLinkColors_mem _ _).1 ha
      obtain ⟨w,hw,z,hz,rfl⟩ := (sbipLinkColors_mem _ _).1 hb
      obtain ⟨x,rfl⟩ := (h.left _).1 hu
      obtain ⟨y,rfl⟩ := (h.left _).1 hw
      obtain ⟨B,rfl⟩ := (h.right _).1 ((sbipSecondClass_mem _ _ _).1 hv).1
      obtain ⟨C,rfl⟩ := (h.right _).1 ((sbipSecondClass_mem _ _ _).1 hz).1
      rw [h.link,h.link]
      exact (VColBipBlk.wlCaseColor_eq_iff_raw X.obj.1.1
        ⟨Or.inl ⟨x.val,x.property.1,rfl⟩,Or.inr B.property⟩
        ⟨Or.inl ⟨y.val,y.property.1,rfl⟩,Or.inr C.property⟩).2
          (hh _ x.property _ y.property _ B.property _ C.property
            ((sbipSecondClass_spec h k B).1 hv) ((sbipSecondClass_spec h k C).1 hz))
  simp only [sbipUseful,Bool.not_eq_true',Bool.eq_false_iff,ne_eq,ht]

/-- The candidates match the mathematical set of useful second-part colors. -/
theorem sbipUsefulColors_spec (k : ℕ) : k ∈ sbipUsefulColors r ↔ k ∈ step7Colors X := by
  have hm : k ∈ sbipSecondColors r ↔ ∃ B ∈ X.obj.1.1.blocks, step7BlkColor X B = k := by
    simp only [sbipSecondColors,List.mem_map]
    constructor
    · rintro ⟨b,hb,hc⟩
      obtain ⟨B,rfl⟩ := (h.right _).1 hb
      exact ⟨B.val,B.property,(h.diagonal B).symm.trans hc⟩
    · rintro ⟨B,hB,hc⟩
      exact ⟨name₂ ⟨B,hB⟩,(h.right _).2 ⟨_,rfl⟩,(h.diagonal _).trans hc⟩
  simp only [sbipUsefulColors,List.mem_filter,hm,sbipUseful_spec h,step7Colors,Set.mem_setOf_eq]

/-- Section 9.4, step 7: the chosen integer is `step7Color`. -/
theorem sbipFirstNontrivial_spec (hd : ¬ AllClassesSmall X) :
    sbipFirstNontrivial r = step7Color X :=
  sbipLeast_sInf _ _ (step7Colors_nonempty X hd) (sbipUsefulColors_spec h)

/-- Section 9.4, step 7: the retained blocks are exactly `step7Blocks`. -/
theorem sbipStep7Right_spec (hd : ¬ AllClassesSmall X) (B : ↥X.obj.1.1.blocks) :
    name₂ B ∈ sbipStep7Right r ↔ B.val ∈ step7Blocks X := by
  rw [sbipStep7Right,sbipFirstNontrivial_spec h hd,sbipSecondClass_spec h]
  exact (and_iff_right B.property).symm

/-- Section 9.4, step 8: the retained link realizes exactly `step8Colors`. -/
theorem sbipStep8Colors_spec (hd : ¬ AllClassesSmall X) (k : ℕ) :
    k ∈ sbipLinkColors (r.1,(r.2.1,sbipStep7Right r)) ↔ k ∈ step8Colors X := by
  rw [sbipLinkColors_mem]
  constructor
  · rintro ⟨u,hu,v,hv,hc⟩
    obtain ⟨x,rfl⟩ := (h.left _).1 hu
    obtain ⟨B,rfl⟩ := (h.right _).1 ((sbipSecondClass_mem _ _ _).1 hv).1
    exact ⟨x.val,x.property,B.val,(sbipStep7Right_spec h hd B).1 hv,(h.link x B).symm.trans hc⟩
  · rintro ⟨x,hx,B,hB,hc⟩
    exact ⟨name₁ ⟨x,hx⟩,(h.left _).2 ⟨_,rfl⟩,name₂ ⟨B,hB.1⟩,
      (sbipStep7Right_spec h hd _).2 hB,(h.link _ _).trans hc⟩

/-- Section 9.4, step 8: the first involved color is exactly `step8Color`. -/
theorem sbipFirstInvolved_spec (hd : ¬ AllClassesSmall X) :
    sbipFirstInvolved (r.1,(r.2.1,sbipStep7Right r)) = step8Color X :=
  sbipLeast_sInf _ _ (step8Colors_nonempty X hd) (sbipStep8Colors_spec h hd)

end Specification
/-- The link for steps 7–8, read on the original table after selecting `W₁`. -/
def sbipLinkInput (r : RawSbipStep5Input) : RawUpccCase :=
  (r.1.1.1.1,(sbipDominant r.1.1,r.1.2))

theorem sbipPoly_linkInput : PolyFun sbipLinkInput := by
  have hc : PolyFun (fun r : RawSbipStep5Input => r.1.1) := polyFun_fst.comp polyFun_fst
  exact ((hc.comp polyFun_fst).comp polyFun_fst).pair
    ((hc.comp sbipPoly_dominant).pair (polyFun_fst.comp polyFun_snd))

/-- The names needed by steps 7–8 follow from the initial table and step 3. -/
theorem sbipLinkInput_names {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    {X : Pt (BipBlockInputs Ω)} {n : ℕ} {e : X.obj.1.1.Vtx ≃ Fin n}
    {r : RawSbipStep5Input} (h : SbipNamedInput X e r.1.1)
    (hr : sbipNamedBlock X e '' Set.univ = {a | a ∈ r.1.2}) (hd : ¬ AllClassesSmall X) :
    SbipLinkNames X (fun x => sbipNamedPoint X e ⟨x.val,x.property.1⟩)
      (sbipNamedBlock X e) (sbipLinkInput (sbipPrepare r)) := by
  have hc (A B : X.obj.1.1.Vtx) :
      binColor (sbipStep3 r.1.1.1.1,(e A,e B)) = VColBipBlk.wlCaseColor X.obj.1.1 A.val B.val := by
    rw [VColBipBlk.wlCaseColor,dif_pos ⟨A.property,B.property⟩]
    exact sbipStep3_named X.obj.1.1 e h.table h.initial A B
  refine ⟨?_,?_,?_,?_⟩
  · intro a
    change a ∈ sbipDominant (sbipNamedClasses r.1.1) ↔ _
    constructor
    · intro ha
      obtain ⟨x,rfl⟩ := sbipName_surj (sbipNamedClasses_names h) (List.mem_of_mem_filter ha)
      exact ⟨⟨x.val,(sbipNamedClasses_dominant h hd x).1 ha⟩,rfl⟩
    · rintro ⟨x,rfl⟩
      exact (sbipNamedClasses_dominant h hd ⟨x.val,x.property.1⟩).2 x.property
  · intro b
    change b ∈ r.1.2 ↔ _
    rw [← show b ∈ sbipNamedBlock X e '' Set.univ ↔ b ∈ r.1.2 from by rw [hr]; rfl]
    simp
  · intro B
    exact hc ⟨B.val,Or.inr B.property⟩ ⟨B.val,Or.inr B.property⟩
  · intro x B
    exact hc ⟨{x.val},Or.inl ⟨x.val,x.property.1,rfl⟩⟩ ⟨B.val,Or.inr B.property⟩

end Algo
