import Workspace.Algo.SplitDesignDominant

/-! # Section 9.7: complementary trace pairs

At the half-rank boundary the output groups a trace with its complement
inside the large twin class. The pair is unordered. Outside the dominant
class the original local color classes stay whole.
-/
namespace Algo
open Babai RAM

def designLocalComp (z : RawUpccCase × ℕ) : List ℕ :=
  (designBigPositions z.1).filter (fun i => !decide (i ∈ designLocalRow z))

def designDomPairEq (z : RawDesignLocal × (ℕ × ℕ)) : Bool :=
  if designDomTest (z.1,z.2.1) then
    if designDomTest (z.1,z.2.2) then
      decide (designLocalRow (z.1.1,z.2.1) = designLocalRow (z.1.1,z.2.2)) ||
      decide (designLocalRow (z.1.1,z.2.1) = designLocalComp (z.1.1,z.2.2))
    else false
  else !designDomTest (z.1,z.2.2)

def designPairPartition (z : RawDesignLocal) : RawColPart :=
  (designLocalColors z.1,relationLabRaw designDomPairEq (z,z.1.2.1))

theorem polyFun_designLocalComp : PolyFun designLocalComp := by
  have ht : PolyFun (fun z : (RawUpccCase × ℕ) × ℕ => !decide (z.2 ∈ designLocalRow z.1)) :=
    polyFun_rawJNot ((polyFun_snd.pair (polyFun_fst.comp polyFun_designLocalRow)).comp
      (polyFun_listMem polyFun_natEq))
  exact (polyFun_id.pair (polyFun_fst.comp polyFun_designBigPositions)).comp
    (PolyFun.filterParam ht)

theorem polyFun_designDomPairEq : PolyFun designDomPairEq := by
  have hx : PolyFun (fun z : RawDesignLocal × (ℕ × ℕ) => (z.1,z.2.1)) :=
    polyFun_fst.pair (polyFun_snd.comp polyFun_fst)
  have hy : PolyFun (fun z : RawDesignLocal × (ℕ × ℕ) => (z.1,z.2.2)) :=
    polyFun_fst.pair (polyFun_snd.comp polyFun_snd)
  have hrow : PolyFun (fun z : RawDesignLocal × ℕ => designLocalRow (z.1.1,z.2)) :=
    ((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp polyFun_designLocalRow
  have hcmp : PolyFun (fun z : RawDesignLocal × ℕ => designLocalComp (z.1.1,z.2)) :=
    ((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp polyFun_designLocalComp
  have hor : PolyFun (fun z : RawDesignLocal × (ℕ × ℕ) =>
      decide (designLocalRow (z.1.1,z.2.1) = designLocalRow (z.1.1,z.2.2)) ||
      decide (designLocalRow (z.1.1,z.2.1) = designLocalComp (z.1.1,z.2.2))) :=
    (PolyFun.ite (((hx.comp hrow).pair (hy.comp hrow)).comp polyFun_listNatEq)
      (polyFun_const true) (((hx.comp hrow).pair (hy.comp hcmp)).comp polyFun_listNatEq)).of_eq
        (fun z => by by_cases hh : designLocalRow (z.1.1,z.2.1) =
          designLocalRow (z.1.1,z.2.2) <;> simp [hh])
  exact PolyFun.ite (hx.comp polyFun_designDomTest)
    (PolyFun.ite (hy.comp polyFun_designDomTest)
      hor
      (polyFun_const false)) (polyFun_rawJNot (hy.comp polyFun_designDomTest))

theorem polyFun_designPairPartition : PolyFun designPairPartition :=
  (polyFun_fst.comp polyFun_designLocalColors).pair
    ((polyFun_id.pair ((polyFun_fst.comp polyFun_snd).comp polyFun_fst)).comp
      (polyFun_relationLabRaw polyFun_designDomPairEq))

section Specification
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {X : BlkDesignObj s} {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {r : RawUpccCase} (h : DesignNames X name₁ name₂ r)
    (e₁ : ↥X.Pt₁ ≃ Fin r.2.1.length) (he₁ : ∀ x, r.2.1[(e₁ x).val] = name₁ x)
    (e₂ : ↥X.blocks ≃ Fin r.2.2.length) (he₂ : ∀ B, r.2.2[(e₂ B).val] = name₂ B)
include h he₁ he₂

theorem designLocalComp_mem (x : ↥X.Pt₁) (B : ↥X.blocks) :
    (e₂ B).val ∈ designLocalComp (r,e₁ x) ↔
      B.val ∈ X.bigTwin \ (X.nbhd x.val ∩ X.bigTwin) := by
  simp only [designLocalComp,List.mem_filter,Bool.not_eq_true',decide_eq_false_iff_not,
    designBigPositions_spec h e₁ he₁ e₂ he₂,designLocalRow_mem h e₁ he₁ e₂ he₂,
    Set.mem_diff]

theorem designLocalRow_eq_comp (x y : ↥X.Pt₁) :
    designLocalRow (r,e₁ x) = designLocalComp (r,e₁ y) ↔
      X.nbhd x.val ∩ X.bigTwin = X.bigTwin \ (X.nbhd y.val ∩ X.bigTwin) := by
  constructor
  · intro hh
    ext B
    by_cases hB : B ∈ X.blocks
    · have hx := designLocalRow_mem h e₁ he₁ e₂ he₂ x ⟨B,hB⟩
      have hy := designLocalComp_mem h e₁ he₁ e₂ he₂ y ⟨B,hB⟩
      rw [hh] at hx
      exact hx.symm.trans hy
    · exact iff_of_false (fun hh => hB (X.nbhd_subset_blocks _ hh.1))
        (fun hh => hB (X.bigTwin_subset_blocks hh.1))
  · intro hh
    have hc : (designLocalComp (r,e₁ y)).Pairwise (· < ·) :=
      (List.pairwise_lt_range.filter _).filter _
    apply (designLocalRow_sorted r (e₁ x)).eq_of_mem_iff hc
    intro i
    by_cases hi : i < r.2.2.length
    · let B := e₂.symm ⟨i,hi⟩
      have hx := designLocalRow_mem h e₁ he₁ e₂ he₂ x B
      have hy := designLocalComp_mem h e₁ he₁ e₂ he₂ y B
      rw [hh] at hx
      simpa only [B,Equiv.apply_symm_apply] using hx.trans hy.symm
    · exact iff_of_false (fun hh => hi (designLocalRow_lt hh))
        (fun hh => hi (List.mem_range.1
          (List.mem_of_mem_filter (List.mem_of_mem_filter hh))))

omit h he₁ he₂ in
/-- Equality of two complementary pairs is decided by either possible image of the first trace. -/
theorem designTracePair_eq (x y : ↥X.Pt₁) :
    ({X.nbhd x.val ∩ X.bigTwin,X.bigTwin \ (X.nbhd x.val ∩ X.bigTwin)} : Set (Set (Set ↥s))) =
      {X.nbhd y.val ∩ X.bigTwin,X.bigTwin \ (X.nbhd y.val ∩ X.bigTwin)} ↔
    X.nbhd x.val ∩ X.bigTwin = X.nbhd y.val ∩ X.bigTwin ∨
      X.nbhd x.val ∩ X.bigTwin = X.bigTwin \ (X.nbhd y.val ∩ X.bigTwin) := by
  rw [Set.pair_eq_pair_iff]
  constructor
  · exact fun hh => hh.elim (fun hh => Or.inl hh.1) (fun hh => Or.inr hh.1)
  · intro hh
    rcases hh with hh | hh
    · exact Or.inl ⟨hh,congrArg (fun T => X.bigTwin \ T) hh⟩
    · refine Or.inr ⟨hh,?_⟩
      rw [hh]
      ext B
      simp only [Set.mem_diff,Set.mem_inter_iff]
      tauto

theorem designDomPairEq_spec (p : ℕ × ℕ) (hb : 0 < p.2) (x y : ↥X.Pt₁) :
    designDomPairEq ((r,p),(e₁ x,e₁ y)) = true ↔
      X.domPairLab (sbipAlphaValue p) x.val = X.domPairLab (sbipAlphaValue p) y.val := by
  classical
  have hx := designDomTest_spec h e₁ he₁ e₂ he₂ p hb x
  have hy := designDomTest_spec h e₁ he₁ e₂ he₂ p hb y
  by_cases hx' : designDomTest ((r,p),e₁ x) = true <;>
    by_cases hy' : designDomTest ((r,p),e₁ y) = true <;>
    simp_all [designDomPairEq,BlkCaseObj.domPairLab,
      designLocalRow_eq h e₁ he₁ e₂ he₂,designLocalRow_eq_comp h e₁ he₁ e₂ he₂]
  · simpa using (designTracePair_eq x y).symm
  · exact (Set.insert_nonempty _ _).ne_empty
  · exact Ne.symm (Set.insert_nonempty _ _).ne_empty

theorem designPairPartition_spec (p : ℕ × ℕ) (hb : 0 < p.2) :
    RawColPart.WF r.2.1.length (designPairPartition (r,p)) ∧
    (∀ x : ↥X.Pt₁, labAt (designPairPartition (r,p)).1 (e₁ x) = X.localSize x.val) ∧
    (∀ x y : ↥X.Pt₁, (decColPartition r.2.1.length (designPairPartition (r,p))).part
        (e₁ x) (e₁ y) ↔
      (labPartition X.Pt₁ X.localSize (X.domPairLab (sbipAlphaValue p))).part
        (mkPt x.property) (mkPt y.property)) := by
  refine ⟨⟨by simp [designPairPartition,designLocalColors],by simp [designPairPartition]⟩,
    fun x => designLocalColors_spec h e₁ he₁ e₂ he₂ x,?_⟩
  intro x y
  have hrel (u v : Fin r.2.1.length) :
      designDomPairEq ((r,p),(u,v)) = true ↔
        X.domPairLab (sbipAlphaValue p) (e₁.symm u).val =
          X.domPairLab (sbipAlphaValue p) (e₁.symm v).val := by
    simpa only [Equiv.apply_symm_apply] using
      designDomPairEq_spec h e₁ he₁ e₂ he₂ p hb (e₁.symm u) (e₁.symm v)
  have heq : Equivalence (fun u v : Fin r.2.1.length =>
      X.domPairLab (sbipAlphaValue p) (e₁.symm u).val =
        X.domPairLab (sbipAlphaValue p) (e₁.symm v).val) :=
    ⟨fun _ => rfl,fun hh => hh.symm,fun ha hb => ha.trans hb⟩
  have hh := relationLabRaw_spec rfl heq hrel (e₁ x) (e₁ y)
  change (labAt (designLocalColors r) (e₁ x),
    labAt (relationLabRaw designDomPairEq ((r,p),r.2.1)) (e₁ x)) =
    (labAt (designLocalColors r) (e₁ y),
    labAt (relationLabRaw designDomPairEq ((r,p),r.2.1)) (e₁ y)) ↔ _
  rw [Prod.mk.injEq,designLocalColors_spec h e₁ he₁ e₂ he₂,
    designLocalColors_spec h e₁ he₁ e₂ he₂]
  change (_ ∧ LabRel _ _ _) ↔ _
  rw [hh]
  simp only [Equiv.symm_apply_apply]
  constructor
  · rintro ⟨hc,hl⟩
    exact Prod.ext hc hl
  · intro hh
    exact ⟨congrArg Prod.fst hh,congrArg Prod.snd hh⟩

theorem designPairPartition_good (p : ℕ × ℕ) (hb : 0 < p.2)
    (hd : X.DomHyp (sbipAlphaValue p)) (ht : designHasDomTwins (r,p) ≠ true)
    (hbound : designDomBoundary (r,p) = true) (iF : Fintype ↥(Subtype.val '' X.Pt₁)) :
    @ColoredPartition.IsAlphaPartition _ _
      (labPartition X.Pt₁ X.localSize (X.domPairLab (sbipAlphaValue p))) iF (sbipAlphaValue p) := by
  obtain ⟨x,hx,hC⟩ := (designDomBoundary_spec h e₁ he₁ e₂ he₂ p hb).1 hbound
  apply hd.domPairPartition_isAlphaPartition iF ?_ hx hC
  intro u hu v hv he
  by_contra huv
  exact ht ((designHasDomTwins_spec h e₁ he₁ e₂ he₂ p hb).2 ⟨u,hu,v,hv,huv,he⟩)

end Specification
end Algo
