import Workspace.Algo.SplitDesignCases

/-! # Section 9.7: degree, arity, and complemented neighborhood rows

The first row reads the common degree. Complementing every row when that
degree exceeds half the second part gives the rank used by the formalized
Design Lemma proof.
-/
namespace Algo
open Babai RAM

def designDegree (r : RawUpccCase) : ℕ :=
  (splitNeighborhoodRow (designBip r,0)).length

theorem polyFun_designDegree : PolyFun designDegree :=
  (polyFun_designBip.pair (polyFun_const 0)).comp
    (polyFun_splitNeighborhoodRow.comp polyFun_length)

def designRank (r : RawUpccCase) : ℕ := min (designDegree r) (r.2.2.length - designDegree r)

theorem polyFun_designRank : PolyFun designRank :=
  polyFun_designDegree.min'
    (((polyFun_snd.comp polyFun_snd).comp polyFun_length).sub polyFun_designDegree)

/-- The rank is carried by a list when passed to the exponentiation routine. -/
def designRankWitness (r : RawUpccCase) : List ℕ := r.2.2.take (designRank r)

theorem polyFun_designRankWitness : PolyFun designRankWitness :=
  ((polyFun_snd.comp polyFun_snd).pair polyFun_designRank).comp polyFun_take

@[simp] theorem designRankWitness_length (r : RawUpccCase) :
    (designRankWitness r).length = designRank r := by
  rw [designRankWitness,List.length_take]
  exact min_eq_left ((min_le_right _ _).trans (Nat.sub_le _ _))

def designCase3a (r : RawUpccCase) : Bool := designSmallRank (r.2.1,designRankWitness r)

theorem polyFun_designCase3a : PolyFun designCase3a :=
  ((polyFun_snd.comp polyFun_fst).pair polyFun_designRankWitness).comp polyFun_designSmallRank

/-- Keep precisely the positions outside a listed subset. -/
def designComplementRow (z : List ℕ × List ℕ) : List ℕ :=
  (List.range z.1.length).filter (fun i => !decide (i ∈ z.2))

theorem polyFun_designComplementRow : PolyFun designComplementRow := by
  have hp : PolyFun (fun z : (List ℕ × List ℕ) × ℕ => !decide (z.2 ∈ z.1.2)) :=
    polyFun_rawJNot ((polyFun_snd.pair (polyFun_fst.comp polyFun_snd)).comp
      (polyFun_listMem polyFun_natEq))
  exact (polyFun_id.pair (polyFun_fst.comp polyFun_rangeLength)).comp (PolyFun.filterParam hp)

theorem designComplementRow_mem (dom row : List ℕ) (i : ℕ) :
    i ∈ designComplementRow (dom,row) ↔ i < dom.length ∧ i ∉ row := by
  simp [designComplementRow]

/-- Both the Design Lemma input and the Johnson labels use the smaller rank. -/
def designUseDirect (r : RawUpccCase) : Bool := decide (2 * designDegree r ≤ r.2.2.length)

theorem polyFun_designUseDirect : PolyFun designUseDirect :=
  ((polyFun_const 2).mul polyFun_designDegree).le
    ((polyFun_snd.comp polyFun_snd).comp polyFun_length)

def designLabel (z : RawUpccCase × ℕ) : List ℕ :=
  if designUseDirect z.1 then splitNeighborhoodRow (designBip z.1,z.2)
  else designComplementRow (z.1.2.2,splitNeighborhoodRow (designBip z.1,z.2))

theorem polyFun_designLabel : PolyFun designLabel := by
  have hr := ((polyFun_fst.comp polyFun_designBip).pair polyFun_snd).comp polyFun_splitNeighborhoodRow
  exact PolyFun.ite (polyFun_fst.comp polyFun_designUseDirect) hr
    ((((polyFun_fst.comp polyFun_snd).comp polyFun_snd).pair hr).comp polyFun_designComplementRow)

/-- One label per first-part position. -/
def designLabels (r : RawUpccCase) : List (List ℕ) :=
  (List.range r.2.1.length).map (fun i => designLabel (r,i))

theorem polyFun_designLabels : PolyFun designLabels :=
  (polyFun_id.pair ((polyFun_snd.comp polyFun_fst).comp polyFun_rangeLength)).comp
    (PolyFun.mapParam polyFun_designLabel)

@[simp] theorem designLabels_length (r : RawUpccCase) :
    (designLabels r).length = r.2.1.length := by simp [designLabels]

section Specification
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {X : BlkDesignObj s} {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {r : RawUpccCase} (h : DesignNames X name₁ name₂ r)
    (e₁ : ↥X.Pt₁ ≃ Fin r.2.1.length) (he₁ : ∀ x, r.2.1[(e₁ x).val] = name₁ x)
    (e₂ : ↥X.blocks ≃ Fin r.2.2.length) (he₂ : ∀ B, r.2.2[(e₂ B).val] = name₂ B)
include h he₁ he₂

theorem designDegree_spec : designDegree r = X.d₁ := by
  obtain ⟨x,hx⟩ := X.part₁_nonempty
  have hn : 0 < r.2.1.length := Nat.zero_lt_of_lt (e₁ ⟨x,hx⟩).isLt
  have hh := designRow_length h e₁ he₁ e₂ he₂ (e₁.symm ⟨0,hn⟩)
  simpa only [Equiv.apply_symm_apply] using hh

theorem designRank_spec : designRank r = X.d' := by
  rw [designRank,designDegree_spec h e₁ he₁ e₂ he₂,designRight_length e₂]
  rfl

theorem designCase3a_spec : designCase3a r = true ↔ X.IsCase3a := by
  rw [designCase3a,designSmallRank,decide_eq_true_eq,designRankWitness_length,
    designRank_spec h e₁ he₁ e₂ he₂,designLeft_length e₁]
  obtain ⟨x,hx⟩ := X.part₁_nonempty
  have hn : 0 < X.n₁ := (Set.ncard_pos (Set.toFinite _)).2 ⟨x,hx⟩
  exact designSmallRank_iff hn

omit h he₁ he₂ in
include e₁ in
theorem designSkeleton_spec : designSkel r.2.1 = X.tSkel := by
  have hn : 0 < r.2.1.length := by
    obtain ⟨x,hx⟩ := X.part₁_nonempty
    exact Nat.zero_lt_of_lt (e₁ ⟨x,hx⟩).isLt
  rw [designSkel_spec _ hn,designLeft_length e₁]
  rfl

/-- Each chosen label lists the neighborhood, or its complement, exactly. -/
theorem designLabel_mem (x : ↥X.Pt₁) (B : ↥X.blocks) :
    (e₂ B).val ∈ designLabel (r,e₁ x) ↔
      if 2 * X.d₁ ≤ X.n₂ then B.val ∈ X.nbhd x.val else B.val ∉ X.nbhd x.val := by
  simp only [designLabel,designUseDirect,designDegree_spec h e₁ he₁ e₂ he₂,
    designRight_length e₂,decide_eq_true_eq]
  split
  · exact designRow_mem h e₁ he₁ e₂ he₂ x B
  · rw [designComplementRow_mem,and_iff_right (e₂ B).isLt,designRow_mem h e₁ he₁ e₂ he₂]

end Specification
end Algo
