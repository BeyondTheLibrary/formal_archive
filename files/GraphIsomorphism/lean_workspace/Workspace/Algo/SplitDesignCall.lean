import Workspace.Algo.SplitDesignRelations
import Workspace.Algo.SplitDesignComplement

/-! # Section 9.7: construct the Design Lemma input

Case 3a uses the full smaller rank. Case 3b uses the skeleton rank.
Both ranks fit one fixed logarithmic guard in the first-part size, so the
whole relation table has a quasipolynomial RAM bound on every raw input.
-/
namespace Algo
open Babai RAM

def designSkelPadding (l : List ℕ) : List ℕ :=
  ((List.replicate 7 (0 : ℕ)).product (0 :: l)).map Prod.snd

theorem polyFun_designSkelPadding : PolyFun designSkelPadding :=
  (((polyFun_const (List.replicate 7 (0 : ℕ))).pair
    (((polyFun_const 0).pair polyFun_id).comp polyFun_cons)).comp
      GIReduction.polyFun_product).comp (PolyFun.map polyFun_snd)

@[simp] theorem designSkelPadding_length (l : List ℕ) :
    (designSkelPadding l).length = 7 * (l.length + 1) := by
  simp [designSkelPadding,List.product]
  omega

def designSkelWitness (r : RawUpccCase) : List ℕ :=
  (designSkelPadding r.2.1).take (designSkel r.2.1)

theorem polyFun_designSkelWitness : PolyFun designSkelWitness :=
  (((polyFun_snd.comp polyFun_fst).comp polyFun_designSkelPadding).pair
    ((polyFun_snd.comp polyFun_fst).comp polyFun_designSkel)).comp polyFun_take

def designCallWitness (r : RawUpccCase) : List ℕ :=
  if designCase3a r then designRankWitness r else designSkelWitness r

theorem polyFun_designCallWitness : PolyFun designCallWitness :=
  PolyFun.ite polyFun_designCase3a polyFun_designRankWitness polyFun_designSkelWitness

def designCallInput (r : RawUpccCase) : RawDesignRelInput :=
  ((designCallWitness r,r.2.1,List.range r.2.2.length),designLabels r)

theorem polyFun_designCallInput : PolyFun designCallInput :=
  (polyFun_designCallWitness.pair ((polyFun_snd.comp polyFun_fst).pair
    ((polyFun_snd.comp polyFun_snd).comp polyFun_rangeLength))).pair polyFun_designLabels

def designCallRelations (r : RawUpccCase) : RawRelStruct := designRelations 3 (designCallInput r)

theorem quasiFun_designCallRelations : QuasiFun designCallRelations :=
  polyFun_designCallInput.comp_quasiFun (quasiFun_designRelations 3)

/-- Both logarithmic ranks fit the same degree-independent guard exponent. -/
theorem designRanks_guard {n d : ℕ} (hn : 2 ≤ n) :
    ((d : ℝ) ≤ 7 / 3 * Real.logb 2 (n : ℝ) → d ≤ guardBound 3 n) ∧
      ⌈7 / 4 * Real.logb 2 (n : ℝ)⌉₊ ≤ guardBound 3 n := by
  have hlog := logb_two_lt_natLog_succ n
  have hl : 2 ≤ Nat.log 2 n + 1 := by
    have hh : 1 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (by simpa using hn)
    omega
  have hp : 3 * (Nat.log 2 n + 1) ≤ (Nat.log 2 n + 1) ^ 3 := by
    let l := Nat.log 2 n + 1
    have h1 : 2 * l ≤ l * l := Nat.mul_le_mul_right l hl
    have h2 : 2 * (l*l) ≤ l*(l*l) := Nat.mul_le_mul_right (l*l) hl
    change 3*l ≤ l^3
    nlinarith
  constructor
  · intro hd
    have hh : (d : ℝ) < 3 * (Nat.log 2 n + 1 : ℕ) := by
      push_cast
      linarith [show (0 : ℝ) ≤ Nat.log 2 n by positivity]
    have hh' : d < 3 * (Nat.log 2 n + 1) := by exact_mod_cast hh
    exact (Nat.le_of_lt hh').trans hp
  · apply le_trans ?_ hp
    rw [Nat.ceil_le]
    push_cast
    linarith [show (0 : ℝ) ≤ Nat.log 2 n by positivity]

section Specification
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {X : BlkDesignObj s} {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {r : RawUpccCase} (h : DesignNames X name₁ name₂ r)
    (e₁ : ↥X.Pt₁ ≃ Fin r.2.1.length) (he₁ : ∀ x, r.2.1[(e₁ x).val] = name₁ x)
    (e₂ : ↥X.blocks ≃ Fin r.2.2.length) (he₂ : ∀ B, r.2.2[(e₂ B).val] = name₂ B)
include h he₁ he₂

/-- The list witness carries exactly the skeleton ceiling. -/
theorem designSkelWitness_length : (designSkelWitness r).length = X.tSkel := by
  rw [designSkelWitness,List.length_take,designSkelPadding_length,
    designSkeleton_spec e₁,designLeft_length e₁]
  exact min_eq_left (designSkel_bound (by
    have hh := X.part₁_nonempty
    exact (Set.ncard_pos (Set.toFinite _)).2 hh))

open scoped Classical in
/-- The input carries the paper's branch-dependent arity. -/
theorem designCallWitness_length : (designCallWitness r).length =
    if X.IsCase3a then X.d' else X.tSkel := by
  classical
  unfold designCallWitness
  by_cases hc : X.IsCase3a
  · rw [if_pos ((designCase3a_spec h e₁ he₁ e₂ he₂).2 hc),if_pos hc,
      designRankWitness_length,designRank_spec h e₁ he₁ e₂ he₂]
  · rw [if_neg (fun hh => hc ((designCase3a_spec h e₁ he₁ e₂ he₂).1 hh)),if_neg hc]
    exact designSkelWitness_length h e₁ he₁ e₂ he₂

/-- The executable table guard follows from the admissible block-design input. -/
theorem designCall_guard (hlt : X.n₂ < X.n₁) :
    (designCallWitness r).length ≤ guardBound 3 r.2.1.length := by
  classical
  rw [designCallWitness_length h e₁ he₁ e₂ he₂,designLeft_length e₁]
  have hh := designRanks_guard (d := X.d') (show 2 ≤ X.n₁ by have := X.five_le_n₁ hlt; omega)
  split
  · exact hh.1 ‹X.IsCase3a›
  · exact hh.2

/-- The computed table is the skeleton relation in the paper's block coordinates. -/
theorem designCallRelations_skeleton (hlt : X.n₂ < X.n₁) (k : ℕ)
    (hk : (designCallWitness r).length = k) (v : Fin k → ↥X.blkAmb) :
    (fun i => designBlockEquiv e₂ (v i)) ∈
      (decRel r.2.2.length k (designCallRelations r)).rel 0 ↔
      v ∈ ((X.nbhdHg.skeleton k).toRelStructureSimple k).rel
        ⟨0,by change 0 < 1; omega⟩ := by
  classical
  have hh := designRelations_skeleton (designCallWitness r) r.2.1
    (List.range r.2.2.length) (designLabels r) hk
    (fun i => List.mem_range.2 i.isLt) (designCall_guard h e₁ he₁ e₂ he₂ hlt)
    (fun i => designBlockEquiv e₂ (v i))
  change (_ ↔ Function.Injective (fun i => designBlockEquiv e₂ (v i)) ∧
    Finset.univ.image (fun i => designBlockEquiv e₂ (v i)) ∈ _) at hh
  rw [show Finset.univ.image (fun i => designBlockEquiv e₂ (v i)) =
    (Finset.univ.image v).image (designBlockEquiv e₂) by rw [Finset.image_image]; rfl,
    Hypergraph.mem_skeleton_edgeSet_image X.nbhdHg _ k (designBlockEquiv e₂)
      (designLabels_image_mem h e₁ he₁ e₂ he₂)] at hh
  change _ ↔ Function.Injective v ∧ _
  exact hh.trans (and_congr
    ⟨fun hi i j hij => hi (congrArg (designBlockEquiv e₂) hij),
      fun hi i j hij => hi ((designBlockEquiv e₂).injective hij)⟩ Iff.rfl)

/-- Case 3b feeds precisely `skelStruct`, with no change to its relation. -/
theorem designCallRelations_case3b (hlt : X.n₂ < X.n₁) (hc : ¬ X.IsCase3a)
    (v : Fin X.tSkel → ↥X.blkAmb) :
    (fun i => designBlockEquiv e₂ (v i)) ∈
      (decRel r.2.2.length X.tSkel (designCallRelations r)).rel 0 ↔
      v ∈ (X.skelStruct X.tSkel).rel ⟨0,by change 0 < 1; omega⟩ := by
  apply designCallRelations_skeleton h e₁ he₁ e₂ he₂ hlt X.tSkel
  rw [designCallWitness_length h e₁ he₁ e₂ he₂,if_neg hc]

/-- Case 3a feeds the full neighborhood relation, because all edges have that rank. -/
theorem designCallRelations_case3a (hlt : X.n₂ < X.n₁) (hc : X.IsCase3a)
    (v : Fin X.d' → ↥X.blkAmb) :
    (fun i => designBlockEquiv e₂ (v i)) ∈
      (decRel r.2.2.length X.d' (designCallRelations r)).rel 0 ↔
      v ∈ (X.nbhdStruct X.d').rel ⟨0,by change 0 < 1; omega⟩ := by
  classical
  have hk : (designCallWitness r).length = X.d' := by
    rw [designCallWitness_length h e₁ he₁ e₂ he₂,if_pos hc]
  have hh := designCallRelations_skeleton h e₁ he₁ e₂ he₂ hlt X.d' hk v
  have hed : (X.nbhdHg.skeleton X.d').edgeSet = X.nbhdHg.edgeSet := by
    ext F
    rw [Hypergraph.mem_skeleton_edgeSet]
    constructor
    · rintro ⟨hcard,i,hsub⟩
      exact ⟨i,(Finset.eq_of_subset_of_card_le hsub
        (by rw [X.nbhdHg_isUniform i,hcard])).symm⟩
    · rintro ⟨i,rfl⟩
      exact ⟨X.nbhdHg_isUniform i,i,Finset.Subset.refl _⟩
  change (_ ↔ Function.Injective v ∧ Finset.univ.image v ∈ _) at hh ⊢
  simpa only [hed] using hh

end Specification
end Algo
