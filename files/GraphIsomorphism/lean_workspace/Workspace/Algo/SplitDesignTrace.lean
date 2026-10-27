import Workspace.Algo.SplitDesignLocal
import Workspace.SplitOrJohnson.BlockDesignCase2

/-! # Section 9.7: exact trace classes

The dominant-class exits use equality of neighborhoods on the large twin
class. Sorted position lists represent these sets without extra choices.
-/
namespace Algo
open Babai RAM

def designDomKey (z : RawDesignLocal × ℕ) : List (List ℕ) :=
  if designDomTest z then [designLocalRow (z.1.1,z.2)] else []

def designDomEq (z : RawDesignLocal × (ℕ × ℕ)) : Bool :=
  decide (designDomKey (z.1,z.2.1) = designDomKey (z.1,z.2.2))

def designDomPartition (z : RawDesignLocal) : RawColPart :=
  (designLocalColors z.1,relationLabRaw designDomEq (z,z.1.2.1))

def designSmallPartition (r : RawUpccCase) : RawColPart :=
  (designLocalColors r,designLocalColors r)

theorem polyFun_designDomKey : PolyFun designDomKey :=
  PolyFun.ite polyFun_designDomTest
    (((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp
      polyFun_designLocalRow |>.comp polyFun_singleton) (polyFun_const [])

theorem polyFun_designDomEq : PolyFun designDomEq :=
  ((((polyFun_fst.pair (polyFun_snd.comp polyFun_fst)).comp polyFun_designDomKey).pair
    ((polyFun_fst.pair (polyFun_snd.comp polyFun_snd)).comp polyFun_designDomKey))).comp
      polyFun_listListNatEq

theorem polyFun_designDomPartition : PolyFun designDomPartition :=
  (polyFun_fst.comp polyFun_designLocalColors).pair
    ((polyFun_id.pair ((polyFun_fst.comp polyFun_snd).comp polyFun_fst)).comp
      (polyFun_relationLabRaw polyFun_designDomEq))

theorem polyFun_designSmallPartition : PolyFun designSmallPartition :=
  polyFun_designLocalColors.pair polyFun_designLocalColors

theorem designLocalRow_lt {r : RawUpccCase} {x i : ℕ}
    (hi : i ∈ designLocalRow (r,x)) : i < r.2.2.length :=
  List.mem_range.1 (List.mem_of_mem_filter (List.mem_of_mem_filter hi))

theorem designLocalRow_sorted (r : RawUpccCase) (x : ℕ) :
    (designLocalRow (r,x)).Pairwise (· < ·) :=
  (List.pairwise_lt_range.filter _).filter _

section Specification
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {X : BlkDesignObj s} {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {r : RawUpccCase} (h : DesignNames X name₁ name₂ r)
    (e₁ : ↥X.Pt₁ ≃ Fin r.2.1.length) (he₁ : ∀ x, r.2.1[(e₁ x).val] = name₁ x)
    (e₂ : ↥X.blocks ≃ Fin r.2.2.length) (he₂ : ∀ B, r.2.2[(e₂ B).val] = name₂ B)
include h he₁ he₂

theorem designLocalRow_eq (x y : ↥X.Pt₁) :
    designLocalRow (r,e₁ x) = designLocalRow (r,e₁ y) ↔
      X.nbhd x.val ∩ X.bigTwin = X.nbhd y.val ∩ X.bigTwin := by
  constructor
  · intro hh
    apply Set.ext
    intro B
    by_cases hB : B ∈ X.blocks
    · have hx := designLocalRow_mem h e₁ he₁ e₂ he₂ x ⟨B,hB⟩
      have hy := designLocalRow_mem h e₁ he₁ e₂ he₂ y ⟨B,hB⟩
      rw [hh] at hx
      exact hx.symm.trans hy
    · exact iff_of_false (fun hh => hB (X.nbhd_subset_blocks _ hh.1))
        (fun hh => hB (X.nbhd_subset_blocks _ hh.1))
  · intro hh
    apply (designLocalRow_sorted r (e₁ x)).eq_of_mem_iff (designLocalRow_sorted r (e₁ y))
    intro i
    by_cases hi : i < r.2.2.length
    · let B := e₂.symm ⟨i,hi⟩
      have hx := designLocalRow_mem h e₁ he₁ e₂ he₂ x B
      have hy := designLocalRow_mem h e₁ he₁ e₂ he₂ y B
      rw [hh] at hx
      simpa only [B,Equiv.apply_symm_apply] using hx.trans hy.symm
    · exact iff_of_false (fun hh => hi (designLocalRow_lt hh))
        (fun hh => hi (designLocalRow_lt hh))

theorem designDomKey_eq (p : ℕ × ℕ) (hb : 0 < p.2) (x y : ↥X.Pt₁) :
    designDomKey ((r,p),e₁ x) = designDomKey ((r,p),e₁ y) ↔
      X.domLab (sbipAlphaValue p) x.val = X.domLab (sbipAlphaValue p) y.val := by
  classical
  have hx := designDomTest_spec h e₁ he₁ e₂ he₂ p hb x
  have hy := designDomTest_spec h e₁ he₁ e₂ he₂ p hb y
  unfold designDomKey BlkCaseObj.domLab
  split <;> split <;> simp_all [designLocalRow_eq h e₁ he₁ e₂ he₂]

theorem designDomPartition_spec (p : ℕ × ℕ) (hb : 0 < p.2) :
    RawColPart.WF r.2.1.length (designDomPartition (r,p)) ∧
    (∀ x : ↥X.Pt₁, labAt (designDomPartition (r,p)).1 (e₁ x) = X.localSize x.val) ∧
    (∀ x y : ↥X.Pt₁, (decColPartition r.2.1.length (designDomPartition (r,p))).part
        (e₁ x) (e₁ y) ↔
      (labPartition X.Pt₁ X.localSize (X.domLab (sbipAlphaValue p))).part
        (mkPt x.property) (mkPt y.property)) := by
  refine ⟨⟨by simp [designDomPartition,designLocalColors],by simp [designDomPartition]⟩,
    fun x => designLocalColors_spec h e₁ he₁ e₂ he₂ x,?_⟩
  intro x y
  have hrel (u v : Fin r.2.1.length) :
      designDomEq ((r,p),(u,v)) = true ↔
        X.domLab (sbipAlphaValue p) (e₁.symm u).val =
          X.domLab (sbipAlphaValue p) (e₁.symm v).val := by
    simpa only [designDomEq,decide_eq_true_eq,Equiv.apply_symm_apply] using
      designDomKey_eq h e₁ he₁ e₂ he₂ p hb (e₁.symm u) (e₁.symm v)
  have heq : Equivalence (fun u v : Fin r.2.1.length =>
      X.domLab (sbipAlphaValue p) (e₁.symm u).val =
        X.domLab (sbipAlphaValue p) (e₁.symm v).val) :=
    ⟨fun _ => rfl,fun hh => hh.symm,fun ha hb => ha.trans hb⟩
  have hh := relationLabRaw_spec rfl heq hrel (e₁ x) (e₁ y)
  change (labAt (designLocalColors r) (e₁ x),
    labAt (relationLabRaw designDomEq ((r,p),r.2.1)) (e₁ x)) =
    (labAt (designLocalColors r) (e₁ y),
    labAt (relationLabRaw designDomEq ((r,p),r.2.1)) (e₁ y)) ↔ _
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

theorem designSmallPartition_spec :
    RawColPart.WF r.2.1.length (designSmallPartition r) ∧
    (∀ x : ↥X.Pt₁, labAt (designSmallPartition r).1 (e₁ x) = X.localSize x.val) ∧
    (∀ x y : ↥X.Pt₁, (decColPartition r.2.1.length (designSmallPartition r)).part
        (e₁ x) (e₁ y) ↔
      (kerPartition X.Pt₁ X.localSize).part (mkPt x.property) (mkPt y.property)) := by
  refine ⟨⟨by simp [designSmallPartition,designLocalColors],
    by simp [designSmallPartition,designLocalColors]⟩,
    fun x => designLocalColors_spec h e₁ he₁ e₂ he₂ x,?_⟩
  intro x y
  change (_,_) = (_,_) ↔ _
  simp only [designSmallPartition,designLocalColors_spec h e₁ he₁ e₂ he₂,Prod.mk.injEq,
    and_self]
  rfl

theorem designSmallPartition_good (p : ℕ × ℕ) (hb : 0 < p.2)
    (hs : designSmall (r,p) = true) (iF : Fintype ↥(Subtype.val '' X.Pt₁)) :
    @ColoredPartition.IsAlphaPartition _ _ (kerPartition X.Pt₁ X.localSize) iF
      (sbipAlphaValue p) := by
  obtain ⟨x₀,hx₀⟩ := X.part₁_nonempty
  refine kerPartition_isAlphaPartition_of_le _ _ _ ⟨x₀,hx₀⟩ (fun x hx => ?_)
  exact (designSmall_spec h e₁ he₁ e₂ he₂ p hb |>.1 hs ⟨x,hx⟩).le

end Specification
end Algo
