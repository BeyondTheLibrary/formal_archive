import Workspace.Algo.SplitDesignKary
import Workspace.Algo.DesignVersionsAmbient

/-! # Section 9.7: run the Design Lemma on the computed input

The case assumptions imply all hypotheses of the Design Lemma. Therefore
the concrete scan returns, and its result is read from the refined table.
The two branches share the threshold three quarters and the same machine.
-/
namespace Algo
open Babai RAM

def designCallGIn (r : RawUpccCase) : AmbientGIn :=
  (((designCallWitness r,r.2.1,List.range r.2.2.length),designCallRelations r),(3,4))

def designCallProcedure (r : RawUpccCase) : Option (List ℕ) :=
  ambientDesignProcedure 3 (designCallGIn r)

def designCallOutcome (r : RawUpccCase) : Option (List ℕ × (List ℕ × ℕ)) :=
  ambientDesignOutcome 3 (designCallGIn r)

theorem quasiFun_designCallGIn : QuasiFun designCallGIn :=
  ((polyFun_designCallInput.comp polyFun_fst).quasiFun.pair
    quasiFun_designCallRelations).pair (polyFun_const (3,4)).quasiFun

theorem quasiFun_designCallProcedure : QuasiFun designCallProcedure :=
  quasiFun_designCallGIn.comp (quasiFun_ambientDesignProcedure 3)

theorem quasiFun_designCallOutcome : QuasiFun designCallOutcome :=
  quasiFun_designCallGIn.comp (quasiFun_ambientDesignOutcome 3)

def designCallVersions (r : RawUpccCase) : List (List ℕ) :=
  ambientDesignVersions 3 (designCallGIn r)

def designCallFamily (r : RawUpccCase) : List (List ℕ × (List ℕ × (List ℕ × ℕ))) :=
  ambientDesignFamily 3 (designCallGIn r)

theorem quasiFun_designCallVersions : QuasiFun designCallVersions :=
  quasiFun_designCallGIn.comp (quasiFun_ambientDesignVersions 3)

theorem quasiFun_designCallFamily : QuasiFun designCallFamily :=
  quasiFun_designCallGIn.comp (quasiFun_ambientDesignFamily 3)

/-- The paper's Design Lemma hypotheses force the executable scan to return. -/
theorem ambientDesignProcedure_nonempty {n k a b c : ℕ} {α : ℝ}
    (ks base dom : List ℕ) (rels : RawRelStruct)
    (hnd : dom.Nodup) (hmem : ∀ i, i ∈ dom ↔ i < n)
    (hk : ks.length = k) (hb : 0 < b) (hab : α = (a : ℝ) / b)
    (hg : ks.length ≤ guardBound c base.length)
    (hα : 1 / 2 ≤ α) (hα1 : α < 1) (hk2 : 2 ≤ k) (hkn : 2*k ≤ n)
    (hdef : (1 : ℝ) - α ≤ (defect (decRel n k rels).Aut : ℝ)) :
    ∃ xs, ambientDesignProcedure c (((ks,base,dom),rels),(a,b)) = some xs := by
  obtain ⟨l,hl,x,hx⟩ := KAryRelStruct.theorem_8_1_5 hα hα1 (decRel n k rels)
    hk2 (by simpa only [Fintype.card_fin] using hkn) hdef
  cases hh : ambientDesignProcedure c (((ks,base,dom),rels),(a,b)) with
  | some xs => exact ⟨xs,rfl⟩
  | none =>
      have hf := (ambientDesignProcedure_none_iff hnd hmem hk hb hab hg).1 hh
      exact (hf l ⟨by omega,x,hx⟩).elim

section Specification
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {X : BlkDesignObj s} {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {r : RawUpccCase} (h : DesignNames X name₁ name₂ r)
    (e₁ : ↥X.Pt₁ ≃ Fin r.2.1.length) (he₁ : ∀ x, r.2.1[(e₁ x).val] = name₁ x)
    (e₂ : ↥X.blocks ≃ Fin r.2.2.length) (he₂ : ∀ B, r.2.2[(e₂ B).val] = name₂ B)
include h he₁ he₂

/-- Both branches satisfy the arity and symmetry-defect conditions of Theorem 8.1.5. -/
theorem designCall_hypotheses (hlt : X.n₂ < X.n₁)
    (h1 : ¬ X.IsCase1) (h2 : ¬ X.IsCase2) :
    let k := (designCallWitness r).length
    2 ≤ k ∧ 2*k ≤ r.2.2.length ∧
      (1 : ℚ)/4 ≤ defect (decRel r.2.2.length k (designCallRelations r)).Aut := by
  classical
  dsimp only
  rw [designCallWitness_length h e₁ he₁ e₂ he₂]
  by_cases hc : X.IsCase3a
  · simp only [if_pos hc]
    refine ⟨X.two_le_d' hlt,?_,?_⟩
    · rw [designRight_length e₂]; exact X.two_mul_d'_le_n₂
    · rw [if_pos hc,designCall_case3a_defect h e₁ he₁ e₂ he₂ hlt hc]
      exact (by norm_num : (1 : ℚ)/4 ≤ 1/2).trans (X.defect_nbhdStruct_ge h2 rfl)
  · simp only [if_neg hc]
    refine ⟨X.two_le_tSkel hlt,?_,?_⟩
    · rw [designRight_length e₂]; exact X.two_mul_tSkel_le_n₂ hlt hc
    · rw [if_neg hc,designCall_case3b_defect h e₁ he₁ e₂ he₂ hlt hc]
      change (1 : ℚ)/4 ≤ defect (X.skelStruct X.tSkel).Aut
      rw [X.aut_skelStruct rfl]
      exact le_of_lt (X.skeleton_defect_nbhdHg hlt h1 hc)

/-- The actual computed input reaches a returning string. -/
theorem designCallProcedure_nonempty (hlt : X.n₂ < X.n₁)
    (h1 : ¬ X.IsCase1) (h2 : ¬ X.IsCase2) :
    ∃ xs, designCallProcedure r = some xs := by
  obtain ⟨hk2,hkn,hdef⟩ := designCall_hypotheses h e₁ he₁ e₂ he₂ hlt h1 h2
  unfold designCallProcedure designCallGIn
  apply ambientDesignProcedure_nonempty (a := 3) (b := 4) (c := 3) (designCallWitness r) r.2.1
    (List.range r.2.2.length) (designCallRelations r) List.nodup_range
    (fun i => List.mem_range) rfl (by omega) (α := (3:ℝ)/4) rfl
    (designCall_guard h e₁ he₁ e₂ he₂ hlt) (by norm_num) (by norm_num) hk2 hkn
  have hh : (1 : ℝ)/4 ≤ (defect (decRel r.2.2.length (designCallWitness r).length
      (designCallRelations r)).Aut : ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).2 hdef
    norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at hh
    exact hh
  norm_num only [show (1 : ℝ)-3/4=1/4 by norm_num]
  exact hh

/-- Reading the returning string always produces an actual raw outcome. -/
theorem designCallOutcome_nonempty (hlt : X.n₂ < X.n₁)
    (h1 : ¬ X.IsCase1) (h2 : ¬ X.IsCase2) :
    ∃ w, designCallOutcome r = some w := by
  obtain ⟨xs,hxs⟩ := designCallProcedure_nonempty h e₁ he₁ e₂ he₂ hlt h1 h2
  exact ⟨_,ambientDesignOutcome_of_some hxs⟩

/-- Keep all returning versions, including the one found by the scan. -/
theorem designCallVersions_nonempty (hlt : X.n₂ < X.n₁)
    (h1 : ¬ X.IsCase1) (h2 : ¬ X.IsCase2) :
    ∃ xs, xs ∈ designCallVersions r := by
  obtain ⟨xs,hxs⟩ := designCallProcedure_nonempty h e₁ he₁ e₂ he₂ hlt h1 h2
  refine ⟨xs,?_⟩
  exact ambientDesignVersions_nonempty List.nodup_range (fun i => List.mem_range)
    rfl (designCall_guard h e₁ he₁ e₂ he₂ hlt) (by norm_num : 0 < 4)
    (α := (3:ℝ)/4) rfl hxs

/-- Each version retains its individualizing tuple and its raw outcome. -/
theorem designCallFamily_nonempty (hlt : X.n₂ < X.n₁)
    (h1 : ¬ X.IsCase1) (h2 : ¬ X.IsCase2) :
    ∃ w, w ∈ designCallFamily r := by
  obtain ⟨xs,hxs⟩ := designCallVersions_nonempty h e₁ he₁ e₂ he₂ hlt h1 h2
  exact ⟨_,List.mem_map.2 ⟨xs,hxs,rfl⟩⟩

end Specification
end Algo
