import Workspace.Algo.SplitDesignCase3Progress
import Workspace.Algo.DesignReadCallValidity
import Workspace.Algo.TestSetNaming

/-! Apply the progress bound to every actual returning tuple. All output
shape and validity premises come from the computed Design Lemma family. -/
namespace Algo
open Babai RAM

section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {X : BlkDesignObj s} {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {r : RawUpccCase} (h : DesignNames X name₁ name₂ r) (hw : r.WF)
    (e₁ : ↥X.Pt₁ ≃ Fin r.2.1.length) (he₁ : ∀ x, r.2.1[(e₁ x).val] = name₁ x)
    (e₂ : ↥X.blocks ≃ Fin r.2.2.length) (he₂ : ∀ B, r.2.2[(e₂ B).val] = name₂ B)
include h hw he₁ he₂

open scoped Classical in
theorem designCallReadSelected_progress (hlt : X.n₂ < X.n₁)
    (h1 : ¬ X.IsCase1) (h2 : ¬ X.IsCase2)
    {xs : List ℕ} {o : RawDesignReadOut} (ho : (xs,o) ∈ designCallReadFamily r) :
    letI : Fintype ↥s := Fintype.ofFinite _
    letI : DecidableEq ↥s := Classical.decEq _
    10 * (designReadSelectedSet r name₂ o).ncard ≤ 9 * X.blocks.ncard ∨
      ((designReadSelectedSet r name₂ o).ncard ≤ X.blocks.ncard ∧
        (X.linkGraph.restrictBlkHint (designReadSelectedSet r name₂ o)
          (designReadMathHint e₂ o)).HasHint) := by
  have hout := (designCallReadFamily_mem r xs o).1 ho |>.2
  let z := ambientDesignAt 3 (designCallGIn r) xs
  have hdom : z.1.2.1 = List.range r.2.2.length := by
    simp [z,ambientDesignAt,designCallGIn]
  cases hp : o.1 with
  | some P =>
    have hpz : (designReadExit z).1 = some P := by rwa [hout] at hp
    have he : o = designReadPartitionExit P := hout.trans (designReadExit_partition_eq hpz)
    have hlen : P.1.length = r.2.2.length := by
      have hh := designReadExit_partition_wf hpz |>.1
      simpa only [hdom,List.length_range] using hh
    have hP := designCallReadFamily_partition_valid h e₁ he₁ e₂ he₂ hlt h1 h2 ho hp
    have hn := designCall_hypotheses h e₁ he₁ e₂ he₂ hlt h1 h2
    rw [he]
    exact designReadPartition_progress h hw e₁ he₁ e₂ he₂ P hlen
      (by rwa [hlen]) (by omega)
  | none =>
    obtain ⟨l,q,he⟩ := designReadExit_of_none (show (designReadExit z).1 = none by rwa [hout] at hp)
    have hoe : o = (none,l,some q) := hout.trans he
    clear hout
    subst o
    obtain ⟨_,hbig,Z,hco,hu,hc⟩ := designCallReadFamily_upcc_valid h e₁ he₁ e₂ he₂ hlt ho rfl
    obtain ⟨hnd,hL⟩ := designCallReadFirst_names r ho
    have hcard := ncard_winSet l hnd hL
    have hbig' : 3 * r.2.2.length < 4 * l.length := by
      simp only [IsDominant,Fintype.card_fin] at hbig
      rw [hcard] at hbig
      have hh : (3:ℝ) * r.2.2.length < 4 * l.length := by linarith
      exact_mod_cast hh
    exact designReadUpcc_progress h hw e₁ he₁ e₂ he₂ l q hnd hL hbig' Z hco hu hc

end
end Algo
