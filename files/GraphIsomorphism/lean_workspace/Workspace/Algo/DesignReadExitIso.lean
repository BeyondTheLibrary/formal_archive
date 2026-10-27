import Workspace.Algo.DesignReadPartitionIso
import Workspace.Algo.DesignReadUpccIso

/-! # Canonicity of each complete computed read-off -/
namespace Algo
open Babai RAM Equiv
open scoped Classical
set_option quotPrecheck false

/-- The ambient map preserves the actual branch, colors, and blocks. -/
def DesignReadOutIso (n : ℕ) (f : Perm (Fin n)) (o o' : RawDesignReadOut) : Prop :=
  (∃ P P',o = (some P,[],none) ∧ o' = (some P',[],none) ∧ ColPartIso n P P' f) ∨
  (∃ L L' q q',o = (none,L,some q) ∧ o' = (none,L',some q') ∧
    f '' winSet n L = winSet n L' ∧ ∀ u v : Fin n,u.val ∈ L → v.val ∈ L →
      binColor (q',(rawLetterIndex (L',(f u).val),rawLetterIndex (L',(f v).val))) =
      binColor (q,(rawLetterIndex (L,u.val),rawLetterIndex (L,v.val))))

section
variable {n k l a b : ℕ} {ks : List ℕ} {p q : RawWL}
  (hp : RawWL.WF n k p) (hq : RawWL.WF n k q) (hk : ks.length = k)
  (hl : l ≤ k) (x : Str (Fin n) l) {α : ℝ} (hb : 0 < b) (hab : α = (a:ℝ)/b)
  (f : Perm (Fin n)) (hf : f ∈ KAryPartStruct.Iso (decWL n k p) (decWL n k q))
local notation "z" => (((ks,tupleOf x),p),(a,b))
local notation "z'" => (((ks,tupleOf (tupleMap f x)),q),(a,b))
local notation "Y" => ((decWL n k p).restrTo hl x)
local notation "Y'" => ((decWL n k q).restrTo hl (tupleMap f x))
local notation "D" => (KAryPartStruct.dominantClass α Y)
local notation "D'" => (KAryPartStruct.dominantClass α Y')
local notation "hi" => (KAryPartStruct.restrTo_canonical _ _ hl x hf)
local notation "d" => (KAryPartStruct.domEquiv (α := α) hi)
local notation "e" => (designDominantEquiv hp hk hl x hb hab)
local notation "e'" => (designDominantEquiv hq hk hl (tupleMap f x) hb hab)
local notation "c" => (fun u v : D => binColor (designDomPairs z,(e u,e v)))
local notation "c'" => (fun u v : D' => binColor (designDomPairs z',(e' u,e' v)))
include hp hq hk hl hb hab hf

/-- The whole output, with the actual branch chosen, is canonical at the tuple. -/
theorem designReadIso_exit : DesignReadOutIso n f (designReadExit z) (designReadExit z') := by
  unfold designReadExit
  rw [designReadIso_components hp hq hk hl x hb hab f hf,
    designReadIso_upcc_test hp hq hk hl x hb hab f hf]
  by_cases hc : designReadHasComponents z = true
  · rw [if_pos hc,if_pos hc]
    have h2 := (designReadHasComponents_spec z).mp hc |>.1
    have h2' : l+2 ≤ k := by simpa only [length_tupleOf,hk] using h2
    exact Or.inl ⟨_,_,rfl,rfl,designReadIso_partition_blocks hp hq hk hl x hb hab f hf h2'⟩
  · rw [if_neg hc,if_neg hc]
    by_cases hu : designReadHasUpcc z = true
    · rw [if_pos hu,if_pos hu]
      have h2 : l+2 ≤ k := by
        simp only [designReadHasUpcc,designReadHasSkeleton,Bool.and_eq_true,
          decide_eq_true_eq,length_tupleOf,hk] at hu
        exact hu.1
      exact Or.inr ⟨_,_,_,_,rfl,rfl,designReadIso_dominant_image hp hq hk hl x hb hab f hf,
        designReadIso_upcc_old_colors hp hq hk hl x hb hab f hf h2⟩
    · rw [if_neg hu,if_neg hu]
      exact Or.inl ⟨_,_,rfl,rfl,designReadIso_plain hp hq hk hl x hb hab f hf⟩

end
end Algo
