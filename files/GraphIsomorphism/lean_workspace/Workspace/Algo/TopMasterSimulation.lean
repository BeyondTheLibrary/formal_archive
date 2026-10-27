import Workspace.Algo.TopMasterCheckedMatch

/-! # Matching a fold after normalizing its state
The relation records exactly the information used by later calls. It
allows a short encoding of a coset to replace another encoding of the
same coset without changing the ordered mathematical call tree.
-/
namespace Algo
open Babai Equiv

 theorem loopMatch_simulation {ι ω α N S Ω A : Type*}
    {R : Round ι ω α} {M : Round N S α}
    {decI : ι → SIInstance Ω A} {decN : N → SIInstance Ω A}
    {decA : α → Set (Perm Ω)} (I : ι) (P : N)
    (Rel : ω → S → Prop) (V : SIInstance Ω A → Prop)
    (hstop : ∀ j s t, Rel s t → R.child (I, j, s) = none → M.child (P, j, t) = none)
    (hcall : ∀ j s t J, Rel s t → R.child (I, j, s) = some J → V (decI J) →
      ∃ K, M.child (P, j, t) = some K ∧ decN K = decI J)
    (hcomb : ∀ j s t a, Rel s t → Rel (R.combine (I, j, s, a)) (M.combine (P, j, t, a)))
    (hfin : ∀ s t, Rel s t → decA (M.finish (P, t)) = decA (R.finish (I, s))) :
    ∀ w j s T, LoopMatch R decI decA I w j s T →
      (∀ J ∈ T.calls, V J) → ∀ t, Rel s t → LoopMatch M decN decA P w j t T := by
  intro w j s T h
  induction h with
  | done w j s a hc ha =>
    intro _ t ht
    exact .done w j t a (hstop j s t ht hc) ((hfin s t ht).trans ha)
  | call w j s J k hc hn ih =>
    intro hV t ht
    have hvJ := hV (decI J) (by simp [SIReduction.calls])
    obtain ⟨K, hK, he⟩ := hcall j s t J ht hc hvJ
    refine (he ▸ LoopMatch.call (R := M) (decI := decN) (decA := decA) (I := P)
      w j t K k hK ?_)
    intro a ha
    have ha' : decA a = (decI J).answer := by rw [← he]; exact ha
    apply he ▸ ih a ha' ?_ _ (hcomb j s t a ht)
    intro L hL
    apply hV L
    simp only [SIReduction.calls_call, List.mem_cons]
    exact Or.inr (by simpa only [he] using hL)

end Algo
