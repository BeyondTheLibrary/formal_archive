import Workspace.Algo.EvaluatorRAM
import Workspace.Algo.NormalizeSI

/-!
# The final bridge after input normalization

The evaluator bounds its frames in the domain size. An arbitrary typed input can have
many repeated generators or large letters, so it must first pass through a polynomial
normalization. The time bound for the composite is measured in the original input size.
The case `norm = id` is the earlier `siWorkspaceRoutine_of_run`.
-/

namespace Algo

open RAM

variable {ω : Type*} [Enc ω]

/-- A polynomial normalization followed by the round evaluator gives the final routine.
The decoding hypothesis refers to the original input. -/
theorem siWorkspaceRoutine_of_norm_run (R : Round RawSI ω RawCoset)
    (C : Round.RunCost R) (c : ℕ) (norm : RawSI → RawSI) (hnorm : PolyFun norm)
    (hdec : ∀ (n s : ℕ) (a : Targets.SIInput n s),
      ∃ b : Option (List (Equiv.Perm (Fin n)) × Equiv.Perm (Fin n)),
        Enc.encode b = Enc.encode (R.runAnswer C c (norm (rawOfSI a))) ∧
          Targets.SIRel n s a b) : SIWorkspaceRoutine := by
  have hrun := hnorm.comp_quasi (R.quasiPolyFun_runAnswer C c)
  obtain ⟨P, T, hT, hP⟩ := hrun.time
  obtain ⟨S, hSb, hSmono, hSle⟩ := hrun.size.exists_polyBound
  refine ⟨P, T, S, hT, hSb, hSmono, fun n s => ?_⟩
  refine CleanSolveAt.transfer (e := rawOfSI)
    (R' := fun (r : RawSI) (b' : RawCoset) =>
      b' = R.runAnswer C c (norm r) ∧ Enc.size b' ≤ S (Enc.size r))
    (fun a => (encode_si_eq a).symm) ?_
    (fun r => ⟨R.runAnswer C c (norm r), ⟨rfl, hSle r⟩, hP r⟩)
  intro a b' hb'
  obtain ⟨b, hbenc, hbrel⟩ := hdec n s a
  have hbb : Enc.encode b = Enc.encode b' := by rw [hbenc, hb'.1]
  have hsize : Enc.size b ≤ S (Enc.size a) := by
    have h1 : Enc.size b = Enc.size b' := size_eq_of_encode_eq hbb
    have h2 : Enc.size (rawOfSI a) = Enc.size a :=
      size_eq_of_encode_eq (encode_si_eq a).symm
    rw [h1, ← h2]
    exact hb'.2
  exact ⟨b, hbb, hbrel, hsize⟩

/-- The concrete bridge: the remaining assembly must prove the raw specification only
after normalization. `rawNormSI_answer` supplies the typed answer and its encoding. -/
theorem siWorkspaceRoutine_of_rawNormSI_run (R : Round RawSI ω RawCoset)
    (C : Round.RunCost R) (c : ℕ)
    (hraw : ∀ (n s : ℕ) (a : Targets.SIInput n s),
      RawSIRel n (rawNormSI (rawOfSI a)) (R.runAnswer C c (rawNormSI (rawOfSI a)))) :
    SIWorkspaceRoutine :=
  siWorkspaceRoutine_of_norm_run R C c rawNormSI polyFun_rawNormSI
    (fun n s a => rawNormSI_answer a _ (hraw n s a))

end Algo

#print axioms Algo.siWorkspaceRoutine_of_norm_run
#print axioms Algo.siWorkspaceRoutine_of_rawNormSI_run
