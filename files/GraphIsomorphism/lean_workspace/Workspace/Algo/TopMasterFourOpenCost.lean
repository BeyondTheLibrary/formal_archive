import Workspace.Algo.TopMasterFourOpen

/-! # Bounds for line 4b in the common master carrier
The parent master input pays for its computed top-action context. Both
state and width bounds are fixed polynomials of the ambient degree, and
the local update bound holds for every raw state and answer.
-/
set_option synthInstance.maxSize 4096
namespace Algo
open RAM RAM.Targets

 def master4OpenStateBound (c d n : ℕ) : ℕ := top4ContextStateBound (topcsContextCap c d n)
 def master4OpenWidthBound (c d n : ℕ) : ℕ := top4ContextWidthBound (topcsContextCap c d n)
 theorem polyBound_master4OpenStateBound (c d : ℕ) : PolyBound (master4OpenStateBound c d) :=
  polyBound_top4ContextStateBound.comp (polyBound_topcsContextCap c d)
 theorem mono_master4OpenStateBound (c d : ℕ) : Monotone (master4OpenStateBound c d) :=
  mono_top4ContextStateBound.comp (mono_topcsContextCap c d)
 theorem polyBound_master4OpenWidthBound (c d : ℕ) : PolyBound (master4OpenWidthBound c d) :=
  polyBound_top4ContextWidthBound.comp (polyBound_topcsContextCap c d)

 theorem masterHintInput_size (p : MasterHintInput) :
    Enc.size p ≤ 4 * Enc.size ((p.1, some p.2) : RawMasterSI) := by
  have h1 := size_pair_le' p
  have h2 := size_fst_le' ((p.1, some p.2) : RawMasterSI)
  have h3 := size_snd_le' ((p.1, some p.2) : RawMasterSI)
  change Enc.size p.1 ≤ Enc.size ((p.1, some p.2) : RawMasterSI) at h2
  rw [size_some_eq] at h3
  omega

 theorem master4Open_uniform_bounds (a b : ℕ) : ∃ c d : ℕ,
    ∀ p : MasterHintInput, MasterInputWF a b (p.1, some p.2) →
      Enc.size (master4OpenInit p) ≤ master4OpenStateBound c d p.1.2.2.2.1.length ∧
      (∀ j s A, Enc.size (master4OpenCombine (p, j, s, A)) ≤
        master4OpenStateBound c d p.1.2.2.2.1.length) ∧
      master4OpenWidth p ≤ master4OpenWidthBound c d p.1.2.2.2.1.length := by
  have hctx : PolyFun (fun p : MasterHintInput => (master4Enter p).1.1.2.1.1) :=
    ((((polyFun_master4Enter.comp polyFun_fst).comp polyFun_fst).comp polyFun_snd).comp
      polyFun_fst).comp polyFun_fst
  obtain ⟨F, hF, hmF, hsF⟩ := hctx.size.exists_polyBound
  obtain ⟨c, d, hcd⟩ := hF.comp ((polyBound_const 4).mul (polyBound_masterInputCap a b))
  refine ⟨c, d, ?_⟩
  intro p hp
  have hsize : Enc.size p ≤ 4 * masterInputCap a b p.1.2.2.2.1.length :=
    (masterHintInput_size p).trans (Nat.mul_le_mul_left 4 hp.1)
  have hC : Enc.size (master4Enter p).1.1.2.1.1 ≤ topcsContextCap c d p.1.2.2.2.1.length :=
    (hsF p).trans ((hmF _ _ hsize).trans (hcd _))
  refine ⟨?_, ?_, ?_⟩
  · exact top4Stored_size_context hC (top4Init_stored (master4Enter p).1.1.2.1)
  · intro j s A
    exact top4Stored_size_context hC
      (top4Combine_stored ((master4Enter p).1.1.2.1, j, s,
        topwCosetImage ((master4Enter p).1.1.1.1.1, (master4Enter p).1.1.1.2.1, A)))
  · exact top4aWidth_context (c := 0) (d := 0) (e := 0) (f := 0) hC (fun _ => none)
end Algo
