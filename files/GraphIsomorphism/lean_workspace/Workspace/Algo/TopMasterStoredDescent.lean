import Workspace.Algo.TopMasterDescentOpenCost

/-! # A uniform master fold over computed descent lists
The list producer is local work. Each recursive call is a normalized
window instance, and the two accumulator cosets stay bounded after every
answer. This carrier also accepts polynomial Cameron representative lists.
-/
namespace Algo
open RAM RAM.Targets

def masterStoredDescOps (f : RawMasterSI → AggnRecomputeInput) : MasterOps AggnRecomputeState where
  width := fun p => masterDescFoldWidth (f p)
  child := fun z => masterDescFoldChild (f z.1, z.2)
  init := fun p => masterDescFoldInit (f p)
  combine := fun z => masterDescFoldCombine (f z.1, z.2)
  finish := fun z => masterDescFoldFinish (f z.1, z.2)

theorem masterStoredDesc_uniform_bounds (a b : ℕ) (f : RawMasterSI → AggnRecomputeInput)
    (hf : QuasiFun f) (hsource : ∀ p, (f p).1.2.2.2.1 = p.1.2.2.2.1) :
    ∃ B : ℕ → ℕ, QuasiPolyBound B ∧ Monotone B ∧
      ∀ p, MasterInputWF a b p →
        Enc.size ((masterStoredDescOps f).init p) ≤ B (masterDegree p) ∧
        (∀ j s A, Enc.size ((masterStoredDescOps f).combine (p, j, s, A)) ≤ B (masterDegree p)) ∧
        (masterStoredDescOps f).width p ≤ B (masterDegree p) := by
  obtain ⟨K, hK, hmK, hsK⟩ := hf.size.exists_quasiPolyBound
  let Q := fun n => K (masterInputCap a b n)
  let B := fun n => 16 * (Q n + chainBound n + 1) + Q n ^ 2
  have hQ : QuasiPolyBound Q := hK.comp (polyBound_masterInputCap a b).quasiPoly
  have hmQ : Monotone Q := fun n m h => hmK _ _ (mono_masterInputCap a b h)
  have hB : QuasiPolyBound B := ((polyBound_const 16).quasiPoly.mul
    ((hQ.add polyBound_chainBound.quasiPoly).add (polyBound_const 1).quasiPoly)).add
      (by simpa only [pow_two] using hQ.mul hQ)
  have hmB : Monotone B := by
    intro n m h
    have h1 := hmQ h
    have h2 := mono_chainBound h
    have h3 := Nat.pow_le_pow_left h1 2
    dsimp only [B]
    omega
  refine ⟨B, hB, hmB, ?_⟩
  intro p hp
  have hk : Enc.size (f p) ≤ Q (masterDegree p) := (hsK p).trans (hmK _ _ hp.1)
  have hx : (f p).1.2.2.2.1.length = masterDegree p := congrArg List.length (hsource p)
  refine ⟨?_, ?_, ?_⟩
  · have h := masterDescFoldInit_size (f p)
    rw [hx] at h
    change Enc.size (masterDescFoldInit (f p)) ≤ _
    dsimp only [B]
    omega
  · intro j s A
    have h := masterDescFoldCombine_size (f p) j s A
    rw [hx] at h
    change Enc.size (masterDescFoldCombine (f p, j, s, A)) ≤ _
    dsimp only [B]
    omega
  · exact ((masterDescFoldWidth_le _).trans (Nat.pow_le_pow_left hk 2)).trans (Nat.le_add_left _ _)

theorem masterStoredDesc_runCostQ (a b : ℕ) (f : RawMasterSI → AggnRecomputeInput)
    (hf : QuasiFun f) (hsource : ∀ p, (f p).1.2.2.2.1 = p.1.2.2.2.1) :
    Nonempty (Round.RunCostQ (masterAdmittedRound a b (masterStoredDescOps f))) := by
  obtain ⟨B, hB, hmB, hbound⟩ := masterStoredDesc_uniform_bounds a b f hf hsource
  refine ⟨masterAdmittedRunCostQ a b (masterStoredDescOps f) B B hB hmB hB
    (hf.comp_poly polyFun_masterDescFoldWidth)
    (((polyFun_fst.comp_quasiFun hf).pair polyFun_snd.quasiFun).comp_poly polyFun_masterDescFoldChild)
    (hf.comp_poly polyFun_masterDescFoldInit)
    (((polyFun_fst.comp_quasiFun hf).pair polyFun_snd.quasiFun).comp_poly polyFun_masterDescFoldCombine)
    (((polyFun_fst.comp_quasiFun hf).pair polyFun_snd.quasiFun).comp_poly polyFun_masterDescFoldFinish)
    (fun p hp => (hbound p hp).1)
    (fun p j s A hp _ _ => (hbound p hp).2.1 j s A) ?_
    (fun p hp => (hbound p hp).2.2)⟩
  intro p s _ _
  have h := masterDescFoldFinish_size (f p) s
  change Enc.size ((masterStoredDescOps f).finish (p, s)) ≤ chainBound (f p).1.2.2.2.1.length at h
  rw [hsource p] at h
  exact h.trans (by unfold masterInputCap masterDegree; omega)
end Algo
