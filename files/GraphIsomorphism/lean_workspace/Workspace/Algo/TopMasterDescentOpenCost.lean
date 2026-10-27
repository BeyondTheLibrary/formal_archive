import Workspace.Algo.TopMasterDescentOpen

/-! # Uniform local bounds for the flattened master descent
The representative table may be quasipolynomial. It is recomputed by the
local routines and is not retained in recursive child inputs. Both state
cosets have the fixed degree bound, including on malformed answers.
-/
namespace Algo
open RAM RAM.Targets

 def masterDescOpenWidth (c : ℕ) (p : MasterDescInput) : ℕ := masterDescFoldWidth (masterDescLists c p)
 def masterDescOpenInit (c : ℕ) (p : MasterDescInput) : AggnRecomputeState :=
  masterDescFoldInit (masterDescLists c p)
 def masterDescOpenChild (c : ℕ) (z : MasterDescInput × ℕ × AggnRecomputeState) : Option RawMasterSI :=
  masterDescFoldChild (masterDescLists c z.1, z.2)
 def masterDescOpenCombine (c : ℕ) (z : MasterDescInput × ℕ × AggnRecomputeState × RawCoset) :
    AggnRecomputeState := masterDescFoldCombine (masterDescLists c z.1, z.2)
 def masterDescOpenFinish (c : ℕ) (z : MasterDescInput × AggnRecomputeState) : RawCoset :=
  masterDescFoldFinish (masterDescLists c z.1, z.2)

 theorem quasiFun_masterDescOpenWidth (c : ℕ) : QuasiFun (masterDescOpenWidth c) :=
  (quasiFun_masterDescLists c).comp_poly polyFun_masterDescFoldWidth
 theorem quasiFun_masterDescOpenInit (c : ℕ) : QuasiFun (masterDescOpenInit c) :=
  (quasiFun_masterDescLists c).comp_poly polyFun_masterDescFoldInit
 theorem quasiFun_masterDescOpenChild (c : ℕ) : QuasiFun (masterDescOpenChild c) :=
  ((polyFun_fst.comp_quasiFun (quasiFun_masterDescLists c)).pair polyFun_snd.quasiFun).comp_poly
    polyFun_masterDescFoldChild
 theorem quasiFun_masterDescOpenCombine (c : ℕ) : QuasiFun (masterDescOpenCombine c) :=
  ((polyFun_fst.comp_quasiFun (quasiFun_masterDescLists c)).pair polyFun_snd.quasiFun).comp_poly
    polyFun_masterDescFoldCombine
 theorem quasiFun_masterDescOpenFinish (c : ℕ) : QuasiFun (masterDescOpenFinish c) :=
  ((polyFun_fst.comp_quasiFun (quasiFun_masterDescLists c)).pair polyFun_snd.quasiFun).comp_poly
    polyFun_masterDescFoldFinish

 theorem masterDescFoldNorm_size {xs : RawStr} {s : AggnRecomputeState} {k : ℕ}
    (ht : s.1 ≤ k) (hi : s.2.1 ≤ k) :
    Enc.size (masterDescFoldNorm (xs, s)) ≤ 16 * (k + chainBound xs.length + 1) := by
  have hc := size_top2NormC_le rfl le_rfl s.2.2.1 (dom := xs)
  have ha := size_top2NormC_le rfl le_rfl s.2.2.2 (dom := xs)
  have h1 := size_pair_le' (masterDescFoldNorm (xs, s))
  have h2 := size_pair_le' (masterDescFoldNorm (xs, s)).2
  have h3 := size_pair_le' (masterDescFoldNorm (xs, s)).2.2
  have h4 := size_nat_le_self s.1
  have h5 := size_nat_le_self s.2.1
  dsimp only [masterDescFoldNorm] at h1 h2 h3 ⊢
  omega

 theorem masterDescFoldInit_size (P : AggnRecomputeInput) :
    Enc.size (masterDescFoldInit P) ≤ 16 * (Enc.size P + chainBound P.1.2.2.2.1.length + 1) :=
  masterDescFoldNorm_size (Nat.zero_le _) (Nat.zero_le _)

 theorem masterDescFoldCombine_size (P : AggnRecomputeInput) (j : ℕ)
    (s : AggnRecomputeState) (A : RawCoset) :
    Enc.size (masterDescFoldCombine (P, j, s, A)) ≤
      16 * (Enc.size P + chainBound P.1.2.2.2.1.length + 1) := by
  have ht : aggnrCount P ≤ Enc.size P := (length_le_size P.2.2.1).trans
    ((size_fst_le' P.2.2).trans ((size_snd_le' P.2).trans (size_snd_le' P)))
  have hi : (aggnrWindows P).length ≤ Enc.size P := (length_le_size P.2.2.2).trans
    ((size_snd_le' P.2.2).trans ((size_snd_le' P.2).trans (size_snd_le' P)))
  apply masterDescFoldNorm_size
  · change (aggnrStep P s.1 s.2.1 s.2.2.2 A).1 ≤ _
    unfold aggnrStep
    split <;> exact (Nat.min_le_right _ _).trans ht
  · change (aggnrStep P s.1 s.2.1 s.2.2.2 A).2.1 ≤ _
    unfold aggnrStep
    split
    · exact (Nat.min_le_right _ _).trans hi
    · exact Nat.zero_le _

 theorem masterDescFoldFinish_size (P : AggnRecomputeInput) (s : AggnRecomputeState) :
    Enc.size (masterDescFoldFinish (P, s)) ≤ chainBound P.1.2.2.2.1.length :=
  size_top2NormC_le rfl le_rfl _

 theorem masterDescFoldWidth_le (P : AggnRecomputeInput) : masterDescFoldWidth P ≤ Enc.size P ^ 2 := by
  have ht : aggnrCount P ≤ Enc.size P := (length_le_size P.2.2.1).trans
    ((size_fst_le' P.2.2).trans ((size_snd_le' P.2).trans (size_snd_le' P)))
  have hi : (aggnrWindows P).length ≤ Enc.size P := (length_le_size P.2.2.2).trans
    ((size_snd_le' P.2.2).trans ((size_snd_le' P.2).trans (size_snd_le' P)))
  simpa only [masterDescFoldWidth, pow_two] using Nat.mul_le_mul ht hi

 theorem masterDescOpen_uniform_bounds (a b c : ℕ) (f : RawMasterSI → MasterDescInput)
    (hf : PolyFun f) (hsource : ∀ p, (f p).1.2.2.2.1 = p.1.2.2.2.1) :
    ∃ B : ℕ → ℕ, QuasiPolyBound B ∧ Monotone B ∧
      ∀ p, MasterInputWF a b p →
        Enc.size (masterDescOpenInit c (f p)) ≤ B (masterDegree p) ∧
        (∀ j s A, Enc.size (masterDescOpenCombine c (f p, j, s, A)) ≤ B (masterDegree p)) ∧
        masterDescOpenWidth c (f p) ≤ B (masterDegree p) := by
  obtain ⟨K, hK, hmK, hsK⟩ := (hf.comp_quasiFun (quasiFun_masterDescLists c)).size.exists_quasiPolyBound
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
  have hk : Enc.size (masterDescLists c (f p)) ≤ Q (masterDegree p) :=
    (hsK p).trans (hmK _ _ hp.1)
  have hx : (masterDescLists c (f p)).1.2.2.2.1.length = masterDegree p :=
    congrArg List.length (hsource p)
  refine ⟨?_, ?_, ?_⟩
  · have h := masterDescFoldInit_size (masterDescLists c (f p))
    rw [hx] at h
    change Enc.size (masterDescOpenInit c (f p)) ≤ _ at h
    dsimp only [B]
    omega
  · intro j s A
    have h := masterDescFoldCombine_size (masterDescLists c (f p)) j s A
    rw [hx] at h
    change Enc.size (masterDescOpenCombine c (f p, j, s, A)) ≤ _ at h
    dsimp only [B]
    omega
  · exact ((masterDescFoldWidth_le _).trans (Nat.pow_le_pow_left hk 2)).trans (Nat.le_add_left _ _)

def masterDescOpenOps (c : ℕ) (f : RawMasterSI → MasterDescInput) : MasterOps AggnRecomputeState where
  width := fun p => masterDescOpenWidth c (f p)
  child := fun z => masterDescOpenChild c (f z.1, z.2)
  init := fun p => masterDescOpenInit c (f p)
  combine := fun z => masterDescOpenCombine c (f z.1, z.2)
  finish := fun z => masterDescOpenFinish c (f z.1, z.2)

/-- A single executable carrier works for every ambient degree. Its local
cost package is independent of the correctness or number of recursive calls. -/
theorem masterDescOpen_runCostQ (a b c : ℕ) (f : RawMasterSI → MasterDescInput)
    (hf : PolyFun f) (hsource : ∀ p, (f p).1.2.2.2.1 = p.1.2.2.2.1) :
    Nonempty (Round.RunCostQ (masterAdmittedRound a b (masterDescOpenOps c f))) := by
  obtain ⟨B, hB, hmB, hbound⟩ := masterDescOpen_uniform_bounds a b c f hf hsource
  refine ⟨masterAdmittedRunCostQ a b (masterDescOpenOps c f) B B hB hmB hB
    (hf.comp_quasiFun (quasiFun_masterDescOpenWidth c))
    (((polyFun_fst.comp hf).pair polyFun_snd).comp_quasiFun (quasiFun_masterDescOpenChild c))
    (hf.comp_quasiFun (quasiFun_masterDescOpenInit c))
    (((polyFun_fst.comp hf).pair polyFun_snd).comp_quasiFun (quasiFun_masterDescOpenCombine c))
    (((polyFun_fst.comp hf).pair polyFun_snd).comp_quasiFun (quasiFun_masterDescOpenFinish c))
    (fun p hp => (hbound p hp).1)
    (fun p j s A hp _ _ => (hbound p hp).2.1 j s A) ?_
    (fun p hp => (hbound p hp).2.2)⟩
  intro p s _ _
  have h := masterDescFoldFinish_size (masterDescLists c (f p)) s
  change Enc.size ((masterDescOpenOps c f).finish (p, s)) ≤ chainBound (f p).1.2.2.2.1.length at h
  rw [hsource p] at h
  exact h.trans (by unfold masterInputCap masterDegree; omega)

end Algo
