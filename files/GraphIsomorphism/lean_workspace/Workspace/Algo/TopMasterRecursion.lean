import Workspace.Algo.EvaluatorP
import Workspace.Algo.FinalBridge
import Workspace.Algo.TopMasterRound

/-! # From the master round to the final routine

Section 15, Procedure String-Isomorphism, run on the RAM.  The input `(G, x, y)` is first
normalized (`Algo.rawNormSI`), then put at the root of the master recursion as the instance
with the whole domain as window, the identity as representative and no hint
(`Algo.masterRoot`), which is what Theorem 1.1.1 starts from: *"we have a group
`G ≤ Sym(Ω)` and two strings `x, y`"*, with nothing found yet by lines 1–3.

The recursion is read with the lift-free evaluator of `Workspace/Algo/EvaluatorP.lean`.  Its
obligations at one degree `n` are collected in `Algo.MasterRecursion`: the good nodes, the
round of the paper each good node walks (taken at the node's own representative), its
correctness, the progress of Sec. 11.4 read on the raw window size and the raw Johnson
parameter, the well-formedness of the answers, and that the root of every normalized input
is good.  `Algo.siWorkspaceRoutine_of_masterRecursion` turns these obligations, with one
quasipolynomial bound on the number of calls of a round uniform in the degree, into the
final obligation `RAM.SIWorkspaceRoutine`.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Pointwise

/-- The root of the master recursion for a raw input `(gens, x, y)`: the whole domain as
window, the identity as representative, no hint. -/
def masterRoot (I : RawSI) : RawMasterSI :=
  ((List.range I.2.1.length, I.1, List.range I.2.1.length, I.2.1, I.2.2), none)

theorem polyFun_masterRoot : PolyFun masterRoot := by
  have hx : PolyFun (fun I : RawSI => I.2.1) := polyFun_snd.comp polyFun_fst
  have hy : PolyFun (fun I : RawSI => I.2.2) := polyFun_snd.comp polyFun_snd
  have hr : PolyFun (fun I : RawSI => List.range I.2.1.length) := hx.comp polyFun_rangeLength
  exact (hr.pair (polyFun_fst.pair (hr.pair (hx.pair hy)))).pair (polyFun_const none)

/-- **A well-formed raw node of degree `n`**: the checked shape of a window instance
(`Algo.AggnCheckedWindowWF`) on the ambient domain `Fin n`, with the window invariant under
the group the generators generate.  This is the raw content of the paper's standing
assumption that each instance is `⟨Kσ, Δ, x, y⟩` with `Δ` invariant under `K`. -/
def MasterRawNode (n : ℕ) (P : RawMasterSI) : Prop :=
  masterDegree P = n ∧ AggnCheckedWindowWF n P.1 ∧
    IsInvariant (decGroup n P.1.2.1) (winSet n P.1.1)

/-- A node without hint whose window instance has the checked shape passes the input check
at every size parameter. -/
theorem masterInputWF_of_checked (a b : ℕ) {n : ℕ} {W : RawWinSI}
    (hW : AggnCheckedWindowWF n W) : MasterInputWF a b (W, none) := by
  have hsize := aggnCheckedWindow_size hW
  have hdeg : masterDegree ((W, none) : RawMasterSI) = n := hW.2.2.2.2.2.1.1
  refine ⟨?_, ?_, le_rfl⟩
  · have hpair := size_pair_le' ((W, none) : RawMasterSI)
    have hn : Enc.size ((W, none) : RawMasterSI).2 = 2 := size_none
    rw [hdeg]
    change Enc.size ((W, none) : RawMasterSI).1 ≤ _ at hsize
    unfold masterInputCap
    omega
  · change W.1.length ≤ W.2.2.2.1.length
    rw [hW.2.2.2.2.2.1.1]
    exact length_le_of_nodup_lt hW.1 hW.2.1

/-- **The root is a well-formed node**: the whole domain as window is invariant, the identity
is a representative, and the letters of a normalized input are below `2n`. -/
theorem masterRoot_rawNode {n : ℕ} {I : RawSI} (hI : NormSIWF n I) :
    MasterRawNode n (masterRoot I) := by
  have hx : I.2.1.length = n := hI.2.2.1.1
  have hΔ : winSet n (List.range I.2.1.length) = Set.univ := by
    ext u; simp [mem_winSet, hx]
  refine ⟨hx, ⟨List.nodup_range, fun i hi => hx ▸ List.mem_range.mp hi, hI.1, hI.2.1, ?_,
    ⟨hI.2.2.1.1, fun a ha => Nat.lt_succ_of_lt (hI.2.2.1.2 a ha)⟩,
    ⟨hI.2.2.2.1, fun a ha => Nat.lt_succ_of_lt (hI.2.2.2.2 a ha)⟩⟩, ?_⟩
  · change RawPerm.WF n (List.range I.2.1.length)
    rw [hx, ← encPerm_one]
    exact wf_encPerm n 1
  · change IsInvariant (decGroup n I.1) (winSet n (List.range I.2.1.length))
    rw [hΔ]
    intro σ _
    exact Set.image_univ_of_surjective σ.surjective

/-- The root describes the input: its answer is `Iso_G(x, y)`. -/
theorem decWinSI_masterRoot_answer {n : ℕ} (I : RawSI) (hx : I.2.1.length = n) :
    (decWinSI n (masterRoot I).1).answer =
      strIso (decGroup n I.1 : Set (Perm (Fin n))) (decStrN n I.2.1) (decStrN n I.2.2) := by
  have hΔ : winSet n (List.range I.2.1.length) = Set.univ := by
    ext u; simp [mem_winSet, hx]
  have hK : decCoset n (some (I.1, List.range I.2.1.length)) =
      (decGroup n I.1 : Set (Perm (Fin n))) := by
    rw [decCoset_some, hx, ← encPerm_one, decPerm_encPerm]
    exact one_smul (Perm (Fin n)) (decGroup n I.1 : Set (Perm (Fin n)))
  change wIso (winSet n (List.range I.2.1.length))
    (decCoset n (some (I.1, List.range I.2.1.length))) _ _ = _
  rw [hΔ, hK, wIso_univ]
  rfl

/-- §15, **the obligations of the master recursion at one degree `n`**, for a round `R` on
master nodes, in the form the lift-free evaluator asks for (`Algo.Round.runQ_eq_answerG`):

* `impl`: at every good node the fold walks the round `ρ P` of the paper (taken at the node's
  own representative), every child being a child in the sense of `Ch`;
* `correct`: `ρ P` returns `Iso^Δ_K(x,y)` of the decoded instance;
* `progress`: the progress of Sec. 11.4 on the raw window size and Johnson parameter, with at
  most `q(n)` calls per round;
* `finish_wf`: the answers the node prints are well formed;
* `root`: the root of every normalized input of degree `n` is a good node. -/
structure MasterRecursion {ω : Type} (R : Round RawMasterSI ω RawCoset) (n : ℕ) where
  Good : RawMasterSI → Prop
  Ch : RawMasterSI → RawMasterSI → Prop
  ρ : RawMasterSI → SIReduction (Fin n) ℕ (Set (Perm (Fin n)))
  q : ℕ → ℕ
  impl : ImplementsG R Good Ch (fun P => decWinSI n P.1) (fun _ => decCoset n) ρ
  correct : ∀ P, Good P → R.WF P → (ρ P).run = (decWinSI n P.1).answer
  progress : RoundProgress R Good Ch (fun P => decWinSI n P.1) ρ masterWindowSize
    masterParameter q
  mono : Monotone q
  win_le : ∀ P, Good P → R.WF P → masterWindowSize P ≤ R.ground P
  finish_wf : ∀ P s, Good P → R.WF P → RawCoset.WF n (R.finish (P, s))
  root : ∀ I : RawSI, NormSIWF n I → Good (masterRoot I) ∧ R.WF (masterRoot I)

/-- **The final routine from the master recursion.**  If at every degree the master round
meets the obligations of `Algo.MasterRecursion`, with one quasipolynomial bound
`q(m) ≤ 2^((log₂ m + 2)^{c₁})` on the calls of a round for all degrees, then normalization,
the root, and the packaged evaluator solve String Isomorphism in quasipolynomial time. -/
theorem siWorkspaceRoutine_of_masterRecursion {ω : Type} [Enc ω]
    (R : Round RawMasterSI ω RawCoset) (C : Round.RunCostQ R) (c₁ : ℕ)
    (hM : ∀ n : ℕ, ∃ M : MasterRecursion R n,
      ∀ m : ℕ, M.q m ≤ 2 ^ ((Nat.log 2 m + 2) ^ c₁)) : SIWorkspaceRoutine := by
  have hent : PolyFun (fun I : RawSI => masterRoot (rawNormSI I)) :=
    polyFun_rawNormSI.comp polyFun_masterRoot
  have hrun := hent.comp_quasi (R.quasiPolyFun_runAnswerQ C c₁)
  obtain ⟨P, T, hT, hP⟩ := hrun.time
  obtain ⟨S, hSb, hSmono, hSle⟩ := hrun.size.exists_polyBound
  refine ⟨P, T, S, hT, hSb, hSmono, fun n s => ?_⟩
  refine CleanSolveAt.transfer (e := rawOfSI)
    (R' := fun (r : RawSI) (b' : RawCoset) =>
      b' = R.runAnswerQ C c₁ (masterRoot (rawNormSI r)) ∧ Enc.size b' ≤ S (Enc.size r))
    (fun a => (encode_si_eq a).symm) ?_
    (fun r => ⟨R.runAnswerQ C c₁ (masterRoot (rawNormSI r)), ⟨rfl, hSle r⟩, hP r⟩)
  intro a b' hb'
  obtain ⟨M, hq⟩ := hM n
  set I := rawNormSI (rawOfSI a) with hIdef
  have hwf : NormSIWF n I := rawNormSI_rawOfSI_wf a
  obtain ⟨hG, hW⟩ := M.root I hwf
  obtain ⟨st, hrunQ, hans⟩ := R.runQ_eq_answerG C M.impl M.correct M.progress M.mono c₁ hq
    M.win_le (masterRoot I) hG hW
  have hb'eq : b' = R.finish (masterRoot I, st) := by
    rw [hb'.1]
    change (R.runQ C c₁ (masterRoot I)).join = _
    rw [hrunQ]
    rfl
  have hraw : RawSIRel n I b' := by
    refine ⟨hb'eq ▸ M.finish_wf _ st hG hW, ?_⟩
    rw [hb'eq, hans, decWinSI_masterRoot_answer I hwf.2.2.1.1]
  obtain ⟨b, hbenc, hbrel⟩ := rawNormSI_answer a b' hraw
  have hsize : Enc.size b ≤ S (Enc.size a) := by
    have h1 : Enc.size b = Enc.size b' := size_eq_of_encode_eq hbenc
    have h2 : Enc.size (rawOfSI a) = Enc.size a :=
      size_eq_of_encode_eq (encode_si_eq a).symm
    rw [h1, ← h2]
    exact hb'.2
  exact ⟨b, hbenc, hbrel, hsize⟩

end Algo

#print axioms Algo.siWorkspaceRoutine_of_masterRecursion
