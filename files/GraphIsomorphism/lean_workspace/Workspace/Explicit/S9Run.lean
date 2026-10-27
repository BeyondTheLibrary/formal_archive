/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5): the family evaluator of
Sec. 9 (Theorem 9.2.2 on the RAM), bounded at an external degree. Not part of the faithful
formalization.
-/
import Workspace.Explicit.S9Node

/-!
# The run of Sec. 9, bounded at the degree

`Explicit.TN.sbipRun`: on a represented root node of encoded size at most `n`,
`Algo.sbipRun c t d` runs in time `2^{A (log₂ n + 2)^k}·(size + 1)^b` with
`k = max (max (c+2) 4) (t+2)`; for `c = 0` and `t = 3` this is `k = 5`.

The loop runs `Algo.Round.roundCount t (size I) = 3·2^{30 (log₂|I|+2)^{t+2}}+1` steps of the
depth-first evaluator (this is where the exponent `t+2` comes from). Every step meets the
precondition of `Explicit.TN.sbipStepDFS`, since the frames of every reachable state carry
nodes with the resources of the root (`Algo.SbipResources.child`). The states are bounded by
the orbit bound `Algo.sbipOrbitBound K L T` of `Algo.sbipOrbit_size_le`, now with explicit
`K` (the size of a node), `L` (the size of a local family) and `T` (the count):

* `K`: a child is made from a stored graph of the turn, and the turn is bounded at the degree
  `sbipCaseEnvelope n` (`Explicit.exists_sbipGraphs_bound`);
* `L`: `init` is bounded at the degree `n`, on nodes of size at most `K`;
* the cap of `Algo.FamilyEvaluator` is never used for the bound: every state of the capped
  run is a state of the uncapped run (`Explicit.familyEvaluator_iterate`).
-/

set_option synthInstance.maxSize 4096

namespace Explicit

open RAM Algo Babai

/-! ## Bounds that depend on the degree only -/

namespace TN

namespace Bounded

variable {α : Type*} [Enc α] {Pre : ℕ → α → Prop} {k : ℕ}

theorem pow {c : ℕ → α → ℕ} (h : Bounded c Pre k) (e : ℕ) :
    Bounded (fun n a => c n a ^ e) Pre k := by
  induction e with
  | zero => exact (const 1).mono fun _ _ _ => by simp
  | succ e ih => exact (ih.mul h).mono fun _ _ _ => by rw [pow_succ]

/-- A bound evaluated at a bounded argument. -/
theorem tsB_comp (A b : ℕ) {g : ℕ → α → ℕ} (h : Bounded g Pre k) :
    Bounded (fun n a => tsB A k b n (g n a)) Pre k := by
  obtain ⟨A', b', h⟩ := h
  exact ⟨A + b * (A' + 1), b' * b, fun n a ha =>
    (tsB_mono le_rfl le_rfl le_rfl le_rfl (h n a ha)).trans (tsB_comp_le A' A k b' b n _)⟩

/-- `2^{A (log₂ n + 2)^{k'}}·(n+1)^b` for `k' ≤ k` and `1 ≤ k`. -/
theorem tsB_self (A b : ℕ) {k' : ℕ} (hk' : k' ≤ k) (hk : 1 ≤ k) :
    Bounded (fun n _ => tsB A k' b n n) Pre k :=
  ((two_pow_lg A k' hk').mul (((deg hk).add (const 1)).pow b)).mono fun _ _ _ => le_rfl

/-- `(log₂ n + 2)^d` for every `d`, with `1 ≤ k`. -/
theorem lg_pow_any (d : ℕ) (hk : 1 ≤ k) : Bounded (fun n _ => lg n ^ d) Pre k :=
  ((const (2 ^ d)).mul (((deg hk).add (const 1)).pow d)).mono fun n _ _ => by
    rw [← mul_pow]
    apply Nat.pow_le_pow_left
    have := Nat.log_le_self 2 n
    unfold lg
    omega

end Bounded

end TN

/-! ## The orbit bound as a power -/

theorem sbipOrbitBound_le_pow {K L T X : ℕ} (h : K + L + T + 1 ≤ X) :
    sbipOrbitBound K L T ≤ 2 ^ 12 * X ^ 5 := by
  have hX : 1 ≤ X := by omega
  have hB : sbipOutcomeBound L (L + T) ≤ 80 * X ^ 2 := by
    unfold sbipOutcomeBound
    have h1 : L * (2 * (L + T + 2) + 1) ≤ X * (2 * X + 5) := Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  have hM : (T + 1) * L ≤ X * X := Nat.mul_le_mul (by omega) (by omega)
  have hList : Round.familyListBound ((T + 1) * L) (sbipOutcomeBound L (L + T)) ≤
      162 * X ^ 4 := by
    unfold Round.familyListBound
    have h2 : (T + 1) * L * (2 * sbipOutcomeBound L (L + T) + 1) ≤
        (X * X) * (160 * X ^ 2 + 1) :=
      Nat.mul_le_mul hM (by omega)
    have h3 : 1 ≤ X ^ 4 := Nat.one_le_pow _ _ hX
    have h4 : X * X * (160 * X ^ 2 + 1) ≤ 161 * X ^ 4 := by
      have : X * X ≤ X ^ 4 := by nlinarith [Nat.one_le_pow 2 X hX]
      nlinarith
    omega
  have hFrame : Round.familyFrameBound K T ((T + 1) * L) (sbipOutcomeBound L (L + T)) ≤
      660 * X ^ 4 := by
    unfold Round.familyFrameBound
    have h3 : X ≤ X ^ 4 := Nat.le_self_pow (by norm_num) X
    have h4 : 1 ≤ X ^ 4 := Nat.one_le_pow _ _ hX
    omega
  unfold sbipOrbitBound Round.familyStateBound
  have h5 : (T + 1) * (2 * Round.familyFrameBound K T ((T + 1) * L)
      (sbipOutcomeBound L (L + T)) + 1) ≤ X * (1321 * X ^ 4) :=
    Nat.mul_le_mul (by omega) (by have : 1 ≤ X ^ 4 := Nat.one_le_pow _ _ hX; omega)
  have h6 : X * (1321 * X ^ 4) = 1321 * X ^ 5 := by ring
  have h7 : X ^ 4 ≤ X ^ 5 := Nat.pow_le_pow_right hX (by norm_num)
  have h8 : 1 ≤ X ^ 5 := Nat.one_le_pow _ _ hX
  norm_num
  omega

/-! ## The capped evaluator follows the uncapped one -/

/-- Every state of the capped family evaluator is a state of the uncapped run, reached in at
most as many steps. -/
theorem familyEvaluator_iterate {σ : Type*} [Enc σ] (next : σ → σ) (cap : ℕ) (s : σ)
    (j : ℕ) : ∃ i ≤ j, (FamilyEvaluator.step next)^[j] (cap, s) = (cap, next^[i] s) := by
  induction j with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ j ih =>
    obtain ⟨i, hi, he⟩ := ih
    rw [Function.iterate_succ_apply', he]
    by_cases hs : Enc.size (next (next^[i] s)) ≤ cap
    · refine ⟨i + 1, by omega, ?_⟩
      simp only [FamilyEvaluator.step, FamilyEvaluator.select, if_pos hs,
        Function.iterate_succ_apply']
    · refine ⟨i, by omega, ?_⟩
      simp only [FamilyEvaluator.step, FamilyEvaluator.select, if_neg hs]

/-! ## The precondition of the run and the bounds of its nodes -/

/-- The precondition of the run of Sec. 9 at degree `n`: a represented root of encoded size at
most `n`. -/
def RunPre (n : ℕ) (I : RawSbipNode) : Prop := (∃ m, SbipNodeValid m I) ∧ Enc.size I ≤ n

theorem RunPre.nodePre {n : ℕ} {I : RawSbipNode} (h : RunPre n I) : NodePre n I := by
  obtain ⟨⟨m, X, hX⟩, hs⟩ := h
  have hr := hX.resources
  exact ⟨m, ⟨hr.valid, hr.degree.trans hs, hr.witness.trans hs,
    hr.alpha.trans (mono_sbipAlphaEnvelope hs)⟩⟩

/-- **The stored graphs of a node**, bounded at the degree of its resources only. -/
theorem exists_sbipGraphs_bound (c : ℕ) :
    ∃ A b, ∀ n I, NodePre n I → Enc.size (sbipNodeGraphs c I) ≤ tsB A 4 b n n := by
  obtain ⟨A, b, hT⟩ := TN.sbipTurnCases.comp_poly polyFun_sbipTurnChildren
  obtain ⟨S, d, hs⟩ := exists_caseEnvelope_poly
  have hT' := hT.scale (r₀ := S) (r := d) (Pre' := fun n z => Enc.size z ≤ sbipCaseEnvelope n)
    (fun n z hz => ⟨sbipCaseEnvelope n, hs n, hz⟩)
  refine ⟨A * (S + 2 * d + 3) ^ 4 + b * (S + 1), d * b, fun n I hI => ?_⟩
  rcases sbipNodeGraphs_cases_or_empty c I with he | ⟨hd, he⟩
  · rw [he, size_nil]
    exact one_le_tsB _ _ _ _ _
  · rw [he]
    have hz : Enc.size (sbipTurnCase I.1) ≤ sbipCaseEnvelope n := hI.turnPre.2 hd
    have hzn : Enc.size (sbipTurnCase I.1) ≤ tsB S 4 d n n := by
      refine (hz.trans (hs n)).trans ?_
      unfold tsB
      exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num)
        (Nat.le_mul_of_pos_right _ (one_le_lg_pow n 4)))
    exact (hT'.size n _ hz).trans ((tsB_mono le_rfl le_rfl le_rfl le_rfl hzn).trans
      (tsB_comp_le S _ 4 d b n n))

/-- The size bound of the nodes below a root of size at most `n`. -/
def sbipKb (A b n : ℕ) : ℕ := n + 256 * (n + tsB A 4 b n n + sbipAlphaEnvelope n + 1)

theorem sbipNodeChild_size_le {c A b n j : ℕ} {I J : RawSbipNode}
    (hG : ∀ n I, NodePre n I → Enc.size (sbipNodeGraphs c I) ≤ tsB A 4 b n n)
    (hI : NodePre n I) (hc : sbipNodeChild c (I, j) = some J) : Enc.size J ≤ sbipKb A b n := by
  obtain ⟨g, hg, rfl, _⟩ := sbipNodeChild_some hc
  obtain ⟨m, hr⟩ := hI
  obtain ⟨X, hX⟩ := hr.valid
  have h1 := hX.makeChild_size hr.degree hr.witness hr.alpha g
  have h2 := (size_mem_le (List.mem_of_getElem? hg)).trans (hG n I ⟨m, hr⟩)
  unfold sbipKb
  exact h1.trans ((Nat.mul_le_mul_left 256 (Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add_left h2 n) _) 1)).trans (Nat.le_add_left _ _))

/-- The size bound of the local families below a root of size at most `n`. -/
def sbipLb (Ai k0 bi Ag bg n : ℕ) : ℕ := tsB Ai k0 bi n (sbipKb Ag bg n) + n + 1

theorem roundCount_le_of_le (t : ℕ) {N n : ℕ} (h : N ≤ n) :
    Round.roundCount t N ≤ Round.roundCount t n := by
  unfold Round.roundCount
  have h1 := Nat.log_mono_right (b := 2) h
  have h2 : (Nat.log 2 N + 2) ^ (t + 2) ≤ (Nat.log 2 n + 2) ^ (t + 2) :=
    Nat.pow_le_pow_left (by omega) _
  have h3 := Nat.pow_le_pow_right (n := 2) (by norm_num) (Nat.mul_le_mul_left 30 h2)
  omega

namespace TN

/-- **The run of Sec. 9** (Theorem 9.2.2 on the RAM, `Algo.sbipRun`), bounded at the degree:
on a represented root of size at most `n`, time `2^{A (log₂ n + 2)^k}·(size + 1)^b` for every
`k ≥ max (max (c+2) 4) (t+2)`. -/
theorem sbipRun (c t d k : ℕ) (hk : max (c + 2) 4 ≤ k) (ht : t + 2 ≤ k) :
    TN (Algo.sbipRun c t d) RunPre k := by
  have hk1 : 1 ≤ k := by omega
  have hsE : PolyFun (Enc.size :
      Round.EvalState RawSbipNode RawSbipAnswers RawSbipAnswers → ℕ) :=
    AggnSizeRoutine.polyFun_size
  have hsI : PolyFun (Enc.size : RawSbipNode → ℕ) := AggnSizeRoutine.polyFun_size
  /- the set-up, one step, and the read-off -/
  have hinit : TN (Algo.sbipNodeInit c) RunPre k :=
    ((TN.sbipNodeInit c).mono_k hk).restrict (fun n I h => h.nodePre)
  have hstart : TN (sbipRound c).startState RunPre k := by
    have hframe := (ofPoly (polyFun_id (α := RawSbipNode)) RunPre k).pair
      ((ofPoly (polyFun_const 0) RunPre k).pair hinit)
    exact (((hframe.pair (ofPoly (polyFun_const []) RunPre k)).comp_poly polyFun_cons).pair
      (ofPoly (polyFun_const none) RunPre k)).of_eq (fun I => rfl)
  have hsetUp : TN (fun I : RawSbipNode => (Round.roundCount t (Enc.size I),
      ((2 ^ ((Nat.log 2 (Enc.size I) + 2) ^ d) : ℕ), (sbipRound c).startState I))) RunPre k :=
    (ofPoly (hsI.comp (Round.polyFun_roundCount t)) _ _).pair
      ((ofPoly (hsI.comp (aggnPolyFun_sizeCap d)) _ _).pair hstart)
  have hstepS : TN (sbipRound c).stepDFS SbipStatePre k := (sbipStepDFS c).mono_k hk
  have hinner : TN (FamilyEvaluator.step (sbipRound c).stepDFS)
      (fun n (y : ℕ × Round.EvalState RawSbipNode RawSbipAnswers RawSbipAnswers) =>
        SbipStatePre n y.2) k :=
    ((ofPoly polyFun_fst _ _).pair (((ofPoly polyFun_fst _ _).pair ((ofPoly polyFun_snd _ _).pair
      (poly_comp polyFun_snd hstepS))).comp_poly (FamilyEvaluator.polyFun_select hsE))).of_eq
      (fun y => rfl)
  have hstep : TN (fun x : ℕ × (ℕ × Round.EvalState RawSbipNode RawSbipAnswers RawSbipAnswers) =>
      (x.1 - 1, FamilyEvaluator.step (sbipRound c).stepDFS x.2))
      (fun n x => SbipStatePre n x.2.2) k :=
    (ofPoly (polyFun_fst.sub (polyFun_const 1)) _ _).pair (poly_comp polyFun_snd hinner)
  have hread : TN (fun x : ℕ × (ℕ × Round.EvalState RawSbipNode RawSbipAnswers RawSbipAnswers) =>
      x.2.2.2) (fun _ _ => True) k :=
    ofPoly ((polyFun_snd.comp polyFun_snd).comp polyFun_snd) _ _
  /- the count -/
  have hcount : ∀ n I, RunPre n I → Round.roundCount t (Enc.size I) ≤ Round.roundCount t n :=
    fun n I h => roundCount_le_of_le t h.2
  have hT : Bounded (fun n (_ : RawSbipNode) => Round.roundCount t n) RunPre k :=
    (((Bounded.const 3).mul (Bounded.two_pow_lg 30 (t + 2) ht)).add (Bounded.const 1)).mono
      (fun n _ _ => by unfold Round.roundCount lg; exact le_rfl)
  /- the nodes and the local families -/
  obtain ⟨Ag, bg, hG⟩ := exists_sbipGraphs_bound c
  obtain ⟨Ai, bi, hIn⟩ := TN.sbipNodeInit c
  have horbit : ∀ n I, RunPre n I → ∀ i ≤ Round.roundCount t (Enc.size I),
      Enc.size ((sbipRound c).stepDFS^[i] ((sbipRound c).startState I)) ≤
        sbipOrbitBound (sbipKb Ag bg n) (sbipLb Ai (max (c + 2) 4) bi Ag bg n)
          (Round.roundCount t n) := by
    intro n I hI i hi
    refine sbipOrbit_size_le c (fun J => NodePre n J ∧ Enc.size J ≤ sbipKb Ag bg n) _ _ _
      ?_ (fun _ h => h.2) ?_ ?_ ⟨hI.nodePre, ?_⟩ (hi.trans (hcount n I hI))
    · intro J j J' hJ hc
      exact ⟨hJ.1.child hc, sbipNodeChild_size_le hG hJ.1 hc⟩
    · intro J hJ
      obtain ⟨m, hr⟩ := hJ.1
      obtain ⟨X, hX⟩ := hr.valid
      have := hX.first_length_le.trans hr.degree
      unfold sbipLb; omega
    · intro J hJ
      have := (hIn.size n J hJ.1).trans (tsB_mono le_rfl le_rfl le_rfl le_rfl hJ.2)
      unfold sbipLb; omega
    · have := hI.2
      unfold sbipKb; omega
  /- the bound on the states, in the degree only -/
  have e1 := Bounded.deg (Pre := RunPre) hk1
  have hKb : Bounded (fun n (_ : RawSbipNode) => sbipKb Ag bg n) RunPre k := by
    have e2 := Bounded.tsB_self (Pre := RunPre) Ag bg (show 4 ≤ k by omega) hk1
    have e3 : Bounded (fun n (_ : RawSbipNode) => sbipAlphaEnvelope n) RunPre k :=
      (((Bounded.const 2).mul e1).add ((((Bounded.const 2).mul e1).add (Bounded.const 1)).mul
        ((Bounded.const 2).mul e1))).mono (fun n _ _ => by unfold sbipAlphaEnvelope; exact le_rfl)
    exact (e1.add ((Bounded.const 256).mul (((e1.add e2).add e3).add (Bounded.const 1)))).mono
      (fun n _ _ => by unfold sbipKb; exact le_rfl)
  have hLb : Bounded (fun n (_ : RawSbipNode) => sbipLb Ai (max (c + 2) 4) bi Ag bg n)
      RunPre k :=
    (((Bounded.tsB_comp Ai bi hKb).add e1).add (Bounded.const 1)).mono (fun n _ _ => by
      unfold sbipLb
      exact Nat.add_le_add_right (Nat.add_le_add_right
        (tsB_mono le_rfl hk le_rfl le_rfl le_rfl) _) _)
  have hX : Bounded (fun n (_ : RawSbipNode) => sbipKb Ag bg n +
      sbipLb Ai (max (c + 2) 4) bi Ag bg n + Round.roundCount t n + 1) RunPre k :=
    ((hKb.add hLb).add hT).add (Bounded.const 1)
  have hF : Bounded (fun n (_ : RawSbipNode) => 2 * (Round.roundCount t n + 2) +
      2 * (2 * (lg n ^ d + 3) + 2 * (2 ^ 12 * (sbipKb Ag bg n +
        sbipLb Ai (max (c + 2) 4) bi Ag bg n + Round.roundCount t n + 1) ^ 5))) RunPre k :=
    ((Bounded.const 2).mul (hT.add (Bounded.const 2))).add ((Bounded.const 2).mul
      (((Bounded.const 2).mul ((Bounded.lg_pow_any d hk1).add (Bounded.const 3))).add
        ((Bounded.const 2).mul ((Bounded.const (2 ^ 12)).mul (hX.pow 5)))))
  obtain ⟨AF, bF, hF⟩ := hF
  refine (iterateSetup (readOff := fun z : ℕ × Round.EvalState RawSbipNode RawSbipAnswers
      RawSbipAnswers => z.2.2) (Prer := fun _ _ => True) hsetUp hstep hread (hT.mono (fun n I h => hcount n I h))
    ⟨AF, bF, fun n I hI j hj => ?_⟩ (fun n I hI j _ => ?_) (fun _ _ _ => trivial)).of_eq
    (fun I => by unfold Algo.sbipRun Round.runFamily FamilyEvaluator.run; rfl)
  · refine le_trans ?_ (hF n I hI)
    obtain ⟨i, hij, he⟩ := familyEvaluator_iterate (sbipRound c).stepDFS
      (2 ^ ((Nat.log 2 (Enc.size I) + 2) ^ d)) ((sbipRound c).startState I) j
    dsimp only
    rw [he]
    generalize hC : Round.roundCount t (Enc.size I) = C at hj ⊢
    have hCn : C ≤ Round.roundCount t n := hC ▸ hcount n I hI
    have h5 := (horbit n I hI i (hij.trans (hC ▸ hj))).trans (sbipOrbitBound_le_pow le_rfl)
    generalize (sbipRound c).stepDFS^[i] ((sbipRound c).startState I) = st at h5 ⊢
    have h1 := Combine.size_pair_le (C - j) ((2 : ℕ) ^ ((Nat.log 2 (Enc.size I) + 2) ^ d), st)
    have h2 := Combine.size_pair_le ((2 : ℕ) ^ ((Nat.log 2 (Enc.size I) + 2) ^ d)) st
    have h3 : Enc.size (C - j) ≤ Round.roundCount t n + 2 := by
      rw [Small.size_nat]; have := size_le_self (C - j); omega
    have h4 : Enc.size ((2 : ℕ) ^ ((Nat.log 2 (Enc.size I) + 2) ^ d)) ≤ lg n ^ d + 3 := by
      rw [Small.size_nat, Nat.size_pow]
      have := Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.log_mono_right (b := 2) hI.2) 2) d
      unfold lg; omega
    omega
  · obtain ⟨i, _, he⟩ := familyEvaluator_iterate (sbipRound c).stepDFS
      (2 ^ ((Nat.log 2 (Enc.size I) + 2) ^ d)) ((sbipRound c).startState I) j
    show SbipStatePre n ((FamilyEvaluator.step (sbipRound c).stepDFS)^[j]
      ((2 ^ ((Nat.log 2 (Enc.size I) + 2) ^ d)), (sbipRound c).startState I)).2
    rw [he]
    exact (sbipRound c).familyNodes_iterate (NodePre n) (fun J j s J' h hc => h.child hc)
      hI.nodePre i

end TN

end Explicit
