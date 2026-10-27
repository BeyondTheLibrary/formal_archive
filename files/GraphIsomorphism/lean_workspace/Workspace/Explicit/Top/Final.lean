/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5), part 2: the assembly.
Not part of the faithful formalization.
-/
import Workspace.Explicit.Top.Recursion
import Workspace.Explicit.Top.Setup
import Workspace.Explicit.Top.Loop
import Workspace.Machine.Final

/-!
# The Master in time `2^{c (log₂ N + 2)^5}`

`Explicit.main_of_bounds`: from the specifications of the parameters (`Explicit.ParamsOK`) and
the explicit costs of one node (`Explicit.StepBounds`), one RAM program solves String
Isomorphism, for every degree and alphabet, within `2^{c (log₂ N + 2)^5}` steps on inputs of
size `N`, for one constant `c`.

The program is: the bridge `up`; the entry (normalization and root); the set-up
`(countE K n, startState J)` with `K = 4Aw + 14Ap + 24` (`Explicit.nodesE_le`); the loop of
`countE K n` depth-first steps; the read-off; the bridge `down`. Its correctness is
`Explicit.runE_eq_answer` at the recursion of `Explicit.masterRecE`; its time is added up
pointwise (`Explicit.runsTo_recursion_pw`), with every state of the run bounded by
`Explicit.STf` (the run invariant, `StepBounds.inv_size`), and the sum is in the class
`Explicit.Q5`.
-/

set_option synthInstance.maxSize 4096

namespace Explicit

open RAM RAM.Targets Algo Babai

variable {p : Params} {cam : RawGens × List ℕ → Option RawCameron}

theorem countE_mono (K : ℕ) : Monotone (countE K) := by
  intro a b hab
  unfold countE
  have h1 := Nat.log_mono_right (b := 2) hab
  have h2 : (Nat.log 2 a + 2) ^ 5 ≤ (Nat.log 2 b + 2) ^ 5 := Nat.pow_le_pow_left (by omega) 5
  have h3 : 2 ^ (K * (Nat.log 2 a + 2) ^ 5) ≤ 2 ^ (K * (Nat.log 2 b + 2) ^ 5) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ h2)
  omega

theorem natSize_le_self (x : ℕ) : Nat.size x ≤ x :=
  Nat.size_le.2 Nat.lt_two_pow_self

/-! ## The time bound -/

/-- The polynomial bound on the root and its degree. -/
def SJf (sb : StepBounds p cam) (N : ℕ) : ℕ := 2 ^ sb.kP * (N + 1) ^ sb.dP

/-- The bound on the states of the run (`StepBounds.inv_size`). -/
def STf (sb : StepBounds p cam) (N : ℕ) : ℕ := 2 ^ (sb.kS * lg (SJf sb N) ^ 5)

/-- The bound on the loop state `(counter, state)`. -/
def PBf (sb : StepBounds p cam) (K N : ℕ) : ℕ :=
  2 * (countE K (SJf sb N) + 2) + 2 * STf sb N

/-- The bound on one round of the loop. -/
def BBf (sb : StepBounds p cam) (K N : ℕ) : ℕ :=
  2 ^ (sb.As * lg (SJf sb N) ^ 5) * (PBf sb K N + 1) ^ sb.ds

/-- **The time bound of the workspace routine** on an input of size `N`: entry, set-up, loop,
read-off. -/
def Tf (sb : StepBounds p cam) (K A₁ b₁ N : ℕ) : ℕ :=
  SJf sb N + (tsB A₁ 5 b₁ (SJf sb N) (SJf sb N) +
    (countE K (SJf sb N) * (BBf sb K N + 2) + 1 + 2 ^ sb.kP * (PBf sb K N + 1) ^ sb.dP))

/-- The bound on the size of the answer. -/
def Sf (sb : StepBounds p cam) (N : ℕ) : ℕ := sb.cost.bound (SJf sb N)

theorem SJf_mono (sb : StepBounds p cam) : Monotone (SJf sb) := by
  intro a b hab
  unfold SJf
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

theorem q5_countE (K : ℕ) : Q5 (countE K) :=
  (((q5_const 3).mul (q5_two_pow_lg K 5 le_rfl)).add (q5_const 1)).mono fun N => le_rfl

theorem q5_Tf (sb : StepBounds p cam) (K A₁ b₁ : ℕ) : Q5 (Tf sb K A₁ b₁) := by
  have hS : ∀ N, SJf sb N ≤ 2 ^ sb.kP * (N + 1) ^ sb.dP := fun N => le_rfl
  have hSJ : Q5 (SJf sb) := q5_poly sb.kP sb.dP
  have hce : Q5 (fun N => countE K (SJf sb N)) := (q5_countE K).comp_poly hS
  have hst : Q5 (STf sb) := (q5_two_pow_lg sb.kS 5 le_rfl).comp_poly hS
  have hPB : Q5 (PBf sb K) :=
    (((q5_const 2).mul (hce.add (q5_const 2))).add ((q5_const 2).mul hst)).mono fun N => le_rfl
  have hBB : Q5 (BBf sb K) :=
    (((q5_two_pow_lg sb.As 5 le_rfl).comp_poly hS).mul ((hPB.add (q5_const 1)).pow sb.ds)).mono
      fun N => le_rfl
  have hts : Q5 (fun N => tsB A₁ 5 b₁ (SJf sb N) (SJf sb N)) := (q5_tsB A₁ b₁).comp_poly hS
  exact (hSJ.add (hts.add (((hce.mul (hBB.add (q5_const 2))).add (q5_const 1)).add
    ((q5_const (2 ^ sb.kP)).mul ((hPB.add (q5_const 1)).pow sb.dP))))).mono fun N => le_rfl

theorem q5_Sf (sb : StepBounds p cam) : Q5 (Sf sb) :=
  ((q5_poly sb.kB sb.dB).mono sb.bound_le).comp_poly (fun N => le_rfl)

theorem Sf_mono (sb : StepBounds p cam) : ∀ n n', n ≤ n' → Sf sb n ≤ Sf sb n' :=
  fun _ _ h => sb.cost.mono_bound (SJf_mono sb h)

/-! ## The workspace routine -/

set_option maxHeartbeats 1000000 in
/-- **One input.** The program `entry; set-up; loop; read-off` on the raw form of an input
`a` of degree `n`: it halts within `Tf (size a)` steps holding an answer related to `a`. -/
theorem runE_top {K : ℕ} (rk : RecOK p cam K) (sb : StepBounds p cam) {Pent P₁ Q P₃ : Program} {A₁ b₁ : ℕ}
    (hPent : CleanComputeAt 16 Pent (fun I : RawSI => masterRoot (rawNormSI I))
      (fun N => 2 ^ sb.kP * (N + 1) ^ sb.dP))
    (hP₁ : ∀ J, RootPre p cam J → RunsTo P₁
      (fun m => m = initMemAt 16 (Enc.encode J))
      (fun m' => m' = initMemAt 16 (Enc.encode (setUpE p cam K J)))
      (tsB A₁ 5 b₁ (Enc.size J) (Enc.size J)))
    (hQ : ∀ (n k : ℕ) (x : EvalStateE), sb.Inv n x →
      RunsTo Q (fun m => m = initMemAt 16 (Enc.encode ((k, x) : ℕ × EvalStateE)))
        (fun m' => m' = initMemAt 16
          (Enc.encode ((k - 1, (masterRoundE p cam).stepDFS x) : ℕ × EvalStateE)))
        (2 ^ (sb.As * (Nat.log 2 n + 2) ^ 5) * (Enc.size ((k, x) : ℕ × EvalStateE) + 1) ^ sb.ds))
    (hP₃ : CleanComputeAt 16 P₃ (fun x : ℕ × EvalStateE => x.2.2.join)
      (fun N => 2 ^ sb.kP * (N + 1) ^ sb.dP))
    (n s : ℕ) (a : SIInput n s) :
    ∃ b : Option (List (Equiv.Perm (Fin n)) × Equiv.Perm (Fin n)),
      (SIRel n s a b ∧ Enc.size b ≤ Sf sb (Enc.size a)) ∧
      RunsTo (seq Pent (seq P₁ (seq (whileNz (16 + 2) Q) P₃)))
        (fun m => m = initMemAt 16 (Enc.encode a))
        (fun m' => m' = initMemAt 16 (Enc.encode b))
        (Tf sb K A₁ b₁ (Enc.size a)) := by
  have hNr : Enc.size (rawOfSI a) = Enc.size a := size_eq_of_encode_eq (encode_si_eq a).symm
  set N := Enc.size a with hNdef
  set I := rawNormSI (rawOfSI a) with hI
  set J := masterRoot I with hJ
  have hwf : NormSIWF n I := rawNormSI_rawOfSI_wf a
  obtain ⟨hG, hW⟩ := (rk.M n).root I hwf
  have hG' : MasterNodeGood n J := rk.good n J hG
  have hW' : (masterRoundE p cam).WF J := hW
  have hground : (masterRoundE p cam).ground J = n := hG'.1.1
  -- sizes
  have hJsize : Enc.size J ≤ SJf sb N := by
    have := sb.entry_size (rawOfSI a)
    rw [hNr] at this
    exact this
  have hgJ : (masterRoundE p cam).ground J ≤ SJf sb N := (sb.cost.ground_le J).trans hJsize
  -- correctness
  have hnodes : (masterRoundE p cam).nodes ((masterRoundE p cam).measure J + 1) J
      ≤ 2 ^ (K * (Nat.log 2 n + 2) ^ 5) := rk.nodes n J hG hW'
  have hN : 3 * (masterRoundE p cam).nodes ((masterRoundE p cam).measure J + 1) J + 1
      ≤ countE K ((masterRoundE p cam).ground J) := by
    rw [hground]
    unfold countE
    omega
  obtain ⟨st, hrun, hans⟩ := runE_eq_answer (masterRoundE p cam) sb.cost (countE K)
    (rk.M n).impl (rk.M n).correct (rk.M n).progress J hG hW' hN
  -- the count and the final state as opaque variables (they must never be unfolded)
  obtain ⟨cnt, hcnt⟩ : ∃ c, c = countE K ((masterRoundE p cam).ground J) := ⟨_, rfl⟩
  obtain ⟨xf, hxf⟩ : ∃ x : EvalStateE,
      x = ((masterRoundE p cam).stepDFS)^[cnt] ((masterRoundE p cam).startState J) := ⟨_, rfl⟩
  have hxf2 : xf.2 = some ((masterRoundE p cam).finish (J, st)) := by
    have := hrun
    rw [runE, stepCountE_of_wf (masterRoundE p cam) sb.cost (countE K) hW', ← hcnt,
      ← hxf] at this
    exact this
  set b' := (masterRoundE p cam).finish (J, st) with hb'
  have hraw : RawSIRel n I b' := by
    refine ⟨(rk.M n).finish_wf J st hG hW', ?_⟩
    exact hans.trans (decWinSI_masterRoot_answer I hwf.2.2.1.1)
  obtain ⟨b, hbenc, hbrel⟩ := rawNormSI_answer a b' hraw
  -- the invariant and the state sizes along the run
  have hGd : MasterNodeGood (masterDegree J) J := by
    have : masterDegree J = n := hG'.1.1
    rw [this]; exact hG'
  have hinv : ∀ j, sb.Inv (masterDegree J)
      (((masterRoundE p cam).stepDFS)^[j] ((masterRoundE p cam).startState J)) := by
    intro j
    induction j with
    | zero => exact sb.inv_start J hW' hGd
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact sb.inv_step _ _ ih
  have hcntle : cnt ≤ countE K (SJf sb N) := by rw [hcnt]; exact countE_mono K hgJ
  have hST : ∀ j, Enc.size (((masterRoundE p cam).stepDFS)^[j]
      ((masterRoundE p cam).startState J)) ≤ STf sb N := by
    intro j
    refine (sb.inv_size _ _ (hinv j)).trans ?_
    have : masterDegree J ≤ SJf sb N := hgJ
    exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (lg_pow_mono this le_rfl))
  have hpair : ∀ k ≤ cnt, ∀ j,
      Enc.size ((k, ((masterRoundE p cam).stepDFS)^[j] ((masterRoundE p cam).startState J)) :
        ℕ × EvalStateE) ≤ PBf sb K N := by
    intro k hk j
    generalize hx : ((masterRoundE p cam).stepDFS)^[j] ((masterRoundE p cam).startState J) = x
    have h4 := hST j
    rw [hx] at h4
    have h1 := Combine.size_pair_le k x
    have h2 : Enc.size k = Nat.size k + 2 := Small.size_nat k
    have h3 := natSize_le_self k
    have h5 : PBf sb K N = 2 * (countE K (SJf sb N) + 2) + 2 * STf sb N := rfl
    generalize Enc.size ((k, x) : ℕ × EvalStateE) = A at h1 ⊢
    generalize Enc.size x = B at h1 h4
    generalize Enc.size k = C at h1 h2
    omega
  -- the answer's size
  have hbsize : Enc.size b ≤ Sf sb N := by
    have h1 : Enc.size b = Enc.size b' := size_eq_of_encode_eq hbenc
    have h2 : Enc.size b' ≤ sb.cost.bound ((masterRoundE p cam).ground J) :=
      (masterRoundE p cam).retOkQ_le sb.cost ((masterRoundE p cam).ground J) cnt xf
        (hxf ▸ (masterRoundE p cam).stateOkQ_iterate sb.cost J hW' cnt) b' hxf2
    rw [h1]
    exact h2.trans (sb.cost.mono_bound hgJ)
  refine ⟨b, ⟨hbrel, hbsize⟩, ?_⟩
  -- the run
  have hQwf : Wf Q := (hQ (masterDegree J) 0 _ (hinv 0)).wf
  have hloopQ : ∀ j < cnt, RunsTo Q
      (fun m => m = initMemAt 16 (Enc.encode ((cnt - j,
        ((masterRoundE p cam).stepDFS)^[j] ((masterRoundE p cam).startState J)) : ℕ × EvalStateE)))
      (fun m' => m' = initMemAt 16 (Enc.encode (((cnt - j) - 1, (masterRoundE p cam).stepDFS
        (((masterRoundE p cam).stepDFS)^[j] ((masterRoundE p cam).startState J))) :
          ℕ × EvalStateE)))
      (BBf sb K N) := by
    intro j hj
    refine (hQ (masterDegree J) (cnt - j) _ (hinv j)).mono ?_
    have h1 : 2 ^ (sb.As * (Nat.log 2 (masterDegree J) + 2) ^ 5)
        ≤ 2 ^ (sb.As * lg (SJf sb N) ^ 5) := by
      have : masterDegree J ≤ SJf sb N := hgJ
      exact Nat.pow_le_pow_right (by norm_num)
        (Nat.mul_le_mul_left _ (lg_pow_mono this le_rfl))
    have h2 := hpair (cnt - j) (Nat.sub_le _ _) j
    have h3 : (Enc.size ((cnt - j, ((masterRoundE p cam).stepDFS)^[j]
        ((masterRoundE p cam).startState J)) : ℕ × EvalStateE) + 1) ^ sb.ds
        ≤ (PBf sb K N + 1) ^ sb.ds := Nat.pow_le_pow_left (by omega) _
    exact Nat.mul_le_mul h1 h3
  have hread : RunsTo P₃ (fun m => m = initMemAt 16 (Enc.encode ((0, xf) : ℕ × EvalStateE)))
      (fun m' => m' = initMemAt 16 (Enc.encode xf.2.join))
      (2 ^ sb.kP * (PBf sb K N + 1) ^ sb.dP) := by
    refine (hP₃ ((0, xf) : ℕ × EvalStateE)).mono (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_left ?_ _))
    have := hpair 0 (Nat.zero_le _) cnt
    rw [← hxf] at this
    omega
  rw [hxf] at hread
  have hset : RunsTo P₁ (fun m => m = initMemAt 16 (Enc.encode J))
      (fun m' => m' = initMemAt 16 (Enc.encode ((cnt, (masterRoundE p cam).startState J) :
        ℕ × EvalStateE)))
      (tsB A₁ 5 b₁ (SJf sb N) (SJf sb N)) := by
    have hsu : setUpE p cam K J
        = ((cnt, (masterRoundE p cam).startState J) : ℕ × EvalStateE) := by
      rw [hcnt]; rfl
    have h := (hP₁ J ⟨hW', rfl, hGd⟩).mono (tsB_mono le_rfl le_rfl le_rfl hJsize hJsize)
    rw [hsu] at h
    exact h
  have hrec : RunsTo (seq P₁ (seq (whileNz (16 + 2) Q) P₃))
      (fun m => m = initMemAt 16 (Enc.encode J))
      (fun m' => m' = initMemAt 16 (Enc.encode
        (((masterRoundE p cam).stepDFS)^[cnt] ((masterRoundE p cam).startState J)).2.join))
      (tsB A₁ 5 b₁ (SJf sb N) (SJf sb N) + (cnt * (BBf sb K N + 2) + 1 +
        2 ^ sb.kP * (PBf sb K N + 1) ^ sb.dP)) :=
    runsTo_recursion_pw (K := 16) (setUp := fun _ : RawMasterSI =>
      ((cnt, (masterRoundE p cam).startState J) : ℕ × EvalStateE))
      (step := (masterRoundE p cam).stepDFS) (readOff := fun x : EvalStateE => x.2.join)
      J hset hloopQ hQwf hread
  have hent : RunsTo Pent (fun m => m = initMemAt 16 (Enc.encode (rawOfSI a)))
      (fun m' => m' = initMemAt 16 (Enc.encode J)) (SJf sb N) := by
    have := hPent (rawOfSI a)
    rw [hNr] at this
    exact this
  have htot := hent.seq hrec
  have henc_a : Enc.encode a = Enc.encode (rawOfSI a) := encode_si_eq a
  have henc_b : Enc.encode b = Enc.encode
      (((masterRoundE p cam).stepDFS)^[cnt] ((masterRoundE p cam).startState J)).2.join := by
    rw [hbenc, ← hxf, hxf2]
    rfl
  rw [henc_a, henc_b]
  refine htot.mono ?_
  have h2 : cnt * (BBf sb K N + 2) ≤ countE K (SJf sb N) * (BBf sb K N + 2) :=
    Nat.mul_le_mul_right _ hcntle
  show _ ≤ SJf sb N + (tsB A₁ 5 b₁ (SJf sb N) (SJf sb N) +
    (countE K (SJf sb N) * (BBf sb K N + 2) + 1 + 2 ^ sb.kP * (PBf sb K N + 1) ^ sb.dP))
  omega

/-- **The workspace routine in time `Tf`.** For every degree and alphabet, the program
`entry; set-up; loop; read-off` solves String Isomorphism at the workspace convention within
`Tf` steps, with answers of size at most `Sf`, once the recursion has `Explicit.RecOK`. -/
theorem cleanSolveAt_of_rec {K : ℕ} (rk : RecOK p cam K) (sb : StepBounds p cam) :
    ∃ (P : Program) (A₁ b₁ : ℕ), ∀ n s : ℕ, CleanSolveAt 16 P
      (fun (a : SIInput n s) (b : Option (List (Equiv.Perm (Fin n)) × Equiv.Perm (Fin n))) =>
        SIRel n s a b ∧ Enc.size b ≤ Sf sb (Enc.size a))
      (Tf sb K A₁ b₁) := by
  obtain ⟨Pent, hPent⟩ := sb.entry
  obtain ⟨A₁, b₁, ⟨⟨P₁, hP₁⟩, -⟩⟩ := ts_setUpE sb K
  obtain ⟨Q, hQ⟩ := sb.step
  obtain ⟨P₃, hP₃⟩ := sb.readOff
  refine ⟨seq Pent (seq P₁ (seq (whileNz (16 + 2) Q) P₃)), A₁, b₁, fun n s a => ?_⟩
  exact runE_top rk sb hPent (fun J hJ => hP₁.2 J hJ) hQ hP₃ n s a

/-- **The Master in time `2^{c(log₂ N+2)^5}`**, from a recursion with `Explicit.RecOK` and the
explicit costs of one node. -/
theorem main_of_rec {K : ℕ} (rk : RecOK p cam K) (sb : StepBounds p cam) :
    ∃ (c : ℕ) (P : Program), ∀ n s : ℕ,
      SolvesInTime P (SIRel n s) (fun N => 2 ^ (c * (Nat.log 2 N + 2) ^ 5)) := by
  obtain ⟨P, A₁, b₁, hP⟩ := cleanSolveAt_of_rec rk sb
  set T := Tf sb K A₁ b₁
  have hq : Q5 (bridgeTime T (Sf sb)) := by
    have := (((((q5_const 18).mul q5_id).add (q5_const 78)).add
      ((q5_Tf sb K A₁ b₁).add
      (((q5_const 7).mul (q5_Sf sb)).add (q5_const 34)))))
    exact this.mono fun N => le_rfl
  obtain ⟨c, hc'⟩ := hq
  exact ⟨c, seq Bridge.up (seq P Bridge.down), fun n s =>
    (solvesInTime_of_cleanSolveAt_small (hP n s) (Sf_mono sb)).mono hc'⟩

/-- **The Master in time `2^{c(log₂ N+2)^5}`**, from the specifications of the parameters and
the explicit costs of one node: one program solves String Isomorphism for every degree and
alphabet within `2^{c (log₂ N + 2)^5}` steps on inputs of size `N`. -/
theorem main_of_bounds (hc : PolyFun cam) (hs : CameronSpec cam) (ok : ParamsOK p)
    (sb : StepBounds p cam) :
    ∃ (c : ℕ) (P : Program), ∀ n s : ℕ,
      SolvesInTime P (SIRel n s) (fun N => 2 ^ (c * (Nat.log 2 N + 2) ^ 5)) := by
  obtain ⟨rk⟩ := recOK_of_paramsOK ok sb hc hs
  exact main_of_rec rk sb

end Explicit
