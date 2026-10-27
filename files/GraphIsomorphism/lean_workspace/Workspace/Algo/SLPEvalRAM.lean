import Workspace.Algo.SLPEvalOut
import Workspace.Machine.Combine

/-!
# The straight-line-program evaluator on the RAM (Observation 11.1.11)

The specification of `Algo.SLPRAM.slpEvalProg`: on the header `(n, (S, Ker))` and a valid
program `(prog, σ)` it outputs `Algo.obsCore`, the marked elements of the sequence with the
kernel generators, and element `σ`; without a program it outputs `none`.  The running time is
`O((n + 1)(ℓ + 1))` plus the word length of `S` and `Ker` (`ℓ` the length of the program):
every element of the sequence is written once as an array of `n` entries, and every entry is
read in constant time.
-/

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Algo
namespace SLPRAM

open RAM Layout LX Pairing Combine

/-- The time of the branch with a program. -/
def someTime (I : Inp) : ℕ :=
  6 + (7 + (I.LS * 8 + 1)) + ((4 + (I.LP * (18 * I.n + 38) + 1)) +
    ((28 + (I.LP * (14 * I.n + 34) + 1)) +
      (7 * ((2 * I.n + 1) * I.prog.length + I.LK + 2 * I.n + 4) +
        5 * (12 + 2 * I.LS + I.LK + 2 * I.LP + 2 * I.n * I.prog.length) + 14 * I.n + 84 +
        7 * I.LK)))

/-- **The branch with a program.** -/
theorem someBranch_spec (I : Inp) (hv : SLPValid I.n I.S I.prog) (hσ : I.σ < I.prog.length)
    {w : Mem} (h8 : w 8 = 17 + I.Ez) (h5 : w 5 = 16 + (8 + I.LS + I.LK)) (h13 : w 13 = I.n)
    (h14 : w 14 = 17 + I.Ez) :
    RunsTo someBranch (St w I.L0) (fun m => m = initMemAt 16 (Enc.encode (obsCore I.z)))
      (someTime I) := by
  refine ((allocT_spec I h8 h5).seq ((genPhase_spec I hv.1).strengthen (fun m hm => ?_) |>.seq
    ((evalPhase_spec I hv).seq ((outHead_spec I hv).seq (outTail_spec I hv hσ))))).mono
    (le_of_eq (by unfold someTime; ring))
  obtain ⟨w', hm', h8', h15', hfr⟩ := hm
  exact ⟨w', hm', h8', h15', by rw [hfr 13 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num), h13], by rw [hfr 14 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num), h14], by rw [hfr 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num), h5]⟩

/-- The inputs on which the evaluator is specified: a program valid for the generators whose
output index `σ` names an element of the sequence. -/
def SLPInputOK (z : ObsHdr × Option RawSLP) : Prop :=
  match z.2 with
  | none => True
  | some p => SLPValid z.1.1 z.1.2.1 p.1 ∧ p.2 < p.1.length

/-- The length of the program (`0` without one). -/
def slpLen (z : ObsHdr × Option RawSLP) : ℕ :=
  match z.2 with
  | none => 0
  | some p => p.1.length

/-- **Observation 11.1.11, the evaluator on the RAM**, exact form: on every valid input the
program outputs `Algo.obsCore` within an explicit bound, linear in `(n + 1)(ℓ + 1)` and in the
word length of the two generator lists. -/
theorem slpEvalProg_runsOn (z : ObsHdr × Option RawSLP) (hz : SLPInputOK z) :
    RunsOn 16 slpEvalProg z (obsCore z)
      (1000 * ((z.1.1 + 1) * (slpLen z + 1) + (Enc.encode z.1.2.1).length +
        (Enc.encode z.1.2.2).length)) := by
  obtain ⟨⟨n, S, K⟩, p⟩ := z
  cases p with
  | none =>
    have hE : (Enc.encode (((n, (S, K)), none) : ObsHdr × Option RawSLP)).length =
        (Enc.encode S).length + (Enc.encode K).length + 8 := by
      rw [encode_none]; simp; omega
    have hsetup := setup_spec n S K
      (Enc.encode (((n, (S, K)), none) : ObsHdr × Option RawSLP)).length [1, 0]
    refine (hsetup.seq (runsTo_of_exists_St (T := 5 * (headW n S K
      (Enc.encode (((n, (S, K)), none) : ObsHdr × Option RawSLP)).length ++ [1, 0]).length + 64 + 2)
      (by wf_tac) (fun m hm => ?_))).conseq (fun m hm => ?_) (fun m hm => hm) ?_
    · obtain ⟨w, hm', -, -, h8, -, h3⟩ := hm
      refine ⟨w, _, hm', ?_⟩
      refine ex_ifz_eq (by norm_num) (by rw [h3]; rfl) (noneBranch_spec (by
        rw [h8, hE, List.length_append, length_headW]; simp; omega)) (by wf_tac)
    · show m = memAt 16 (fun _ => 0) _
      rw [hm, initMemAt_eq_memAt]
      exact congrArg _ (inWords_none n S K)
    · simp only [slpLen, List.length_append, length_headW, List.length_cons,
        List.length_nil]
      nlinarith
  | some q =>
    obtain ⟨prog, σ⟩ := q
    obtain ⟨hv, hσ⟩ := hz
    let I : Inp := ⟨n, S, K, prog, σ⟩
    have hsetup := setup_spec n S K I.Ez I.Tl
    refine (hsetup.seq (runsTo_of_exists_St (T := someTime I + 2) (by wf_tac)
      (fun m hm => ?_))).conseq (fun m hm => ?_) (fun m hm => hm) ?_
    · obtain ⟨w, hm', h13, h14, h8, h5, h3⟩ := hm
      refine ⟨w, _, hm', ?_⟩
      exact ex_ifz_ne (by norm_num) (by rw [h3]; simp [Inp.Tl])
        (someBranch_spec I hv hσ h8 h5 h13 h14) (by wf_tac)
    · show m = memAt 16 (fun _ => 0) _
      rw [hm, initMemAt_eq_memAt]
      exact congrArg _ I.L0_eq.symm
    · have hLP := I.LP_eq
      simp only [someTime, slpLen]
      show 13 + (someTime I + 2) ≤ _
      simp only [someTime]
      rw [hLP]
      simp only [Inp.LS, Inp.LK] at *
      nlinarith

/-! ## Observation 11.1.11 as a routine on the RAM -/

theorem polyFun_obsHdr : PolyFun obsHdr :=
  ((((polyFun_fst.comp polyFun_fst).comp polyFun_length).pair
    ((polyFun_fst.comp polyFun_snd).pair polyFun_rawPointStab))).of_eq (fun _ => rfl)

/-- The routine of Observation 11.1.11: the header `(n, (S, Ker))` is computed from the group
and the window (the kernel by `Algo.rawPointStab`), paired with the program, and handed to the
evaluator. -/
def obsWindowProg (Ph : Program) : Program :=
  seq (pairProg 16 (seq (fstProg 16) Ph) (sndProg 16)) slpEvalProg

theorem length_encode_slp (h : ObsHdr) (q : Option RawSLP) :
    (Enc.encode q).length ≤ 11 * slpLen (h, q) + 4 := by
  cases q with
  | none => simp [slpLen, Enc.encode]
  | some q =>
    obtain ⟨prog, σ⟩ := q
    show (1 :: (frame (Enc.encode prog) ++ frame [σ])).length ≤ _
    simp [frame, slpLen, length_encode_prog]

theorem length_encode_hdr (h : ObsHdr) :
    (Enc.encode h.2.1).length + (Enc.encode h.2.2).length ≤ (Enc.encode h).length := by
  show _ ≤ (frame (Enc.encode h.1) ++ frame (frame (Enc.encode h.2.1) ++
    frame (Enc.encode h.2.2))).length
  simp [frame]; omega

/-- **Observation 11.1.11 on the RAM.**  On the group `G = ⟨S⟩` on a domain of `n` points, the
window `Δ`, and a straight-line program of length `ℓ` (valid for the generators, its output
index naming an element of the sequence), the routine outputs the generators of
`Aut^Δ_G(x)` and the representative `σ` of `Iso^Δ_G(x, y)` (`Algo.obsWindow`), in time
`C (n + 1)(ℓ + 1) + p(size of the group and the window)` with `p` a polynomial.

> The straight-line program [...] can be evaluated in `O(nℓ)` time, where `ℓ` is the length
> of the program.  Computing the kernel of the `G`-action on `Δ` takes `poly(n)` time. -/
theorem obsWindow_runsOn : ∃ (P : Program) (C : ℕ) (p : ℕ → ℕ), PolyBound p ∧
    ∀ x : ((List ℕ × RawGens) × List ℕ) × Option RawSLP, SLPInputOK (obsHdr x.1, x.2) →
      RunsOn 16 P x (obsWindow x)
        (C * ((x.1.1.1.length + 1) * (slpLen (obsHdr x.1, x.2) + 1)) + p (Enc.size x.1)) := by
  obtain ⟨Ph, Th, ⟨cT, dT, hTb⟩, hPh⟩ := polyFun_obsHdr.time
  obtain ⟨cF, dF, hF⟩ := polyFun_obsHdr.size
  refine ⟨obsWindowProg Ph, 5000,
    fun s => 300 * s + 1100 * (cF * (s + 1) ^ dF) + 10 * (cT * (s + 1) ^ dT) + 3000,
    ((((polyBound_const 300).mul polyBound_id).add
      ((polyBound_const 1100).mul (polyBound_witness cF dF))).add
      ((polyBound_const 10).mul (polyBound_witness cT dT))).add (polyBound_const 3000),
    fun x hx => ?_⟩
  set X := Enc.encode x.1 with hX
  set Y := Enc.encode x.2 with hY
  set F := Enc.encode (obsHdr x.1) with hF'
  have hXs : X.length ≤ Enc.size x.1 := (length_lt_listSize _).le
  have hFs : F.length ≤ cF * (Enc.size x.1 + 1) ^ dF :=
    le_trans (length_lt_listSize _).le (hF x.1)
  have hYl := length_encode_slp (obsHdr x.1) x.2
  have hHl := length_encode_hdr (obsHdr x.1)
  have hTh := hTb (Enc.size x.1)
  have hf : RunsTo (seq (fstProg 16) Ph) (fun m => m = initMemAt 16 (Enc.encode x))
      (fun m => m = initMemAt 16 F) (19 * X.length + 5 * Y.length + 16 + 70 + Th (Enc.size x.1)) :=
    (runsTo_fstProg (by norm_num) X Y).seq (hPh x.1)
  have hg : RunsTo (sndProg 16) (fun m => m = initMemAt 16 (Enc.encode x))
      (fun m => m = initMemAt 16 Y) (19 * Y.length + 5 * X.length + 16 + 80) :=
    runsTo_sndProg (by norm_num) X Y
  have hp := runsTo_pairProg (K := 16) (by norm_num) hf hg
  have he := slpEvalProg_runsOn (obsHdr x.1, x.2) hx
  refine (hp.seq he).mono ?_
  have hE : (Enc.encode x).length = X.length + Y.length + 2 := by
    show (frame X ++ frame Y).length = _
    simp [frame]; omega
  rw [hE]
  have hn : (obsHdr x.1).1 = x.1.1.1.length := rfl
  simp only [hn]
  set n := x.1.1.1.length
  set ℓ := slpLen (obsHdr x.1, x.2)
  have h1 : ℓ + 1 ≤ (n + 1) * (ℓ + 1) := Nat.le_mul_of_pos_left _ (by omega)
  nlinarith

end SLPRAM
end Algo
