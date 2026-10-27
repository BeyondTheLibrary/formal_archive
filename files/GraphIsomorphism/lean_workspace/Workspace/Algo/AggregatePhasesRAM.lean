/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the two phases of Procedure AggregateCertificates (§13.2) as one RAM
routine.
-/
import Workspace.Algo.LocalCertCompareRAM
import Workspace.Algo.ListMapRAM
import Workspace.LocalCertificates.AggregateRound

/-!
# The certificate and comparison phases of Theorem 13.2.1 on the RAM

The proof of Theorem 13.2.1 (§13.2) opens with two phases:

> Run the LocalCertificates routine for both inputs `x`, `y` and all test sets `T`.
> Run the CompareLocalCertificates routine for all pairs `((x, T), (x', T'))` where `x` is
> fixed, `x' ∈ {x, y}`, and `T, T'` are test sets (a total of `2·C(m,t)²` runs).

`Algo.theorem_13_2_1_phases_ram` runs both phases as one RAM routine. It takes the prepared
inputs of the runs (one list for the certificate runs, one for the comparison runs), runs the
program of `Algo.theorem_13_1_3_ram` on each entry of the first list and the program of
`Algo.proposition_13_1_11_ram` on each entry of the second, and returns the two lists of
answers. As in §13.1, the String Isomorphism calls are counted apart from the rest: the
routine runs within

  `10¹¹ · ∑_{W ∈ calls} τ(W) + (#runs + 2) · t! · poly(size of the input)`

steps, and `Algo.theorem_13_2_1_phases_ram_spec` says the calls number at most
`#runs · t!·n²`, all on windows of at most `n/t` points; with the paper's `2·C(m,t)`
certificate runs and `2·C(m,t)²` comparison runs this is at most `Babai.aggregateRoundCost`.

What is not here: the preparation of the inputs (the enumeration of the test sets, the
initial states `G_T`, and the transporter cosets of line 01 of the comparison), and the case
analysis (1), (2a), (2b), (3) that follows the two phases. The whole of Theorem 13.2.1, with
these steps, is `Algo.theorem_13_2_1_ram` (`Algo/Agg1321RAM.lean`), which uses this routine.
-/

namespace Algo
open RAM RAM.Targets Babai
open Equiv (Perm)

variable {n m : ℕ} {G : Subgroup (Perm (Fin n))}

/-- §13.2: the input of one certificate run is prepared: a string `x`, a test set `T` of
`t` points, and the state `G_T` of line 01 of Procedure LocalCertificates. -/
def CertRunInput (ϕ : G →* Perm (Fin m)) (t : ℕ) (p : RawLCLoop) : Prop :=
  ∃ hc : LCCtxWF n m p.1.1 p.1.2,
    StateFor hc (stages ϕ (decStrN n p.1.1) (winSet m p.1.2) 0) p.2 ∧ p.1.2.length = t

/-- §13.2: the input of one comparison run is prepared: strings `x`, `x'`, a test set `T` of
`t` points with the state `G_T`, and the transporter coset of line 01 for some `T'`. -/
def CompareRunInput (ϕ : G →* Perm (Fin m)) (t : ℕ) (z : RawPCLoop) : Prop :=
  ∃ hc : LCCtxWF n m z.1.1.1 z.1.1.2, z.2.1.length = n ∧
    StateFor hc (stages ϕ (decStrN n z.1.1.1) (winSet m z.1.1.2) 0) z.1.2 ∧
    (∃ T' : Set (Fin m), decCoset n z.2.2 = pcTransporters ϕ (winSet m z.1.1.2) T') ∧
    z.1.1.2.length = t

/-- The String Isomorphism calls of the two phases. -/
def phaseCalls (ansQ : RawWinSI → RawCoset) (l1 : List RawLCLoop) (l2 : List RawPCLoop) :
    List RawWinSI :=
  l1.flatMap (lcCallsQ ansQ) ++ l2.flatMap (pcCallsQ ansQ)

/-- The output of Procedure LocalCertificates is polynomially bounded in its input, whatever
answers the calls receive. -/
theorem exists_size_lcOut_le :
    ∃ c d : ℕ, ∀ (solve : RawLCSI → RawCoset) (p : RawLCLoop),
      Enc.size (lcOut solve p) ≤ pw c d (Enc.size p) := by
  obtain ⟨-, co, dO, -, hs⟩ := polyFun_witness lcwPolyFun_out
  obtain ⟨Z, hZ⟩ : ∃ f : ℕ → ℕ, ∀ M, f M = pw co dO (4 * M + 2 * lcStBound M) :=
    ⟨_, fun _ => rfl⟩
  have hZp : PolyBound Z := by
    rw [show Z = _ from funext hZ]
    exact (polyBound_pw co dO).comp (((polyBound_const 4).mul polyBound_id).add
      ((polyBound_const 2).mul polyBound_lcStBound))
  obtain ⟨c, d, hcd⟩ := hZp
  refine ⟨c, d, fun solve p => ?_⟩
  rw [lcwOut_eq]
  have e : lcRun solve p = (lcStep solve)^[p.1.1.length] p := rfl
  have h1 := hs (lcRun solve p)
  have h2 := size_pair_le' (lcRun solve p)
  have h3 : (lcRun solve p).1 = p.1 := by rw [e]; exact lcStep_iterate_fst solve _ p
  have h4 : Enc.size (lcRun solve p).2 ≤ max (Enc.size p.2) (lcStBound (Enc.size p.1)) := by
    rw [e]; exact size_lcStep_iterate_le solve _ p
  have h5 := size_fst_le' p
  have h6 := size_snd_le' p
  have h7 : lcStBound (Enc.size p.1) ≤ lcStBound (Enc.size p) := mono_lcStBound h5
  have h8 : max (Enc.size p.2) (lcStBound (Enc.size p.1))
      ≤ Enc.size p + lcStBound (Enc.size p) := max_le (by omega) (by omega)
  rw [h3] at h2
  have h9 : Enc.size (lcRun solve p) ≤ 4 * Enc.size p + 2 * lcStBound (Enc.size p) := by
    omega
  have h10 : co * (Enc.size (lcRun solve p) + 1) ^ dO
      ≤ pw co dO (4 * Enc.size p + 2 * lcStBound (Enc.size p)) := pw_mono co dO h9
  have h11 := hcd (Enc.size p)
  rw [hZ] at h11
  exact le_trans h1 (le_trans h10 h11)

/-- The output of the paired comparison procedure is polynomially bounded in its input. -/
theorem size_pcOut_le {ϕ : G →* Perm (Fin m)} {t : ℕ} {z : RawPCLoop}
    (hz : CompareRunInput ϕ t z) {ansQ : RawWinSI → RawCoset}
    (hQ : ∀ W, WinWF n W → decCoset n (ansQ W) = (decWinSI n W).answer) :
    Enc.size (pcOut (lcSolveQ ansQ) z) ≤ Enc.size z + lcBound (4 * Enc.size z) := by
  obtain ⟨⟨⟨xs, tdom⟩, st0⟩, ys, q0⟩ := z
  obtain ⟨hc, hy, h0, ⟨T', hq0⟩, -⟩ := hz
  have hsolve : ∀ I, LCWF n I → decCoset n (lcSolveQ ansQ I) = (decLCSI n I).answer :=
    fun I hI => lcSolveQ_correct hQ hI
  set z0 : RawPCLoop := (((xs, tdom), st0), ys, q0) with hz0
  have hliveI : ∀ j, pcCond ((pcStep (lcSolveQ ansQ))^[j] z0) = true →
      LCWF n (pcInst ((pcStep (lcSolveQ ansQ))^[j] z0)) := by
    intro j hj
    obtain ⟨-, st, h1, h2⟩ := pc_live hsolve hy h0 hq0 hj
    have hctx := pcStep_iterate_ctx (lcSolveQ ansQ) j z0
    have he : (pcStep (lcSolveQ ansQ))^[j] z0
        = (((xs, tdom), st), ys, ((pcStep (lcSolveQ ansQ))^[j] z0).2.2) :=
      Prod.ext h1 (Prod.ext hctx.2 rfl)
    rw [he]; exact lcwf_pcInst h2 hy _
  have h1 := size_pcStep_iterate_q hliveI xs.length
  have h2 : Enc.size q0 ≤ Enc.size z0 :=
    le_trans (size_snd_le' z0.2) (size_snd_le' z0)
  have hxs : Enc.size xs ≤ Enc.size z0 :=
    le_trans (size_fst_le' z0.1.1) (le_trans (size_fst_le' z0.1) (size_fst_le' z0))
  have hys : Enc.size ys ≤ Enc.size z0 := le_trans (size_fst_le' z0.2) (size_snd_le' z0)
  have hxy : Enc.size ((xs, ys) : RawStr × RawStr) ≤ 4 * Enc.size z0 := by
    have := size_pair_le' ((xs, ys) : RawStr × RawStr); simp only at this; omega
  have h3 : lcBound (Enc.size ((xs, ys) : RawStr × RawStr)) ≤ lcBound (4 * Enc.size z0) :=
    mono_lcBound hxy
  have e : pcOut (lcSolveQ ansQ) z0 = ((pcStep (lcSolveQ ansQ))^[xs.length] z0).2.2 := rfl
  rw [e]
  have h2' : Enc.size z0.2.2 ≤ Enc.size z0 := h2
  refine le_trans h1 (max_le (by omega) ?_)
  exact le_trans h3 (Nat.le_add_left _ _)

/-- A list whose entries are bounded by `pw c d` of the size of the list. -/
theorem size_map_le_pw {α β : Type*} [Enc α] [Enc β] (f : α → β) (l : List α) {g : ℕ → ℕ}
    (hg : Monotone g) (hf : ∀ a ∈ l, Enc.size (f a) ≤ g (Enc.size a)) :
    Enc.size (l.map f) ≤ 1 + Enc.size l * (2 * g (Enc.size l) + 1) := by
  have h1 := size_list_le_of_entries (l.map f) (g (Enc.size l)) (by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hb
    exact le_trans (hf a ha) (hg (size_mem_le ha)))
  have h2 := length_le_size l
  rw [List.length_map] at h1
  have h3 : l.length * (2 * g (Enc.size l) + 1) ≤ Enc.size l * (2 * g (Enc.size l) + 1) :=
    Nat.mul_le_mul_right _ h2
  omega

set_option maxHeartbeats 4000000 in
/-- **Theorem 13.2.1 on the RAM, the two phases** (§13.2). One program transformer `F`: for
every program `Q` that answers the well-formed String Isomorphism instances, `F Q` runs, on
the prepared inputs `l₁` of the certificate runs and `l₂` of the comparison runs,
Procedure LocalCertificates on each entry of `l₁` and the comparison procedure on each entry
of `l₂`, within

  `10¹¹ · ∑_{W ∈ calls} τ(W) + (|l₁| + |l₂| + 2) · t! · poly(size of the input)`

steps, where `τ(W)` is the number of steps of `Q` on the call `W` and the calls are
`Algo.phaseCalls`. So the calls are paid at their own cost and every run costs
`t! · poly` besides; the number and size of the calls is
`Algo.theorem_13_2_1_phases_ram_spec`. The polynomial depends on the polynomial `S` that
bounds the size of the answers of `Q`, and on nothing else. -/
theorem theorem_13_2_1_phases_ram (S : ℕ → ℕ) (hS : PolyBound S) :
    ∃ (F : Program → Program) (c d : ℕ), ∀ Q : Program, Wf Q → Wf (F Q) ∧
      ∀ {n m : ℕ} {G : Subgroup (Perm (Fin n))} {ϕ : G →* Perm (Fin m)} {t : ℕ}
        (l1 : List RawLCLoop) (l2 : List RawPCLoop),
        (∀ p ∈ l1, CertRunInput ϕ t p) → (∀ z ∈ l2, CompareRunInput ϕ t z) →
        ∀ (ansQ : RawWinSI → RawCoset) (τ : RawWinSI → ℕ),
        (∀ W, WinWF n W → RunsOn 16 Q W (ansQ W) (τ W) ∧ Enc.size (ansQ W) ≤ S (Enc.size W) ∧
          decCoset n (ansQ W) = (decWinSI n W).answer) →
        RunsOn 16 (F Q) ((l1, l2) : List RawLCLoop × List RawPCLoop)
          ((l1.map (lcOut (lcSolveQ ansQ)), l2.map (pcOut (lcSolveQ ansQ)))
            : List RawLCOut × List RawCoset)
          (10 ^ 11 * ((phaseCalls ansQ l1 l2).map τ).sum
            + (l1.length + l2.length + 2) * Nat.factorial t
              * pw c d (Enc.size ((l1, l2) : List RawLCLoop × List RawPCLoop))) := by
  obtain ⟨F1, c1, d1, hF1⟩ := theorem_13_1_3_ram S hS
  obtain ⟨F2, c2, d2, hF2⟩ := proposition_13_1_11_ram S hS
  obtain ⟨Fm1, cm1, dm1, hFm1⟩ := MapFold.exists_mapProg (α := RawLCLoop) (β := RawLCOut)
  obtain ⟨Fm2, cm2, dm2, hFm2⟩ := MapFold.exists_mapProg (α := RawPCLoop) (β := RawCoset)
  obtain ⟨co1, do1, hso1⟩ := exists_size_lcOut_le
  obtain ⟨Pf, cf, df, hPf, -⟩ := polyFun_witness
    (polyFun_fst : PolyFun (fun z : List RawLCLoop × List RawPCLoop => z.1))
  obtain ⟨Ps, cs, ds, hPs, -⟩ := polyFun_witness
    (polyFun_snd : PolyFun (fun z : List RawLCLoop × List RawPCLoop => z.2))
  -- the overhead polynomial
  obtain ⟨O1, hO1⟩ : ∃ f : ℕ → ℕ, ∀ M, f M = 1 + M * (2 * pw co1 do1 M + 1) := ⟨_, fun _ => rfl⟩
  obtain ⟨O2, hO2⟩ : ∃ f : ℕ → ℕ, ∀ M, f M = 1 + M * (2 * (M + lcBound (4 * M)) + 1) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Gf, hGf⟩ : ∃ f : ℕ → ℕ, ∀ M, f M = 19 * M + 19 * O1 M + 19 * O2 M + 376
      + 10 * pw cf df M + 10 * pw cs ds M + 1000 * pw c1 d1 M + 10 * pw cm1 dm1 (M + O1 M)
      + 1000 * pw c2 d2 M + 10 * pw cm2 dm2 (M + O2 M) := ⟨_, fun _ => rfl⟩
  have hGp : PolyBound Gf := by
    have pO1 : PolyBound O1 := by
      rw [show O1 = _ from funext hO1]
      exact (polyBound_const 1).add (polyBound_id.mul
        (((polyBound_const 2).mul (polyBound_pw co1 do1)).add (polyBound_const 1)))
    have pO2 : PolyBound O2 := by
      rw [show O2 = _ from funext hO2]
      exact (polyBound_const 1).add (polyBound_id.mul (((polyBound_const 2).mul
        (polyBound_id.add (polyBound_lcBound.comp ((polyBound_const 4).mul polyBound_id)))).add
        (polyBound_const 1)))
    rw [show Gf = _ from funext hGf]
    exact (((((((((((polyBound_const 19).mul polyBound_id).add ((polyBound_const 19).mul pO1)).add
      ((polyBound_const 19).mul pO2)).add (polyBound_const 376)).add
      ((polyBound_const 10).mul (polyBound_pw cf df))).add
      ((polyBound_const 10).mul (polyBound_pw cs ds))).add
      ((polyBound_const 1000).mul (polyBound_pw c1 d1))).add
      ((polyBound_const 10).mul ((polyBound_pw cm1 dm1).comp (polyBound_id.add pO1)))).add
      ((polyBound_const 1000).mul (polyBound_pw c2 d2))).add
      ((polyBound_const 10).mul ((polyBound_pw cm2 dm2).comp (polyBound_id.add pO2))))
  obtain ⟨c, d, hcd⟩ := hGp
  refine ⟨fun Q => Pairing.pairProg 16 (RAM.seq Pf (Fm1 (F1 Q))) (RAM.seq Ps (Fm2 (F2 Q))),
    c, d, ?_⟩
  intro Q hQwf
  obtain ⟨hF1wf, hF1run⟩ := hF1 Q hQwf
  obtain ⟨hF2wf, hF2run⟩ := hF2 Q hQwf
  obtain ⟨hm1wf, hm1⟩ := hFm1 (F1 Q) hF1wf
  obtain ⟨hm2wf, hm2⟩ := hFm2 (F2 Q) hF2wf
  refine ⟨Pairing.wf_pairProg 16 (wf_seq (CleanComputeAt.wf' hPf) hm1wf)
    (wf_seq (CleanComputeAt.wf' hPs) hm2wf), ?_⟩
  intro n m G ϕ t l1 l2 hl1 hl2 ansQ τ hQ
  have hQc : ∀ W, WinWF n W → decCoset n (ansQ W) = (decWinSI n W).answer :=
    fun W hW => (hQ W hW).2.2
  -- notation
  set o1 := lcOut (lcSolveQ ansQ) with ho1
  set o2 := pcOut (lcSolveQ ansQ) with ho2
  set a : List RawLCLoop × List RawPCLoop := (l1, l2) with ha
  obtain ⟨M, hM⟩ : ∃ M, M = Enc.size a := ⟨_, rfl⟩
  set f := Nat.factorial t with hf
  have hf1 : 1 ≤ f := Nat.factorial_pos _
  have hl1M : Enc.size l1 ≤ M := hM ▸ size_fst_le' a
  have hl2M : Enc.size l2 ≤ M := hM ▸ size_snd_le' a
  -- the per-run costs
  let τ1 : RawLCLoop → ℕ := fun p => 10 ^ 7 * ((lcCallsQ ansQ p).map τ).sum
    + Nat.factorial p.1.2.length * pw c1 d1 (Enc.size p)
  let τ2 : RawPCLoop → ℕ := fun z => 10 ^ 8 * ((pcCallsQ ansQ z).map τ).sum
    + Nat.factorial z.1.1.2.length * pw c2 d2 (Enc.size z)
  have hrun1 : ∀ p ∈ l1, RunsOn 16 (F1 Q) p (o1 p) (τ1 p) := by
    intro p hp
    obtain ⟨hc, h0, -⟩ := hl1 p hp
    exact hF1run hc h0 ansQ τ hQ
  have hrun2 : ∀ z ∈ l2, RunsOn 16 (F2 Q) z (o2 z) (τ2 z) := by
    intro z hz
    obtain ⟨hc, hy, h0, ⟨T', hq0⟩, -⟩ := hl2 z hz
    exact hF2run hc hy h0 hq0 ansQ τ hQ
  have r1 := (hPf.runsOn a).seq (hm1 o1 τ1 l1 hrun1)
  have r2 := (hPs.runsOn a).seq (hm2 o2 τ2 l2 hrun2)
  have r := RunsOn.pair (K := 16) (by omega) r1 r2
  refine r.mono ?_
  -- the sizes of the outputs
  have hso1' : Enc.size (l1.map o1) ≤ O1 M := by
    have h := size_map_le_pw o1 l1 (pw_mono co1 do1) (fun p _ => hso1 _ p)
    have h' : 1 + Enc.size l1 * (2 * pw co1 do1 (Enc.size l1) + 1)
        ≤ 1 + M * (2 * pw co1 do1 M + 1) :=
      Nat.add_le_add_left (Nat.mul_le_mul hl1M (by have := pw_mono co1 do1 hl1M; omega)) _
    rw [hO1]; omega
  have hso2' : Enc.size (l2.map o2) ≤ O2 M := by
    have hmono : Monotone (fun x => x + lcBound (4 * x)) :=
      fun x y hxy => Nat.add_le_add hxy (mono_lcBound (by omega))
    have h := size_map_le_pw o2 l2 hmono (fun z hz => size_pcOut_le (hl2 z hz) hQc)
    have h' : 1 + Enc.size l2 * (2 * (Enc.size l2 + lcBound (4 * Enc.size l2)) + 1)
        ≤ 1 + M * (2 * (M + lcBound (4 * M)) + 1) :=
      Nat.add_le_add_left (Nat.mul_le_mul hl2M (by have := hmono hl2M; simp only at this; omega)) _
    rw [hO2]; omega
  -- the sums over the runs
  have hsum1 : (l1.map τ1).sum ≤ 10 ^ 7 * ((l1.flatMap (lcCallsQ ansQ)).map τ).sum
      + l1.length * (f * pw c1 d1 M) := by
    have h := MapFold.sum_map_le_add_mul l1 τ1
      (fun p => 10 ^ 7 * ((lcCallsQ ansQ p).map τ).sum) (f * pw c1 d1 M) (by
        intro p hp
        obtain ⟨-, -, ht⟩ := hl1 p hp
        have e1 : Nat.factorial p.1.2.length = f := by rw [ht]
        have e2 : pw c1 d1 (Enc.size p) ≤ pw c1 d1 M :=
          pw_mono c1 d1 (le_trans (size_mem_le hp) hl1M)
        show 10 ^ 7 * _ + Nat.factorial p.1.2.length * pw c1 d1 (Enc.size p) ≤ _
        rw [e1]
        exact Nat.add_le_add_left (Nat.mul_le_mul_left _ e2) _)
    rw [sum_map_flatMap, ← List.sum_map_mul_left]
    exact h
  have hsum2 : (l2.map τ2).sum ≤ 10 ^ 8 * ((l2.flatMap (pcCallsQ ansQ)).map τ).sum
      + l2.length * (f * pw c2 d2 M) := by
    have h := MapFold.sum_map_le_add_mul l2 τ2
      (fun z => 10 ^ 8 * ((pcCallsQ ansQ z).map τ).sum) (f * pw c2 d2 M) (by
        intro z hz
        obtain ⟨-, -, -, -, ht⟩ := hl2 z hz
        have e1 : Nat.factorial z.1.1.2.length = f := by rw [ht]
        have e2 : pw c2 d2 (Enc.size z) ≤ pw c2 d2 M :=
          pw_mono c2 d2 (le_trans (size_mem_le hz) hl2M)
        show 10 ^ 8 * _ + Nat.factorial z.1.1.2.length * pw c2 d2 (Enc.size z) ≤ _
        rw [e1]
        exact Nat.add_le_add_left (Nat.mul_le_mul_left _ e2) _)
    rw [sum_map_flatMap, ← List.sum_map_mul_left]
    exact h
  have hcalls : ((phaseCalls ansQ l1 l2).map τ).sum
      = ((l1.flatMap (lcCallsQ ansQ)).map τ).sum + ((l2.flatMap (pcCallsQ ansQ)).map τ).sum := by
    rw [phaseCalls, List.map_append, List.sum_append]
  rw [hcalls, ← hM]
  -- the pieces of the overhead
  have p1 : cf * (Enc.size a + 1) ^ df ≤ pw cf df M := by rw [hM]; rfl
  have p2 : cs * (Enc.size a + 1) ^ ds ≤ pw cs ds M := by rw [hM]; rfl
  have p3 : pw cm1 dm1 (Enc.size l1 + Enc.size (l1.map o1)) ≤ pw cm1 dm1 (M + O1 M) :=
    pw_mono cm1 dm1 (by omega)
  have p4 : pw cm2 dm2 (Enc.size l2 + Enc.size (l2.map o2)) ≤ pw cm2 dm2 (M + O2 M) :=
    pw_mono cm2 dm2 (by omega)
  have hGM := hcd M
  rw [hGf] at hGM
  set L := l1.length + l2.length + 2 with hL
  have hLf : 1 ≤ L * f := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have q1 : (l1.length + 2) * pw cm1 dm1 (M + O1 M) ≤ L * f * pw cm1 dm1 (M + O1 M) :=
    Nat.mul_le_mul_right _ (le_trans (by omega : l1.length + 2 ≤ L) (Nat.le_mul_of_pos_right _ hf1))
  have q2 : (l2.length + 2) * pw cm2 dm2 (M + O2 M) ≤ L * f * pw cm2 dm2 (M + O2 M) :=
    Nat.mul_le_mul_right _ (le_trans (by omega : l2.length + 2 ≤ L) (Nat.le_mul_of_pos_right _ hf1))
  have q3 : l1.length * (f * pw c1 d1 M) ≤ L * f * pw c1 d1 M := by
    rw [← Nat.mul_assoc]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
  have q4 : l2.length * (f * pw c2 d2 M) ≤ L * f * pw c2 d2 M := by
    rw [← Nat.mul_assoc]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
  have q5 : ∀ x, x ≤ L * f * x := fun x => Nat.le_mul_of_pos_left x hLf
  have q6 := q5 (19 * M + 19 * O1 M + 19 * O2 M + 376 + 10 * pw cf df M + 10 * pw cs ds M)
  have hdist : L * f * (19 * M + 19 * O1 M + 19 * O2 M + 376 + 10 * pw cf df M
      + 10 * pw cs ds M + 1000 * pw c1 d1 M + 10 * pw cm1 dm1 (M + O1 M)
      + 1000 * pw c2 d2 M + 10 * pw cm2 dm2 (M + O2 M))
      = L * f * (19 * M + 19 * O1 M + 19 * O2 M + 376 + 10 * pw cf df M + 10 * pw cs ds M)
        + 1000 * (L * f * pw c1 d1 M) + 10 * (L * f * pw cm1 dm1 (M + O1 M))
        + 1000 * (L * f * pw c2 d2 M) + 10 * (L * f * pw cm2 dm2 (M + O2 M)) := by ring
  have hfin : L * f * (19 * M + 19 * O1 M + 19 * O2 M + 376 + 10 * pw cf df M
      + 10 * pw cs ds M + 1000 * pw c1 d1 M + 10 * pw cm1 dm1 (M + O1 M)
      + 1000 * pw c2 d2 M + 10 * pw cm2 dm2 (M + O2 M)) ≤ L * f * pw c d M :=
    Nat.mul_le_mul_left _ hGM
  have hsa : Enc.size a = M := hM.symm
  have hsz1 : Enc.size (l1.map o1) ≤ O1 M := hso1'
  have hsz2 : Enc.size (l2.map o2) ≤ O2 M := hso2'
  simp only [hsa] at *
  have q1' := Nat.mul_le_mul_left (l1.length + 2) p3
  have q2' := Nat.mul_le_mul_left (l2.length + 2) p4
  omega

/-- **Theorem 13.2.1 on the RAM, the two phases** (§13.2): what the routine of
`Algo.theorem_13_2_1_phases_ram` computes and which calls it makes. Each answer of the first
phase is the paper's `(W(T), K(T), M(T))` for its run (`Algo.theorem_13_1_3_ram_spec`), each
answer of the second is `Iso_G(x_T^{W(T)}, (x')_{T'}^{W(T')})` for its run
(`Algo.proposition_13_1_11_ram_spec`). The calls number at most `(|l₁| + |l₂|)·t!·n²`, each
on a window of at most `n/t` points; with at most `2·C(m,t)` certificate runs and at most
`2·C(m,t)²` comparison runs this is at most `Babai.aggregateRoundCost m t n`, the count of
§13.2. -/
theorem theorem_13_2_1_phases_ram_spec {ϕ : G →* Perm (Fin m)} {t : ℕ} (h5 : 5 ≤ t)
    {l1 : List RawLCLoop} {l2 : List RawPCLoop}
    (hl1 : ∀ p ∈ l1, CertRunInput ϕ t p) (hl2 : ∀ z ∈ l2, CompareRunInput ϕ t z)
    (ansQ : RawWinSI → RawCoset)
    (hQ : ∀ W, WinWF n W → decCoset n (ansQ W) = (decWinSI n W).answer) :
    (phaseCalls ansQ l1 l2).length ≤ (l1.length + l2.length) * (Nat.factorial t * n ^ 2) ∧
      (∀ W ∈ phaseCalls ansQ l1 l2, WinWF n W ∧ t * W.1.length ≤ n) ∧
      (l1.length ≤ 2 * m.choose t → l2.length ≤ 2 * (m.choose t) ^ 2 →
        (phaseCalls ansQ l1 l2).length ≤ aggregateRoundCost m t n) := by
  have hlen1 : (l1.flatMap (lcCallsQ ansQ)).length ≤ l1.length * (Nat.factorial t * n ^ 2) := by
    refine length_flatMap_le l1 _ _ (fun p hp => ?_)
    obtain ⟨hc, h0, ht⟩ := hl1 p hp
    have := (theorem_13_1_3_ram_spec hc h0 ansQ hQ).2.2.2.2.1
    rw [ht] at this
    exact this
  have hlen2 : (l2.flatMap (pcCallsQ ansQ)).length ≤ l2.length * (Nat.factorial t * n ^ 2) := by
    refine length_flatMap_le l2 _ _ (fun z hz => ?_)
    obtain ⟨hc, hy, h0, ⟨T', hq0⟩, ht⟩ := hl2 z hz
    have := length_pcCallsQ_le hQ hy (by rw [ht]; exact h5) h0 hq0
    rw [ht] at this
    exact this
  have hlen : (phaseCalls ansQ l1 l2).length
      ≤ (l1.length + l2.length) * (Nat.factorial t * n ^ 2) := by
    rw [phaseCalls, List.length_append, Nat.add_mul]
    omega
  refine ⟨hlen, ?_, ?_⟩
  · intro W hW
    rw [phaseCalls, List.mem_append, List.mem_flatMap, List.mem_flatMap] at hW
    rcases hW with ⟨p, hp, hW⟩ | ⟨z, hz, hW⟩
    · obtain ⟨hc, h0, ht⟩ := hl1 p hp
      have := (theorem_13_1_3_ram_spec hc h0 ansQ hQ).2.2.2.2.2 (by rw [ht]; exact h5) W hW
      rw [ht] at this
      exact this
    · obtain ⟨hc, hy, h0, ⟨T', hq0⟩, ht⟩ := hl2 z hz
      have := window_pcCallsQ_le hQ hy (by rw [ht]; exact h5) h0 hq0 W hW
      rw [ht] at this
      exact this
  · intro h1 h2
    refine le_trans hlen ?_
    rw [aggregateRoundCost]
    have e1 : l1.length * (Nat.factorial t * n ^ 2)
        ≤ 2 * m.choose t * (Nat.factorial t * n ^ 2) := Nat.mul_le_mul_right _ h1
    have e2 : l2.length * (Nat.factorial t * n ^ 2)
        ≤ 2 * (m.choose t) ^ 2 * (2 * Nat.factorial t * n ^ 2) := by
      calc l2.length * (Nat.factorial t * n ^ 2)
          ≤ 2 * (m.choose t) ^ 2 * (Nat.factorial t * n ^ 2) := Nat.mul_le_mul_right _ h2
        _ ≤ 2 * (m.choose t) ^ 2 * (2 * Nat.factorial t * n ^ 2) :=
          Nat.mul_le_mul_left _ (by nlinarith)
    rw [Nat.add_mul]
    omega

end Algo
