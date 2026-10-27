/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

§1.1, Corollary 1.1.3: the running time of the reduction to the orbits.
-/
import Workspace.Algo.OrbitLoop
import Workspace.Algo.PolyWitness
import Workspace.Machine.RunsOn
import Workspace.Machine.TargetsCor113

/-!
# Corollary 1.1.3: the running time

The loop of `Workspace/Algo/OrbitLoop.lean` runs on the RAM as

`seq P₁ (seq (whileNz 18 Q) P₃)`,

with `P₁` the set-up, `P₃` the read-off, and `Q` one step: the counter is decreased, and the
state goes through the preparation of the restricted instance, the routine `P` of Theorem 1.1.1,
and the lift. Everything except the call of `P` is a `RAM.PolyFun`, so costs a polynomial in the
size of the state; the call costs `T` of the size of the normalized restricted instance, which
is at most `normSIBound |Δ| ≤ normSIBound n₀(G)`. The loop runs once per orbit, and the states
it passes through are polynomially bounded in the input size (the coset is kept short by
`Algo.tidyGens`). The cost is therefore a polynomial in the input size times a quasipolynomial in
`n₀(G)` (`Algo.orbit_workspace`), and the bridge to the top-level convention gives
`RAM.Targets.Corollary_1_1_3_statement` (`Algo.corollary_1_1_3`).
-/

namespace Algo
open RAM RAM.Targets Babai Equiv

/-! ## The routines of the loop are polynomial -/

theorem polyFun_orbWin : PolyFun orbWin := by
  have hO : PolyFun (fun st : OrbState => st.1) := polyFun_fst
  have hx : PolyFun (fun st : OrbState => st.2.1) := polyFun_snd.comp polyFun_fst
  have hy : PolyFun (fun st : OrbState => st.2.2.1) :=
    (polyFun_snd.comp polyFun_snd).comp polyFun_fst
  have hc : PolyFun (fun st : OrbState => st.2.2.2) :=
    (polyFun_snd.comp polyFun_snd).comp polyFun_snd
  have hh : PolyFun (fun st : OrbState => st.1.headD []) :=
    (((hO.pair (polyFun_const 0)).pair (polyFun_const [])).comp polyFun_getD).of_eq
      (fun st => by cases st.1 <;> rfl)
  have hg : PolyFun (fun st : OrbState => st.2.2.2.getD ([], [])) :=
    (hc.pair (polyFun_const (([], []) : RawGens × RawPerm))).comp polyFun_optionGetD
  exact (hh.pair ((hg.comp polyFun_fst).pair ((hg.comp polyFun_snd).pair (hx.pair hy)))).of_eq
    (fun _ => rfl)

theorem polyFun_orbPre : PolyFun orbPre :=
  (polyFun_orbWin.comp polyFun_primitiveWindowInput).comp polyFun_rawNormSI

theorem polyFun_orbPost : PolyFun orbPost := by
  have hO : PolyFun (fun q : OrbState × RawCoset => q.1.1) := polyFun_fst.comp polyFun_fst
  have hx : PolyFun (fun q : OrbState × RawCoset => q.1.2.1) :=
    polyFun_fst.comp (polyFun_snd.comp polyFun_fst)
  have hy : PolyFun (fun q : OrbState × RawCoset => q.1.2.2.1) :=
    polyFun_fst.comp ((polyFun_snd.comp polyFun_snd).comp polyFun_fst)
  have hc : PolyFun (fun q : OrbState × RawCoset => q.1.2.2.2) :=
    polyFun_fst.comp ((polyFun_snd.comp polyFun_snd).comp polyFun_snd)
  have hh : PolyFun (fun q : OrbState × RawCoset => q.1.1.headD []) :=
    (((hO.pair (polyFun_const 0)).pair (polyFun_const [])).comp polyFun_getD).of_eq
      (fun q => by cases q.1.1 <;> rfl)
  have hbody : PolyFun (fun z : (RawGens × RawPerm) × (OrbState × RawCoset) =>
      top3Shift (z.2.1.2.1, z.1.2,
        topwCosetPreimage ((z.2.1.2.1, z.1.1), z.2.1.1.headD [], z.2.2))) := by
    have zx : PolyFun (fun z : (RawGens × RawPerm) × (OrbState × RawCoset) => z.2.1.2.1) :=
      polyFun_snd.comp hx
    have zg : PolyFun (fun z : (RawGens × RawPerm) × (OrbState × RawCoset) => z.1.1) :=
      polyFun_fst.comp polyFun_fst
    have zr : PolyFun (fun z : (RawGens × RawPerm) × (OrbState × RawCoset) => z.1.2) :=
      polyFun_fst.comp polyFun_snd
    have zh : PolyFun (fun z : (RawGens × RawPerm) × (OrbState × RawCoset) =>
        z.2.1.1.headD []) := polyFun_snd.comp hh
    have za : PolyFun (fun z : (RawGens × RawPerm) × (OrbState × RawCoset) => z.2.2) :=
      polyFun_snd.comp polyFun_snd
    exact (zx.pair (zr.pair (((zx.pair zg).pair (zh.pair za)).comp
      polyFun_topwCosetPreimage))).comp polyFun_top3Shift
  have hbind : PolyFun (fun q : OrbState × RawCoset => q.1.2.2.2.bind fun c =>
      top3Shift (q.1.2.1, c.2, topwCosetPreimage ((q.1.2.1, c.1), q.1.1.headD [], q.2))) :=
    ((hc.pair polyFun_id).comp (PolyFun.optionElim (polyFun_none) hbody)).of_eq
      (fun q => by cases q.1.2.2.2 <;> rfl)
  exact ((hO.comp polyFun_tail).pair (hx.pair (hy.pair hbind))).of_eq (fun _ => rfl)

theorem polyFun_orbSetUp : PolyFun orbSetUp := by
  have hx : PolyFun (fun r : RawSI => r.2.1) := polyFun_snd.comp polyFun_fst
  have hy : PolyFun (fun r : RawSI => r.2.2) := polyFun_snd.comp polyFun_snd
  have hg : PolyFun (fun r : RawSI => tidyGens (r.2.1, r.1)) :=
    (hx.pair polyFun_fst).comp polyFun_tidyGens
  have hO : PolyFun (fun r : RawSI => rawOrbits (tidyGens (r.2.1, r.1), r.2.1)) :=
    (hg.pair hx).comp polyFun_rawOrbits
  exact ((hO.comp polyFun_length).pair (hO.pair (hx.pair (hy.pair
    ((hg.pair (hx.comp polyFun_rawOne)).comp polyFun_some))))).of_eq (fun _ => rfl)

theorem polyFun_orbReadOff : PolyFun (fun p : ℕ × OrbState => p.2.2.2.2) :=
  polyFun_snd.comp ((polyFun_snd.comp polyFun_snd).comp polyFun_snd)

theorem polyFun_orbPred : PolyFun (fun p : ℕ × OrbState => p.1 - 1) :=
  polyFun_fst.sub (polyFun_const 1)

/-- The length of an orbit of the group is at most `n₀(G)`. -/
theorem length_orbit_le_maxOrbitLength {n : ℕ} {gs : RawGens} (hgs : RawGens.WF n gs)
    {gens : List (Perm (Fin n))} (hG : decGroup n gs = genGroup gens) {w : List ℕ}
    (hw : w.length = n) {u : List ℕ} (hu : u ∈ rawOrbits (gs, w)) :
    u.length ≤ maxOrbitLength gens := by
  obtain ⟨j, hj, rfl⟩ := rawOrbits_mem hgs hw hu
  rw [length_rawOrbit_eq_ncard hgs hj, hG]
  exact Finset.le_sup (f := fun u : Fin n => (MulAction.orbit (genGroup gens) u).ncard)
    (Finset.mem_univ (⟨j, hj⟩ : Fin n))

theorem normSIBound_mono : Monotone normSIBound := by
  intro a b h
  unfold normSIBound
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

/-! ## The run -/

section Run

variable {P : Program} {T S : ℕ → ℕ}

theorem solverSpec_normSolve (hP : IsSIRoutine P T S) : SolverSpec (normSolve hP) :=
  fun _ _ h => (normSolve_spec hP h).2.2.1

/-- The final arithmetic: a polynomial plus the product of a polynomial and a quantity `Q ≥ 1`
is at most a (bigger) polynomial times `Q`. -/
theorem add_mul_le_mul {A B Q : ℕ} (hQ : 1 ≤ Q) : A + B * Q ≤ (A + B) * Q := by
  rw [Nat.add_mul]
  exact Nat.add_le_add_right (Nat.le_mul_of_pos_right A hQ) _

/-- The arithmetic of the final bound. -/
theorem orbit_arith {N X Y R R' Z Q : ℕ} (hQ1 : 1 ≤ Q) (hNle : N ≤ Y) (hro : R' ≤ R)
    (hAm : (Y + 1) * (X + 103) + R ≤ Z) : Y + (N * (X + 100 * Q + 2) + 1 + R') ≤ Z * Q := by
  have h1 : N * (X + 100 * Q + 2) ≤ Y * (X + 100 * Q + 2) := Nat.mul_le_mul_right _ hNle
  have h2 : Y * (X + 100 * Q + 2) = Y * X + 2 * Y + 100 * (Y * Q) := by ring
  have h6 : Y * X ≤ Y * X * Q := Nat.le_mul_of_pos_right _ hQ1
  have h7 : R ≤ R * Q := Nat.le_mul_of_pos_right _ hQ1
  have h8 : ((Y + 1) * (X + 103) + R) * Q ≤ Z * Q := Nat.mul_le_mul_right _ hAm
  have h9 : ((Y + 1) * (X + 103) + R) * Q = Y * X * Q + 103 * (Y * Q) + X * Q +
      103 * Q + R * Q := by ring
  have h10 : Y ≤ Y * Q := Nat.le_mul_of_pos_right _ hQ1
  have h11 : 1 ≤ 103 * Q := by omega
  omega

/-- **Corollary 1.1.3 in the workspace convention.**  One program which, on every input of
String Isomorphism, halts with an admissible answer (Def. 11.1.2) of size at most
`chainBound` of the input size, within `c (N + 1)^d · U(normSIBound n₀(G))` steps, for the input
size `N` and the quasipolynomial `U` that bounds the routine of Theorem 1.1.1. -/
theorem orbit_workspace_of (hP : IsSIRoutine P T S) {cT : ℕ}
    (hT : ∀ m, T m ≤ 2 ^ ((Nat.log 2 m + 2) ^ cT)) (hSb : PolyBound S)
    (hSmono : ∀ m m', m ≤ m' → S m ≤ S m') :
    ∃ (Prog : Program) (c d : ℕ), ∀ (n s : ℕ) (a : SIInput n s),
      ∃ b, SIRel n s a b ∧ Enc.size b ≤ chainBound (Enc.size a) ∧
        RunsOn 16 Prog a b (pw c d (Enc.size a) *
          2 ^ ((Nat.log 2 (normSIBound (maxOrbitLength a.1)) + 2) ^ cT)) := by
  classical
  set sol := normSolve hP with hsoldef
  have hsol : SolverSpec sol := solverSpec_normSolve hP
  -- the routines
  obtain ⟨Ppre, cpre, dpre, hPpre, hSpre⟩ := polyFun_witness polyFun_orbPre
  obtain ⟨Ppost, cpost, dpost, hPpost, hSpost⟩ := polyFun_witness polyFun_orbPost
  obtain ⟨Pid, cid, did, hPid, -⟩ := polyFun_witness (polyFun_id (α := OrbState))
  obtain ⟨Psnd, csnd, dsnd, hPsnd, -⟩ := polyFun_witness (polyFun_snd (α := ℕ) (β := OrbState))
  obtain ⟨Ppred, cpred, dpred, hPpred, hSpred⟩ := polyFun_witness polyFun_orbPred
  obtain ⟨Pset, cset, dset, hPset, hSset⟩ := polyFun_witness polyFun_orbSetUp
  obtain ⟨Pro, cro, dro, hPro, -⟩ := polyFun_witness polyFun_orbReadOff
  -- the step
  let Pstep : Program := RAM.seq (Pairing.pairProg 16 Pid (RAM.seq Ppre P)) Ppost
  let Q : Program := Pairing.pairProg 16 Ppred (RAM.seq Psnd Pstep)
  -- the polynomial part of the cost of one step, in the size of the loop state
  let Z : ℕ → ℕ := fun m => 2 * m + 2 * S (pw cpre dpre m)
  let F : ℕ → ℕ := fun m =>
    19 * m + 19 * pw cpred dpred m + 19 * pw cpost dpost (Z m) + 10 * pw cpred dpred m +
      10 * (pw csnd dsnd m + (38 * m + 19 * S (pw cpre dpre m) + 10 * pw cid did m +
        10 * pw cpre dpre m + 176 + 200 + pw cpost dpost (Z m))) + 176 + 200
  have hZmono : Monotone Z := fun a b h => by
    have := hSmono _ _ (pw_mono cpre dpre h); simp only [Z]; omega
  have hFmono : Monotone F := fun a b h => by
    have h1 := pw_mono cpred dpred h
    have h2 := pw_mono cpost dpost (hZmono h)
    have h3 := pw_mono csnd dsnd h
    have h4 := hSmono _ _ (pw_mono cpre dpre h)
    have h5 := pw_mono cid did h
    have h6 := pw_mono cpre dpre h
    simp only [F]; omega
  have hFpoly : PolyBound F := by
    have hZ : PolyBound Z := ((polyBound_const 2).mul polyBound_id).add
      ((polyBound_const 2).mul (hSb.comp (polyBound_pw cpre dpre)))
    have hpost := (polyBound_pw cpost dpost).comp hZ
    have hpred := polyBound_pw cpred dpred
    have hin : PolyBound (fun m => 38 * m + 19 * S (pw cpre dpre m) + 10 * pw cid did m +
        10 * pw cpre dpre m + 176 + 200 + pw cpost dpost (Z m)) :=
      (((((((polyBound_const 38).mul polyBound_id).add
          ((polyBound_const 19).mul (hSb.comp (polyBound_pw cpre dpre)))).add
          ((polyBound_const 10).mul (polyBound_pw cid did))).add
          ((polyBound_const 10).mul (polyBound_pw cpre dpre))).add (polyBound_const 176)).add
          (polyBound_const 200)).add hpost
    have hmid := (polyBound_const 10).mul ((polyBound_pw csnd dsnd).add hin)
    exact ((((((((polyBound_const 19).mul polyBound_id).add ((polyBound_const 19).mul hpred)).add
      ((polyBound_const 19).mul hpost)).add ((polyBound_const 10).mul hpred)).add hmid).add
      (polyBound_const 176)).add (polyBound_const 200))
  -- one run of the step, for every state
  have hQ : ∀ p : ℕ × OrbState, RunsOn 16 Q p ((p.1 - 1, orbStep sol p.2) : ℕ × OrbState)
      (F (Enc.size p) + 100 * T (Enc.size (orbPre p.2))) := by
    intro p
    set st := p.2
    have hwf : NormSIWF (orbWin st).1.length (orbPre st) := normSIWF_window (orbWin st)
    obtain ⟨hrun, -, -, hsz⟩ := normSolve_spec hP hwf
    rw [← hsoldef] at hrun hsz
    have h1 : RunsOn 16 (RAM.seq Ppre P) st (sol (orbPre st))
        (pw cpre dpre (Enc.size st) + T (Enc.size (orbPre st))) :=
      (hPpre.runsOn st).seq hrun
    have h2 := RunsOn.pair (le_refl 16) (hPid.runsOn st) h1
    have h3 := h2.seq (hPpost.runsOn (id st, sol (orbPre st)))
    have h4 := (hPsnd.runsOn p).seq h3
    have h5 := RunsOn.pair (le_refl 16) (hPpred.runsOn p) h4
    refine h5.mono ?_
    -- the sizes
    have hst : Enc.size st ≤ Enc.size p := size_snd_le' p
    have hpre : Enc.size (orbPre st) ≤ pw cpre dpre (Enc.size p) :=
      le_trans (hSpre st) (pw_mono cpre dpre hst)
    have hsol' : Enc.size (sol (orbPre st)) ≤ S (pw cpre dpre (Enc.size p)) :=
      le_trans hsz (hSmono _ _ hpre)
    have hpair : Enc.size ((id st, sol (orbPre st)) : OrbState × RawCoset)
        ≤ Z (Enc.size p) := by
      have := Combine.size_pair_le st (sol (orbPre st))
      simp only [Z]
      change Enc.size ((st, sol (orbPre st)) : OrbState × RawCoset) ≤ _
      omega
    have hstep : Enc.size (orbPost (id st, sol (orbPre st))) ≤ pw cpost dpost (Z (Enc.size p)) :=
      le_trans (hSpost _) (pw_mono cpost dpost hpair)
    have hpost : pw cpost dpost (Enc.size ((id st, sol (orbPre st)) : OrbState × RawCoset))
        ≤ pw cpost dpost (Z (Enc.size p)) := pw_mono cpost dpost hpair
    have hpred' : Enc.size (p.1 - 1) ≤ pw cpred dpred (Enc.size p) := hSpred p
    have hid : pw cid did (Enc.size st) ≤ pw cid did (Enc.size p) := pw_mono cid did hst
    have hpre' : pw cpre dpre (Enc.size st) ≤ pw cpre dpre (Enc.size p) := pw_mono cpre dpre hst
    have hsol'' : S (pw cpre dpre (Enc.size st)) ≤ S (pw cpre dpre (Enc.size p)) :=
      hSmono _ _ hpre'
    have hsz2 : Enc.size (sol (orbPre st)) ≤ S (pw cpre dpre (Enc.size p)) := hsol'
    change 19 * Enc.size p + 19 * Enc.size (p.1 - 1) + 19 * Enc.size (orbPost (id st, sol (orbPre st)))
      + 10 * pw cpred dpred (Enc.size p) + 10 * (pw csnd dsnd (Enc.size p) +
        ((19 * Enc.size st + 19 * Enc.size (id st) + 19 * Enc.size (sol (orbPre st)) +
          10 * pw cid did (Enc.size st) + 10 * (pw cpre dpre (Enc.size st) +
            T (Enc.size (orbPre st))) + 11 * 16 + 200) +
          pw cpost dpost (Enc.size ((id st, sol (orbPre st)) : OrbState × RawCoset)))) +
      11 * 16 + 200 ≤ F (Enc.size p) + 100 * T (Enc.size (orbPre st))
    simp only [F, id]
    simp only [id] at hstep hpost
    omega
  -- the whole program
  refine ⟨RAM.seq Pset (RAM.seq (whileNz (16 + 2) Q) Pro), ?_⟩
  -- the polynomial part, in the input size
  let Sst : ℕ → ℕ := fun m =>
    2 * pw cset dset m + 2 * (2 * pw cset dset m + 2 * (2 * m + 2 * (2 * m + 2 * chainBound m)))
  let A : ℕ → ℕ := fun m =>
    (pw cset dset m + 1) * (F (Sst m) + 103) + pw cro dro (Sst m)
  have hSstpoly : PolyBound Sst := by
    have hs := polyBound_pw cset dset
    exact ((polyBound_const 2).mul hs).add ((polyBound_const 2).mul
      (((polyBound_const 2).mul hs).add ((polyBound_const 2).mul
        (((polyBound_const 2).mul polyBound_id).add ((polyBound_const 2).mul
          (((polyBound_const 2).mul polyBound_id).add
            ((polyBound_const 2).mul polyBound_chainBound)))))))
  have hApoly : PolyBound A :=
    (((polyBound_pw cset dset).add (polyBound_const 1)).mul
      ((hFpoly.comp hSstpoly).add (polyBound_const 103))).add
      ((polyBound_pw cro dro).comp hSstpoly)
  obtain ⟨cA, dA, hA⟩ := hApoly
  refine ⟨cA, dA, fun n s a => ?_⟩
  -- the raw input and the loop
  set r := rawOfSI a with hr
  have hx : r.2.1.length = n := length_encStr _
  set g₀ := tidyGens (r.2.1, r.1) with hg₀
  have hg₀wf : RawGens.WF n g₀ := wf_tidyGens hx _
  have hg₀l : g₀.length ≤ n * n := length_tidyGens hx _
  have hG : decGroup n g₀ = genGroup a.1 := by
    rw [hg₀, decGroup_tidyGens hx]
    exact decGroup_map_encPerm n a.1
  set Os := rawOrbits (g₀, r.2.1) with hOsdef
  have hOs : OrbitsOK n (decGroup n g₀) Os := orbitsOK_rawOrbits hg₀wf hx
  have hiter := orbStep_iterate_spec hsol hx hOs (orbInv_zero (y := r.2.2) hg₀wf hg₀l hx Os)
  set N := Os.length with hN
  set st₀ : OrbState := (Os, r.2.1, r.2.2, some (g₀, rawOne r.2.1)) with hst₀
  have hsetup : orbSetUp r = (N, st₀) := rfl
  set m := Enc.size r with hm
  have hma : Enc.size a = m := size_eq_of_encode_eq (encode_si_eq a)
  -- sizes along the loop
  have hn_le : n ≤ m := by
    have h1 := length_le_size r.2.1
    have h2 := size_fst_le' r.2
    have h3 := size_snd_le' r
    omega
  have hsetsz : Enc.size (orbSetUp r) ≤ pw cset dset m := hSset r
  have hNsz : Enc.size N ≤ pw cset dset m := by
    have := size_fst_le' (orbSetUp r); rw [hsetup] at this; exact le_trans this (hsetsz)
  have hOssz : Enc.size Os ≤ pw cset dset m := by
    have h1 := size_snd_le' (orbSetUp r)
    have h2 := size_fst_le' (orbSetUp r).2
    rw [hsetup] at h1 h2
    exact le_trans h2 (le_trans h1 hsetsz)
  have hxsz : Enc.size r.2.1 ≤ m := le_trans (size_fst_le' r.2) (size_snd_le' r)
  have hysz : Enc.size r.2.2 ≤ m := le_trans (size_snd_le' r.2) (size_snd_le' r)
  have hstate : ∀ j ≤ N, Enc.size ((N - j, (orbStep sol)^[j] st₀) : ℕ × OrbState) ≤ Sst m := by
    intro j hj
    obtain ⟨c, hc, hinv⟩ := hiter j hj
    rw [hc]
    have hcsz : Enc.size c ≤ chainBound m := by
      cases c with
      | none =>
        have := chainBound_ge m
        rw [size_none]; omega
      | some q =>
        obtain ⟨g, ρ⟩ := q
        obtain ⟨h1, h2, h3, -⟩ := hinv.2 g ρ rfl
        exact size_coset_le' hn_le h1 h2 h3
    have e1 := size_pair_le' ((N - j, (Os.drop j, r.2.1, r.2.2, c)) : ℕ × OrbState)
    have e2 := size_pair_le' ((Os.drop j, r.2.1, r.2.2, c) : OrbState)
    have e3 := size_pair_le' ((r.2.1, r.2.2, c) : RawStr × RawStr × RawCoset)
    have e4 := size_pair_le' ((r.2.2, c) : RawStr × RawCoset)
    have e5 : Enc.size (N - j) ≤ Enc.size N := size_nat_le_of_le (Nat.sub_le _ _)
    have e6 : Enc.size (Os.drop j) ≤ Enc.size Os := size_drop_le j Os
    simp only at e1 e2 e3 e4
    simp only [Sst]
    omega
  -- the cost of the calls
  set n₀ := maxOrbitLength a.1 with hn₀
  set Qn := 2 ^ ((Nat.log 2 (normSIBound n₀) + 2) ^ cT) with hQn
  have hQ1 : 1 ≤ Qn := Nat.one_le_two_pow
  have hcall : ∀ j < N, T (Enc.size (orbPre ((orbStep sol)^[j] st₀))) ≤ Qn := by
    intro j hj
    obtain ⟨c, hc, -⟩ := hiter j hj.le
    rw [hc]
    have hwf := normSIWF_window (orbWin (Os.drop j, r.2.1, r.2.2, c))
    have hsz := hwf.size_le
    have hwin : (orbWin (Os.drop j, r.2.1, r.2.2, c)).1 = Os[j] := by
      simp only [orbWin]
      rw [List.drop_eq_getElem_cons hj]; rfl
    have hmemj : Os[j]'hj ∈ rawOrbits (g₀, r.2.1) := List.getElem_mem hj
    have hlen : (Os[j]'hj).length ≤ n₀ :=
      length_orbit_le_maxOrbitLength (gs := g₀) (gens := a.1) (w := r.2.1) hg₀wf hG hx hmemj
    have hlen' : (orbWin (Os.drop j, r.2.1, r.2.2, c)).1.length ≤ n₀ := by
      rw [hwin]; exact hlen
    exact le_trans (hT _) (quasiPolyBound_witness_mono cT
      (le_trans hsz (normSIBound_mono hlen')))
  have hB : ∀ j < N, F (Enc.size ((N - j, (orbStep sol)^[j] st₀) : ℕ × OrbState)) +
      100 * T (Enc.size (orbPre ((N - j, (orbStep sol)^[j] st₀) : ℕ × OrbState).2)) ≤
      F (Sst m) + 100 * Qn := by
    intro j hj
    have h1 := hFmono (hstate j hj.le)
    have h2 := hcall j hj
    simp only at h2 ⊢
    omega
  have hloop := runsOn_iterate (K := 16) (W := fun p : ℕ × OrbState =>
      F (Enc.size p) + 100 * T (Enc.size (orbPre p.2))) hQ N st₀ _ hB
  have hlast := hPro.runsOn ((0, (orbStep sol)^[N] st₀) : ℕ × OrbState)
  have hrun := (hPset.runsOn r).seq (hloop.seq hlast)
  -- the answer
  obtain ⟨hwfc, hdec⟩ := orbFinal_spec hsol a
  rw [← hr, hsetup] at hwfc hdec
  obtain ⟨b, hbenc, hbrel⟩ := exists_SIRel_of_decCoset a _ hwfc hdec
  refine ⟨b, hbrel, ?_, ?_⟩
  · rw [size_eq_of_encode_eq hbenc, hma]
    obtain ⟨c, hc, hinv⟩ := hiter N le_rfl
    simp only [hc]
    cases c with
    | none => have := chainBound_ge m; rw [size_none]; omega
    | some q =>
      obtain ⟨g, ρ⟩ := q
      obtain ⟨h1, h2, h3, -⟩ := hinv.2 g ρ rfl
      exact size_coset_le' hn_le h1 h2 h3
  · have hrun' := hrun.congr (encode_si_eq a) hbenc
    refine hrun'.mono ?_
    rw [hma]
    -- the arithmetic
    have hNle : N ≤ pw cset dset m := le_trans (length_le_size Os) hOssz
    have hro : pw cro dro (Enc.size ((0, (orbStep sol)^[N] st₀) : ℕ × OrbState)) ≤
        pw cro dro (Sst m) := by
      have := hstate N le_rfl
      rw [Nat.sub_self] at this
      exact pw_mono cro dro this
    have hAm : A m ≤ pw cA dA m := hA m
    have hAdef : A m = (pw cset dset m + 1) * (F (Sst m) + 103) + pw cro dro (Sst m) := rfl
    rw [hAdef] at hAm
    show pw cset dset m + (N * (F (Sst m) + 100 * Qn + 2) + 1 +
      pw cro dro (Enc.size ((0, (orbStep sol)^[N] st₀) : ℕ × OrbState))) ≤ pw cA dA m * Qn
    exact orbit_arith hQ1 hNle hro hAm

end Run

end Algo
