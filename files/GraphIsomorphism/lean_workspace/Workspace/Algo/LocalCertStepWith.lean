import Workspace.Algo.LocalCertProc

/-!
# A solver-free step of Procedure LocalCertificates (§13.1)

The child supplies one answer. Both uses of the old solver call read that same answer.
The state update normalizes generators and images, so its size bound needs no bound on
this answer. These functions are intended for the fold state of the node of lines 5–7.
-/

namespace Algo

open RAM RAM.Targets
open Equiv (Perm)

/-- The new generators, read from one child's answer (§13.1, line 04). -/
def lcwGens (q : RawCoset × RawLCLoop) : RawGens :=
  tidyGens (q.2.1.1, q.1.elim [] Prod.fst)

/-- The images of those generators in the old action (§13.1, line 04). -/
def lcwImgs (q : RawCoset × RawLCLoop) : RawGens :=
  (lcwGens q).map (fun g => normPerm (q.2.1.2, rawImgOf (lcAct q.2, g)))

/-- One step of §13.1 with the answer supplied by a child of the master round. -/
def lcStepWith (a : RawCoset) (p : RawLCLoop) : RawLCLoop :=
  if lcCond p then (p.1, lcAffNew p, lcwGens (a, p), lcwImgs (a, p)) else p

/-- Both occurrences of the solver call have the same argument. -/
theorem lcwStep_eq (solve : RawLCSI → RawCoset) (p : RawLCLoop) :
    lcStep solve p = lcStepWith (solve (lcInst p)) p := rfl

theorem lcwPolyFun_gens : PolyFun lcwGens := by
  have he : PolyFun (fun q : RawCoset × RawLCLoop => q.1.elim ([] : RawGens) Prod.fst) :=
    (PolyFun.optionElim (g := fun _ : RawLCLoop => ([] : RawGens))
      (h := fun z : (RawGens × RawPerm) × RawLCLoop => z.1.1)
      (polyFun_const _) (polyFun_fst.comp polyFun_fst)).of_eq (fun _ => rfl)
  exact (((polyFun_snd.comp polyFun_lcStr).pair he).comp polyFun_tidyGens).of_eq
    (fun _ => rfl)

theorem lcwPolyFun_imgs : PolyFun lcwImgs := by
  have hf : PolyFun (fun z : RawLCLoop × RawPerm =>
      normPerm (z.1.1.2, rawImgOf (lcAct z.1, z.2))) :=
    ((polyFun_fst.comp polyFun_lcTdom).pair
      (((polyFun_fst.comp polyFun_lcAct).pair polyFun_snd).comp polyFun_rawImgOf)).comp
      polyFun_normPerm
  exact ((polyFun_snd.pair lcwPolyFun_gens).comp (PolyFun.mapParam hf)).of_eq
    (fun _ => rfl)

/-- The update has polynomial cost, with no solver hypothesis. -/
theorem lcwPolyFun_step : PolyFun (fun q : RawCoset × RawLCLoop => lcStepWith q.1 q.2) := by
  have hn : PolyFun (fun q : RawCoset × RawLCLoop =>
      ((q.2.1, lcAffNew q.2, lcwGens q, lcwImgs q) : RawLCLoop)) :=
    (polyFun_snd.comp polyFun_fst).pair ((polyFun_snd.comp polyFun_lcAffNew).pair
      (lcwPolyFun_gens.pair lcwPolyFun_imgs))
  exact (PolyFun.ite (polyFun_snd.comp polyFun_lcCond) hn polyFun_snd).of_eq
    (fun _ => rfl)

/-- The context does not change. -/
@[simp] theorem lcwStep_fst (a : RawCoset) (p : RawLCLoop) :
    (lcStepWith a p).1 = p.1 := lcStep_fst (fun _ => a) p

/-- The state bound from session 4 holds for every answer, including malformed ones. -/
theorem lcwSize_step (a : RawCoset) (p : RawLCLoop) :
    Enc.size (lcStepWith a p).2 ≤ max (Enc.size p.2) (lcStBound (Enc.size p.1)) :=
  size_lcStep_snd_le (fun _ => a) p

section Invariant

open scoped Classical
variable {n m : ℕ} {G : Subgroup (Perm (Fin n))} {ϕ : G →* Perm (Fin m)}
  {xs : RawStr} {tdom : List ℕ} {hc : LCCtxWF n m xs tdom}
  {s : Babai.Stage ϕ (decStrN n xs) (winSet m tdom)} {st : RawLCSt}

/-- §13.1, lines 03–04 preserve the stage invariant using just the current answer. -/
theorem lcwStateFor_step {a : RawCoset}
    (ha : decCoset n a = (decLCSI n (lcInst ((xs, tdom), st))).answer)
    (h : StateFor hc s st) (hcond : lcCond ((xs, tdom), st) = true) :
    StateFor hc s.step (lcStepWith a ((xs, tdom), st)).2 := by
  let solve : RawLCSI → RawCoset := fun _ => a
  change StateFor hc s.step (lcStep solve ((xs, tdom), st)).2
  -- the answer of line 04 is `H(W_new)`
  have hans : decCoset n (solve (lcInst ((xs, tdom), st)))
      = (s.step.H : Set (Perm (Fin n))) := by
    rw [ha]
    exact answer_lcInst h
  obtain ⟨a, σ, hsome, hgrpa⟩ := decGroup_of_decCoset_eq hans
  -- the new state
  have hstep : lcStep solve ((xs, tdom), st)
      = ((xs, tdom), (lcAffNew ((xs, tdom), st), lcNewGens solve ((xs, tdom), st),
          lcNewImgs solve ((xs, tdom), st))) := by
    rw [lcStep, if_pos hcond]
  have hgens : lcNewGens solve ((xs, tdom), st) = tidyGens (xs, a) := by
    rw [lcNewGens, hsome]
    rfl
  have hwfG : RawGens.WF n (lcNewGens solve ((xs, tdom), st)) := by
    rw [hgens]; exact wf_tidyGens hc.lenStr a
  have hgrp : decGroup n (lcNewGens solve ((xs, tdom), st)) = s.step.H := by
    rw [hgens, decGroup_tidyGens hc.lenStr, hgrpa]
  -- every new generator lies in the old group
  have hsub : ∀ g ∈ lcNewGens solve ((xs, tdom), st), decPerm n g ∈ decGroup n st.2.1 := by
    intro g hg
    have h1 : decPerm n g ∈ decGroup n (lcNewGens solve ((xs, tdom), st)) :=
      Subgroup.subset_closure (List.mem_map_of_mem hg)
    rw [hgrp] at h1
    rw [h.grp]
    exact s.step_H_le h1
  have himg : ∀ (g : RawPerm) (hg : g ∈ lcNewGens solve ((xs, tdom), st)),
      rawImgOf (lcAct ((xs, tdom), st), g)
        = encPerm tdom.length
            (psiFin ϕ tdom hc.nodup hc.ltM h.le ⟨decPerm n g, hsub g hg⟩) :=
    fun g hg => rawImgOf_state h (hwfG g hg) (hsub g hg)
  rw [hstep]
  refine ⟨nodup_lcAffNew _, fun u hu => lt_lcAffNew hc hu, ?_, hwfG, ?_, hgrp, ?_, ?_⟩
  · show winSet n (lcAffNew ((xs, tdom), st)) = s.step.W
    rw [winSet_lcAffNew h, Babai.Stage.step_W]
  · show (lcNewGens solve ((xs, tdom), st)).length ≤ n * n
    rw [hgens]; exact length_tidyGens hc.lenStr a
  · -- the images are well-formed permutations of the test set
    intro y hy
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hy
    exact wf_normPerm rfl _
  · -- and they really are the images
    intro hle
    refine ⟨by simp [lcNewImgs], ?_⟩
    intro i hi hi'
    have hi2 : i < (lcNewGens solve ((xs, tdom), st)).length := by
      simpa using hi
    have hmemg : (lcNewGens solve ((xs, tdom), st))[i] ∈ lcNewGens solve ((xs, tdom), st) :=
      List.getElem_mem hi2
    simp only [lcNewImgs, List.getElem_map]
    rw [decPerm_normPerm rfl, himg _ hmemg, decPerm_encPerm]
    exact psiFin_congr hc.nodup hc.ltM h.le hle _ _


/-- The indexed form used by the outer fold. -/
theorem lcwStateFor_succ {a : RawCoset} {i : ℕ}
    (ha : decCoset n a = (decLCSI n (lcInst ((xs, tdom), st))).answer)
    (h : StateFor hc (Babai.stages ϕ (decStrN n xs) (winSet m tdom) i) st)
    (hcond : lcCond ((xs, tdom), st) = true) :
    StateFor hc (Babai.stages ϕ (decStrN n xs) (winSet m tdom) (i + 1))
      (lcStepWith a ((xs, tdom), st)).2 := by
  exact lcwStateFor_step ha h hcond

end Invariant

/-- The test of §13.1, line 02 has failed. -/
def lcDone (p : RawLCLoop) : Bool := !lcCond p

/-- Read lines 06–10 from a completed loop state (§13.1). -/
def lcOutOf (p : RawLCLoop) : RawLCOut :=
  (p.2.1, rawIsFullT (p.1.2, p.2.2.2), rawCertK (lcFinalWin p),
    rawCertM (p.1.2, p.2.2.2))

theorem lcwOut_eq (solve : RawLCSI → RawCoset) (p : RawLCLoop) :
    lcOut solve p = lcOutOf (lcRun solve p) := rfl

theorem lcwPolyFun_done : PolyFun lcDone := by
  exact (PolyFun.ite polyFun_lcCond (polyFun_const false) (polyFun_const true)).of_eq
    (fun p => by cases h : lcCond p <;> simp [lcDone, h])

theorem lcwDone_iff (p : RawLCLoop) : lcDone p = true ↔ lcCond p = false := by
  simp [lcDone]

theorem lcwStep_of_done (a : RawCoset) (p : RawLCLoop) (h : lcDone p = true) :
    lcStepWith a p = p := by
  simp [lcStepWith, (lcwDone_iff p).1 h]

theorem lcwPolyFun_out : PolyFun lcOutOf := by
  have ht := polyFun_lcTdom.pair polyFun_lcImgsOf
  exact (polyFun_lcWin.pair ((ht.comp polyFun_rawIsFullT).pair
    ((polyFun_lcFinalWin.comp polyFun_rawCertK).pair (ht.comp polyFun_rawCertM)))).of_eq
    (fun _ => rfl)

section ReadOff
open scoped Classical
variable {n m : ℕ} {G : Subgroup (Perm (Fin n))} {ϕ : G →* Perm (Fin m)}
  {xs : RawStr} {tdom : List ℕ} {hc : LCCtxWF n m xs tdom} {st : RawLCSt}
  (h : StateFor hc (Babai.outStage ϕ (decStrN n xs) (winSet m tdom)) st)

include h

/-- At the output stage the stopping test is true (§13.1, line 02). -/
theorem lcwDone_outStage : lcDone ((xs, tdom), st) = true := by
  apply (lcwDone_iff _).2
  cases hb : lcCond ((xs, tdom), st)
  · rfl
  · exact (Babai.not_loopCond_outStage ϕ (decStrN n xs) (winSet m tdom)
      ((lcCond_eq_true_iff h).1 hb)).elim

theorem lcwOut_window : winSet n (lcOutOf ((xs, tdom), st)).1 =
    Babai.windowOut ϕ (decStrN n xs) (winSet m tdom) := h.winW

/-- The flag is the exact test on line 07. -/
theorem lcwOut_full : (lcOutOf ((xs, tdom), st)).2.1 = true ↔
    Babai.isFullOut ϕ (decStrN n xs) (winSet m tdom) := rawIsFullT_stateFor h

/-- The final window satisfies the hypotheses of the certificate routine. -/
theorem lcwFinalWin_wf : WinWF n (lcFinalWin ((xs, tdom), st)) := by
  have hinv : rawIsInvariant (st.2.1, st.1) = true := by
    rw [rawIsInvariant_eq_true_iff h.wfG h.ltW]
    change Babai.IsInvariant (decGroup n st.2.1) (winSet n st.1)
    rw [h.winW, h.grp]
    exact (Babai.outStage ϕ (decStrN n xs) (winSet m tdom)).inv
  refine ⟨hc.lenStr, hc.lenStr, h.nodupW, h.ltW, h.wfG, h.lenG, ?_, hinv⟩
  show RawPerm.WF n (rawOne xs)
  rw [rawOne, hc.lenStr, ← encPerm_one]
  exact wf_encPerm n _

/-- §13.1, line 08 reads off `K(T)` without calling a solver. -/
theorem lcwOut_certK : decGroup n (lcOutOf ((xs, tdom), st)).2.2.1 =
    Babai.certK ϕ (decStrN n xs) (winSet m tdom) := by
  change decGroup n (rawCertK (lcFinalWin ((xs, tdom), st))) = _
  rw [decGroup_rawCertK (lcwFinalWin_wf h)]
  change Babai.pointwiseStabilizer (decGroup n st.2.1) (winSet n st.1)ᶜ = _
  rw [h.grp, h.winW]
  rfl

/-- §13.1, line 10 reads off `M(T)`, transported through the test-set naming. -/
theorem lcwOut_certM : decGroup tdom.length (lcOutOf ((xs, tdom), st)).2.2.2 =
    (Babai.certM ϕ (decStrN n xs) (winSet m tdom)).map
      ((tName m tdom hc.nodup hc.ltM).symm.permCongrHom).toMonoidHom := by
  change decGroup tdom.length (rawCertM (tdom, st.2.2)) = _
  have he : decGroup tdom.length (rawCertM (tdom, st.2.2)) =
      (psiFin ϕ tdom hc.nodup hc.ltM h.le).range :=
    decGroup_rawCertM (gens := st.2.1.map (decPerm n)) (td := (tdom, st.2.2))
      h.wfI (h.himgs h.le)
  rw [he, range_psiFin]
  exact congrArg (fun K => K.map
    ((tName m tdom hc.nodup hc.ltM).symm.permCongrHom).toMonoidHom)
    (Babai.imgOn_congr h.grp h.le
      (Babai.outStage ϕ (decStrN n xs) (winSet m tdom)).le)

end ReadOff
end Algo
