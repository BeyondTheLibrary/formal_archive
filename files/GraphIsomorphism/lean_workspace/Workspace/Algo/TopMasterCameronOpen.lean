import Workspace.Algo.TopMasterCameronAdmission

/-! # The live transitive Cameron coset fold
Each representative gives one master call with its computed giant hint.
The index is at most the ambient degree on this branch. Capping the raw
width by that degree also bounds malformed machine states.
-/
set_option backward.isDefEq.respectTransparency false
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Pointwise

def masterCamOpenWidth (p : RawCameron × MasterDescInput) : ℕ :=
  min (masterDescWidth (masterCameronDescInput p)) p.2.1.2.2.2.1.length

def masterCamOpenChild (z : (RawCameron × MasterDescInput) × ℕ × RawCoset) :
    Option RawMasterSI :=
  if z.2.1 < masterCamOpenWidth z.1 then
    let p := masterCameronChildInput (z.1, z.2.1)
    some (p.1, some p.2)
  else none

def masterCamOpenOps (f : RawMasterSI → RawCameron × MasterDescInput) : MasterOps RawCoset where
  width := fun p => masterCamOpenWidth (f p)
  child := fun z => masterCamOpenChild (f z.1, z.2)
  init := fun _ => none
  combine := fun z => masterDescJoin (z.1.1.2.2.2.1, z.2.2.1, z.2.2.2)
  finish := fun z => top2NormC z.1.1.2.2.2.1 z.2

theorem polyFun_masterCamOpenWidth : PolyFun masterCamOpenWidth := by
  have hw : PolyFun (fun p : RawCameron × MasterDescInput => p.2.1) :=
    polyFun_snd.comp polyFun_fst
  have hx := (((hw.comp polyFun_snd).comp polyFun_snd).comp polyFun_snd).comp
    (polyFun_fst.comp polyFun_length)
  exact (((polyFun_masterCameronDescInput.comp polyFun_masterDescWidth).pair hx).comp
    polyFun_min).of_eq (fun _ => rfl)

theorem polyFun_masterCamOpenChild : PolyFun masterCamOpenChild := by
  have hinput : PolyFun (fun z : (RawCameron × MasterDescInput) × ℕ × RawCoset =>
      masterCameronChildInput (z.1, z.2.1)) :=
    (polyFun_fst.pair (polyFun_snd.comp polyFun_fst)).comp polyFun_masterCameronChildInput
  exact (PolyFun.ite
    (((polyFun_snd.comp polyFun_fst).add (polyFun_const 1)).le
      (polyFun_fst.comp polyFun_masterCamOpenWidth))
    (((hinput.comp polyFun_fst).pair ((hinput.comp polyFun_snd).comp polyFun_some)).comp
      polyFun_some) (polyFun_const none)).of_eq (fun z => by
      simp only [masterCamOpenChild, decide_eq_true_eq, Nat.add_one_le_iff])

theorem masterCamOpen_runCostQ (a b : ℕ) (f : RawMasterSI → RawCameron × MasterDescInput)
    (hf : PolyFun f) (hsource : ∀ p, (f p).2.1.2.2.2.1 = p.1.2.2.2.1) :
    Nonempty (Round.RunCostQ (masterAdmittedRound a b (masterCamOpenOps f))) := by
  have hx : PolyFun (fun p : RawMasterSI => p.1.2.2.2.1) :=
    (((polyFun_fst.comp polyFun_snd).comp polyFun_snd).comp polyFun_snd).comp polyFun_fst
  have hc : PolyFun (fun z : RawMasterSI × ℕ × RawCoset =>
      masterCamOpenChild (f z.1, z.2)) :=
    ((polyFun_fst.comp hf).pair polyFun_snd).comp polyFun_masterCamOpenChild
  have hu : PolyFun (fun z : RawMasterSI × ℕ × RawCoset × RawCoset =>
      masterDescJoin (z.1.1.2.2.2.1, z.2.2.1, z.2.2.2)) :=
    ((polyFun_fst.comp hx).pair (polyFun_snd.comp polyFun_snd)).comp polyFun_masterDescJoin
  have hfin : PolyFun (fun z : RawMasterSI × RawCoset => top2NormC z.1.1.2.2.2.1 z.2) :=
    ((polyFun_fst.comp hx).pair polyFun_snd).comp polyFun_top2NormC
  refine ⟨masterAdmittedRunCostQ a b (masterCamOpenOps f) chainBound id
    polyBound_chainBound.quasiPoly mono_chainBound polyBound_id.quasiPoly
    (show QuasiFun ((masterCamOpenOps f).width) from
      (hf.comp polyFun_masterCamOpenWidth).quasiFun)
    (by
      dsimp only [masterCamOpenOps]
      exact hc.quasiFun)
    (polyFun_const none).quasiFun
    hu.quasiFun hfin.quasiFun
    ?_ ?_ ?_ ?_⟩
  · intro p _
    change Enc.size (none : RawCoset) ≤ chainBound _
    rw [size_none]
    unfold chainBound
    omega
  · intro p j s A _ _ _
    exact size_top2NormC_le rfl le_rfl _
  · intro p s _ _
    have hs := size_top2NormC_le (n := masterDegree p) (dom := p.1.2.2.2.1) rfl le_rfl s
    exact hs.trans (by unfold masterInputCap; omega)
  · intro p _
    exact (Nat.min_le_right _ _).trans_eq (congrArg List.length (hsource p))

section Match
variable {n m a b : ℕ} {p : MasterDescInput} {c : RawCameron}
    {φ : decGroup n p.1.2.1 →* Perm (Fin m)}
    (hp : RawAction.WF n m (masterDescAction p) φ) (h : c.WF m)
    (hhi : (decGroup m p.2.2).map (permCongrHom (decCameron c h)).toMonoidHom ≤
      wreathProduct (JohnsonS c.k c.t) c.s)
    (hW : AggnCheckedWindowWF n p.1) (hm : m ≤ p.1.1.length)
    (hidx : (camNbar c h).relIndex (decGroup m p.2.2) ≤ m)
    (hinv : IsInvariant (decGroup n p.1.2.1) (winSet n p.1.1))
    (hcap : masterCameronChildBound n ≤ masterInputCap a b n)

include hp hhi hW hm hidx in
theorem masterCamOpenWidth_eq :
    masterCamOpenWidth (c, p) = masterDescWidth (masterCameronDescInput (c, p)) := by
  apply Nat.min_eq_left
  rw [masterCameronDesc_width hp h hhi, hW.2.2.2.2.2.1.1]
  exact hidx.trans (hm.trans (length_le_of_nodup_lt hW.1 hW.2.1))

/-- Admission reads its parent only through the degree and the raw measure. -/
theorem masterAdmitChild_congr {a b : ℕ} {P Q : RawMasterSI}
    (hd : masterDegree P = masterDegree Q) (hr : masterRawMeasure P = masterRawMeasure Q)
    (o : Option RawMasterSI) : masterAdmitChild a b (P, o) = masterAdmitChild a b (Q, o) := by
  simp only [masterAdmitChild, masterAdmit, hd, hr]

variable {S : Type} {F : MasterOps S} (u : RawCoset → S) (P : RawMasterSI)
    (hP1 : P.1.1 = p.1.1) (hPx : P.1.2.2.2.1 = p.1.2.2.2.1) (hP2 : P.2 = none)
    (hw : F.width P = masterCamOpenWidth (c, p))
    (hc : ∀ j s, F.child (P, j, u s) = masterCamOpenChild ((c, p), j, s))
    (hi : F.init P = u none)
    (hu : ∀ j s A, F.combine (P, j, u s, A) =
      u (masterDescJoin (p.1.2.2.2.1, s, A)))
    (hf : ∀ s, F.finish (P, u s) = top2NormC p.1.2.2.2.1 s)

include hP1 hPx hP2 in
theorem masterCamOpen_admit_parent (o : Option RawMasterSI) :
    masterAdmitChild a b (P, o) = masterAdmitChild a b ((p.1, none), o) := by
  apply masterAdmitChild_congr
  · exact congrArg List.length hPx
  · unfold masterRawMeasure masterParameter masterDegree
    rw [hP2]
    simp only [Option.elim, masterWindowSize, hP1, hPx]

include hp hhi hW hm hidx hinv hcap hP1 hPx hP2 hw hc hu hf in
theorem masterCamOpen_loop_at : ∀ w j s,
    j + w = masterDescWidth (masterCameronDescInput (c, p)) →
    LoopMatch (masterAdmittedRound a b F) (fun J => decWinSI n J.1) (decCoset n)
      P w j (u s)
      (descentChain (decGroup n (camLiftGens (c, masterDescAction p))) (decWinSI n p.1).Δ
        (decWinSI n p.1).x (decWinSI n p.1).y (decCoset n s)
        ((List.range' j w).map (fun k => decPerm n
          (masterDescRep (masterCameronDescInput (c, p), k))))) := by
  intro w
  induction w with
  | zero =>
    intro j s hj
    simp only [List.range'_zero, List.map_nil, descentChain]
    refine .done 0 j (u s) _ ?_ ?_
    · apply (masterAdmittedRound a b F).child_eq_none
      change F.width P ≤ j
      rw [hw, masterCamOpenWidth_eq hp h hhi hW hm hidx]
      omega
    · change decCoset n (F.finish (P, u s)) = _
      rw [hf]
      exact decCoset_top2NormC hp.1 s
  | succ w ih =>
    intro j s hj
    have hj' : j < masterCamOpenWidth (c, p) := by
      rw [masterCamOpenWidth_eq hp h hhi hW hm hidx]
      omega
    rw [List.range'_succ, List.map_cons, descentChain]
    have hjob := masterDescJob_spec (p := masterCameronDescInput (c, p)) (n := n) j
    change decWinSI n (masterCameronChildInput ((c, p), j)).1 =
      ⟨decPerm n (masterDescRep (masterCameronDescInput (c, p), j)) •
        (decGroup n (camLiftGens (c, masterDescAction p)) : Set (Perm (Fin n))),
        (decWinSI n p.1).Δ, (decWinSI n p.1).x, (decWinSI n p.1).y⟩ at hjob
    rw [← hjob]
    let J : RawMasterSI := ((masterCameronChildInput ((c, p), j)).1,
      some (masterCameronChildInput ((c, p), j)).2)
    change LoopMatch _ _ _ _ _ _ _ (.call (decWinSI n J.1) _)
    refine .call w j (u s) J _ ?_ ?_
    · change masterGuardedChild a b F (P, j, u s) = some J
      unfold masterGuardedChild
      rw [hw, if_pos hj', hc]
      unfold masterCamOpenChild
      rw [if_pos hj', masterCamOpen_admit_parent P hP1 hPx hP2]
      exact masterCameronChildInput_admitted hp h hhi hW hm hinv hcap j
    · intro A hA
      change LoopMatch _ _ _ _ _ _ (F.combine (P, j, u s, A)) _
      rw [hu]
      have hh := ih (j + 1) (masterDescJoin (p.1.2.2.2.1, s, A)) (by omega)
      have he : decCoset n (masterDescJoin (p.1.2.2.2.1, s, A)) =
          cosetHull (decCoset n s ∪ (decWinSI n J.1).answer) := by
        change decCoset n (top2NormC p.1.2.2.2.1 (rawCosetJoin (p.1.2.2.2.1, s, A))) = _
        have hx : p.1.2.2.2.1.length = n := hp.1
        rw [decCoset_top2NormC hx, decCoset_rawCosetJoin hx, hA]
      rw [he] at hh
      exact hh

include hp hhi hW hm hidx hinv hcap hP1 hPx hP2 hw hc hi hu hf in
/-- The coset fold at any node with the same window, source and no hint. -/
theorem masterCamOpen_match_at :
    LoopMatch (masterAdmittedRound a b F) (fun J => decWinSI n J.1) (decCoset n)
      P (F.width P) 0 (F.init P)
      (masterDescTree n (masterCameronDescInput (c, p))) := by
  rw [hw, masterCamOpenWidth_eq hp h hhi hW hm hidx, hi]
  simpa only [masterDescTree, masterDescPerms, List.range_eq_range', decCoset]
    using masterCamOpen_loop_at hp h hhi hW hm hidx hinv hcap u P hP1 hPx hP2 hw hc hu hf
      (masterDescWidth (masterCameronDescInput (c, p))) 0 none (Nat.zero_add _)

include hp hhi hW hm hidx hinv hcap in
theorem masterCamOpen_match
    (hw : F.width (p.1, none) = masterCamOpenWidth (c, p))
    (hc : ∀ j s, F.child ((p.1, none), j, u s) = masterCamOpenChild ((c, p), j, s))
    (hi : F.init (p.1, none) = u none)
    (hu : ∀ j s A, F.combine ((p.1, none), j, u s, A) =
      u (masterDescJoin (p.1.2.2.2.1, s, A)))
    (hf : ∀ s, F.finish ((p.1, none), u s) = top2NormC p.1.2.2.2.1 s) :
    LoopMatch (masterAdmittedRound a b F) (fun J => decWinSI n J.1) (decCoset n)
      (p.1, none) (F.width (p.1, none)) 0 (F.init (p.1, none))
      (masterDescTree n (masterCameronDescInput (c, p))) :=
  masterCamOpen_match_at hp h hhi hW hm hidx hinv hcap u (p.1, none) rfl rfl rfl hw hc hi hu hf
end Match
end Algo
