import Workspace.Algo.TopMasterCheckedMatch
import Workspace.Algo.TopMasterWinLink

/-! # Line 4b calls the master carrier directly
The already flattened top-action fold emits normalized ambient inputs.
Alphabet and window bounds of the exact supplied tree prove that the
master admission checks preserve every actual call.
-/
set_option synthInstance.maxSize 4096
namespace Algo
open RAM RAM.Targets Babai Equiv

 def master4OpenRead (J : Master4Node) : RawWinSI := J.1.2.getD ([], [], [], [], [])
 def master4OpenChild (e f u v : ℕ) (z : MasterHintInput × ℕ × Top4State) : Option RawMasterSI :=
  (master4Child e f u v (master4Enter z.1, z.2)).map
    (fun J => masterCheckedCall (z.1.1.2.2.2.1, master4OpenRead J))
 def master4OpenWidth (p : MasterHintInput) : ℕ :=
  if (master4Enter p).1.1.2.2.2 then top4Width (master4Enter p).1.1.2.1.1 else 0
 def master4OpenInit (p : MasterHintInput) : Top4State := master4Init (master4Enter p)
 def master4OpenCombine (z : MasterHintInput × ℕ × Top4State × RawCoset) : Top4State :=
  master4Combine (master4Enter z.1, z.2)
 def master4OpenFinish (z : MasterHintInput × Top4State) : RawCoset :=
  master4Finish (fun _ => none) (master4Enter z.1, z.2)

 theorem master4OpenWidth_eq (a b c d e f u v : ℕ) (solve : RawWinSI → RawCoset) (p : MasterHintInput) :
    (master4Round a b c d e f u v solve).width (master4Enter p) = master4OpenWidth p := rfl

 theorem master4OpenFinish_eq (solve : RawWinSI → RawCoset) (p : MasterHintInput) (s : Top4State) :
    master4OpenFinish (p, s) = master4Finish solve (master4Enter p, s) := rfl

 theorem polyFun_master4OpenRead : PolyFun master4OpenRead := by
  exact (((polyFun_fst.comp polyFun_snd).pair (polyFun_const (0 : ℕ))).comp
    (PolyFun.optionElim (polyFun_const (([], [], [], [], []) : RawWinSI)) polyFun_fst)).of_eq
      (fun J => by unfold master4OpenRead; cases J.1.2 <;> rfl)

 theorem polyFun_master4OpenChild (e f u v : ℕ) : PolyFun (master4OpenChild e f u v) := by
  have hc := ((polyFun_fst.comp polyFun_master4Enter).pair polyFun_snd).comp
    (polyFun_master4Child e f u v)
  have hx : PolyFun (fun z : MasterHintInput × ℕ × Top4State => z.1.1.2.2.2.1) :=
    ((((polyFun_fst.comp polyFun_fst).comp polyFun_snd).comp polyFun_snd).comp polyFun_snd).comp polyFun_fst
  have hbody : PolyFun (fun z : Master4Node × RawStr =>
      some (masterCheckedCall (z.2, master4OpenRead z.1))) :=
    ((polyFun_snd.pair (polyFun_fst.comp polyFun_master4OpenRead)).comp
      polyFun_masterCheckedCall).comp polyFun_some
  exact ((hc.pair hx).comp (PolyFun.optionElim (polyFun_const none) hbody)).of_eq (fun z => by
    unfold master4OpenChild
    cases master4Child e f u v (master4Enter z.1, z.2) <;> rfl)

 theorem polyFun_master4OpenWidth : PolyFun master4OpenWidth := by
  have hI := polyFun_master4Enter
  have hP := (((hI.comp polyFun_fst).comp polyFun_fst).comp polyFun_snd)
  exact PolyFun.ite ((hP.comp polyFun_snd).comp polyFun_snd)
    (((hP.comp polyFun_fst).comp polyFun_fst).comp polyFun_top4Width) (polyFun_const 0)

 theorem polyFun_master4OpenInit : PolyFun master4OpenInit :=
  polyFun_master4Enter.comp polyFun_master4Init
 theorem polyFun_master4OpenCombine : PolyFun master4OpenCombine :=
  ((polyFun_fst.comp polyFun_master4Enter).pair polyFun_snd).comp polyFun_master4Combine
 theorem quasiFun_master4OpenFinish : QuasiFun master4OpenFinish :=
  ((polyFun_fst.comp polyFun_master4Enter).pair polyFun_snd).comp_quasiFun
    (quasiFun_master4Finish (quasiFun_const none))

 theorem master4OpenRead_decode {n e f u v : ℕ} {I J : Master4Node} {j : ℕ} {s : Top4State}
    (hJ : master4Child e f u v (I, j, s) = some J) :
    master4Decode n J = decWinSI n (master4OpenRead J) := by
  obtain ⟨K, hK, rfl⟩ := Option.map_eq_some_iff.mp hJ
  obtain ⟨_, W, rfl, _⟩ := top4wChild_some hK
  rfl

 theorem master4OpenFinish_size (p : MasterHintInput) (s : Top4State) :
    Enc.size (master4OpenFinish (p, s)) ≤ chainBound p.1.2.2.2.1.length :=
  master4Finish_size (fun _ => none) (master4Enter p) s

/-- Every call of line 4b is a coset instance (Sec. 15, line 4b: the calls of the giant
top-action round of Sec. 13, lifted from the window). -/
 theorem master4Tree_calls_coset {n m : ℕ} {p : MasterHintInput}
    (hgs : RawGens.WF n p.1.2.1) (hnd : p.1.1.Nodup) (hlt : ∀ u ∈ p.1.1, u < n)
    (hinv : IsInvariant (decGroup n p.1.2.1) (winSet n p.1.1))
    {ϕ : decGroup p.1.1.length (masterHintTop p).1.1.2 →* Perm (Fin m)}
    (hp : RawAction.WF p.1.1.length m (masterHintTop p).1 ϕ)
    (hG : IsTransitive (decGroup p.1.1.length (masterHintTop p).1.1.2))
    (hϕ : IsGiantRep ϕ) (hn : 64 ≤ p.1.1.length) (hr : masterHintRoute p = 3) :
    ∀ J ∈ (master4Tree hnd hlt hinv hp hG hϕ hn hr).calls,
      IsCosetInstance (decGroup n p.1.2.1) J := by
  have hc := masterLine4b_inner_coset (n := n) hp hG hϕ hn hr
  rw [masterLine4b_group hgs hnd hlt hinv] at hc
  simp only [master4Tree, masterLine4bTree, SIReduction.calls_bind, SIReduction.calls_done,
    List.append_nil]
  exact top4wTree_calls_isCosetInstance hnd hlt hinv _ _ hc

 theorem masterAdmittedRound_four_match {S : Type} (a b e f u v : ℕ) {F : MasterOps S}
    {n m : ℕ} {p : MasterHintInput}
    (hx : RawStr.WF n (2 * n + 1) p.1.2.2.2.1)
    (hy : RawStr.WF n (2 * n + 1) p.1.2.2.2.2)
    (hgs : RawGens.WF n p.1.2.1) (hnd : p.1.1.Nodup) (hlt : ∀ z ∈ p.1.1, z < n)
    (hinv : IsInvariant (decGroup n p.1.2.1) (winSet n p.1.1))
    {ϕ : decGroup p.1.1.length (masterHintTop p).1.1.2 →* Perm (Fin m)}
    (hp : RawAction.WF p.1.1.length m (masterHintTop p).1 ϕ)
    (hG : IsTransitive (decGroup p.1.1.length (masterHintTop p).1.1.2))
    (hϕ : IsGiantRep ϕ) (hn : 64 ≤ p.1.1.length) (hr : masterHintRoute p = 3)
    (hcap : TopwpCap e f) (houter : Top4wCap e f u v)
    (emb : Top4State → S)
    (hwidth : F.width (p.1, some p.2) = master4OpenWidth p)
    (hchild : ∀ j s, F.child ((p.1, some p.2), j, emb s) = master4OpenChild e f u v (p, j, s))
    (hinit : F.init (p.1, some p.2) = emb (master4OpenInit p))
    (hcombine : ∀ j s A, F.combine ((p.1, some p.2), j, emb s, A) = emb (master4OpenCombine (p, j, s, A)))
    (hfinish : ∀ s, F.finish ((p.1, some p.2), emb s) = master4OpenFinish (p, s)) :
    LoopMatch (masterAdmittedRound a b F) (fun J => decWinSI n J.1) (decCoset n)
      (p.1, some p.2) (F.width (p.1, some p.2)) 0 (F.init (p.1, some p.2))
      (master4Tree hnd hlt hinv hp hG hϕ hn hr) := by
  have hwsize : masterWindowSize (p.1, some p.2) ≤ masterDegree (p.1, some p.2) := by
    change p.1.1.length ≤ p.1.2.2.2.1.length
    rw [hx.1]
    exact length_le_of_nodup_lt hnd hlt
  apply masterAdmittedRound_checked_match a b (p := (p.1, some p.2))
    (R := master4Round 0 0 0 0 e f u v (fun _ => none))
    (I := master4Enter p) hx.1 hwsize master4OpenRead emb (master4Decode n)
    (fun _ _ _ h => master4OpenRead_decode h) hwidth hchild hinit hcombine hfinish
    (master4Enter_loop hx.1 hgs hnd hlt hinv hp hG hϕ hn hr hcap houter (fun _ => none))
  intro J hJ
  refine ⟨master4Tree_letters hx hy hgs hnd hlt hinv hp hG hϕ hn hr J hJ, ?_,
    _, master4Tree_calls_coset hgs hnd hlt hinv hp hG hϕ hn hr J hJ⟩
  have hsize := (master4Tree_spec hx.1 hgs hnd hlt hinv hp hG hϕ hn hr).2.2 J hJ
  change J.windowSize < p.1.1.length
  omega
end Algo
