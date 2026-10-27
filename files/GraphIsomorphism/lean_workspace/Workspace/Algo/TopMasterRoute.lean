import Workspace.Algo.TopPrimitiveWindowCost
import Workspace.Master.Sec15

/-! # The computed tests of Section 15
An inherited hint stores the target domain, the images of the current
window generators in their existing order, and the standard-block arity.
The source action is recomputed by restriction, so its generators cannot
silently differ from those of the current instance. The target is shifted
as in Equation (59) before any string-dependent test.

The route numbers are 0 for Reduce-to-Johnson, 1 for line 2, 2 for line
4a, 3 for line 4b, 4 for lines 4c–4d, and 5 for AggregateCertificates.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv

abbrev RawMasterHint := (List ℕ × RawGens) × ℕ
abbrev RawMasterSI := RawWinSI × Option RawMasterHint
abbrev MasterHintInput := RawWinSI × RawMasterHint

def masterHintTop (p : MasterHintInput) : RawTop3 :=
  (((p.1.1, (primitiveWindowInput p.1).1), p.2.1), (primitiveWindowInput p.1).2)

def masterHintRoute (p : MasterHintInput) : ℕ :=
  if p.2.1.1.length ≤ ellOf p.1.1.length then 1
  else if primitiveCaseTest ((masterHintTop p).1, p.2.2) then
    if p.2.2 = 1 then 2
    else if primitiveSmallDefect ((masterHintTop p).1, (masterHintTop p).2.1) then 3 else 4
  else 5

def masterRoute (p : RawMasterSI) : ℕ := p.2.elim 0 (fun h => masterHintRoute (p.1, h))

theorem polyFun_masterHintTop : PolyFun masterHintTop := by
  have hw : PolyFun (fun p : MasterHintInput => p.1.1) := polyFun_fst.comp polyFun_fst
  have hp : PolyFun (fun p : MasterHintInput => primitiveWindowInput p.1) :=
    polyFun_fst.comp polyFun_primitiveWindowInput
  exact ((hw.pair (hp.comp polyFun_fst)).pair (polyFun_snd.comp polyFun_fst)).pair
    (hp.comp polyFun_snd)

theorem polyFun_masterHintRoute : PolyFun masterHintRoute := by
  have ha := polyFun_masterHintTop.comp polyFun_fst
  have ht : PolyFun (fun p : MasterHintInput => p.2.2) := polyFun_snd.comp polyFun_snd
  have hm : PolyFun (fun p : MasterHintInput => p.2.1.1.length) :=
    ((polyFun_snd.comp polyFun_fst).comp polyFun_fst).comp polyFun_length
  have hn : PolyFun (fun p : MasterHintInput => ellOf p.1.1.length) :=
    polyFun_powConst (((polyFun_fst.comp polyFun_fst).comp polyFun_length).comp polyFun_log2) 3
  have hi := (ha.pair ht).comp polyFun_primitiveCaseTest
  have hs := (ha.pair ((polyFun_masterHintTop.comp polyFun_snd).comp polyFun_fst)).comp
    polyFun_primitiveSmallDefect
  exact (PolyFun.ite (hm.le hn) (polyFun_const 1)
    (PolyFun.ite hi (PolyFun.ite (ht.natEq (polyFun_const 1)) (polyFun_const 2)
      (PolyFun.ite hs (polyFun_const 3) (polyFun_const 4))) (polyFun_const 5))).of_eq
        (fun p => by simp only [masterHintRoute, decide_eq_true_eq])

theorem polyFun_masterRoute : PolyFun masterRoute :=
  ((polyFun_snd.pair polyFun_fst).comp
    (PolyFun.optionElim (polyFun_const 0)
      ((polyFun_snd.pair polyFun_fst).comp polyFun_masterHintRoute))).of_eq
    (fun p => by unfold masterRoute; cases p.2 <;> rfl)

theorem masterHintRoute_line2 (p : MasterHintInput) :
    masterHintRoute p = 1 ↔ p.2.1.1.length ≤ ellOf p.1.1.length := by
  unfold masterHintRoute
  split_ifs <;> simp_all

theorem masterHintRoute_line4a (p : MasterHintInput) :
    masterHintRoute p = 2 ↔ ellOf p.1.1.length < p.2.1.1.length ∧
      primitiveCaseTest ((masterHintTop p).1, p.2.2) = true ∧ p.2.2 = 1 := by
  unfold masterHintRoute
  split_ifs <;> simp_all

theorem masterHintRoute_line4b (p : MasterHintInput) :
    masterHintRoute p = 3 ↔ ellOf p.1.1.length < p.2.1.1.length ∧
      primitiveCaseTest ((masterHintTop p).1, p.2.2) = true ∧ p.2.2 ≠ 1 ∧
        primitiveSmallDefect ((masterHintTop p).1, (masterHintTop p).2.1) = true := by
  unfold masterHintRoute
  split_ifs <;> simp_all

theorem masterHintRoute_line4cd (p : MasterHintInput) :
    masterHintRoute p = 4 ↔ ellOf p.1.1.length < p.2.1.1.length ∧
      primitiveCaseTest ((masterHintTop p).1, p.2.2) = true ∧ p.2.2 ≠ 1 ∧
        primitiveSmallDefect ((masterHintTop p).1, (masterHintTop p).2.1) = false := by
  unfold masterHintRoute
  split_ifs <;> simp_all

theorem masterHintRoute_aggregate (p : MasterHintInput) :
    masterHintRoute p = 5 ↔ ellOf p.1.1.length < p.2.1.1.length ∧
      primitiveCaseTest ((masterHintTop p).1, p.2.2) = false := by
  unfold masterHintRoute
  split_ifs <;> simp_all

theorem masterRoute_line1 (p : RawMasterSI) : masterRoute p = 0 ↔ p.2 = none := by
  cases hh : p.2 with
  | none => simp [masterRoute, hh]
  | some h => simp only [masterRoute, hh, Option.elim_some, Option.some_ne_none, iff_false]
              unfold masterHintRoute
              split_ifs <;> decide

theorem masterHintRoute_huge {m : ℕ} {p : MasterHintInput}
    (hg : p.2.1.1.length = m) (hn : 64 ≤ p.1.1.length) (hr : masterHintRoute p ≠ 1) :
    HugeM m (Nat.card (Fin p.1.1.length)) := by
  have h := mt (masterHintRoute_line2 p).mpr hr
  rw [hg] at h
  simpa only [Nat.card_fin] using hugeM_of_line2 hn (Nat.lt_of_not_ge h)

/-- The live input of line 4b, including its computed twin classes and
automatic alignment, inside the original ambient window. -/
def masterLine4bInput (p : MasterHintInput) : Top4wInput :=
  (((p.1.2.2.2.1, p.1.2.1), p.1.1, p.1.2.2.2.1), top4PrimitiveInput (masterHintTop p))
def masterLine4bEnter (p : MasterHintInput) : Top4wNode := top4wEnter (masterLine4bInput p)

theorem polyFun_masterLine4bInput : PolyFun masterLine4bInput := by
  have hp : PolyFun (fun p : MasterHintInput => p.1) := polyFun_fst
  have hx := (((hp.comp polyFun_snd).comp polyFun_snd).comp polyFun_snd).comp polyFun_fst
  have hg := (hp.comp polyFun_snd).comp polyFun_fst
  have hw := hp.comp polyFun_fst
  exact ((hx.pair hg).pair (hw.pair hx)).pair
    (polyFun_masterHintTop.comp polyFun_top4PrimitiveInput)
theorem polyFun_masterLine4bEnter : PolyFun masterLine4bEnter :=
  polyFun_masterLine4bInput.comp polyFun_top4wEnter

theorem masterLine4bEnter_uniform_wf (A B c d e f u v : ℕ) : ∃ a b : ℕ,
    ∀ (n : ℕ) (p : MasterHintInput), p.1.2.2.2.1.length = n → Enc.size p ≤ topcsContextCap A B n →
      Top4wWF a b c d e f u v (masterLine4bEnter p) := by
  obtain ⟨F, hF, hmF, hsF⟩ := polyFun_masterLine4bInput.size.exists_polyBound
  obtain ⟨aa, bb, hab⟩ := hF.comp (polyBound_topcsContextCap A B)
  obtain ⟨a, b, h⟩ := top4wEnter_uniform_wf aa bb c d e f u v
  exact ⟨a, b, fun n p hn hp => h n (masterLine4bInput p) hn
    ((hsF p).trans ((hmF _ _ hp).trans (hab n)))⟩

/-- The computed line 4a route supplies the giant-window premise. -/
theorem masterLine4a_loop (a b : ℕ) {n m : ℕ} {p : MasterHintInput}
    (hx : p.1.2.2.2.1.length = n) (hgs : RawGens.WF n p.1.2.1)
    (hnd : p.1.1.Nodup) (hlt : ∀ u ∈ p.1.1, u < n)
    (hinv : IsInvariant (decGroup n p.1.2.1) (winSet n p.1.1))
    {ϕ : decGroup p.1.1.length (masterHintTop p).1.1.2 →* Perm (Fin m)}
    (hp : RawAction.WF p.1.1.length m (masterHintTop p).1 ϕ)
    (hG : IsTransitive (decGroup p.1.1.length (masterHintTop p).1.1.2))
    (hϕ : IsGiantRep ϕ) (hn : 64 ≤ p.1.1.length)
    (hr : masterHintRoute p = 2) :
    LoopMatch (primitiveWindowRound a b) (decWinSI n) (decCoset n) p.1 0 0 0
      (line4aReduction (decWinSI n p.1)) := by
  obtain ⟨_, ht, hone⟩ := (masterHintRoute_line4a p).mp hr
  have hm := masterHintRoute_huge hp.2.1 hn (by omega : masterHintRoute p ≠ 1)
  rw [hone] at ht
  have hg := primitiveCase_one_giant (top4PrimitiveId hp hG hϕ hm ht) hϕ
  have he := decGroup_rawRestrictGens_of_raw (dom := p.1.2.2.2.1) hgs hnd hlt hinv
  change alternatingGroup (Fin p.1.1.length) ≤ decGroup p.1.1.length
    (rawRestrictGens ((p.1.2.2.2.1, p.1.2.1), p.1.1)) at hg
  rw [he] at hg
  exact primitiveWindow_loop a b hx hgs hnd hlt hinv hg

end Algo
