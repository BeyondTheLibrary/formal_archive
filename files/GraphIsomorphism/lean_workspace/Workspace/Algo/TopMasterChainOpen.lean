import Workspace.Algo.TopMasterMeasure
import Workspace.Algo.A15Kinds

/-! # The orbit chain calls the master machine directly
The local phase's cached leaf is read as a new master input. The child,
initial state, update, and final coset shift are all polynomial routines;
none invokes a string-isomorphism solver. The ordered fold is unchanged.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv

/-- Read a phase leaf as an unhinted master call. -/
def masterChainOpenRead (J : MasterChainReturnNode) : RawMasterSI :=
  (J.1.2.getD J.1.1.1, none)

def masterChainOpenChild (z : RawWinSI × ℕ × RawCoset) : Option RawMasterSI :=
  (masterChainReturnChild (masterChainReturnEnter z.1, z.2)).map masterChainOpenRead

def masterChainOpenInit (W : RawWinSI) : RawCoset :=
  masterChainReturnInit (masterChainReturnEnter W)

def masterChainOpenCombine (z : RawWinSI × ℕ × RawCoset × RawCoset) : RawCoset :=
  top2NormC z.1.2.2.2.1 z.2.2.2

def masterChainOpenFinish (z : RawWinSI × RawCoset) : RawCoset :=
  top3Shift (z.1.2.2.2.1, normPerm (z.1.2.2.2.1, z.1.2.2.1),
    top2NormC z.1.2.2.2.1 z.2)

theorem polyFun_masterChainOpenRead : PolyFun masterChainOpenRead := by
  have ho : PolyFun (fun J : MasterChainReturnNode => J.1.2) := polyFun_fst.comp polyFun_snd
  have hd : PolyFun (fun J : MasterChainReturnNode => J.1.1.1) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_fst
  exact (((ho.pair hd).comp (PolyFun.optionElim polyFun_id polyFun_fst)).pair
    (polyFun_const (none : Option RawMasterHint))).of_eq (fun J => by
      unfold masterChainOpenRead
      cases J.1.2 <;> rfl)

theorem polyFun_masterChainOpenChild : PolyFun masterChainOpenChild := by
  have h := ((polyFun_fst.comp polyFun_masterChainReturnEnter).pair polyFun_snd).comp
    polyFun_masterChainReturnChild
  exact ((h.pair (polyFun_const (0 : ℕ))).comp
    (PolyFun.optionElim (polyFun_const none)
      ((polyFun_fst.comp polyFun_masterChainOpenRead).comp polyFun_some))).of_eq
    (fun z => by
      unfold masterChainOpenChild
      cases masterChainReturnChild (masterChainReturnEnter z.1, z.2) <;> rfl)

theorem polyFun_masterChainOpenInit : PolyFun masterChainOpenInit :=
  polyFun_masterChainReturnEnter.comp polyFun_masterChainReturnInit

theorem polyFun_masterChainOpenCombine : PolyFun masterChainOpenCombine :=
  (((((polyFun_fst.comp polyFun_snd).comp polyFun_snd).comp polyFun_snd).comp polyFun_fst).pair
    ((polyFun_snd.comp polyFun_snd).comp polyFun_snd)).comp polyFun_top2NormC

theorem polyFun_masterChainOpenFinish : PolyFun masterChainOpenFinish := by
  have hx : PolyFun (fun z : RawWinSI × RawCoset => z.1.2.2.2.1) :=
    (((polyFun_fst.comp polyFun_snd).comp polyFun_snd).comp polyFun_snd).comp polyFun_fst
  have hr : PolyFun (fun z : RawWinSI × RawCoset => z.1.2.2.1) :=
    ((polyFun_fst.comp polyFun_snd).comp polyFun_snd).comp polyFun_fst
  exact (hx.pair (((hx.pair hr).comp polyFun_normPerm).pair
    ((hx.pair polyFun_snd).comp polyFun_top2NormC))).comp polyFun_top3Shift

theorem masterChainOpenChild_eq_none (W : RawWinSI) (j : ℕ) (s : RawCoset)
    (hj : (winOrbits (W.2.1, W.1)).length ≤ j) : masterChainOpenChild (W, j, s) = none := by
  have h := (masterChainReturnRound 0 0 (fun _ => none)).child_eq_none
    (masterChainReturnEnter W) j s hj
  change masterChainReturnChild (masterChainReturnEnter W, j, s) = none at h
  simp [masterChainOpenChild, h]

theorem masterChainOpenChild_some {W : RawWinSI} {j : ℕ} {s : RawCoset} {J : RawMasterSI}
    (hc : masterChainOpenChild (W, j, s) = some J) :
    ∃ c, s = some c ∧ j < (winOrbits (W.2.1, W.1)).length ∧
      J = (masterChainLeaf ((masterChainPreparedEnter W).1, j, c), none) := by
  obtain ⟨K, hK, rfl⟩ := Option.map_eq_some_iff.mp hc
  obtain ⟨L, hL, rfl⟩ := Option.map_eq_some_iff.mp hK
  obtain ⟨c, _, hs, hj, rfl⟩ := masterChainChild_some hL
  exact ⟨c, hs, hj, rfl⟩

theorem masterChainOpenChild_degree {W : RawWinSI} {j : ℕ} {s : RawCoset} {J : RawMasterSI}
    (hc : masterChainOpenChild (W, j, s) = some J) : masterDegree J = masterDegree (W, none) := by
  obtain ⟨c, _, _, rfl⟩ := masterChainOpenChild_some hc
  rfl

theorem masterChainOpenChild_progress {n : ℕ} {W : RawWinSI} {j : ℕ} {s : RawCoset}
    {J : RawMasterSI} (hw : RawGens.WF n W.2.1) (hnd : W.1.Nodup)
    (hlt : ∀ u ∈ W.1, u < n) (hinv : rawIsInvariant (W.2.1, W.1) = true)
    (h2 : 1 < (winOrbits (W.2.1, W.1)).length)
    (hc : masterChainOpenChild (W, j, s) = some J) : masterWindowSize J < W.1.length := by
  obtain ⟨c, _, hj, rfl⟩ := masterChainOpenChild_some hc
  change ((winOrbits (W.2.1, W.1)).getD j []).length < _
  rw [List.getD_eq_getElem _ _ hj]
  exact winOrbits_length_lt hw hnd hlt hinv hj h2

theorem masterChainOpenChild_measure {n : ℕ} {W : RawWinSI} {j : ℕ} {s : RawCoset}
    {J : RawMasterSI} (hx : W.2.2.2.1.length = n)
    (hw : RawGens.WF n W.2.1) (hnd : W.1.Nodup)
    (hlt : ∀ u ∈ W.1, u < n) (hinv : rawIsInvariant (W.2.1, W.1) = true)
    (h2 : 1 < (winOrbits (W.2.1, W.1)).length)
    (hc : masterChainOpenChild (W, j, s) = some J) :
    masterRawMeasure J < masterRawMeasure (W, none) := by
  have hwin := masterChainOpenChild_progress hw hnd hlt hinv h2 hc
  have hlen := length_le_of_nodup_lt hnd hlt
  have hn := masterChainOpenChild_degree hc
  have hm : masterParameter J = 2 * masterWindowSize J := by
    obtain ⟨c, _, _, rfl⟩ := masterChainOpenChild_some hc
    rfl
  apply masterRawMeasure_lt hn hwin.le _ (Or.inl hwin)
  rw [hm]
  change 2 * masterWindowSize J ≤ 2 * W.2.2.2.1.length
  rw [hx]
  omega

/-- Move a fold to a master node while independently remapping its children.
Only the individual raw routines and child decoders are compared. -/
theorem loopMatch_reparent {ι ω α N S Ω A : Type*}
    {R : Round ι ω α} {M : Round N S α}
    {decI : ι → SIInstance Ω A} {decN : N → SIInstance Ω A}
    {decA : α → Set (Perm Ω)} (e : ι → N) (u : ω → S) (I : ι) (P : N)
    (hdec : ∀ J, decN (e J) = decI J)
    (hchild : ∀ j s, M.child (P, j, u s) = (R.child (I, j, s)).map e)
    (hcomb : ∀ j s a, M.combine (P, j, u s, a) = u (R.combine (I, j, s, a)))
    (hfin : ∀ s, M.finish (P, u s) = R.finish (I, s)) :
    ∀ w j s T, LoopMatch R decI decA I w j s T → LoopMatch M decN decA P w j (u s) T := by
  intro w j s T h
  induction h with
  | done w j s a hc ha =>
    refine .done w j (u s) a ?_ ?_
    · rw [hchild, hc]; rfl
    · rw [hfin]; exact ha
  | call w j s J k hc hn ih =>
    have hJ := hdec J
    refine (hJ ▸ LoopMatch.call (R := M) (decI := decN) (decA := decA) (I := P)
      w j (u s) (e J) k ?_ ?_)
    · rw [hchild, hc]; rfl
    · intro a ha
      have ha' : decA a = (decI J).answer := by rw [← hJ]; exact ha
      rw [hcomb]
      exact hJ ▸ ih a ha'

 theorem loopMatch_reparent_onCalls {ι ω α N S Ω A : Type*}
    {R : Round ι ω α} {M : Round N S α}
    {decI : ι → SIInstance Ω A} {decN : N → SIInstance Ω A}
    {decA : α → Set (Perm Ω)} (e : ι → N) (u : ω → S) (I : ι) (P : N)
    (V : SIInstance Ω A → Prop)
    (hdec : ∀ j s J, R.child (I, j, s) = some J → V (decI J) → decN (e J) = decI J)
    (hstop : ∀ j s, R.child (I, j, s) = none → M.child (P, j, u s) = none)
    (hcall : ∀ j s J, R.child (I, j, s) = some J → V (decI J) →
      M.child (P, j, u s) = some (e J))
    (hcomb : ∀ j s a, M.combine (P, j, u s, a) = u (R.combine (I, j, s, a)))
    (hfin : ∀ s, M.finish (P, u s) = R.finish (I, s)) :
    ∀ w j s T, LoopMatch R decI decA I w j s T →
      (∀ J ∈ T.calls, V J) → LoopMatch M decN decA P w j (u s) T := by
  intro w j s T h
  induction h with
  | done w j s a hc ha =>
    intro _
    refine .done w j (u s) a (hstop j s hc) ?_
    rw [hfin]; exact ha
  | call w j s J k hc hn ih =>
    intro hV
    have hvJ := hV (decI J) (by simp [SIReduction.calls])
    have hJ := hdec j s J hc hvJ
    refine (hJ ▸ LoopMatch.call (R := M) (decI := decN) (decA := decA) (I := P)
      w j (u s) (e J) k (hcall j s J hc hvJ) ?_)
    intro a ha
    have ha' : decA a = (decI J).answer := by rw [← hJ]; exact ha
    rw [hcomb]
    apply hJ ▸ ih a ha'
    intro K hK
    apply hV K
    simp only [SIReduction.calls_call, List.mem_cons]
    exact Or.inr (by simpa only [hJ] using hK)

/-- Every call of the orbit chain of line 1 is a coset instance: its window is invariant
under the group of its coset (Sec. 15, line 1; `calls_chainRuleCoset_isCosetInstance`). -/
theorem masterChainReturn_calls_coset {n B C₀ : ℕ} {W : RawWinSI}
    (hw : RawGens.WF n W.2.1) (hnd : W.1.Nodup) (hlt : ∀ u ∈ W.1, u < n)
    (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1))
    (hr : masterReduceRoute B C₀ W = 2) (q : ℕ) (hC : 1 < C₀) :
    ∀ J ∈ (masterChainReturnTree hw hnd hlt hinv hr q hC).calls,
      ∃ G : Subgroup (Perm (Fin n)), IsCosetInstance G J := by
  intro J hJ
  rw [masterChainReturn_calls] at hJ
  exact ⟨_, calls_chainRuleCoset_isCosetInstance (masterChainData hw hlt hinv)
    ⟨_, (masterChainRoute_nonempty hw hnd hlt hinv hr hC).choose_spec⟩ J hJ⟩

/-- The solver-free master routines match the live, ordered line-1 choice. The target
round need only follow the chain's child at the states whose call is a coset instance. -/
theorem masterChainOpen_match {n B C₀ : ℕ} {W : RawWinSI}
    (hx : W.2.2.2.1.length = n) (hw : RawGens.WF n W.2.1)
    (hnd : W.1.Nodup) (hlt : ∀ u ∈ W.1, u < n)
    (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1))
    (hr : masterReduceRoute B C₀ W = 2) (q : ℕ) (hC : 1 < C₀)
    {N S : Type*} (M : Round N S RawCoset) (e : RawMasterSI → N) (u : RawCoset → S)
    (P : N) (decN : N → SIInstance (Fin n) ℕ)
    (hdec : ∀ V, decN (e V) = decWinSI n V.1)
    (hstop : ∀ j s, masterChainOpenChild (W, j, s) = none → M.child (P, j, u s) = none)
    (hcall : ∀ j s J, masterChainOpenChild (W, j, s) = some J →
      (∃ G : Subgroup (Perm (Fin n)), IsCosetInstance G (decWinSI n J.1)) →
      M.child (P, j, u s) = some (e J))
    (hcomb : ∀ j s a, M.combine (P, j, u s, a) = u (masterChainOpenCombine (W, j, s, a)))
    (hfin : ∀ s, M.finish (P, u s) = masterChainOpenFinish (W, s)) :
    LoopMatch M decN (decCoset n) P (winOrbits (W.2.1, W.1)).length 0
      (u (masterChainOpenInit W)) (masterChainReturnTree hw hnd hlt hinv hr q hC) := by
  refine loopMatch_reparent_onCalls (R := masterChainReturnRound 0 0 (fun _ => none))
    (fun J => e (masterChainOpenRead J)) u (masterChainReturnEnter W) P
    (fun J => ∃ G : Subgroup (Perm (Fin n)), IsCosetInstance G J)
    (fun _ _ J _ _ => (hdec _).trans rfl) ?_ ?_ hcomb hfin _ _ _ _
    (masterChainReturn_match hx hw hnd hlt hinv hr q hC 0 0 (fun _ => none))
    (masterChainReturn_calls_coset hw hnd hlt hinv hr q hC)
  · intro j s hc
    apply hstop
    change (masterChainReturnChild (masterChainReturnEnter W, j, s)).map _ = none
    rw [show masterChainReturnChild (masterChainReturnEnter W, j, s) = none from hc]
    rfl
  · intro j s J hc hV
    apply hcall j s (masterChainOpenRead J) _ hV
    change (masterChainReturnChild (masterChainReturnEnter W, j, s)).map _ = _
    rw [show masterChainReturnChild (masterChainReturnEnter W, j, s) = some J from hc]
    rfl
end Algo
