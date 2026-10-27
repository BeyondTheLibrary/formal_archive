import Workspace.Algo.AggNodePairMatch

/-! # Opening one comparison from the aggregate context -/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Pointwise

/-- Action, source string, target string, source test set, target test set. -/
abbrev AggnPairRequest := RawAction × RawStr × RawStr × List ℕ × List ℕ

def aggnPairPrepare (z : AggnPairRequest) : AggnPairCtx :=
  (((z.2.1, z.2.2.2.1), aggnInitialState (z.1, z.2.2.2.1)), z.2.2.1,
    (aggnTransport (z.1, z.2.2.2)).map (fun r => (topStab (z.1, z.2.2.2.1), r)))

theorem aggnPolyFun_pairPrepare : PolyFun aggnPairPrepare := by
  have hA : PolyFun (fun z : AggnPairRequest => z.1) := polyFun_fst
  have hx : PolyFun (fun z : AggnPairRequest => z.2.1) := polyFun_snd.comp polyFun_fst
  have hy : PolyFun (fun z : AggnPairRequest => z.2.2.1) := (polyFun_snd.comp polyFun_snd).comp polyFun_fst
  have hrows : PolyFun (fun z : AggnPairRequest => z.2.2.2) := (polyFun_snd.comp polyFun_snd).comp polyFun_snd
  have hrow := hrows.comp polyFun_fst
  have hg := (hA.pair hrow).comp polyFun_topStab
  have ht := (hA.pair hrows).comp aggnPolyFun_transport
  have hq : PolyFun (fun z : AggnPairRequest =>
      (aggnTransport (z.1, z.2.2.2)).map (fun r => (topStab (z.1, z.2.2.2.1), r))) := by
    exact ((ht.pair hg).comp (PolyFun.optionElim (polyFun_const none)
      ((polyFun_snd.pair polyFun_fst).comp polyFun_some))).of_eq
      (fun z => by cases aggnTransport (z.1, z.2.2.2) <;> rfl)
  exact ((hx.pair hrow).pair ((hA.pair hrow).comp aggnPolyFun_initialState)).pair (hy.pair hq)

/-- The executable initial transporter and paired loop give the exact
`compareStrong` tree for the fixed mathematical choices. -/
theorem aggnPairPrepare_phase {n m : ℕ} {A : RawAction} {xs ys row row' : List ℕ}
    {ϕ : decGroup n A.1.2 →* Perm (Fin m)}
    (c : ℕ) (solve : RawWinSI → RawCoset) (hc : LCCtxWF n m xs row)
    (hA : RawAction.WF n m A ϕ) (hg : IsGiantRep ϕ)
    (hr' : row'.Nodup) (hlt' : ∀ u ∈ row', u < m) (hlen : row.length = row'.length)
    (h2 : 2 ≤ row.length) (hguard : row.length ≤ guardBound c xs.length) (hs : row.SortedLE) :
    let C := aggnPairPrepare (A, xs, ys, row, row')
    PhaseMatch (aggnPairRound c n solve) (aggnPairDecode n) (decCoset n) (C, none)
      (2 * n * (Nat.factorial row.length * n)) 0 (aggnPairStart c C.1 C.2.1 C.2.2 none)
      (compareStrong ϕ (decStrN n xs) (winSet m row) (decStrN n ys)
        (aggnCanonTransport ϕ (winSet m row) (winSet m row'))
        (aggnCanonicalPair ϕ (decStrN n xs) (decStrN n ys) (winSet m row)
          ((aggnCanonTransport ϕ (winSet m row) (winSet m row')).getD 1)))
      (fun B j v => decCoset n v.2.1 = B ∧ aggnPairActive v = false ∧
        j ≤ 2 * n * (Nat.factorial row.length * n)) := by
  classical
  dsimp only
  obtain ⟨r, hr, hw, hm⟩ := aggnTransport_spec hA hg hc.nodup hr' hc.ltM hlt' hlen h2
  have hne : (AggnTransportSet ϕ (winSet m row) (winSet m row')).Nonempty := ⟨_, hm.1⟩
  have ht : aggnCanonTransport ϕ (winSet m row) (winSet m row') = some (decPerm n r) := by
    rw [aggnCanonTransport, if_pos hne, aggnLeastPerm_eq hm]
  obtain ⟨hσ, hmap⟩ := hm.1
  have hQ : decCoset n (some (topStab (A, row), r)) =
      decPerm n r • (bigGT ϕ (winSet m row) : Set (Perm (Fin n))) := by
    rw [decCoset_some, topStab_bigGT_of_wf (A, row) ϕ hA hg]
  have hinit := aggnInitialState_for hc hA hg
  have hphase := aggnPairPhase_run (ys := ys) c solve hinit hguard hs hσ hQ
  rw [ht, compareStrong]
  simpa only [Option.getD_some, aggnPairPrepare, hr, Option.map_some] using hphase

end Algo
