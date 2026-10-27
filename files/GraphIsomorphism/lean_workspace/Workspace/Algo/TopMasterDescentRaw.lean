import Workspace.Algo.TopMasterHintRebase
import Workspace.Algo.Descent

/-! # Luks descent through a supplied action
The subgroup is the action kernel. The count is computed as the order of
the stored image group, and each representative is read in binary from
the action's stabilizer chain. Children retain the original window and
strings, with the candidate cosets of Equation (62).
-/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Pointwise

abbrev MasterDescInput := RawWinSI × (List ℕ × RawGens)

def masterDescAction (p : MasterDescInput) : RawAction :=
  ((p.1.2.2.2.1, p.1.2.1), p.2)
def masterDescWidth (p : MasterDescInput) : ℕ := rawOrder p.2

def masterDescRep (p : MasterDescInput × ℕ) : RawPerm :=
  rawMul (normPerm (p.1.1.2.2.2.1, p.1.1.2.2.1),
    normPerm (p.1.1.2.2.2.1, actCosetRep (masterDescAction p.1, p.2)))

def masterDescJob (p : MasterDescInput × ℕ) : RawWinSI :=
  (p.1.1.1, topKernel (masterDescAction p.1), masterDescRep p,
    p.1.1.2.2.2.1, p.1.1.2.2.2.2)

def masterDescJoin (p : RawStr × RawCoset × RawCoset) : RawCoset :=
  top2NormC p.1 (rawCosetJoin p)

theorem polyFun_masterDescAction : PolyFun masterDescAction :=
  (((((polyFun_fst.comp polyFun_snd).comp polyFun_snd).comp polyFun_snd).comp polyFun_fst).pair
    ((polyFun_fst.comp polyFun_snd).comp polyFun_fst)).pair polyFun_snd

theorem polyFun_masterDescWidth : PolyFun masterDescWidth := polyFun_snd.comp polyFun_rawOrder

theorem polyFun_masterDescRep : PolyFun masterDescRep := by
  have hw : PolyFun (fun p : MasterDescInput × ℕ => p.1.1) := polyFun_fst.comp polyFun_fst
  have hx := (((hw.comp polyFun_snd).comp polyFun_snd).comp polyFun_snd).comp polyFun_fst
  have hr := ((hw.comp polyFun_snd).comp polyFun_snd).comp polyFun_fst
  have hrep := ((polyFun_fst.comp polyFun_masterDescAction).pair polyFun_snd).comp polyFun_actCosetRep
  exact (((hx.pair hr).comp polyFun_normPerm).pair ((hx.pair hrep).comp polyFun_normPerm)).comp
    polyFun_rawMul

theorem polyFun_masterDescJob : PolyFun masterDescJob := by
  have hw : PolyFun (fun p : MasterDescInput × ℕ => p.1.1) := polyFun_fst.comp polyFun_fst
  have hxy := ((hw.comp polyFun_snd).comp polyFun_snd).comp polyFun_snd
  exact (hw.comp polyFun_fst).pair
    (((polyFun_fst.comp polyFun_masterDescAction).comp polyFun_topKernel).pair
      (polyFun_masterDescRep.pair hxy))

theorem polyFun_masterDescJoin : PolyFun masterDescJoin :=
  (polyFun_fst.pair polyFun_rawCosetJoin).comp polyFun_top2NormC

section Spec
variable {n m : ℕ} {p : MasterDescInput}
  {ϕ : decGroup n p.1.2.1 →* Perm (Fin m)}
  (hp : RawAction.WF n m (masterDescAction p) ϕ)

include hp in
theorem masterDescWidth_spec : masterDescWidth p = Nat.card ϕ.range := by
  have h := rawOrder_spec p.2.1 hp.2.1 (p.2.2.map (decPerm m))
  rw [map_encPerm_decPerm (show RawGens.WF m p.2.2 from hp.2.2.2.1)] at h
  exact h.trans (congrArg (fun H : Subgroup (Perm (Fin m)) => Nat.card H) hp.2.2.2.2.range_eq_genGroup.symm)

include hp in
theorem masterDescRep_spec (j : ℕ) :
    decPerm n (masterDescRep (p, j)) = decPerm n p.1.2.2.1 *
      decPerm n (actCosetRep (masterDescAction p, j)) := by
  have hx : p.1.2.2.2.1.length = n := hp.1
  simp only [masterDescRep, rawMul_of_wf (wf_normPerm hx _) (wf_normPerm hx _),
    decPerm_encPerm, decPerm_normPerm hx]

include hp in
theorem masterDescKernel_spec : decGroup n (topKernel (masterDescAction p)) = kerSubgroup ϕ := by
  have h := decGroup_topKernel hp.1 hp.2.1 hp.2.2.2.2
  simpa only [map_encPerm_decPerm hp.2.2.1, map_encPerm_decPerm hp.2.2.2.1] using h

noncomputable def masterDescPerms (n : ℕ) (p : MasterDescInput) : List (Perm (Fin n)) :=
  (List.range (masterDescWidth p)).map (fun j => decPerm n (masterDescRep (p, j)))

include hp in
theorem masterDesc_cover : (decWinSI n p.1).K = ⋃ σ ∈ masterDescPerms n p,
    σ • (decGroup n (topKernel (masterDescAction p)) : Set (Perm (Fin n))) := by
  have hc := cover_actCosetRep hp.1 hp.2.1 hp.2.2.2.2
  have hi := actCosetIndex_eq_card_range hp.1 hp.2.1 hp.2.2.2.2
  rw [map_encPerm_decPerm hp.2.2.1, map_encPerm_decPerm hp.2.2.2.1] at hc
  have hw : actCosetIndex n m p.1.2.2.2.1 p.2.1 (p.1.2.1.map (decPerm n))
      (p.2.2.map (decPerm m)) = masterDescWidth p := hi.trans (masterDescWidth_spec hp).symm
  have hl : masterDescPerms n p = (List.range (masterDescWidth p)).map
      (fun j => decPerm n p.1.2.2.1 * decPerm n (actCosetRep (masterDescAction p, j))) :=
    List.map_congr_left (fun j _ => masterDescRep_spec hp j)
  rw [show (decWinSI n p.1).K = decPerm n p.1.2.2.1 •
    (decGroup n p.1.2.1 : Set (Perm (Fin n))) from decCoset_some _ _ _]
  rw [hl, masterDescKernel_spec hp]
  change _ = ⋃ σ ∈ _, σ • (actKer (p.1.2.1.map (decPerm n)) ϕ : Set (Perm (Fin n)))
  rw [← smul_biUnion_index]
  apply congrArg (fun S : Set (Perm (Fin n)) => decPerm n p.1.2.2.1 • S)
  simpa only [masterDescAction, hw] using hc

/-- The exact raw job is the corresponding candidate coset in Equation (62). -/
theorem masterDescJob_spec (j : ℕ) : decWinSI n (masterDescJob (p, j)) =
    ⟨decPerm n (masterDescRep (p, j)) •
      (decGroup n (topKernel (masterDescAction p)) : Set (Perm (Fin n))),
      (decWinSI n p.1).Δ, (decWinSI n p.1).x, (decWinSI n p.1).y⟩ := by
  simp only [decWinSI, masterDescJob, decCoset_some]

noncomputable def masterDescTree (n : ℕ) (p : MasterDescInput) :
    SIReduction (Fin n) ℕ (Set (Perm (Fin n))) :=
  descentChain (decGroup n (topKernel (masterDescAction p))) (decWinSI n p.1).Δ
    (decWinSI n p.1).x (decWinSI n p.1).y ∅ (masterDescPerms n p)

include hp in
theorem masterDescTree_spec (hinv : IsInvariant (decGroup n p.1.2.1) (winSet n p.1.1)) :
    (masterDescTree n p).run = (decWinSI n p.1).answer := by
  apply run_descentChain _ _ _ _ _ _ (masterDesc_cover hp)
  intro τ hτ
  refine ⟨wAutSubgroup (decGroup n p.1.2.1) (winSet n p.1.1) hinv (decStrN n p.1.2.2.2.1), ?_⟩
  simp only [decWinSI, decCoset_some] at hτ ⊢
  exact wIso_eq_smul_wAut hinv (decPerm n p.1.2.2.1) hτ
end Spec
end Algo
