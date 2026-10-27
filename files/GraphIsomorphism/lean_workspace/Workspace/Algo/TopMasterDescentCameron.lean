import Workspace.Algo.TopMasterDescentMatch

/-! # The Cameron subgroup enters the action descent carrier
The computed signed-coordinate action determines both the subgroup and
the number of cosets. Its index bound is the multiplicative cost of
Theorem 11.2.1, now applied to the actual ordered raw phase.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv

theorem masterKernel_index {Ω H : Type*} [Group H] {G : Subgroup (Perm Ω)} (ϕ : G →* H) :
    (kerSubgroup ϕ).relIndex G = Nat.card ϕ.range := by
  have hsub : (kerSubgroup ϕ).subgroupOf G = ϕ.ker := by
    rw [kerSubgroup, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective G)]
  rw [Subgroup.relIndex, hsub, Subgroup.index]
  exact Nat.card_congr (QuotientGroup.quotientKerEquivRange ϕ).toEquiv

theorem masterDescWidth_index {n m : ℕ} {p : MasterDescInput}
    {ϕ : decGroup n p.1.2.1 →* Perm (Fin m)} (hp : RawAction.WF n m (masterDescAction p) ϕ) :
    masterDescWidth p = (decGroup n (topKernel (masterDescAction p))).relIndex (decGroup n p.1.2.1) := by
  rw [masterDescKernel_spec hp, masterKernel_index]
  exact masterDescWidth_spec hp

def masterCameronDescInput (p : RawCameron × MasterDescInput) : MasterDescInput :=
  (p.2.1, (camLiftSign (p.1, masterDescAction p.2)).2)

theorem polyFun_masterCameronDescInput : PolyFun masterCameronDescInput :=
  (polyFun_snd.comp polyFun_fst).pair
    (((polyFun_fst.pair (polyFun_snd.comp polyFun_masterDescAction)).comp polyFun_camLiftSign).comp
      polyFun_snd)

section Cameron
variable {n m : ℕ} {p : MasterDescInput} {c : RawCameron}
  {ϕ : decGroup n p.1.2.1 →* Perm (Fin m)}
  (hp : RawAction.WF n m (masterDescAction p) ϕ) (h : c.WF m)
  (hhi : (decGroup m p.2.2).map (permCongrHom (decCameron c h)).toMonoidHom ≤
    wreathProduct (JohnsonS c.k c.t) c.s)

theorem masterCameronDesc_wf : RawAction.WF n (c.s * 2)
    (masterDescAction (masterCameronDescInput (c, p)))
      (camLiftSignHom (p := masterDescAction p) hp h hhi) := camLiftSign_wf hp h hhi

include hp hhi in
theorem masterCameronDesc_width : masterDescWidth (masterCameronDescInput (c, p)) =
    (camNbar c h).relIndex (decGroup m p.2.2) :=
  (masterDescWidth_index (masterCameronDesc_wf hp h hhi)).trans (camLiftGens_index hp h hhi)

/-- The actual source generators in every displayed recursive job are `G₁`. -/
theorem masterCameronDesc_job (j : ℕ) :
    (masterDescJob (masterCameronDescInput (c, p), j)).2.1 =
      camLiftGens (c, masterDescAction p) := rfl

include hp hhi in
theorem masterCameronDesc_calls
    (hidx : (camNbar c h).relIndex (decGroup m p.2.2) ≤ m) :
    (masterDescTree n (masterCameronDescInput (c, p))).calls.length ≤ m := by
  rw [masterDescTree_calls, masterCameronDesc_width hp h hhi]
  exact hidx

include hp hhi in
theorem masterCameronDesc_enter_wf {a b : ℕ}
    (hs : Enc.size (masterCameronDescInput (c, p)) ≤ topcsContextCap a b (masterDescX p).length)
    (hidx : (camNbar c h).relIndex (decGroup m p.2.2) ≤ m) (hm : m ≤ n) :
    MasterDescWF a b 1 1 (masterDescEnter (masterCameronDescInput (c, p))) := by
  apply masterDescEnter_wf hs
  have hw := (masterCameronDesc_width hp h hhi).le.trans hidx |>.trans hm
  change masterDescWidth _ ≤ 1 * ((masterDescX p).length + 1) ^ 1
  have hx : (masterDescX p).length = n := hp.1
  rw [hx]
  simpa using hw.trans (Nat.le_succ n)

end Cameron
end Algo
