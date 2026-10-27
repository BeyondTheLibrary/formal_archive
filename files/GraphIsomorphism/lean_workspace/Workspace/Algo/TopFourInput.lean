import Workspace.Algo.TopFourWindowAuto
import Workspace.Algo.OmegaCutRaw

/-! # Preparing the top-action 4 input from the original action
The first window is Ω(C). The remaining windows are Ω₀ through Ωₜ₋₁,
with t read from the computed label of point zero. The target is aligned
before restriction, as in Corollary 12.0.10.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Classical

/-- The remaining windows in the paper's order. -/
def top4Rest (p : RawAction × List ℕ) : List (List ℕ) :=
  rawOmegaCuts (p, rawTpoint (p.1, 0))

theorem polyFun_top4Rest : PolyFun top4Rest :=
  (polyFun_id.pair ((polyFun_fst.pair (polyFun_const 0)).comp polyFun_rawTpoint)).comp polyFun_rawOmegaCuts

 theorem top4Rest_spec {n m : ℕ} {dom gdom : List ℕ} {gens : List (Perm (Fin n))}
    {imgs : List (Perm (Fin m))} {ϕ : genGroup gens →* Perm (Fin m)}
    (hd : dom.length = n) (hg : gdom.length = m) (hI : ImgsOf gens imgs ϕ)
    (hG : IsTransitive (genGroup gens)) (hϕ : IsGiantRep ϕ)
    (hk : VeryLargeK m (maxOrbitLength (genGroup gens))) (C : List ℕ) :
    (top4Rest (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), C)).map (winSet n) =
      (List.range (tOf hG ϕ)).map (omegaCut ϕ (winSet m C)) := by
  have hn : 0 < n := by
    obtain ⟨u⟩ := hG.nonempty
    exact lt_of_le_of_lt (Nat.zero_le u.val) u.isLt
  let p : RawAction := ((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m)))
  have hb : ∀ j ∈ rawTpoint (p, 0), j < m := fun j hj =>
    ((mem_rawTpoint_iff hd hg hI hϕ hk ⟨0, hn⟩ j).mp hj).1
  have hl : (rawTpoint (p, 0)).length = tOf hG ϕ := by
    rw [← ncard_winSet _ (nodup_rawTpoint _) hb, winSet_rawTpoint hd hg hI hϕ hk ⟨0, hn⟩]
    exact tPoint_eq_tOf hG ϕ hϕ hk ⟨0, hn⟩
  rw [top4Rest, map_winSet_rawOmegaCuts hd hg hI hϕ hk C, hl]

/-- Original action and strings, source color class, aligning element,
and target color class. -/
abbrev Top4Input := (RawTop3 × List ℕ) × RawPerm × List ℕ

def top4InputContext (q : Top4Input) : Top4Context :=
  let p := q.1.1
  let C := q.1.2
  let y := top4aTarget (p.1.1.1, q.2.1, p.2.2)
  top4WindowContext (((topRAction (p.1, C), p.2.1, y), top4Omega (p.1, C)), top4Rest (p.1, C))

def top4InputEnter (q : Top4Input) : Top4aNode :=
  top4aEnter (top4InputContext q, q.2.1, q.1.2, q.2.2)

 theorem polyFun_top4InputContext : PolyFun top4InputContext := by
  have hp : PolyFun (fun q : Top4Input => q.1.1) := polyFun_fst.comp polyFun_fst
  have ha := hp.comp polyFun_fst
  have hxy := hp.comp polyFun_snd
  have hC : PolyFun (fun q : Top4Input => q.1.2) := polyFun_fst.comp polyFun_snd
  have hc := ha.pair hC
  have hy := ((((ha.comp polyFun_fst).comp polyFun_fst).pair
    ((polyFun_snd.comp polyFun_fst).pair (hxy.comp polyFun_snd))).comp polyFun_top4aTarget)
  exact ((((hc.comp polyFun_topRAction).pair ((hxy.comp polyFun_fst).pair hy)).pair
    (hc.comp polyFun_top4Omega)).pair (hc.comp polyFun_top4Rest)).comp polyFun_top4WindowContext

 theorem polyFun_top4InputEnter : PolyFun top4InputEnter :=
  (polyFun_top4InputContext.pair ((polyFun_snd.comp polyFun_fst).pair
    ((polyFun_fst.comp polyFun_snd).pair (polyFun_snd.comp polyFun_snd)))).comp polyFun_top4aEnter

 theorem top4InputContext_uniform_cap (C D : ℕ) : ∃ c d : ℕ, ∀ (n : ℕ) (p : Top4Input),
    Enc.size p ≤ topcsContextCap C D n → Enc.size (top4InputContext p) ≤ topcsContextCap c d n := by
  obtain ⟨F, hF, hmF, hsF⟩ := polyFun_top4InputContext.size.exists_polyBound
  obtain ⟨c, d, hcd⟩ := hF.comp (polyBound_topcsContextCap C D)
  exact ⟨c, d, fun n p hp => (hsF p).trans ((hmF _ _ hp).trans (hcd n))⟩

/-- The list's numbering supplies the color labels in the live data record. -/
noncomputable def top4ClassLabel {m : ℕ} (C : List ℕ) (hnd : C.Nodup) (hlt : ∀ u ∈ C, u < m) :
    winSet m C ≃ Fin (winSet m C).ncard :=
  (winEquiv m C hnd hlt).symm.trans (finCongr (ncard_winSet C hnd hlt).symm)

end Algo
