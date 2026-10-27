import Workspace.Algo.TopFourAlignData

/-! # Lifting the computed color-class alignment
The lift is a source-group element whenever it is returned. If the two
class sizes agree, the even target isomorphism lies in the giant image,
so the lift exists. The identity fills the unused rejecting branch.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Classical

def top4AlignLift (p : RawAction × List ℕ × List ℕ) : Option RawPerm :=
  (top4ClassMap (p.1.2.1, p.2.1, p.2.2)).bind (fun r => actPreimage (p.1, r))

def top4AlignElement (p : RawAction × List ℕ × List ℕ) : RawPerm :=
  (top4AlignLift p).getD (rawOne p.1.1.1)

 theorem polyFun_top4AlignLift : PolyFun top4AlignLift := by
  have ht : PolyFun (fun p : RawAction × List ℕ × List ℕ => top4ClassMap (p.1.2.1, p.2.1, p.2.2)) :=
    ((((polyFun_fst.comp polyFun_snd).comp polyFun_fst).pair polyFun_snd).comp polyFun_top4ClassMap)
  exact ((ht.pair polyFun_fst).comp
    (PolyFun.optionElim (polyFun_const none) ((polyFun_snd.pair polyFun_fst).comp polyFun_actPreimage))).of_eq
      (fun p => by unfold top4AlignLift; cases top4ClassMap (p.1.2.1, p.2.1, p.2.2) <;> rfl)

 theorem polyFun_top4AlignElement : PolyFun top4AlignElement :=
  (polyFun_top4AlignLift.pair (((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_rawOne)).comp
    polyFun_optionGetD

section Encoded
variable {n m : ℕ} {dom gdom C D : List ℕ} {gens : List (Perm (Fin n))}
    {imgs : List (Perm (Fin m))} {ϕ : genGroup gens →* Perm (Fin m)}
    (hd : dom.length = n) (hg : gdom.length = m) (hI : ImgsOf gens imgs ϕ)
include hd hg hI

 theorem top4AlignLift_some {a : RawPerm}
    (ha : top4AlignLift (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), C, D) = some a) :
    RawPerm.WF n a ∧ ∃ h : decPerm n a ∈ genGroup gens,
      ϕ ⟨decPerm n a, h⟩ '' winSet m C = winSet m D := by
  obtain ⟨r, hr, hl⟩ := Option.bind_eq_some_iff.mp ha
  have hs := top4ClassMap_some hg hr
  have hl' : actPreimage (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), encPerm m (decPerm m r)) = some a := by
    rwa [encPerm_decPerm hs.1]
  obtain ⟨σ, hσ, he, himg⟩ := actPreimage_eq_some hd hg hI (decPerm m r) hl'
  rw [he, decPerm_encPerm]
  exact ⟨wf_encPerm _ _, hσ, by rw [himg]; exact hs.2.2⟩

 theorem top4AlignLift_ne_none (hϕ : IsGiantRep ϕ) (hm : 3 ≤ m)
    (hc : (winSet m C).ncard = (winSet m D).ncard) :
    top4AlignLift (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), C, D) ≠ none := by
  obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.mp (top4ClassMap_ne_none hg hm hc)
  have hs := top4ClassMap_some hg hr
  intro hn
  rw [top4AlignLift, hr, Option.bind_some] at hn
  have he : encPerm m (decPerm m r) = r := encPerm_decPerm hs.1
  have hn' : actPreimage (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), encPerm m (decPerm m r)) = none := by
    rwa [he]
  exact ((actPreimage_eq_none_iff hd hg hI (decPerm m r)).mp hn') (hϕ hs.2.1)

 theorem top4AlignElement_mem :
    decPerm n (top4AlignElement (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), C, D)) ∈ genGroup gens := by
  cases h : top4AlignLift (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), C, D) with
  | none =>
    simp only [top4AlignElement, h, Option.getD_none, rawOne_eq]
    rw [hd, decPerm_encPerm]
    exact (genGroup gens).one_mem
  | some a =>
    simpa only [top4AlignElement, h, Option.getD_some] using (top4AlignLift_some hd hg hI h).2.choose

 theorem top4AlignElement_spec (hϕ : IsGiantRep ϕ) (hm : 3 ≤ m)
    (hc : (winSet m C).ncard = (winSet m D).ncard) :
    ϕ ⟨decPerm n (top4AlignElement (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), C, D)),
      top4AlignElement_mem hd hg hI⟩ '' winSet m C = winSet m D := by
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp (top4AlignLift_ne_none hd hg hI hϕ hm hc)
  have hs := (top4AlignLift_some hd hg hI ha).2.choose_spec
  simpa only [top4AlignElement, ha, Option.getD_some] using hs

end Encoded
end Algo
