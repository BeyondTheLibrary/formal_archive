import Workspace.Algo.TopFourLive

/-! # Computing the choices and input of top-action 3
The two alternating generators, kernel orbit order, and odd representative
are read from the actual raw routines. Their specifications supply the
checked tree; no separate choice of these data is used.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Classical

noncomputable def topcsActionOrbits {n m : ℕ} {p : RawAction}
    {ϕ : decGroup n p.1.2 →* Perm (Fin m)} (hp : RawAction.WF n m p ϕ) : OrbitEnum (kerSubgroup ϕ) :=
  topCosetOrbitEnum hp.1 hp.2.1 hp.2.2.2.2

noncomputable def topcsOddChoice {n m : ℕ} {p : RawAction}
    {ϕ : decGroup n p.1.2 →* Perm (Fin m)} (hp : RawAction.WF n m p ϕ) : TopActionOdd ϕ where
  representative := decPerm n ((topOddLift p).getD (rawOne p.1.1))
  spec := by
    intro hodd
    have ho := topOddLift_spec hp.1 hp.2.1 hp.2.2.2.2 hodd
    rw [map_encPerm_decPerm hp.2.2.1, map_encPerm_decPerm hp.2.2.2.1] at ho
    obtain ⟨σ, hσ, he, hs⟩ := ho
    simp only [he, Option.getD_some, decPerm_encPerm]
    exact ⟨hσ, hs⟩

def topcsAutoPrepare (p : RawTop3) : TopcsInput :=
  topcsPrepare (p, topAltGens p.1.2.1, top3Odd p)

theorem polyFun_topcsAutoPrepare : PolyFun topcsAutoPrepare :=
  (polyFun_id.pair
    ((((polyFun_fst.comp polyFun_snd).comp polyFun_fst).comp polyFun_topAltGens).pair polyFun_top3Odd)).comp
      polyFun_topcsPrepare

 theorem topcsPrepare_spec_raw {n m : ℕ} {p : RawAction}
    {ϕ : decGroup n p.1.2 →* Perm (Fin m)} (hp : RawAction.WF n m p ϕ)
    (S : List (alternatingGroup (Fin m))) (O : TopActionOdd ϕ) (x y : Fin n → ℕ) :
    TopcsSpec (topcsPrepare ((p, encStrN x, encStrN y),
      S.map (fun σ : alternatingGroup (Fin m) => encPerm m σ), encPerm n O.representative))
      ϕ S O (topcsActionOrbits hp) x y := by
  have h := topcsPrepare_spec hp.1 hp.2.1 hp.2.2.2.2 S O x y
  simpa only [map_encPerm_decPerm hp.2.2.1, map_encPerm_decPerm hp.2.2.2.1] using h

 theorem topcsAutoPrepare_spec {n m : ℕ} {p : RawAction}
    {ϕ : decGroup n p.1.2 →* Perm (Fin m)} (hp : RawAction.WF n m p ϕ)
    (hm : 3 ≤ m) (x y : RawStr) :
    TopcsSpec (topcsAutoPrepare (p, x, y)) ϕ (topAltGensTyped p.2.1 hp.2.1 hm)
      (topcsOddChoice hp) (topcsActionOrbits hp) (decStrN n x) (decStrN n y) := by
  have h := topcsPrepare_spec_raw hp (topAltGensTyped p.2.1 hp.2.1 hm)
    (topcsOddChoice hp) (decStrN n x) (decStrN n y)
  have hf (z : RawStr) : fixStr (p.1.1, z) = encStrN (decStrN n z) := by
    rw [← decStrN_fixStr hp.1]
    exact (encStrN_decStrN ((length_fixStr _).trans hp.1)).symm
  have he : topcsAutoPrepare (p, x, y) = topcsPrepare ((p, encStrN (decStrN n x), encStrN (decStrN n y)),
      (topAltGensTyped p.2.1 hp.2.1 hm).map (fun σ : alternatingGroup (Fin m) => encPerm m σ),
      encPerm n (topcsOddChoice hp).representative) := by
    simp only [topcsAutoPrepare, topcsPrepare, map_topAltGensTyped, top3Odd,
      topcsOddChoice, hf, decStrN_encStrN, normPerm_eq_enc hp.1, decPerm_encPerm]
  rw [he]
  exact h

 theorem topcsAutoPrepare_uniform_cap (C D : ℕ) : ∃ c d : ℕ, ∀ (n : ℕ) (p : RawTop3),
    Enc.size p ≤ topcsContextCap C D n → Enc.size (topcsAutoPrepare p) ≤ topcsContextCap c d n := by
  obtain ⟨F, hF, hmF, hsF⟩ := polyFun_topcsAutoPrepare.size.exists_polyBound
  obtain ⟨c, d, hcd⟩ := hF.comp (polyBound_topcsContextCap C D)
  exact ⟨c, d, fun n p hp => (hsF p).trans ((hmF _ _ hp).trans (hcd n))⟩

end Algo
