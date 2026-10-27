import Workspace.Algo.TopWindowPrepared

/-! # Computing the complete window-phase input
The restricted action, strings, alternating pair, odd representative, and
kernel windows are all computed here. The phase matcher uses their actual
outputs. The only action hypothesis is the factorization through the window
proved for Ω(C) in `TopFourAction`.
-/
set_option maxHeartbeats 1000000
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Classical

 theorem topwRestrictStr_decode {n : ℕ} {Δ : List ℕ} (hnd : Δ.Nodup)
    (hlt : ∀ u ∈ Δ, u < n) (x : RawStr) :
    decStrN Δ.length (rawRestrictStr (x, Δ)) = fun i => decStrN n x (winEquiv n Δ hnd hlt i) := by
  funext i
  change (rawRestrictStr (x, Δ)).getD i.val 0 = _
  rw [List.getD_eq_getElem _ _ (by simpa only [length_rawRestrictStr] using i.isLt)]
  simp only [rawRestrictStr, List.getElem_map, decStrN, winEquiv_coe Δ hnd hlt i.isLt]
  rfl

abbrev Top4WindowInput := (RawTop3 × List ℕ) × List (List ℕ)

def top4WindowContext (q : Top4WindowInput) : Top4Context :=
  let p := q.1.1.1
  let Δ := q.1.2
  let x := fixStr (p.1.1, q.1.1.2.1)
  let y := fixStr (p.1.1, q.1.1.2.2)
  let P := topcsAutoPrepare (topwAction (p, Δ), rawRestrictStr (x, Δ), rawRestrictStr (y, Δ))
  (((p.1, Δ, x), P), q.2, y)

 theorem polyFun_top4WindowContext : PolyFun top4WindowContext := by
  have hp : PolyFun (fun q : Top4WindowInput => q.1.1.1) := (polyFun_fst.comp polyFun_fst).comp polyFun_fst
  have hΔ : PolyFun (fun q : Top4WindowInput => q.1.2) := polyFun_fst.comp polyFun_snd
  have hd := (hp.comp polyFun_fst).comp polyFun_fst
  have hxy : PolyFun (fun q : Top4WindowInput => q.1.1.2) := (polyFun_fst.comp polyFun_fst).comp polyFun_snd
  have hx := (hd.pair (hxy.comp polyFun_fst)).comp polyFun_fixStr
  have hy := (hd.pair (hxy.comp polyFun_snd)).comp polyFun_fixStr
  have ha := (hp.pair hΔ).comp polyFun_topwAction
  have hi := (ha.pair (((hx.pair hΔ).comp polyFun_rawRestrictStr).pair
    ((hy.pair hΔ).comp polyFun_rawRestrictStr))).comp polyFun_topcsAutoPrepare
  exact ((((hp.comp polyFun_fst).pair (hΔ.pair hx)).pair hi).pair (polyFun_snd.pair hy))

 theorem top4WindowContext_loop {n m c d e f : ℕ} {p : RawAction}
    {ψ : decGroup n p.1.2 →* Perm (Fin m)} (hp : RawAction.WF n m p ψ)
    {Δ : List ℕ} (hnd : Δ.Nodup) (hlt : ∀ u ∈ Δ, u < n)
    (hinv : IsInvariant (decGroup n p.1.2) (winSet n Δ))
    (ϕ : restrictTo (decGroup n p.1.2) (winSet n Δ) hinv →* Perm (Fin m))
    (hfactor : ∀ g : decGroup n p.1.2, ψ g = ϕ ⟨restrictHom (decGroup n p.1.2) (winSet n Δ) hinv g, ⟨g, rfl⟩⟩)
    (hϕ : IsGiantRep ϕ) (hm : 3 ≤ m) (hpos : 0 < Δ.length)
    (hcap : TopwpCap e f) (x y : RawStr) (rest : List (List ℕ)) (solve : RawWinSI → RawCoset) :
    let hw := topwAction_WF_exact hp hnd hlt hinv ϕ hfactor
    let Q := topwPreparedCompat hp.2.2.1 hnd hlt hinv ϕ
    let O := Q.odd (topcsOddChoice hw)
    let E := Q.orbits (topcsActionOrbits hw)
    let C := top4WindowContext (((p, x, y), Δ), rest)
    LoopMatch (top4Round c d e f solve) (top4Decode n) (decCoset n) (C, none)
      (top4Width C) 0 (top4Init (C, none))
      (top4LiveBody hnd hlt hinv ϕ (topAltGensTyped p.2.1 hp.2.1 hm) O E
        (decStrN n x) (decStrN n y) (rest.map (winSet n))) := by
  intro hw Q O E C
  let x' := fixStr (p.1.1, x)
  let y' := fixStr (p.1.1, y)
  have hP := (topcsAutoPrepare_spec hw hm (rawRestrictStr (x', Δ)) (rawRestrictStr (y', Δ))).sameDomain Q
  rw [topwRestrictStr_decode hnd hlt, topwRestrictStr_decode hnd hlt] at hP
  have hh := top4LiveLoopMatch (c := c) (d := d) (rest := rest) hp.1
    ((length_fixStr _).trans hp.1) hnd hlt hinv hcap ϕ
    (topAltGensTyped p.2.1 hp.2.1 hm) O E hP hpos hϕ
    (topAltGensTyped_spec p.2.1 hp.2.1 hm).2 solve
  simpa only [top4WindowContext, x', y', map_encPerm_decPerm hp.2.2.1, decStrN_fixStr hp.1] using hh

 theorem top4WindowContext_uniform_cap (C D : ℕ) : ∃ c d : ℕ, ∀ (n : ℕ) (p : Top4WindowInput),
    Enc.size p ≤ topcsContextCap C D n → Enc.size (top4WindowContext p) ≤ topcsContextCap c d n := by
  obtain ⟨F, hF, hmF, hsF⟩ := polyFun_top4WindowContext.size.exists_polyBound
  obtain ⟨c, d, hcd⟩ := hF.comp (polyBound_topcsContextCap C D)
  exact ⟨c, d, fun n p hp => (hsF p).trans ((hmF _ _ hp).trans (hcd n))⟩

end Algo
