import Workspace.Algo.TopFourAmbientCost

/-! # Preparing and checking the outer top-action entry
The outer context fixes the ambient group, the ordered window, and the
reference source. Its size is charged to the original domain.
-/
set_option synthInstance.maxSize 4096
namespace Algo
open RAM RAM.Targets Babai Equiv

abbrev Top4wInput := TopwContext × Top4AutoInput
def top4wContext (p : Top4wInput) : Top4wContext := (p.1, top4AutoEnter p.2)
def top4wEnter (p : Top4wInput) : Top4wNode := (top4wContext p, none)

theorem polyFun_top4wContext : PolyFun top4wContext :=
  polyFun_fst.pair (polyFun_snd.comp polyFun_top4AutoEnter)
theorem polyFun_top4wEnter : PolyFun top4wEnter :=
  polyFun_top4wContext.pair (polyFun_const none)

theorem top4wEnter_uniform_wf (A B c d e f u v : ℕ) : ∃ a b : ℕ,
    ∀ (n : ℕ) (p : Top4wInput), p.1.2.2.length = n →
      Enc.size p ≤ topcsContextCap A B n → Top4wWF a b c d e f u v (top4wEnter p) := by
  obtain ⟨F, hF, hmF, hsF⟩ := polyFun_top4wContext.size.exists_polyBound
  obtain ⟨a, b, hab⟩ := hF.comp (polyBound_topcsContextCap A B)
  refine ⟨a, b, fun n p hn hp => ⟨?_, by simp [top4wEnter]⟩⟩
  change Enc.size (top4wContext p) ≤ topcsContextCap a b p.1.2.2.length
  rw [hn]
  exact (hsF p).trans ((hmF _ _ hp).trans (hab n))

theorem Top4Source.autoTree_calls_K {k m : ℕ} (F : Top4Source k m)
    {κ : Type*} (hm : HugeM m (Nat.card (Fin k))) (x y : RawStr) (Cy : List ℕ)
    (col : (Fin k → ℕ) → Fin m → κ) (color : κ)
    (hCx : colorClass col (decStrN k x) color = winSet m F.color)
    (hCy : colorClass col (decStrN k y) color = winSet m Cy) :
    ∀ J ∈ (F.autoTree hm x y Cy col color hCx hCy).calls,
      J.K ⊆ (genGroup F.gens : Set (Perm (Fin k))) := by
  intro J hJ
  exact (isCosetInstance_calls_cosetTopAction4With F.transitive F.hom F.giant hm
    col color (decStrN k x) (decStrN k y) _ _ _ J hJ).K_subset

/-- Every call of the supplied top-action tree is a coset instance for the generated group. -/
theorem Top4Source.autoTree_calls_coset {k m : ℕ} (F : Top4Source k m)
    {κ : Type*} (hm : HugeM m (Nat.card (Fin k))) (x y : RawStr) (Cy : List ℕ)
    (col : (Fin k → ℕ) → Fin m → κ) (color : κ)
    (hCx : colorClass col (decStrN k x) color = winSet m F.color)
    (hCy : colorClass col (decStrN k y) color = winSet m Cy) :
    ∀ J ∈ (F.autoTree hm x y Cy col color hCx hCy).calls, IsCosetInstance (genGroup F.gens) J :=
  fun J hJ => isCosetInstance_calls_cosetTopAction4With F.transitive F.hom F.giant hm
    col color (decStrN k x) (decStrN k y) _ _ _ J hJ

theorem top4wTree_calls {n : ℕ} {Δ : List ℕ} (hnd : Δ.Nodup)
    (hlt : ∀ u ∈ Δ, u < n) {G : Subgroup (Perm (Fin n))}
    (hinv : IsInvariant G (winSet n Δ)) (x : Fin n → ℕ)
    (T : SIReduction (Fin Δ.length) ℕ (Set (Perm (Fin Δ.length))))
    (hT : ∀ J ∈ T.calls, J.K ⊆ ((winRestrictHom n Δ hnd hlt G hinv).range : Set (Perm (Fin Δ.length)))) :
    (top4wTree Δ hnd hlt G hinv x T).calls = T.calls.map (topwInstance Δ hnd hlt G hinv x) := by
  rw [top4wTree, SIReduction.calls_bind, SIReduction.calls_done, List.append_nil,
    calls_topwReduction hnd hlt hinv x T hT]

theorem top4wTree_run {n : ℕ} {Δ : List ℕ} (hnd : Δ.Nodup)
    (hlt : ∀ u ∈ Δ, u < n) {G : Subgroup (Perm (Fin n))}
    (hinv : IsInvariant G (winSet n Δ)) (x : Fin n → ℕ)
    (T : SIReduction (Fin Δ.length) ℕ (Set (Perm (Fin Δ.length))))
    (hT : ∀ J ∈ T.calls, J.K ⊆ ((winRestrictHom n Δ hnd hlt G hinv).range : Set (Perm (Fin Δ.length)))) :
    (top4wTree Δ hnd hlt G hinv x T).run = topwPreimageSet Δ hnd hlt G hinv T.run := by
  rw [top4wTree, SIReduction.run_bind, SIReduction.run_done, run_topwReduction hnd hlt hinv x T hT]

theorem top4wSource_loop {n m a b c d e f u v : ℕ} {dom Δ x : List ℕ}
    {gens : List (Perm (Fin n))} (hd : dom.length = n) (hx : x.length = n)
    (hnd : Δ.Nodup) (hlt : ∀ i ∈ Δ, i < n) (hinv : IsInvariant (genGroup gens) (winSet n Δ))
    (F : Top4Source Δ.length m)
    (hgroup : genGroup F.gens = (winRestrictHom n Δ hnd hlt (genGroup gens) hinv).range)
    {κ : Type*} (hm : HugeM m (Nat.card (Fin Δ.length)))
    (hcap : TopwpCap e f) (houter : Top4wCap e f u v)
    (ix iy : RawStr) (Cy : List ℕ) (hCy : Cy.Nodup) (hCylt : ∀ i ∈ Cy, i < m)
    (col : (Fin Δ.length → ℕ) → Fin m → κ) (color : κ)
    (hCx : colorClass col (decStrN Δ.length ix) color = winSet m F.color)
    (hCyset : colorClass col (decStrN Δ.length iy) color = winSet m Cy)
    (hcol : IsCanonicalColoring F.hom col)
    (hgiant : ∀ α : Perm (Fin m), α ∈ alternatingGroup (Fin m) →
      (∀ γ, γ ∉ colorClass col (decStrN Δ.length ix) color → α γ = γ) →
      ∃ β ∈ homImage F.hom (strAut (genGroup F.gens : Set (Perm (Fin Δ.length))) (decStrN Δ.length ix)),
        ∀ γ ∈ colorClass col (decStrN Δ.length ix) color, β γ = α γ)
    (solve : RawWinSI → RawCoset) :
    let I := top4wEnter (((dom, gens.map (encPerm n)), Δ, x), (((F.action, ix, iy), F.color), Cy))
    LoopMatch (top4wRound a b c d e f u v solve) (top4wDecode n) (decCoset n) I
      ((top4wRound a b c d e f u v solve).width I) 0 (top4wInit I)
      (top4wTree Δ hnd hlt (genGroup gens) hinv (decStrN n x)
        (F.autoTree hm ix iy Cy col color hCx hCyset)) := by
  apply top4wLoopMatch hd hx hnd hlt hinv houter solve
    (F.autoTree_loop hm hcap ix iy Cy hCy hCylt col color hCx hCyset solve)
  · intro J hJ
    rw [← hgroup]
    exact F.autoTree_calls_K hm ix iy Cy col color hCx hCyset J hJ
  · rw [(F.autoTree_spec hm ix iy Cy col color hCx hCyset hcol hgiant).1, ← hgroup]
    exact fun _ h => h.1

end Algo
