import Workspace.Algo.TopDomainChoices

/-! # Raw matching for the supplied window and remaining-window phases
The induced action is read in the computed window labels. Its actual orbit
order and odd representative supply the choices of the checked window tree.
The same raw round and uniform RAM bound apply to this tree.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Classical

noncomputable def top4LiveBody {n m : ℕ} {Δ : List ℕ} (hnd : Δ.Nodup)
    (hlt : ∀ u ∈ Δ, u < n) {G : Subgroup (Perm (Fin n))} (hinv : IsInvariant G (winSet n Δ))
    (ϕ : restrictTo G (winSet n Δ) hinv →* Perm (Fin m))
    (S : List (alternatingGroup (Fin m)))
    (O : TopActionOdd (topwInducedHom hnd hlt hinv ϕ))
    (E : OrbitEnum (kerSubgroup (topwInducedHom hnd hlt hinv ϕ)))
    (x y : Fin n → ℕ) (rest : List (Set (Fin n))) : SIReduction (Fin n) ℕ (Set (Perm (Fin n))) :=
  (cosetWindowTopAction3With G (winSet n Δ) hinv ϕ S
    ((topwCompat hnd hlt hinv ϕ).odd O) ((topwCompat hnd hlt hinv ϕ).orbits E) x y).bind
    (fun A => match A with | none => .done ∅ | some B => Babai.cosetChain x y rest B)

 theorem top4LivePhaseMatch {n m c d e f : ℕ} {dom Δ x y : List ℕ} {rest : List (List ℕ)}
    {gens : List (Perm (Fin n))} {P : TopcsInput}
    (hd : dom.length = n) (hx : x.length = n) (hnd : Δ.Nodup) (hlt : ∀ u ∈ Δ, u < n)
    (hinv : IsInvariant (genGroup gens) (winSet n Δ)) (hcap : TopwpCap e f)
    (ϕ : restrictTo (genGroup gens) (winSet n Δ) hinv →* Perm (Fin m))
    (S : List (alternatingGroup (Fin m)))
    (O : TopActionOdd (topwInducedHom hnd hlt hinv ϕ))
    (E : OrbitEnum (kerSubgroup (topwInducedHom hnd hlt hinv ϕ)))
    (hP : TopcsSpec P (topwInducedHom hnd hlt hinv ϕ) S O E
      (fun i => decStrN n x (winEquiv n Δ hnd hlt i))
      (fun i => decStrN n y (winEquiv n Δ hnd hlt i)))
    (hpos : 0 < Δ.length) (hϕ : IsGiantRep ϕ)
    (hS : Subgroup.closure {σ : alternatingGroup (Fin m) | σ ∈ S} = ⊤)
    (solve : RawWinSI → RawCoset) :
    let C : Top4Context := ((((dom, gens.map (encPerm n)), Δ, x), P), rest, y)
    PhaseMatch (top4Round c d e f solve) (top4Decode n) (decCoset n) (C, none)
      (top4Width C) 0 (top4Init (C, none))
      (top4LiveBody hnd hlt hinv ϕ S O E (decStrN n x) (decStrN n y) (rest.map (winSet n)))
      (fun A j s => Top4TailInv n C [] A j s) := by
  intro C
  have hh := top4Body_live hnd hlt hinv ϕ S O ((topwCompat hnd hlt hinv ϕ).odd O)
    E ((topwCompat hnd hlt hinv ϕ).orbits E) rfl rfl hS (decStrN n x) (decStrN n y)
    (rest.map (winSet n))
  exact topcsPhaseMatch_congr
    (top4PhaseMatch hd hx hnd hlt hinv hcap (topwInducedHom hnd hlt hinv ϕ) S O E _ _ hP
      hpos (topwInducedHom_giant hnd hlt hinv ϕ hϕ) hS solve) hh.1 hh.2

 theorem top4LiveLoopMatch {n m c d e f : ℕ} {dom Δ x y : List ℕ} {rest : List (List ℕ)}
    {gens : List (Perm (Fin n))} {P : TopcsInput}
    (hd : dom.length = n) (hx : x.length = n) (hnd : Δ.Nodup) (hlt : ∀ u ∈ Δ, u < n)
    (hinv : IsInvariant (genGroup gens) (winSet n Δ)) (hcap : TopwpCap e f)
    (ϕ : restrictTo (genGroup gens) (winSet n Δ) hinv →* Perm (Fin m))
    (S : List (alternatingGroup (Fin m)))
    (O : TopActionOdd (topwInducedHom hnd hlt hinv ϕ))
    (E : OrbitEnum (kerSubgroup (topwInducedHom hnd hlt hinv ϕ)))
    (hP : TopcsSpec P (topwInducedHom hnd hlt hinv ϕ) S O E
      (fun i => decStrN n x (winEquiv n Δ hnd hlt i))
      (fun i => decStrN n y (winEquiv n Δ hnd hlt i)))
    (hpos : 0 < Δ.length) (hϕ : IsGiantRep ϕ)
    (hS : Subgroup.closure {σ : alternatingGroup (Fin m) | σ ∈ S} = ⊤)
    (solve : RawWinSI → RawCoset) :
    let C : Top4Context := ((((dom, gens.map (encPerm n)), Δ, x), P), rest, y)
    LoopMatch (top4Round c d e f solve) (top4Decode n) (decCoset n) (C, none)
      (top4Width C) 0 (top4Init (C, none))
      (top4LiveBody hnd hlt hinv ϕ S O E (decStrN n x) (decStrN n y) (rest.map (winSet n))) := by
  intro C
  exact loopMatch_of_phaseMatch
    (top4LivePhaseMatch hd hx hnd hlt hinv hcap ϕ S O E hP hpos hϕ hS solve)
    (fun A j s h => top4Tail_finish (P := C) hx solve h) le_rfl

end Algo
