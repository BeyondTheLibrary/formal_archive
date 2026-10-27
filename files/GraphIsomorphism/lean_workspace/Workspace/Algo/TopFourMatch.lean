import Workspace.Algo.TopFourTail

/-! # Exact matching of the two top-action phases
The first phase returns its restricted-domain coset. The machine computes
its full preimage and then follows the remaining windows. The subset needed
for the preimage routine follows from Corollary 12.0.8's checked value.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Classical

noncomputable def top4Body {n : ℕ} (Δ : List ℕ) (hnd : Δ.Nodup)
    (hlt : ∀ u ∈ Δ, u < n) (G : Subgroup (Perm (Fin n))) (hinv : IsInvariant G (winSet n Δ))
    (x y : Fin n → ℕ) (rest : List (Set (Fin n)))
    (T : SIReduction (Fin Δ.length) ℕ (Option (Set (Perm (Fin Δ.length))))) :
    SIReduction (Fin n) ℕ (Set (Perm (Fin n))) :=
  (topwReduction Δ hnd hlt G hinv x T).bind fun A =>
    match A with
    | none => .done ∅
    | some B => Babai.cosetChain x y rest (topwPreimageSet Δ hnd hlt G hinv B)

 theorem top4PhaseMatch {n m c d e f : ℕ} {dom Δ x y : List ℕ} {rest : List (List ℕ)}
    {gens : List (Perm (Fin n))} {P : TopcsInput}
    (hd : dom.length = n) (hx : x.length = n) (hnd : Δ.Nodup) (hlt : ∀ u ∈ Δ, u < n)
    (hinv : IsInvariant (genGroup gens) (winSet n Δ)) (hcap : TopwpCap e f)
    (ϕ : (winRestrictHom n Δ hnd hlt (genGroup gens) hinv).range →* Perm (Fin m))
    (S : List (alternatingGroup (Fin m))) (O : TopActionOdd ϕ) (E : OrbitEnum (kerSubgroup ϕ))
    (ix iy : Fin Δ.length → ℕ) (hP : TopcsSpec P ϕ S O E ix iy)
    (hpos : 0 < Δ.length) (hϕ : IsGiantRep ϕ)
    (hS : Subgroup.closure {σ : alternatingGroup (Fin m) | σ ∈ S} = ⊤)
    (solve : RawWinSI → RawCoset) :
    let C : Top4Context := ((((dom, gens.map (encPerm n)), Δ, x), P), rest, y)
    PhaseMatch (top4Round c d e f solve) (top4Decode n) (decCoset n) (C, none)
      (top4Width C) 0 (top4Init (C, none))
      (top4Body Δ hnd hlt (genGroup gens) hinv (decStrN n x) (decStrN n y) (rest.map (winSet n))
        (cosetTopAction3With ϕ S O E ix iy))
      (fun A j s => Top4TailInv n C [] A j s) := by
  intro C
  have hfirst := top4Phase_inner (C := C) solve (topwpPhaseMatch (c := c) (d := d)
    hd hx hnd hlt hinv hcap ϕ S O E ix iy hP hpos hϕ hS solve)
  have hval := top4Phase_value hfirst
  have hrun := run_topwReduction hnd hlt hinv (decStrN n x)
    (cosetTopAction3With ϕ S O E ix iy) (calls_cosetTopAction3With_K ϕ S O E ix iy)
  rw [run_cosetTopAction3With ϕ S O hS] at hrun
  change PhaseMatch _ _ _ _ (top4Base C + rest.length) _ _ _ _
  unfold top4Body
  refine phaseMatch_bind hval ?_
  rintro A j s ⟨hA, u, rfl, hu⟩
  have hX : (top4X C).length = n := hx
  have hcos : decCoset Δ.length ((topcsAnswer P u).getD none) = A.getD ∅ := by
    rw [← decTop1State_getD, hu.2.1]
  have hsub : A.getD ∅ ⊆
      ((winRestrictHom n Δ hnd hlt (genGroup gens) hinv).range : Set (Perm (Fin Δ.length))) := by
    rw [hA, hrun]
    split
    · exact fun g hg => hg.1
    · exact Set.empty_subset _
  have hpre := topwCosetPreimage_spec hd hnd hlt hinv ((topcsAnswer P u).getD none)
    (by rw [hcos]; exact hsub)
  have hcur : decCoset n (top4Open C u).2.2 = topwPreimageSet Δ hnd hlt (genGroup gens) hinv (A.getD ∅) := by
    change decCoset n (top2NormC x _) = _
    rw [decCoset_top2NormC hx, hpre, hcos]
  have hclosed : topcsJobs C.1.2 ≤ (top4Open C u).1.1 := le_of_eq hu.1.symm
  cases A with
  | none =>
    apply phaseMatch_mono (phaseMatch_done ?_) (Nat.zero_le _)
    refine ⟨hclosed, ?_, Or.inr rfl, Nat.zero_le _, hu.2.2⟩
    simpa only [Option.getD_none, topwPreimageSet, Set.mem_empty_iff_false,
      and_false, exists_false, Set.setOf_false] using hcur
  | some A =>
    have hh := top4Phase_tail (c := c) (d := d) (e := e) (f := f) C hX solve
      (rest.map (winSet n)) (topwPreimageSet Δ hnd hlt (genGroup gens) hinv A) j (top4Open C u)
      ⟨hclosed, hcur, Or.inl rfl, Nat.zero_le _, hu.2.2⟩
    simpa only [List.length_map] using hh

 theorem top4LoopMatch {n m c d e f : ℕ} {dom Δ x y : List ℕ} {rest : List (List ℕ)}
    {gens : List (Perm (Fin n))} {P : TopcsInput}
    (hd : dom.length = n) (hx : x.length = n) (hnd : Δ.Nodup) (hlt : ∀ u ∈ Δ, u < n)
    (hinv : IsInvariant (genGroup gens) (winSet n Δ)) (hcap : TopwpCap e f)
    (ϕ : (winRestrictHom n Δ hnd hlt (genGroup gens) hinv).range →* Perm (Fin m))
    (S : List (alternatingGroup (Fin m))) (O : TopActionOdd ϕ) (E : OrbitEnum (kerSubgroup ϕ))
    (ix iy : Fin Δ.length → ℕ) (hP : TopcsSpec P ϕ S O E ix iy)
    (hpos : 0 < Δ.length) (hϕ : IsGiantRep ϕ)
    (hS : Subgroup.closure {σ : alternatingGroup (Fin m) | σ ∈ S} = ⊤)
    (solve : RawWinSI → RawCoset) :
    let C : Top4Context := ((((dom, gens.map (encPerm n)), Δ, x), P), rest, y)
    LoopMatch (top4Round c d e f solve) (top4Decode n) (decCoset n) (C, none)
      (top4Width C) 0 (top4Init (C, none))
      (top4Body Δ hnd hlt (genGroup gens) hinv (decStrN n x) (decStrN n y) (rest.map (winSet n))
        (cosetTopAction3With ϕ S O E ix iy)) := by
  intro C
  exact loopMatch_of_phaseMatch
    (top4PhaseMatch hd hx hnd hlt hinv hcap ϕ S O E ix iy hP hpos hϕ hS solve)
    (fun A j s h => top4Tail_finish (P := C) hx solve h) le_rfl

end Algo
