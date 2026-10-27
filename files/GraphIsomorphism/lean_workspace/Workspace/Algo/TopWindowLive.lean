import Workspace.Algo.TopDomainThree
import Workspace.Master.CosetCompose

/-! # The live window tree in the computed domain labels
The raw inner tree uses the positions of the computed window list. The
paper uses the window subtype. This comparison transports every supplied
choice and proves equality of ordered calls and returned values.
-/
namespace Algo
open Babai Equiv
open scoped Classical

noncomputable def topwCompat {n m : ℕ} {Δ : List ℕ} (hnd : Δ.Nodup)
    (hlt : ∀ u ∈ Δ, u < n) {G : Subgroup (Perm (Fin n))} (hinv : IsInvariant G (winSet n Δ))
    (ϕ : restrictTo G (winSet n Δ) hinv →* Perm (Fin m)) :
    TopdCompat (winEquiv n Δ hnd hlt) (topwInducedHom hnd hlt hinv ϕ) ϕ where
  group := topwGroupEquiv Δ hnd hlt G hinv
  coe := topwGroupEquiv_coe hnd hlt hinv
  hom := fun _ => rfl

noncomputable def topwLivePrefix {n : ℕ} (Δ : List ℕ) (hnd : Δ.Nodup)
    (hlt : ∀ u ∈ Δ, u < n) (G : Subgroup (Perm (Fin n))) (hinv : IsInvariant G (winSet n Δ))
    (x : Fin n → ℕ) (T : SIReduction (Fin Δ.length) ℕ (Option (Set (Perm (Fin Δ.length))))) :
    SIReduction (Fin n) ℕ (Option (Set (Perm (Fin n)))) :=
  (topwReduction Δ hnd hlt G hinv x T).bind fun A => .done (A.map (topwPreimageSet Δ hnd hlt G hinv))

section Live
variable {n m : ℕ} {Δ : List ℕ} (hnd : Δ.Nodup) (hlt : ∀ u ∈ Δ, u < n)
    {G : Subgroup (Perm (Fin n))} (hinv : IsInvariant G (winSet n Δ))
    (ϕ : restrictTo G (winSet n Δ) hinv →* Perm (Fin m))
    (S : List (alternatingGroup (Fin m)))
    (O : TopActionOdd (topwInducedHom hnd hlt hinv ϕ)) (O' : TopActionOdd ϕ)
    (E : OrbitEnum (kerSubgroup (topwInducedHom hnd hlt hinv ϕ))) (F : OrbitEnum (kerSubgroup ϕ))
    (hE : F.windows = E.windows.map (fun W => (winEquiv n Δ hnd hlt) '' W))
    (hO : O'.representative = (winEquiv n Δ hnd hlt).permCongr O.representative)
    (hS : Subgroup.closure {σ : alternatingGroup (Fin m) | σ ∈ S} = ⊤)
    (x y : Fin n → ℕ)
include hE hO hS

 theorem topwLivePrefix_match :
    let ix := fun i => x (winEquiv n Δ hnd hlt i)
    let iy := fun i => y (winEquiv n Δ hnd hlt i)
    let T := topwLivePrefix Δ hnd hlt G hinv x
      (cosetTopAction3With (topwInducedHom hnd hlt hinv ϕ) S O E ix iy)
    let U := cosetWindowTopAction3With G (winSet n Δ) hinv ϕ S O' F x y
    T.calls = U.calls ∧ T.run = U.run := by
  intro ix iy T U
  have hx : ix ∘ (winEquiv n Δ hnd hlt).symm = restrictStr (winSet n Δ) x := by
    funext w
    simp only [Function.comp_apply, ix, Equiv.apply_symm_apply, restrictStr]
  have hy : iy ∘ (winEquiv n Δ hnd hlt).symm = restrictStr (winSet n Δ) y := by
    funext w
    simp only [Function.comp_apply, iy, Equiv.apply_symm_apply, restrictStr]
  have hc := topdTop3_calls (topwCompat hnd hlt hinv ϕ) S E F hE ix iy O O' hO hS
  have hv := topdTop3_run (topwCompat hnd hlt hinv ϕ) S E F hE ix iy O O' hS
  rw [hx, hy] at hc hv
  constructor
  · change (topwLivePrefix _ _ _ _ _ _ _).calls = (cosetWindowTopAction3With _ _ _ _ _ _ _ _ _).calls
    rw [topwLivePrefix, cosetWindowTopAction3With, SIReduction.calls_bind,
      SIReduction.calls_bind, SIReduction.calls_done, SIReduction.calls_done,
      List.append_nil, List.append_nil,
      calls_topwReduction hnd hlt hinv x _ (calls_cosetTopAction3With_K _ S O E ix iy),
      SIReduction.calls_window hinv x _ (calls_cosetTopAction3With_K ϕ S O' F _ _), hc,
      List.map_map]
    apply List.map_congr_left
    intro J _
    exact topwInstance_eq_windowInstance hnd hlt hinv x J
  · change (topwLivePrefix _ _ _ _ _ _ _).run = (cosetWindowTopAction3With _ _ _ _ _ _ _ _ _).run
    rw [topwLivePrefix, cosetWindowTopAction3With, SIReduction.run_bind,
      SIReduction.run_bind, SIReduction.run_done, SIReduction.run_done,
      run_topwReduction hnd hlt hinv x _ (calls_cosetTopAction3With_K _ S O E ix iy),
      SIReduction.run_window hinv x _ (calls_cosetTopAction3With_K ϕ S O' F _ _), hv]
    cases (cosetTopAction3With (topwInducedHom hnd hlt hinv ϕ) S O E ix iy).run with
    | none => rfl
    | some A => exact congrArg some (topwPreimage_eq_windowPreim hnd hlt hinv A)

 theorem top4Body_live (rest : List (Set (Fin n))) :
    let ix := fun i => x (winEquiv n Δ hnd hlt i)
    let iy := fun i => y (winEquiv n Δ hnd hlt i)
    let T := top4Body Δ hnd hlt G hinv x y rest
      (cosetTopAction3With (topwInducedHom hnd hlt hinv ϕ) S O E ix iy)
    let U := (cosetWindowTopAction3With G (winSet n Δ) hinv ϕ S O' F x y).bind
      (fun A => match A with | none => .done ∅ | some B => Babai.cosetChain x y rest B)
    T.calls = U.calls ∧ T.run = U.run := by
  intro ix iy T U
  have he : T = (topwLivePrefix Δ hnd hlt G hinv x
      (cosetTopAction3With (topwInducedHom hnd hlt hinv ϕ) S O E ix iy)).bind
      (fun A => match A with | none => .done ∅ | some B => Babai.cosetChain x y rest B) := by
    rw [topwLivePrefix, SIReduction.bind_assoc]
    change (topwReduction _ _ _ _ _ _ _).bind _ = _
    congr 1
    funext A
    cases A <;> rfl
  have hh := topwLivePrefix_match hnd hlt hinv ϕ S O O' E F hE hO hS x y
  dsimp only at hh
  rw [he]
  change (SIReduction.bind _ _).calls = (SIReduction.bind _ _).calls ∧
    (SIReduction.bind _ _).run = (SIReduction.bind _ _).run
  simp only [SIReduction.calls_bind, SIReduction.run_bind]
  rw [hh.1, hh.2]
  exact ⟨rfl, rfl⟩

end Live
end Algo
