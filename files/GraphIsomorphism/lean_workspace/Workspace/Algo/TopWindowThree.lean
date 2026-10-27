import Workspace.Algo.TopThreeRound
import Workspace.Algo.TopRestrict
import Workspace.TopAction.CosetTopAction4

/-!
# The restriction route for Corollary 12.0.10

The window of a child on `Fin Δ.length` must be read on the outer domain.
`topw3LiftWindow` computes this map and `topw3LiftWindow_spec` identifies it.
The loop uses the child's list, including on malformed inputs.

Domain transport alone does not turn `top3Round` into `cosetTopAction3`.
The first candidate set of each raw lifting test is a group. The coset
version uses the preimage of the requested top permutation. For a nonidentity
request the latter excludes the identity. `topw3_start_ne_preimage` and
`topw3_windowPreim_ne_preimage` record this obstruction to direct reuse.

This file does not define the window round. See the A12 session 9 note in
`Algo/DESIGN.md` for the additional fixed choices in the target tree.
-/

namespace Algo

open RAM RAM.Targets
open Equiv (Perm)

/-- Read a child window in the labels of the outer window. Out of range
labels are discarded. -/
def topw3LiftWindow (p : List ℕ × List ℕ) : List ℕ :=
  (p.2.filter (fun i => decide (i < p.1.length))).map (fun i => rawGet (p.1, i))

/-- The named guard keeps the polynomial-time proof small. -/
def topw3InWindow (p : List ℕ × ℕ) : Bool := decide (p.2 < p.1.length)

theorem polyFun_topw3InWindow : PolyFun topw3InWindow := by
  exact ((polyFun_snd.add (polyFun_const 1)).le
    (polyFun_fst.comp polyFun_length)).of_eq (fun p => by
      simp only [topw3InWindow, Nat.lt_iff_add_one_le])

/-- The transport is polynomial on all raw inputs. -/
theorem polyFun_topw3LiftWindow : PolyFun topw3LiftWindow := by
  have hf : PolyFun (fun p : List ℕ × List ℕ =>
      p.2.filter (fun i => topw3InWindow (p.1, i))) :=
    PolyFun.filterParam polyFun_topw3InWindow
  exact ((polyFun_fst.pair hf).comp (PolyFun.mapParam polyFun_rawGet)).of_eq
    (fun _ => rfl)

/-- The decoded window is the image under the list's bijection with the
outer window. This map preserves the size of every child window. -/
theorem topw3LiftWindow_spec {n : ℕ} (Δ W : List ℕ) (hnd : Δ.Nodup)
    (hlt : ∀ u ∈ Δ, u < n) :
    winSet n (topw3LiftWindow (Δ, W)) =
      (fun i : Fin Δ.length => ((winEquiv n Δ hnd hlt i : ↥(winSet n Δ)) : Fin n)) ''
        winSet Δ.length W := by
  ext u
  constructor
  · intro hu
    obtain ⟨i, hi, he⟩ := List.mem_map.1 hu
    obtain ⟨hiW, hi⟩ := List.mem_filter.1 hi
    have hi' : i < Δ.length := of_decide_eq_true hi
    refine ⟨⟨i, hi'⟩, hiW, Fin.ext ?_⟩
    change (((winEquiv n Δ hnd hlt ⟨i, hi'⟩ : ↥(winSet n Δ)) : Fin n) : ℕ) = u.val
    rw [winEquiv_coe Δ hnd hlt hi']
    exact (List.getD_eq_getElem Δ 0 hi').symm.trans he
  · rintro ⟨i, hi, rfl⟩
    apply List.mem_map.2
    refine ⟨i.val, List.mem_filter.2 ⟨hi, by simp [i.isLt]⟩, ?_⟩
    change rawGet (Δ, i.val) = (((winEquiv n Δ hnd hlt i : ↥(winSet n Δ)) : Fin n) : ℕ)
    rw [winEquiv_coe Δ hnd hlt i.isLt]
    exact List.getD_eq_getElem Δ 0 i.isLt

theorem topw3LiftWindow_size {n : ℕ} (Δ W : List ℕ) (hnd : Δ.Nodup)
    (hlt : ∀ u ∈ Δ, u < n) :
    (winSet n (topw3LiftWindow (Δ, W))).ncard = (winSet Δ.length W).ncard := by
  rw [topw3LiftWindow_spec Δ W hnd hlt]
  exact Set.ncard_image_of_injective _
    (Subtype.val_injective.comp (winEquiv n Δ hnd hlt).injective)

section Calls

variable {Ω H : Type*} [Group H] {G : Subgroup (Perm Ω)}

/-- A nonidentity lifting request excludes the identity from its candidate
set, independently of its window and strings. -/
theorem topw3_one_not_mem_preimage (ϕ : G →* H) {σ : H} (hσ : σ ≠ 1) :
    (1 : Perm Ω) ∉ Babai.preimageSet ϕ σ := by
  rintro ⟨h1, he⟩
  have he' : ϕ (1 : G) = σ := he
  rw [map_one] at he'
  exact hσ he'.symm

/-- The raw start of a lifting test is a group. It cannot be the candidate
set of a nonidentity coset lifting request. -/
theorem topw3_start_ne_preimage {n : ℕ} {q : RawTopLift}
    (hd : q.1.1.1.length = n) {K : Subgroup (Perm (Fin n))}
    (ϕ : K →* H) {σ : H} (hσ : σ ≠ 1) :
    decCoset n (topWinStart q) ≠ Babai.preimageSet ϕ σ := by
  intro he
  have h1 : (1 : Perm (Fin n)) ∈ decCoset n (topWinStart q) := by
    rw [decCoset_topWinStart hd]
    exact (decGroup n (topWinGens q)).one_mem
  exact topw3_one_not_mem_preimage ϕ hσ (he ▸ h1)

/-- Lifting a group from a restricted domain still includes the identity.
Thus restriction and full preimage do not remove the call mismatch. -/
theorem topw3_windowPreim_ne_preimage (Δ : Set Ω) (hinv : Babai.IsInvariant G Δ)
    (L : Subgroup (Perm Δ)) (ϕ : G →* H) {σ : H} (hσ : σ ≠ 1) :
    Babai.windowPreim G Δ hinv (L : Set (Perm Δ)) ≠ Babai.preimageSet ϕ σ := by
  intro he
  have h1 : (1 : Perm Ω) ∈ Babai.windowPreim G Δ hinv (L : Set (Perm Δ)) := by
    refine ⟨G.one_mem, ?_⟩
    change Babai.restrictHom G Δ hinv (1 : G) ∈ L
    rw [map_one]
    exact L.one_mem
  exact topw3_one_not_mem_preimage ϕ hσ (he ▸ h1)

end Calls

end Algo
