import Workspace.Algo.TopFourComputedEntry

/-! # Top-action input from arbitrary certified action arrays
The semantic source record uses decoded generators. Well-formedness proves
that encoding them again gives exactly the original raw action arrays.
-/
namespace Algo
open Babai Equiv

noncomputable def Top4Source.ofRaw {n m : ℕ} {p : RawAction}
    {ϕ : decGroup n p.1.2 →* Perm (Fin m)} (hp : RawAction.WF n m p ϕ)
    (hG : IsTransitive (decGroup n p.1.2)) (hϕ : IsGiantRep ϕ)
    (hk : VeryLargeK m (maxOrbitLength (decGroup n p.1.2)))
    (C : List ℕ) (hnd : C.Nodup) (hlt : ∀ u ∈ C, u < m)
    (hC : m < 2 * (winSet m C).ncard) : Top4Source n m where
  dom := p.1.1
  gdom := p.2.1
  gens := p.1.2.map (decPerm n)
  imgs := p.2.2.map (decPerm m)
  hom := ϕ
  dom_length := hp.1
  gdom_length := hp.2.1
  images := hp.2.2.2.2
  transitive := hG
  giant := hϕ
  large := hk
  color := C
  color_nodup := hnd
  color_lt := hlt
  color_large := hC

 theorem Top4Source.ofRaw_action {n m : ℕ} {p : RawAction}
    {ϕ : decGroup n p.1.2 →* Perm (Fin m)} (hp : RawAction.WF n m p ϕ)
    (hG : IsTransitive (decGroup n p.1.2)) (hϕ : IsGiantRep ϕ)
    (hk : VeryLargeK m (maxOrbitLength (decGroup n p.1.2)))
    (C : List ℕ) (hnd : C.Nodup) (hlt : ∀ u ∈ C, u < m)
    (hC : m < 2 * (winSet m C).ncard) :
    (Top4Source.ofRaw hp hG hϕ hk C hnd hlt hC).action = p := by
  simp only [Top4Source.ofRaw, Top4Source.action,
    map_encPerm_decPerm hp.2.2.1, map_encPerm_decPerm hp.2.2.2.1]

end Algo
