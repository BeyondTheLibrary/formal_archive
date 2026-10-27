import Workspace.Algo.AggNodeTransport
import Workspace.Algo.Restrict

/-! # Prescribed maps between ordered test sets

The local-guide relation asks whether a stored coset contains the map
between two ordered tuples. The orderings supply one permutation with
that prescribed action. Restriction then tests its action on the source
set without requiring it to belong to the ambient group.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv

/-- The base transporter carries each coordinate to the corresponding coordinate. -/
theorem aggnTransportBase_apply {m : ℕ} {dom u v : List ℕ}
    (hd : dom.length = m) (hu : u.Nodup) (hv : v.Nodup)
    (hult : ∀ a ∈ u,a < m) (hvlt : ∀ a ∈ v,a < m)
    (hlen : u.length = v.length) (i : Fin u.length) :
    decPerm m (aggnTransportBase (dom,u,v)) (winPt m u hult i).val =
      (winPt m v hvlt (i.cast hlen)).val := by
  have hus := wf_rawOrd hd hu hult
  have hvs := wf_rawOrd hd hv hvlt
  have him : i.val < m := lt_of_lt_of_le i.isLt (length_le_of_nodup_lt hu hult)
  have hs : decPerm m (rawOrd (dom,u)) ⟨i.val,him⟩ = (winPt m u hult i).val := by
    apply Fin.ext
    rw [decPerm_val_of_wf hus]
    exact List.getElem_append_left i.isLt
  have ht : decPerm m (rawOrd (dom,v)) ⟨i.val,him⟩ =
      (winPt m v hvlt (i.cast hlen)).val := by
    apply Fin.ext
    rw [decPerm_val_of_wf hvs]
    exact List.getElem_append_left (by simpa only [← hlen] using i.isLt)
  rw [aggnTransportBase,rawMul_of_wf hvs (wf_rawInv hus),decPerm_encPerm,
    rawInv_of_wf hus,decPerm_encPerm,← hs]
  simpa using ht

/-- Equality of two restrictions is exactly agreement at every listed source point. -/
theorem aggnRestrict_eq_iff {m : ℕ} {u : List ℕ} (hu : u.Nodup)
    (hlt : ∀ a ∈ u,a < m) {H K : Subgroup (Perm (Fin m))}
    (hH : IsInvariant H (winSet m u)) (hK : IsInvariant K (winSet m u))
    (g : H) (h : K) :
    winRestrictHom m u hu hlt H hH g = winRestrictHom m u hu hlt K hK h ↔
      ∀ a ∈ winSet m u,g.val a = h.val a := by
  constructor
  · intro he a ha
    let i := (winEquiv m u hu hlt).symm ⟨a,ha⟩
    have he' := congrArg (fun p : Perm (Fin u.length) =>
      ((winEquiv m u hu hlt (p i)).val)) he
    simp only [winRestrictHom_apply,Equiv.apply_symm_apply] at he'
    change g.val (winEquiv m u hu hlt i).val = h.val (winEquiv m u hu hlt i).val at he'
    simpa only [i,Equiv.apply_symm_apply] using he'
  · intro he
    apply DFunLike.ext
    intro i
    rw [winRestrictHom_apply,winRestrictHom_apply]
    apply congrArg (winEquiv m u hu hlt).symm
    apply Subtype.ext
    exact he _ (winEquiv m u hu hlt i).property

/-- The full stabilizer of a set supplies the restriction of a candidate map. -/
def aggnSetStab {m : ℕ} (T : Set (Fin m)) : Subgroup (Perm (Fin m)) :=
  { carrier := {g | g '' T = T}
    one_mem' := by simp
    mul_mem' := by
      intro a b ha hb
      change (a * b) '' T = T
      rw [perm_mul_image,hb,ha]
    inv_mem' := by
      intro a ha
      change (a⁻¹ : Perm (Fin m)) '' T = T
      rw [← ha,Set.image_image]
      simp only [Perm.inv_def,Equiv.symm_apply_apply,Set.image_id]
      simpa using ha.symm }

theorem aggnSetStab_invariant {m : ℕ} (T : Set (Fin m)) :
    IsInvariant (aggnSetStab T) T := fun _ h => h

end Algo
