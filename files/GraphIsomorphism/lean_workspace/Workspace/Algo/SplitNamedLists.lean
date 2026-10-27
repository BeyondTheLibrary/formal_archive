import Workspace.Algo.SplitImprimitiveScan
import Mathlib.Data.List.NodupEquivFin

/-! # Read an injective naming in its supplied list order -/
namespace Algo

/-- The position bijection follows the stored order. It does not choose a new
order on the abstract carrier. -/
theorem splitNameEquiv_exists {A : Type*} (name : A → ℕ)
    (hinj : Function.Injective name) (l : List ℕ) (hnd : l.Nodup)
    (hcover : ∀ a, a ∈ l ↔ ∃ x, name x = a) :
    ∃ e : A ≃ Fin l.length, ∀ x, l[(e x).val] = name x := by
  classical
  let f : A → {a // a ∈ l} := fun x => ⟨name x,(hcover _).2 ⟨x,rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y h; exact hinj (congrArg Subtype.val h)
    · rintro ⟨a,ha⟩
      obtain ⟨x,rfl⟩ := (hcover _).1 ha
      exact ⟨x,rfl⟩
  let e := (Equiv.ofBijective f hf).trans (List.Nodup.getEquiv l hnd).symm
  refine ⟨e,fun x => ?_⟩
  exact congrArg Subtype.val ((List.Nodup.getEquiv l hnd).apply_symm_apply (f x))

end Algo
