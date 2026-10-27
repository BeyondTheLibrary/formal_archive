import Workspace.Algo.TopWindowImage

/-! # Extending strings in the raw window transport

The reference source supplies every letter outside the restricted domain.
Inside that domain the list position supplies the new letter, exactly as
`Babai.extendStr` requires in every transported recursive call.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv

abbrev TopwStringInput := RawStr × List ℕ × RawStr

def topwExtendStr (p : TopwStringInput) : RawStr :=
  (rawOne p.1).map fun u =>
    if u ∈ p.2.1 then rawGet (p.2.2, rawInvLookup (p.2.1.zipIdx, u)) else rawGet (p.1, u)

@[simp] theorem length_topwExtendStr (p : TopwStringInput) :
    (topwExtendStr p).length = p.1.length := by simp [topwExtendStr, rawOne]

theorem topwExtendStr_spec {n : ℕ} {x : RawStr} {Δ : List ℕ} (hx : x.length = n)
    (hnd : Δ.Nodup) (hlt : ∀ u ∈ Δ, u < n) (z : RawStr) :
    decStrN n (topwExtendStr (x, Δ, z)) = extendStr (winSet n Δ) (decStrN n x)
      (fun w => decStrN Δ.length z ((winEquiv n Δ hnd hlt).symm w)) := by
  funext u
  have hu : u.val < (topwExtendStr (x, Δ, z)).length := by rw [length_topwExtendStr, hx]; exact u.isLt
  change (topwExtendStr (x, Δ, z)).getD u.val 0 = _
  rw [List.getD_eq_getElem _ _ hu]
  simp only [topwExtendStr, List.getElem_map, rawOne, List.getElem_range]
  by_cases h : u.val ∈ Δ
  · rw [if_pos h]
    have hw : u ∈ winSet n Δ := h
    rw [extendStr, dif_pos hw]
    let k := (winEquiv n Δ hnd hlt).symm ⟨u, hw⟩
    have he : Δ[k.val] = u.val := by
      have he' := congrArg (fun w : ↥(winSet n Δ) => (w : Fin n).val)
        ((winEquiv n Δ hnd hlt).apply_symm_apply ⟨u, hw⟩)
      exact he'
    have hk : rawInvLookup (Δ.zipIdx, u.val) = k.val := by
      rw [← he]
      exact rawInvLookup_getElem hnd k.isLt
    rw [hk]
    rfl
  · rw [if_neg h]
    have hw : u ∉ winSet n Δ := h
    rw [extendStr, dif_neg hw]
    rfl

private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd

theorem polyFun_topwExtendStr : PolyFun topwExtendStr := by
  have hx : PolyFun (fun p : TopwStringInput × ℕ => p.1.1) := pfst polyFun_fst
  have hw : PolyFun (fun p : TopwStringInput × ℕ => p.1.2.1) := pfst (psnd polyFun_fst)
  have hz : PolyFun (fun p : TopwStringInput × ℕ => p.1.2.2) := psnd (psnd polyFun_fst)
  have hmem := (polyFun_snd.pair hw).comp (polyFun_listMem polyFun_natEq)
  have hlook := ((hw.comp polyFun_zipIdx).pair polyFun_snd).comp polyFun_rawInvLookup
  have hbody := PolyFun.ite hmem ((hz.pair hlook).comp polyFun_rawGet)
    ((hx.pair polyFun_snd).comp polyFun_rawGet)
  exact ((polyFun_id.pair (polyFun_fst.comp polyFun_rawOne)).comp
    (PolyFun.mapParam hbody)).of_eq (fun p => by simp [topwExtendStr])

end Algo
