import Workspace.Algo.TopFourRawSource
import Workspace.Algo.AlignParity

/-! # Computing the aligning lift for the two color classes
The two classes are two-color partitions. The existing partition-isomorphism
routine finds an even bijection between them, and the action preimage routine
lifts it to the source group. Equal class sizes guarantee this lift exists.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Classical

/-- Each color class is one cell, so the second labeling is constant. -/
def top4ClassPart (p : List ℕ × List ℕ) : RawColPart := (top4ClassLab p, [])

theorem polyFun_top4ClassPart : PolyFun top4ClassPart := polyFun_top4ClassLab.pair (polyFun_const [])

theorem top4ClassPart_length (p : List ℕ × List ℕ) : (top4ClassPart p).1.length = p.1.length := by
  simp only [top4ClassPart, top4ClassLab, List.length_map, rawOne, List.length_range]

 theorem top4ClassLab_value {m : ℕ} {dom C : List ℕ} (hd : dom.length = m) (i : Fin m) :
    labAt (top4ClassLab (dom, C)) i = if i.val ∈ C then 1 else 0 := by
  have hi : i.val < (rawOne dom).length := by simpa only [rawOne, List.length_range, hd] using i.isLt
  change ((rawOne dom).map (fun j => if j ∈ C then 1 else 0)).getD i.val 0 = _
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hi)]
  simp only [List.getElem_map, rawOne, List.getElem_range]

 theorem top4ClassPart_iso {m : ℕ} {dom C D : List ℕ} (hd : dom.length = m) (f : Perm (Fin m)) :
    ColPartIso m (top4ClassPart (dom, C)) (top4ClassPart (dom, D)) f ↔
      f '' winSet m C = winSet m D := by
  constructor
  · intro hf
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      apply (top4ClassLab_spec hd (f u)).mp
      exact (hf.1 u).trans ((top4ClassLab_spec hd u).mpr hu)
    · intro hv
      refine ⟨f.symm v, ?_, f.apply_symm_apply v⟩
      apply (top4ClassLab_spec hd (f.symm v)).mp
      change labAt (top4ClassPart (dom, C)).1 (f.symm v) = 1
      rw [← hf.1 (f.symm v), f.apply_symm_apply]
      exact (top4ClassLab_spec hd v).mpr hv
  · intro he
    have hm (u : Fin m) : u.val ∈ C ↔ (f u).val ∈ D := by
      change u ∈ winSet m C ↔ f u ∈ winSet m D
      rw [← he]
      exact ⟨fun hu => ⟨u, hu, rfl⟩, fun ⟨v, hv, hvu⟩ => f.injective hvu ▸ hv⟩
    have hl (u : Fin m) : labAt (top4ClassPart (dom, D)).1 (f u) = labAt (top4ClassPart (dom, C)).1 u := by
      simp only [top4ClassPart, top4ClassLab_value hd, hm]
    refine ⟨hl, fun u v => ?_⟩
    simp only [cellOf, top4ClassPart, labAt, List.getD_nil, Prod.mk.injEq, and_true]
    exact congrArg₂ (fun a b : ℕ => a = b) (hl u).symm (hl v).symm |>.to_iff

def top4ClassMap (p : List ℕ × List ℕ × List ℕ) : Option RawPerm :=
  alignColPartIso (true, (top4ClassPart (p.1, p.2.1), top4ClassPart (p.1, p.2.2)))

theorem polyFun_top4ClassMap : PolyFun top4ClassMap :=
  ((polyFun_const true).pair (((polyFun_fst.pair (polyFun_snd.comp polyFun_fst)).comp polyFun_top4ClassPart).pair
    ((polyFun_fst.pair (polyFun_snd.comp polyFun_snd)).comp polyFun_top4ClassPart))).comp polyFun_alignColPartIso

 theorem top4ClassMap_some {m : ℕ} {dom C D r : List ℕ} (hd : dom.length = m)
    (hr : top4ClassMap (dom, C, D) = some r) :
    RawPerm.WF m r ∧ decPerm m r ∈ alternatingGroup (Fin m) ∧
      decPerm m r '' winSet m C = winSet m D := by
  obtain ⟨hw, hi, he⟩ := alignColPartIso_some ((top4ClassPart_length _).trans hd)
    ((top4ClassPart_length _).trans hd) hr
  exact ⟨hw, (Equiv.Perm.mem_alternatingGroup).mpr (he rfl), (top4ClassPart_iso hd _).mp hi⟩

 theorem top4ClassMap_ne_none {m : ℕ} {dom C D : List ℕ} (hd : dom.length = m) (hm : 3 ≤ m)
    (hc : (winSet m C).ncard = (winSet m D).ncard) : top4ClassMap (dom, C, D) ≠ none := by
  obtain ⟨f, hf, himg⟩ := exists_alternating_image_eq (Δ := Fin m) (by simpa using hm) hc
  intro hn
  have hsign := (alignColPartIso_eq_none ((top4ClassPart_length _).trans hd)
    ((top4ClassPart_length _).trans hd) hn f ((top4ClassPart_iso hd f).mpr himg)).2
  rw [(Equiv.Perm.mem_alternatingGroup).mp hf] at hsign
  have hn : (1 : ℤˣ) ≠ -1 := by decide
  exact hn hsign

end Algo
