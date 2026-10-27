import Workspace.Algo.TopParity

/-!
# Sec. 12: computing two generators of the alternating group

Corollary 12.0.6 uses two generators to obtain three kernel tests.
We compute the witnesses proved in `Babai.TwoGen`: a cycle and a
three-cycle. The degree arrives as a list, which supplies the loop bound.
-/

namespace Algo

open RAM RAM.Targets
open Equiv (Perm)

/-- The cycle through the points from zero to the given endpoint. -/
def topCycle (p : List ℕ × ℕ) : RawPerm :=
  (rawOne p.1).map (fun i => if i < p.2 then i + 1 else if i = p.2 then 0 else i)

theorem topCycle_spec {m : ℕ} {dom : List ℕ} (hd : dom.length = m) (d : Fin m) :
    topCycle (dom, d.val) = encPerm m (Fin.cycleRange d) := by
  apply List.ext_getElem
  · simp [topCycle, rawOne, hd]
  · intro i hi hi'
    have him : i < m := by simpa using hi'
    simp only [topCycle, rawOne, List.getElem_map, List.getElem_range,
      getElem_encPerm m _ i him]
    by_cases hil : i < d.val
    · rw [if_pos hil, Fin.coe_cycleRange_of_lt (show (⟨i, him⟩ : Fin m) < d from hil)]
    · rw [if_neg hil]
      by_cases hie : i = d.val
      · have he : (⟨i, him⟩ : Fin m) = d := Fin.ext hie
        rw [if_pos hie, he, Fin.coe_cycleRange_of_le le_rfl, if_pos rfl]
      · rw [if_neg hie, Fin.cycleRange_of_gt (show d < (⟨i, him⟩ : Fin m) from by
          change d.val < i; omega)]

theorem polyFun_topCycle : PolyFun topCycle := by
  have hi : PolyFun (fun p : ℕ × ℕ => p.2 + 1) := polyFun_snd.add (polyFun_const 1)
  have h : PolyFun (fun p : ℕ × ℕ =>
      if p.2 < p.1 then p.2 + 1 else if p.2 = p.1 then 0 else p.2) :=
    (PolyFun.ite (hi.le polyFun_fst) hi
      (PolyFun.ite ((polyFun_snd.pair polyFun_fst).comp polyFun_natEq)
        (polyFun_const 0) polyFun_snd)).of_eq (fun _ => by simp)
  exact ((polyFun_snd.pair (polyFun_fst.comp polyFun_rawOne)).comp
    (PolyFun.mapParam h)).of_eq (fun _ => rfl)

/-- A three-cycle as two swaps, in the same order as `Babai.thr`. -/
def topThreeCycle (p : List ℕ × ℕ × ℕ × ℕ) : RawPerm :=
  rawMul (rawTopSwap (p.1, p.2.1, p.2.2.1), rawTopSwap (p.1, p.2.2.1, p.2.2.2))

theorem topThreeCycle_spec {m : ℕ} {dom : List ℕ} (hd : dom.length = m)
    (a b c : Fin m) :
    topThreeCycle (dom, a.val, b.val, c.val) = encPerm m (Babai.thr a b c) := by
  rw [topThreeCycle, rawTopSwap_spec hd a b, rawTopSwap_spec hd b c, rawMul_encPerm]
  rfl

theorem polyFun_topThreeCycle : PolyFun topThreeCycle := by
  have hab : PolyFun (fun p : List ℕ × ℕ × ℕ × ℕ => (p.1, p.2.1, p.2.2.1)) :=
    polyFun_fst.pair ((polyFun_snd.comp polyFun_fst).pair
      ((polyFun_snd.comp polyFun_snd).comp polyFun_fst))
  have hbc : PolyFun (fun p : List ℕ × ℕ × ℕ × ℕ => (p.1, p.2.2.1, p.2.2.2)) :=
    polyFun_fst.pair (polyFun_snd.comp polyFun_snd)
  exact ((hab.comp polyFun_rawTopSwap).pair (hbc.comp polyFun_rawTopSwap)).comp polyFun_rawMul

/-- Corollary 12.0.6: the two top generators, computed from the degree. -/
def topAltGens (dom : List ℕ) : RawGens :=
  if dom.length % 2 = 0 then
    [topThreeCycle (dom, dom.length - 1, 0, 1), topCycle (dom, dom.length - 2)]
  else
    [topThreeCycle (dom, dom.length - 1, dom.length - 2, 0), topCycle (dom, dom.length - 3)]

@[simp] theorem length_topAltGens (dom : List ℕ) : (topAltGens dom).length = 2 := by
  unfold topAltGens
  split <;> rfl

theorem polyFun_topAltGens : PolyFun topAltGens := by
  have hn : PolyFun (fun dom : List ℕ => dom.length) := polyFun_length
  have hfirst := ((polyFun_id.pair ((hn.sub (polyFun_const 1)).pair
    ((polyFun_const 0).pair (polyFun_const 1)))).comp polyFun_topThreeCycle)
  have hsecond := ((polyFun_id.pair ((hn.sub (polyFun_const 1)).pair
    ((hn.sub (polyFun_const 2)).pair (polyFun_const 0)))).comp polyFun_topThreeCycle)
  have hl : ∀ d : ℕ, PolyFun (fun dom : List ℕ => [topCycle (dom, dom.length - d)]) := by
    intro d
    exact ((((polyFun_id.pair (hn.sub (polyFun_const d))).comp polyFun_topCycle).pair
      (polyFun_const [])).comp polyFun_cons)
  exact (PolyFun.ite (((hn.mod (polyFun_const 2)).pair (polyFun_const 0)).comp polyFun_natEq)
    ((hfirst.pair (hl 2)).comp polyFun_cons)
    ((hsecond.pair (hl 3)).comp polyFun_cons)).of_eq (fun _ => by simp [topAltGens])

/-- The computed pair generates precisely the alternating group. -/
theorem decGroup_topAltGens {m : ℕ} {dom : List ℕ} (hd : dom.length = m) (hm : 3 ≤ m) :
    decGroup m (topAltGens dom) = alternatingGroup (Fin m) := by
  by_cases hp : m % 2 = 0
  · obtain ⟨d, rfl⟩ : ∃ d, m = d + 2 := ⟨m - 2, by omega⟩
    rw [topAltGens, hd, if_pos hp]
    have h1 : d + 2 - 1 = d + 1 := by omega
    rw [h1, Nat.add_sub_cancel, topThreeCycle_spec hd
      (⟨d + 1, by omega⟩ : Fin (d + 2)) ⟨0, by omega⟩ ⟨1, by omega⟩,
      topCycle_spec hd (⟨d, by omega⟩ : Fin (d + 2))]
    simpa [decGroup, genGroup] using Babai.TwoGen.two_generated_even
      (d := d) (by omega) (Nat.even_iff.2 (by omega))
  · obtain ⟨d, rfl⟩ : ∃ d, m = d + 3 := ⟨m - 3, by omega⟩
    rw [topAltGens, hd, if_neg hp]
    have h1 : d + 3 - 1 = d + 2 := by omega
    have h2 : d + 3 - 2 = d + 1 := by omega
    rw [h1, h2, Nat.add_sub_cancel, topThreeCycle_spec hd
      (⟨d + 2, by omega⟩ : Fin (d + 3)) ⟨d + 1, by omega⟩ ⟨0, by omega⟩,
      topCycle_spec hd (⟨d, by omega⟩ : Fin (d + 3))]
    simpa [decGroup, genGroup] using Babai.TwoGen.two_generated_odd
      (d := d) (Nat.even_iff.2 (by omega))

theorem topAltGens_wf {m : ℕ} {dom : List ℕ} (hd : dom.length = m) (hm : 3 ≤ m) :
    RawGens.WF m (topAltGens dom) := by
  have hthree (a b c : ℕ) (ha : a < m) (hb : b < m) (hc : c < m) :
      RawPerm.WF m (topThreeCycle (dom, a, b, c)) := by
    rw [topThreeCycle_spec hd (⟨a, ha⟩ : Fin m) ⟨b, hb⟩ ⟨c, hc⟩]
    exact wf_encPerm _ _
  have hcycle (d : ℕ) (hlt : d < m) : RawPerm.WF m (topCycle (dom, d)) := by
    rw [topCycle_spec hd (⟨d, hlt⟩ : Fin m)]
    exact wf_encPerm _ _
  intro r hr
  unfold topAltGens at hr
  split at hr <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hr <;>
    rcases hr with rfl | rfl
  · exact hthree _ _ _ (by omega) (by omega) (by omega)
  · exact hcycle _ (by omega)
  · exact hthree _ _ _ (by omega) (by omega) (by omega)
  · exact hcycle _ (by omega)

/-- Corollary 12.0.6: the subgroup for the two-branch Luks descent. -/
def topAltPreimage (p : RawAction) : RawGens :=
  tidyGens (p.1.1, actLiftGens (p, topAltGens p.2.1))

theorem polyFun_topAltPreimage : PolyFun topAltPreimage :=
  ((polyFun_fst.comp polyFun_fst).pair
    ((polyFun_id.pair ((polyFun_snd.comp polyFun_fst).comp polyFun_topAltGens)).comp
      polyFun_actLiftGens)).comp polyFun_tidyGens

/-- The descent subgroup is exactly the preimage of the alternating group. -/
theorem decGroup_topAltPreimage {n m : ℕ} {dom gdom : List ℕ}
    {gens : List (Perm (Fin n))} {imgs : List (Perm (Fin m))}
    {ϕ : genGroup gens →* Perm (Fin m)} (hd : dom.length = n) (hg : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (hm : 3 ≤ m) (hgiant : Babai.IsGiantRep ϕ) :
    decGroup n (topAltPreimage ((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m)))) =
      Babai.preimageAlt ϕ := by
  have hsub : genGroup ((topAltGens gdom).map (decPerm m)) ≤ ϕ.range := by
    change decGroup m (topAltGens gdom) ≤ _
    rw [decGroup_topAltGens hg hm]
    exact hgiant
  rw [topAltPreimage, decGroup_tidyGens hd]
  conv_lhs => rw [← map_encPerm_decPerm (topAltGens_wf hg hm)]
  rw [decGroup_actLiftGens hd hg hI _ hsub]
  change (Subgroup.comap ϕ (decGroup m (topAltGens gdom))).map _ = _
  rw [decGroup_topAltGens hg hm]
  rfl

theorem topAltPreimage_wf {n : ℕ} (p : RawAction) (hd : p.1.1.length = n) :
    RawGens.WF n (topAltPreimage p) ∧ (topAltPreimage p).length ≤ n * n :=
  ⟨wf_tidyGens hd _, length_tidyGens hd _⟩

/-- Read the computed pair as elements of the alternating group. -/
noncomputable def topAltGensTyped {m : ℕ} (dom : List ℕ) (hd : dom.length = m) (hm : 3 ≤ m) :
    List (alternatingGroup (Fin m)) :=
  (topAltGens dom).attach.map (fun r => ⟨decPerm m r.val, by
    rw [← decGroup_topAltGens hd hm]
    exact Subgroup.subset_closure (List.mem_map.2 ⟨r.val, r.property, rfl⟩)⟩)

theorem map_topAltGensTyped {m : ℕ} (dom : List ℕ) (hd : dom.length = m) (hm : 3 ≤ m) :
    (topAltGensTyped dom hd hm).map (fun r => encPerm m r.val) = topAltGens dom := by
  rw [topAltGensTyped, List.map_map]
  calc
    _ = (topAltGens dom).attach.map Subtype.val := by
      apply List.map_congr_left
      intro r _
      exact encPerm_decPerm (topAltGens_wf hd hm r.val r.property)
    _ = _ := by simpa using (List.attach_map_val (l := topAltGens dom) (f := id))

theorem topAltGensTyped_spec {m : ℕ} (dom : List ℕ) (hd : dom.length = m) (hm : 3 ≤ m) :
    (topAltGensTyped dom hd hm).length = 2 ∧
      Subgroup.closure {r | r ∈ topAltGensTyped dom hd hm} = ⊤ := by
  classical
  refine ⟨by simp [topAltGensTyped], ?_⟩
  apply Subgroup.map_injective (alternatingGroup (Fin m)).subtype_injective
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.subtype_range]
  have he : (alternatingGroup (Fin m)).subtype '' {r | r ∈ topAltGensTyped dom hd hm} =
      {r | r ∈ (topAltGens dom).map (decPerm m)} := by
    ext r
    simp [topAltGensTyped]
    intro x hx he
    change r ∈ alternatingGroup (Fin m)
    rw [← he, ← decGroup_topAltGens hd hm]
    exact Subgroup.subset_closure (List.mem_map.2 ⟨x, hx, rfl⟩)
  rw [he]
  exact decGroup_topAltGens hd hm

end Algo
