import Workspace.Algo.TopLift
import Workspace.TopAction.Stabilizer

/-!
# Sec. 12: the set stabilizer on the RAM

Proposition 12.0.9 first finds the set stabilizer in the top group and then
takes its preimage. We list swaps within the two parts and products of two
such swaps. The even products include the three-cycles within a part and
the products of a swap on each side. Redundant products keep the construction
uniform when a part has fewer than three points.
-/

namespace Algo

open RAM RAM.Targets
open Equiv (Perm swap)
open Equiv.Perm

section Generation

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A nontrivial swap whose two points belong to the same part. -/
def PartSwap (C : Set α) (s : Perm α) : Prop :=
  ∃ a b, a ≠ b ∧ (a ∈ C ↔ b ∈ C) ∧ s = swap a b

theorem PartSwap.isSwap {C : Set α} {s : Perm α} (h : PartSwap C s) : s.IsSwap := by
  obtain ⟨a, b, hab, _, rfl⟩ := h
  exact ⟨a, b, hab, rfl⟩

theorem PartSwap.image {C : Set α} {s : Perm α} (h : PartSwap C s) : s '' C = C := by
  obtain ⟨a, b, hab, hC, rfl⟩ := h
  have hm : ∀ x, swap a b x ∈ C ↔ x ∈ C := by
    intro x
    by_cases ha : x = a
    · subst x; simpa using hC.symm
    by_cases hb : x = b
    · subst x; simpa using hC
    simp [Equiv.swap_apply_of_ne_of_ne ha hb]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩; exact (hm y).2 hy
  · intro hx
    exact ⟨swap a b x, (hm x).2 hx, by simp⟩

/-- The explicit generators suffice for a giant set stabilizer. Removing a
swap reduces the support. If that swap is outside the giant, remove a second
swap. Their product is even, so it belongs to the giant. -/
theorem giant_stabilizer_le (H L : Subgroup (Perm α)) (C : Set α)
    (hH : alternatingGroup α ≤ H)
    (hs : ∀ s, PartSwap C s → s ∈ H → s ∈ L)
    (hp : ∀ s t, PartSwap C s → PartSwap C t → s * t ∈ L) :
    Babai.setwiseStabilizer H C ≤ L := by
  suffices ∀ k (g : Perm α), g.support.card = k →
      g ∈ Babai.setwiseStabilizer H C → g ∈ L by
    intro g hg
    exact this _ g rfl hg
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro g hgcard hg
    by_cases hg1 : g = 1
    · subst g; exact L.one_mem
    have hmove : ∃ a, g a ≠ a := by
      by_contra h
      push_neg at h
      exact hg1 (Equiv.ext h)
    obtain ⟨a, ha⟩ := hmove
    have hpart : PartSwap C (swap a (g a)) :=
      ⟨a, g a, ha.symm,
        ((Babai.isInvariant_iff_mem _ _).1
          (Babai.isInvariant_setwiseStabilizer H C) g hg a), rfl⟩
    have hsmall : (swap a (g a) * g).support.card < k := by
      rw [← hgcard]
      exact card_support_swap_mul ha
    by_cases hsH : swap a (g a) ∈ H
    · have hg' : swap a (g a) * g ∈ Babai.setwiseStabilizer H C :=
        (Babai.setwiseStabilizer H C).mul_mem ⟨hsH, hpart.image⟩ hg
      have hL := L.mul_mem (hs _ hpart hsH) (ih _ hsmall _ rfl hg')
      simpa [← mul_assoc] using hL
    · have hg'1 : swap a (g a) * g ≠ 1 := by
        intro he
        have he' : g = swap a (g a) := by
          simpa [← mul_assoc] using congrArg (fun z => swap a (g a) * z) he
        exact hsH (he' ▸ hg.1)
      obtain ⟨b, hb⟩ : ∃ b, (swap a (g a) * g) b ≠ b := by
        by_contra h
        push_neg at h
        exact hg'1 (Equiv.ext h)
      have hg'top : swap a (g a) * g ∈ Babai.setwiseStabilizer ⊤ C :=
        (Babai.setwiseStabilizer ⊤ C).mul_mem ⟨Subgroup.mem_top _, hpart.image⟩
          ⟨Subgroup.mem_top _, hg.2⟩
      have htpart : PartSwap C (swap b ((swap a (g a) * g) b)) :=
        ⟨b, _, hb.symm,
          ((Babai.isInvariant_iff_mem _ _).1
            (Babai.isInvariant_setwiseStabilizer ⊤ C) _ hg'top b), rfl⟩
      have hpH : swap b ((swap a (g a) * g) b) * swap a (g a) ∈ H :=
        hH (mul_mem_alternatingGroup_of_isSwap htpart.isSwap hpart.isSwap)
      have hgg : swap b ((swap a (g a) * g) b) * (swap a (g a) * g)
          ∈ Babai.setwiseStabilizer H C := by
        refine ⟨?_, ?_⟩
        · simpa [mul_assoc] using H.mul_mem hpH hg.1
        · exact ((Babai.setwiseStabilizer ⊤ C).mul_mem
            ⟨Subgroup.mem_top _, htpart.image⟩ hg'top).2
      have hsmaller := (card_support_swap_mul hb).trans hsmall
      have hL := L.mul_mem (hp _ _ hpart htpart) (ih _ hsmaller _ rfl hgg)
      simpa [mul_assoc, ← mul_assoc (swap b ((swap a (g a) * g) b))] using hL

end Generation

/-! ## Listing the top generators -/

/-- Ordered pairs from a list. The list itself supplies the loop bound. -/
def topPairs {α : Type*} (l : List α) : List (α × α) :=
  (l.map (fun a => l.map (fun b => (a, b)))).flatten

@[simp] theorem mem_topPairs {α : Type*} {l : List α} {a b : α} :
    (a, b) ∈ topPairs l ↔ a ∈ l ∧ b ∈ l := by
  simp [topPairs]

theorem polyFun_topPairs {α : Type*} [Enc α] : PolyFun (topPairs (α := α)) := by
  have h : PolyFun (fun p : List α × α => p.1.map (fun b => (p.2, b))) :=
    (polyFun_snd.pair polyFun_fst).comp (PolyFun.mapParam polyFun_id)
  exact ((polyFun_id.pair polyFun_id).comp (PolyFun.flatMapParam h)).of_eq (fun _ => rfl)

/-- A transposition in list form. -/
def rawTopSwap (p : List ℕ × (ℕ × ℕ)) : RawPerm :=
  (rawOne p.1).map (fun k => if k = p.2.1 then p.2.2 else if k = p.2.2 then p.2.1 else k)

theorem rawTopSwap_spec {m : ℕ} {dom : List ℕ} (hd : dom.length = m) (a b : Fin m) :
    rawTopSwap (dom, (a.val, b.val)) = encPerm m (swap a b) := by
  apply List.ext_getElem
  · simp [rawTopSwap, rawOne, hd]
  · intro i hi hi'
    have him : i < m := by simpa using hi'
    simp only [rawTopSwap, rawOne, List.getElem_map, List.getElem_range,
      getElem_encPerm m _ i him, Equiv.swap_apply_def]
    by_cases ha : i = a.val <;> by_cases hb : i = b.val <;>
      simp_all [Fin.ext_iff]

theorem polyFun_rawTopSwap : PolyFun rawTopSwap := by
  have h : PolyFun (fun p : (ℕ × ℕ) × ℕ =>
      if p.2 = p.1.1 then p.1.2 else if p.2 = p.1.2 then p.1.1 else p.2) := by
    refine (PolyFun.ite
      ((polyFun_snd.pair (polyFun_fst.comp polyFun_fst)).comp polyFun_natEq)
      (polyFun_fst.comp polyFun_snd)
      (PolyFun.ite
        ((polyFun_snd.pair (polyFun_fst.comp polyFun_snd)).comp polyFun_natEq)
        (polyFun_fst.comp polyFun_fst) polyFun_snd)).of_eq ?_
    intro p
    simp
  exact ((polyFun_snd.pair (polyFun_fst.comp polyFun_rawOne)).comp
    (PolyFun.mapParam h)).of_eq (fun _ => rfl)

/-- Select distinct points on the same side of the set. -/
def topSameSide (p : List ℕ × (ℕ × ℕ)) : Bool :=
  if p.2.1 = p.2.2 then false else
    if p.2.1 ∈ p.1 then decide (p.2.2 ∈ p.1)
    else if p.2.2 ∈ p.1 then false else true

theorem topSameSide_spec (C : List ℕ) (a b : ℕ) :
    topSameSide (C, (a, b)) = true ↔ a ≠ b ∧ (a ∈ C ↔ b ∈ C) := by
  by_cases hab : a = b <;> by_cases ha : a ∈ C <;> by_cases hb : b ∈ C <;>
    simp_all [topSameSide]

theorem polyFun_topSameSide : PolyFun topSameSide := by
  have ha : PolyFun (fun p : List ℕ × (ℕ × ℕ) => decide (p.2.1 ∈ p.1)) :=
    ((polyFun_snd.comp polyFun_fst).pair polyFun_fst).comp polyFun_natListMem
  have hb : PolyFun (fun p : List ℕ × (ℕ × ℕ) => decide (p.2.2 ∈ p.1)) :=
    ((polyFun_snd.comp polyFun_snd).pair polyFun_fst).comp polyFun_natListMem
  refine (PolyFun.ite (polyFun_snd.comp polyFun_natEq) (polyFun_const false)
    (PolyFun.ite ha hb (PolyFun.ite hb (polyFun_const false) (polyFun_const true)))).of_eq ?_
  intro p
  simp [topSameSide]

/-- All swaps inside the set and inside its complement. -/
def topPartSwaps (p : List ℕ × List ℕ) : RawGens :=
  ((topPairs (rawOne p.1)).filter (fun q => topSameSide (p.2, q))).map
    (fun q => rawTopSwap (p.1, q))

theorem polyFun_topPartSwaps : PolyFun topPartSwaps := by
  have hp : PolyFun (fun p : List ℕ × List ℕ =>
      (topPairs (rawOne p.1)).filter (fun q => topSameSide (p.2, q))) :=
    (polyFun_snd.pair ((polyFun_fst.comp polyFun_rawOne).comp polyFun_topPairs)).comp
      (PolyFun.filterParam polyFun_topSameSide)
  exact ((polyFun_fst.pair hp).comp (PolyFun.mapParam polyFun_rawTopSwap)).of_eq (fun _ => rfl)

theorem mem_topPartSwaps {m : ℕ} {dom C : List ℕ} (hd : dom.length = m) {r : RawPerm} :
    r ∈ topPartSwaps (dom, C) ↔
      ∃ s : Perm (Fin m), PartSwap (winSet m C) s ∧ r = encPerm m s := by
  constructor
  · intro hr
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.1 hr
    obtain ⟨hab, hs⟩ := List.mem_filter.1 hab
    obtain ⟨ha, hb⟩ := mem_topPairs.1 hab
    have ha' : a < m := by simpa [rawOne, hd] using ha
    have hb' : b < m := by simpa [rawOne, hd] using hb
    obtain ⟨hne, hside⟩ := (topSameSide_spec C a b).1 hs
    refine ⟨swap ⟨a, ha'⟩ ⟨b, hb'⟩,
      ⟨⟨a, ha'⟩, ⟨b, hb'⟩, fun h => hne (congrArg Fin.val h), hside, rfl⟩, ?_⟩
    exact rawTopSwap_spec hd ⟨a, ha'⟩ ⟨b, hb'⟩
  · rintro ⟨s, ⟨a, b, hab, hside, rfl⟩, rfl⟩
    refine List.mem_map.2 ⟨(a.val, b.val), List.mem_filter.2 ⟨?_, ?_⟩,
      rawTopSwap_spec hd a b⟩
    · exact mem_topPairs.2 ⟨by simp [rawOne, hd], by simp [rawOne, hd]⟩
    · exact (topSameSide_spec C _ _).2 ⟨fun h => hab (Fin.ext h), hside⟩

/-- A polynomial list containing the swaps and the even products. -/
def topCandidates (p : List ℕ × List ℕ) : RawGens :=
  let ss := topPartSwaps p
  ss ++ (topPairs ss).map rawMul

theorem polyFun_topCandidates : PolyFun topCandidates :=
  (polyFun_topPartSwaps.pair ((polyFun_topPartSwaps.comp polyFun_topPairs).comp
    (PolyFun.map polyFun_rawMul))).comp polyFun_append

theorem mem_topCandidates {m : ℕ} {dom C : List ℕ} (hd : dom.length = m) {r : RawPerm} :
    r ∈ topCandidates (dom, C) ↔
      ∃ s : Perm (Fin m), (PartSwap (winSet m C) s ∨
        ∃ a b, PartSwap (winSet m C) a ∧ PartSwap (winSet m C) b ∧ s = a * b) ∧
        r = encPerm m s := by
  simp only [topCandidates, List.mem_append, List.mem_map]
  constructor
  · rintro (hs | ⟨⟨a, b⟩, hab, rfl⟩)
    · obtain ⟨s, hs', rfl⟩ := (mem_topPartSwaps hd).1 hs
      exact ⟨s, Or.inl hs', rfl⟩
    · obtain ⟨ha, hb⟩ := mem_topPairs.1 hab
      obtain ⟨a, ha', rfl⟩ := (mem_topPartSwaps hd).1 ha
      obtain ⟨b, hb', rfl⟩ := (mem_topPartSwaps hd).1 hb
      exact ⟨a * b, Or.inr ⟨a, b, ha', hb', rfl⟩, rawMul_encPerm m a b⟩
  · rintro ⟨s, hs | ⟨a, b, ha, hb, rfl⟩, rfl⟩
    · exact Or.inl ((mem_topPartSwaps hd).2 ⟨s, hs, rfl⟩)
    · exact Or.inr ⟨(encPerm m a, encPerm m b), mem_topPairs.2
        ⟨(mem_topPartSwaps hd).2 ⟨a, ha, rfl⟩,
          (mem_topPartSwaps hd).2 ⟨b, hb, rfl⟩⟩, rawMul_encPerm m a b⟩

/-- Keep precisely the candidates in the given image group. -/
def topImageStab (p : (List ℕ × RawGens) × List ℕ) : RawGens :=
  (topCandidates (p.1.1, p.2)).filter (fun r => rawMem (p.1, r))

theorem polyFun_topImageStab : PolyFun topImageStab :=
  (polyFun_fst.pair (((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp
    polyFun_topCandidates)).comp (PolyFun.filterParam polyFun_rawMem)

theorem wf_topImageStab {m : ℕ} {dom C : List ℕ} (hd : dom.length = m) (rs : RawGens) :
    RawGens.WF m (topImageStab ((dom, rs), C)) := by
  intro r hr
  obtain ⟨s, _, rfl⟩ := (mem_topCandidates hd).1 (List.mem_filter.1 hr).1
  exact wf_encPerm m s

/-- Sec. 12, Proposition 12.0.9: the computed top generators give the full
set stabilizer when the top group contains the alternating group. -/
theorem decGroup_topImageStab {m : ℕ} {dom C : List ℕ} (hd : dom.length = m)
    (imgs : List (Perm (Fin m))) (hgiant : alternatingGroup (Fin m) ≤ genGroup imgs) :
    decGroup m (topImageStab ((dom, imgs.map (encPerm m)), C)) =
      Babai.setwiseStabilizer (genGroup imgs) (winSet m C) := by
  have hmem : ∀ s : Perm (Fin m),
      encPerm m s ∈ topCandidates (dom, C) → s ∈ genGroup imgs →
        s ∈ decGroup m (topImageStab ((dom, imgs.map (encPerm m)), C)) := by
    intro s hs hH
    apply Subgroup.subset_closure
    exact List.mem_map.2 ⟨encPerm m s,
      List.mem_filter.2 ⟨hs, (rawMem_spec dom hd imgs s).2 hH⟩, decPerm_encPerm m s⟩
  apply le_antisymm
  · apply (Subgroup.closure_le _).2
    intro s hs
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hs
    obtain ⟨hc, hm⟩ := List.mem_filter.1 hr
    obtain ⟨s, hsc, rfl⟩ := (mem_topCandidates hd).1 hc
    rw [decPerm_encPerm]
    refine ⟨(rawMem_spec dom hd imgs s).1 hm, ?_⟩
    rcases hsc with hsc | ⟨a, b, ha, hb, rfl⟩
    · exact hsc.image
    · exact ((Babai.setwiseStabilizer ⊤ (winSet m C)).mul_mem
        ⟨Subgroup.mem_top _, ha.image⟩ ⟨Subgroup.mem_top _, hb.image⟩).2
  · apply giant_stabilizer_le _ _ _ hgiant
    · intro s hs hH
      exact hmem s ((mem_topCandidates hd).2 ⟨s, Or.inl hs, rfl⟩) hH
    · intro s t hs ht
      exact hmem (s * t)
        ((mem_topCandidates hd).2 ⟨s * t, Or.inr ⟨s, t, hs, ht, rfl⟩, rfl⟩)
        (hgiant (mul_mem_alternatingGroup_of_isSwap hs.isSwap ht.isSwap))

/-! ## Lifting a subgroup of the top group -/

variable {n m : ℕ} {gens : List (Perm (Fin n))} {imgs : List (Perm (Fin m))}

theorem ImgsOf.range_eq_genGroup {ϕ : genGroup gens →* Perm (Fin m)}
    (hI : ImgsOf gens imgs ϕ) : ϕ.range = genGroup imgs := by
  refine (range_eq_closure_gens ϕ).trans ?_
  congr 1
  ext y
  constructor
  · rintro ⟨g, hg, hgen, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hgen
    have hi' : i < imgs.length := by rw [← hI.1]; exact hi
    exact (hI.2 i hi hi') ▸ List.getElem_mem hi'
  · intro hy
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
    have hi' : i < gens.length := by rw [hI.1]; exact hi
    exact ⟨gens[i], Subgroup.subset_closure (List.getElem_mem hi'),
      List.getElem_mem hi', hI.2 i hi' hi⟩

/-- Lift each top generator and add generators of the kernel. -/
def actLiftGens (p : RawAction × RawGens) : RawGens :=
  p.2.map (fun r => (actPreimage (p.1, r)).getD (rawOne p.1.1.1)) ++ actKerGens p.1

theorem polyFun_actLiftGens : PolyFun actLiftGens := by
  have h : PolyFun (fun p : RawAction × RawPerm =>
      (actPreimage p).getD (rawOne p.1.1.1)) :=
    (polyFun_actPreimage.pair
      (((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_rawOne)).comp
        polyFun_optionGetD
  exact ((PolyFun.mapParam h).pair (polyFun_fst.comp polyFun_actKerGens)).comp polyFun_append

/-- Sec. 12, Proposition 12.0.9, the preimage step. Lifts of generators
together with the kernel generate the full subgroup preimage. -/
theorem decGroup_actLiftGens {dom gdom : List ℕ} (hd : dom.length = n) (hm : gdom.length = m)
    {ϕ : genGroup gens →* Perm (Fin m)} (hI : ImgsOf gens imgs ϕ)
    (ts : List (Perm (Fin m))) (ht : genGroup ts ≤ ϕ.range) :
    decGroup n (actLiftGens (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))),
      ts.map (encPerm m))) = (Subgroup.comap ϕ (genGroup ts)).map (genGroup gens).subtype := by
  let p : RawAction := ((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m)))
  let as : RawGens := (ts.map (encPerm m)).map
    (fun r => (actPreimage (p, r)).getD (rawOne dom))
  let L := decGroup n (as ++ actKerGens p)
  have hk : decGroup n (actKerGens p) = actKer gens ϕ := decGroup_actKerGens hd hm hI
  have hak : decGroup n as ≤ L := by
    dsimp only [L]; rw [decGroup_append]; exact le_sup_left
  have hker : actKer gens ϕ ≤ L := by
    dsimp only [L]; rw [decGroup_append, hk]; exact le_sup_right
  have hlift : ∀ t ∈ ts, ∃ (s : Perm (Fin n)) (hs : s ∈ genGroup gens),
      (actPreimage (p, encPerm m t)).getD (rawOne dom) = encPerm n s ∧ ϕ ⟨s, hs⟩ = t := by
    intro t ht'
    have htmem := ht (Subgroup.subset_closure ht')
    cases he : actPreimage (p, encPerm m t) with
    | none => exact False.elim ((actPreimage_eq_none_iff hd hm hI t).1 he htmem)
    | some r =>
      obtain ⟨s, hs, hr, hst⟩ := actPreimage_eq_some hd hm hI t he
      exact ⟨s, hs, hr, hst⟩
  have hliftL : ∀ t ∈ ts, ∃ s : genGroup gens, s.val ∈ L ∧ ϕ s = t := by
    intro t ht'
    obtain ⟨s, hs, he, ht''⟩ := hlift t ht'
    refine ⟨⟨s, hs⟩, hak (Subgroup.subset_closure ?_), ht''⟩
    refine List.mem_map.2 ⟨(actPreimage (p, encPerm m t)).getD (rawOne dom), ?_, ?_⟩
    · exact List.mem_map.2 ⟨encPerm m t, List.mem_map.2 ⟨t, ht', rfl⟩, rfl⟩
    · rw [he, decPerm_encPerm]
  change L = _
  apply le_antisymm
  · change decGroup n (as ++ actKerGens p) ≤ _
    rw [decGroup_append, hk]
    refine sup_le ?_ ?_
    · apply (Subgroup.closure_le _).2
      intro z hz
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hz
      obtain ⟨r, hr', rfl⟩ := List.mem_map.1 hr
      obtain ⟨t, ht', rfl⟩ := List.mem_map.1 hr'
      obtain ⟨s, hs, he, hst⟩ := hlift t ht'
      rw [he, decPerm_encPerm]
      refine ⟨⟨s, hs⟩, ?_, rfl⟩
      change ϕ ⟨s, hs⟩ ∈ genGroup ts
      rw [hst]
      exact Subgroup.subset_closure ht'
    · rintro z ⟨s, hs, rfl⟩
      refine ⟨s, ?_, rfl⟩
      change ϕ s ∈ genGroup ts
      rw [MonoidHom.mem_ker.1 hs]
      exact Subgroup.one_mem _
  · let K := L.comap (genGroup gens).subtype
    have hmap : genGroup ts ≤ K.map ϕ := by
      apply (Subgroup.closure_le _).2
      intro t ht'
      obtain ⟨s, hs, he⟩ := hliftL t ht'
      exact ⟨s, hs, he⟩
    rintro z ⟨s, hs, rfl⟩
    obtain ⟨t, htK, he⟩ := hmap hs
    have hkt : s * t⁻¹ ∈ ϕ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, he, mul_inv_cancel]
    have hkL : (s * t⁻¹).val ∈ L := hker ⟨s * t⁻¹, hkt, rfl⟩
    have htL : t.val ∈ L := htK
    simpa using L.mul_mem hkL htL

/-- Sec. 12, Proposition 12.0.9: compute the set stabilizer through the
action, then shorten the resulting generators. -/
def topStab (p : RawAction × List ℕ) : RawGens :=
  tidyGens (p.1.1.1, actLiftGens (p.1, topImageStab (p.1.2, p.2)))

theorem polyFun_topStab : PolyFun topStab :=
  (((polyFun_fst.comp polyFun_fst).comp polyFun_fst).pair
    ((polyFun_fst.pair (((polyFun_fst.comp polyFun_snd).pair polyFun_snd).comp
      polyFun_topImageStab)).comp polyFun_actLiftGens)).comp polyFun_tidyGens

/-- Sec. 12, Proposition 12.0.9: the raw answer decodes to `G_C`, with
the subgroup of `G` included into the full symmetric group by `G.subtype`. -/
theorem decGroup_topStab {dom gdom C : List ℕ} (hd : dom.length = n) (hm : gdom.length = m)
    {ϕ : genGroup gens →* Perm (Fin m)} (hI : ImgsOf gens imgs ϕ)
    (hgiant : Babai.IsGiantRep ϕ) :
    decGroup n (topStab (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), C)) =
      (Babai.setwiseStabViaHom ϕ (winSet m C)).map (genGroup gens).subtype := by
  let ts := topImageStab ((gdom, imgs.map (encPerm m)), C)
  have hts : RawGens.WF m ts := wf_topImageStab hm _
  have htop : decGroup m ts = Babai.setwiseStabilizer ϕ.range (winSet m C) := by
    rw [hI.range_eq_genGroup]
    exact decGroup_topImageStab hm imgs (by rw [← hI.range_eq_genGroup]; exact hgiant)
  have hsub : genGroup (ts.map (decPerm m)) ≤ ϕ.range := by
    change decGroup m ts ≤ _
    rw [htop]
    exact fun _ h => h.1
  rw [topStab, decGroup_tidyGens hd]
  change decGroup n (actLiftGens (_, ts)) = _
  conv_lhs => rw [← map_encPerm_decPerm hts]
  rw [decGroup_actLiftGens hd hm hI _ hsub]
  change (Subgroup.comap ϕ (decGroup m ts)).map _ = _
  rw [htop, ← Babai.Proposition_12_0_9 ϕ hgiant]

/-- The answer uses at most `n²` well-formed generators. -/
theorem topStab_wf {p : RawAction × List ℕ} (hd : p.1.1.1.length = n) :
    RawGens.WF n (topStab p) ∧ (topStab p).length ≤ n * n :=
  ⟨wf_tidyGens hd _, length_tidyGens hd _⟩

/-- Proposition 12.0.9 on arbitrary well-formed raw input. -/
theorem topStab_spec_of_wf (p : RawAction × List ℕ)
    (ϕ : decGroup n p.1.1.2 →* Perm (Fin m))
    (hp : RawAction.WF n m p.1 ϕ) (hgiant : Babai.IsGiantRep ϕ) :
    decGroup n (topStab p) =
      (Babai.setwiseStabViaHom ϕ (winSet m p.2)).map (decGroup n p.1.1.2).subtype := by
  obtain ⟨hd, hm, hgs, his, hI⟩ := hp
  have h := decGroup_topStab (C := p.2) hd hm hI hgiant
  rwa [map_encPerm_decPerm hgs, map_encPerm_decPerm his] at h

end Algo
