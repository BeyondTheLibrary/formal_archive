/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: Procedure Align, lines 7–11 (§14.1) — the orbits of
`G*` in the dominant window, a dominant orbit first, and the test between case 1 and cases
2–3 of the repair.
-/
import Workspace.Algo.AlignDomShape
import Workspace.Algo.TopOrbits
import Workspace.Algo.TestSetNaming

/-!
# The orbits of `G*` in the dominant window, and the size test of `m*`

In cases 2 and 3 of the repair of lines 7–11 the round on the dominant
window `Ω(Δ_j)` is the Chain Rule over the orbits of `G*` in that window, with a dominant
orbit (one of more than `2n/3` points) first. Here `G* = G₁ = ϕ⁻¹(Aut(X'))`, whose
generators the machine holds after line 2 of Procedure Align.

* `Algo.alignDomOrbits` lists those orbits: the orbits in the window (`Algo.winOrbits`), the
  large ones first. At most one orbit is large, so the list is the one the Master side asks
  for (`Babai.AlignDominantEnum.Spec`, clauses `orbits` and `first`):
  `Algo.perm_alignDomOrbits` and `Algo.alignDomOrbits_first`.
* `Algo.rawMaxOrbit` is the length of a longest orbit, `Babai.maxOrbitLength`
  (`Algo.rawMaxOrbit_eq`).
* `Algo.rawVeryLarge` decides `Babai.VeryLargeK` (`Algo.rawVeryLarge_iff`), the test that
  tells case 1 of the repair from cases 2 and 3 (`Babai.AlignDominantRoundData.LargeParam`).
-/

namespace Algo
open RAM RAM.Targets Babai Equiv MulAction

/-! ## The orbits in the window, a large one first -/

/-- An orbit (as a list of points) is large when it has more than `2n/3` points. -/
def alignDomBig (p : ℕ × List ℕ) : Bool := decide (2 * p.1 < 3 * p.2.length)

/-- The large entries first, then the others, each part in the given order. -/
def alignDomFirst (p : ℕ × List (List ℕ)) : List (List ℕ) :=
  p.2.filter (fun O => alignDomBig (p.1, O)) ++ p.2.filter (fun O => !alignDomBig (p.1, O))

/-- §14.1, lines 7–11, cases 2 and 3 of the repair: **the orbits of `G*` in the dominant
window, a dominant orbit first**. The input is the generators of `G*`, the window and the
degree `n`. -/
def alignDomOrbits (p : (RawGens × List ℕ) × ℕ) : List (List ℕ) :=
  alignDomFirst (p.2, winOrbits p.1)

theorem perm_alignDomFirst (p : ℕ × List (List ℕ)) : (alignDomFirst p).Perm p.2 := by
  unfold alignDomFirst
  exact List.filter_append_perm _ _

section Spec

variable {n : ℕ} {gs : RawGens} {win : List ℕ}

theorem nodup_decoded_winOrbits' (hgs : RawGens.WF n gs) (hlt : ∀ j ∈ win, j < n) :
    ((winOrbits (gs, win)).map (winSet n)).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  apply List.pairwise_iff_getElem.2
  intro i j hi hj hij he
  have hwi := List.getElem_mem hi
  obtain ⟨a, ha, heq⟩ := winOrbits_mem hwi
  have han := hlt a ha
  have hamem : a ∈ (winOrbits (gs, win))[i] := by
    rw [heq]
    exact (mem_rawOrbit_iff hgs han a).2 ⟨han, mem_orbit_self _⟩
  have hother : a ∈ (winOrbits (gs, win))[j] :=
    show (⟨a, han⟩ : Fin n) ∈ winSet n _ from he ▸ hamem
  exact (List.pairwise_iff_getElem.1 (winOrbits_pairwise hgs hlt) i j hi hj hij) a hamem hother

/-- Every listed orbit, read as a set, is an orbit of `G*` inside the window. -/
theorem mem_orbitListOn_of_winOrbits (hgs : RawGens.WF n gs) (hlt : ∀ j ∈ win, j < n)
    (hinv : rawIsInvariant (gs, win) = true) {O : List ℕ} (hO : O ∈ winOrbits (gs, win)) :
    winSet n O ∈ orbitListOn (decGroup n gs) (winSet n win) := by
  rw [mem_orbitListOn]
  obtain ⟨i, hi, rfl⟩ := winOrbits_mem hO
  have hin : i < n := hlt i hi
  refine ⟨?_, ?_⟩
  · rw [winSet_rawOrbit hgs ⟨i, hin⟩]
    exact orbit_mem_orbitList _ _
  · intro u hu
    exact winOrbits_subset hgs hlt hinv hO u hu

/-- **The orbits of `G*` in the window, listed once each** (the clause `orbits` of
`Babai.AlignDominantEnum.Spec`). -/
theorem perm_alignDomOrbits (hgs : RawGens.WF n gs) (hlt : ∀ j ∈ win, j < n)
    (hinv : rawIsInvariant (gs, win) = true) :
    ((alignDomOrbits ((gs, win), n)).map (winSet n)).Perm
      (orbitListOn (decGroup n gs) (winSet n win)) := by
  classical
  refine ((perm_alignDomFirst (n, winOrbits (gs, win))).map (winSet n)).trans ?_
  have hn := nodup_decoded_winOrbits' hgs hlt
  have ho := nodup_orbitListOn (decGroup n gs) (winSet n win)
  have hf : (winOrbits (gs, win)).map (winSet n) ⊆ orbitListOn (decGroup n gs) (winSet n win) := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hw
    exact mem_orbitListOn_of_winOrbits hgs hlt hinv hv
  have hb : orbitListOn (decGroup n gs) (winSet n win) ⊆ (winOrbits (gs, win)).map (winSet n) := by
    intro w hw
    obtain ⟨hw1, hw2⟩ := mem_orbitListOn.1 hw
    obtain ⟨u, rfl⟩ := mem_orbitList hw1
    have hu : u ∈ winSet n win := hw2 (mem_orbit_self u)
    have hc : u ∈ ⋃ v ∈ (winOrbits (gs, win)).map (winSet n), v := by
      rw [iUnion_winOrbits hgs hlt hinv]; exact hu
    obtain ⟨v, hv, huv⟩ := Set.mem_iUnion₂.1 hc
    obtain ⟨O, hO, rfl⟩ := List.mem_map.1 hv
    obtain ⟨i, hi, rfl⟩ := winOrbits_mem hO
    have hin : i < n := hlt i hi
    rw [winSet_rawOrbit hgs ⟨i, hin⟩] at huv
    have he : orbit (decGroup n gs) u = orbit (decGroup n gs) (⟨i, hin⟩ : Fin n) :=
      orbit_eq_iff.2 huv
    rw [he]
    exact List.mem_map.2 ⟨rawOrbit (gs, i), hO, winSet_rawOrbit hgs ⟨i, hin⟩⟩
  exact (hn.subperm hf).antisymm (ho.subperm hb)

/-- A listed orbit has as many points as entries. -/
theorem ncard_winSet_winOrbits (hgs : RawGens.WF n gs) (hlt : ∀ j ∈ win, j < n)
    (hinv : rawIsInvariant (gs, win) = true) {O : List ℕ} (hO : O ∈ winOrbits (gs, win)) :
    (winSet n O).ncard = O.length :=
  ncard_winSet O (winOrbits_nodup hO) (winOrbits_lt hgs hlt hinv hO)

/-- **A dominant orbit comes first** (the clause `first` of
`Babai.AlignDominantEnum.Spec`): two disjoint sets cannot both have more than `2n/3` points,
so at most one orbit is large, and it heads the list. -/
theorem alignDomOrbits_first (hgs : RawGens.WF n gs) (hlt : ∀ j ∈ win, j < n)
    (hinv : rawIsInvariant (gs, win) = true) :
    ∀ S ∈ (alignDomOrbits ((gs, win), n)).map (winSet n), 2 * n < 3 * S.ncard →
      ∃ rest, (alignDomOrbits ((gs, win), n)).map (winSet n) = S :: rest ∧ S ∉ rest := by
  classical
  intro S hS hbig
  set L := winOrbits (gs, win) with hL
  obtain ⟨O, hO, rfl⟩ := List.mem_map.1 hS
  have hOL : O ∈ L := (perm_alignDomFirst (n, L)).subset hO
  have hlen : ∀ P ∈ L, (winSet n P).ncard = P.length := fun P hP =>
    ncard_winSet_winOrbits hgs hlt hinv hP
  have hbigO : alignDomBig (n, O) = true := by
    unfold alignDomBig
    rw [decide_eq_true_iff, ← hlen O hOL]
    exact hbig
  -- any large entry of the list is `O`
  have huniq : ∀ P ∈ L, alignDomBig (n, P) = true → P = O := by
    intro P hP hPb
    by_contra hne
    have hpw := winOrbits_pairwise hgs hlt (gs := gs) (Δ := win)
    have hdisj : Disjoint (winSet n P) (winSet n O) := by
      rw [Set.disjoint_left]
      intro u hu hu'
      obtain ⟨i, hi, hiP⟩ := List.mem_iff_getElem.1 hP
      obtain ⟨k, hk, hkO⟩ := List.mem_iff_getElem.1 hOL
      have hik : i ≠ k := by
        rintro rfl
        exact hne (hiP.symm.trans hkO)
      rcases lt_or_gt_of_ne hik with h | h
      · have := List.pairwise_iff_getElem.1 hpw i k hi hk h (u : ℕ)
        rw [hiP, hkO] at this
        exact this hu hu'
      · have := List.pairwise_iff_getElem.1 hpw k i hk hi h (u : ℕ)
        rw [hiP, hkO] at this
        exact this hu' hu
    have hsum : (winSet n P).ncard + (winSet n O).ncard ≤ n := by
      rw [← Set.ncard_union_eq hdisj]
      have := Set.ncard_le_card (winSet n P ∪ winSet n O)
      simpa using this
    unfold alignDomBig at hPb hbigO
    rw [decide_eq_true_iff] at hPb hbigO
    rw [hlen P hP, hlen O hOL] at hsum
    change 2 * n < 3 * P.length at hPb
    change 2 * n < 3 * O.length at hbigO
    omega
  -- the large part of the list is `[O]`
  have hnd : L.Nodup := by
    have := nodup_decoded_winOrbits' hgs hlt (gs := gs) (win := win)
    exact List.Nodup.of_map _ this
  have hfilt : L.filter (fun P => alignDomBig (n, P)) = [O] := by
    have hnd' : (L.filter (fun P => alignDomBig (n, P))).Nodup := hnd.filter _
    have hmem : ∀ P, P ∈ L.filter (fun P => alignDomBig (n, P)) ↔ P = O := by
      intro P
      rw [List.mem_filter]
      constructor
      · rintro ⟨hP, hPb⟩; exact huniq P hP hPb
      · rintro rfl; exact ⟨hOL, hbigO⟩
    generalize L.filter (fun P => alignDomBig (n, P)) = l at hnd' hmem
    match l, hnd', hmem with
    | [], _, hm => exact absurd ((hm O).2 rfl) List.not_mem_nil
    | [a], _, hm => rw [(hm a).1 List.mem_cons_self]
    | a :: b :: t, hd, hm =>
      have ha := (hm a).1 List.mem_cons_self
      have hb := (hm b).1 (List.mem_cons_of_mem _ List.mem_cons_self)
      exact ((List.nodup_cons.1 hd).1 (by rw [ha, ← hb]; exact List.mem_cons_self)).elim
  refine ⟨(L.filter (fun P => !alignDomBig (n, P))).map (winSet n), ?_, ?_⟩
  · change (alignDomFirst (n, L)).map (winSet n) = _
    rw [alignDomFirst]
    dsimp only
    rw [hfilt]
    rfl
  · intro hmem
    obtain ⟨P, hP, hPe⟩ := List.mem_map.1 hmem
    rw [List.mem_filter] at hP
    have hPL := hP.1
    have hPs : alignDomBig (n, P) = false := by simpa using hP.2
    unfold alignDomBig at hPs
    rw [decide_eq_false_iff_not, ← hlen P hPL, hPe, hlen O hOL] at hPs
    exact hPs (by rw [hlen O hOL] at hbig; exact hbig)

end Spec

/-! ## The longest orbit and the size test -/

/-- The length of a longest orbit, over the domain given by the list `dom`. -/
def rawMaxOrbit (p : RawGens × List ℕ) : ℕ :=
  ((rawOrbits p).map List.length).foldl max 0

/-- §14.1, lines 7–11: **the size test** of the repair, `Babai.VeryLargeK k L`, that is
`max(9, 2 log₂ L) ≤ k`, decided as `9 ≤ k` and `L² ≤ 2^k`. -/
def rawVeryLarge (p : ℕ × ℕ) : Bool := decide (9 ≤ p.1) && decide (Nat.size (p.2 * p.2 - 1) ≤ p.1)

/-- The bit length decides the power bound. -/
theorem size_pred_le_iff (x k : ℕ) : Nat.size (x - 1) ≤ k ↔ x ≤ 2 ^ k := by
  rw [Nat.size_le]
  have := Nat.one_le_two_pow (n := k)
  omega

theorem rawVeryLarge_iff (k L : ℕ) : rawVeryLarge (k, L) = true ↔ VeryLargeK k L := by
  unfold rawVeryLarge VeryLargeK
  rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff, size_pred_le_iff, max_le_iff]
  have h9 : ((9 : ℝ) ≤ (k : ℝ)) ↔ 9 ≤ k := by exact_mod_cast Iff.rfl
  rw [h9]
  refine and_congr Iff.rfl ?_
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · simp
  · have hLr : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
    have hLL : (0 : ℝ) < (L : ℝ) * (L : ℝ) := mul_pos hLr hLr
    have hlog : 2 * Real.logb 2 (L : ℝ) = Real.logb 2 ((L : ℝ) * (L : ℝ)) := by
      rw [Real.logb_mul hLr.ne' hLr.ne']; ring
    rw [hlog, Real.logb_le_iff_le_rpow (by norm_num) hLL, Real.rpow_natCast]
    constructor
    · intro h; exact_mod_cast h
    · intro h; exact_mod_cast h

section MaxOrbit

variable {n : ℕ} {gs : RawGens} {dom : List ℕ}

private theorem foldl_max_spec' (l : List ℕ) (a : ℕ) :
    a ≤ l.foldl max a ∧ (∀ x ∈ l, x ≤ l.foldl max a) ∧ (l.foldl max a = a ∨ l.foldl max a ∈ l) := by
  induction l generalizing a with
  | nil => simp
  | cons x rest ih =>
    rw [List.foldl_cons]
    obtain ⟨h1, h2, h3⟩ := ih (max a x)
    refine ⟨le_trans (le_max_left _ _) h1, ?_, ?_⟩
    · intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact le_trans (le_max_right _ _) h1
      · exact h2 y hy
    · rcases h3 with h | h
      · rcases le_total a x with hle | hle
        · right; rw [h, max_eq_right hle]; exact List.mem_cons_self
        · left; rw [h, max_eq_left hle]
      · right; exact List.mem_cons_of_mem _ h

private theorem foldl_max_spec (l : List (List ℕ)) :
    (∀ O ∈ l, O.length ≤ (l.map List.length).foldl max 0) ∧
      ((l.map List.length).foldl max 0 = 0 ∨
        ∃ O ∈ l, (l.map List.length).foldl max 0 = O.length) := by
  obtain ⟨-, h2, h3⟩ := foldl_max_spec' (l.map List.length) 0
  refine ⟨fun O hO => h2 _ (List.mem_map_of_mem hO), ?_⟩
  rcases h3 with h | h
  · exact Or.inl h
  · obtain ⟨O, hO, he⟩ := List.mem_map.1 h
    exact Or.inr ⟨O, hO, he.symm⟩

/-- **The longest orbit** (`Babai.maxOrbitLength`). -/
theorem rawMaxOrbit_eq (hgs : RawGens.WF n gs) (hd : dom.length = n) :
    rawMaxOrbit (gs, dom) = maxOrbitLength (decGroup n gs) := by
  classical
  obtain ⟨h2, h3⟩ := foldl_max_spec (rawOrbits (gs, dom))
  have hcard : ∀ O ∈ rawOrbits (gs, dom), ∃ u : Fin n, O.length = Nat.card (orbit (decGroup n gs) u) := by
    intro O hO
    obtain ⟨j, hj, rfl⟩ := rawOrbits_mem hgs hd hO
    refine ⟨⟨j, hj⟩, ?_⟩
    have hlt : ∀ k ∈ rawOrbit (gs, j), k < n := fun k hk =>
      ((mem_rawOrbit_iff hgs hj k).1 hk).1
    rw [Nat.card_coe_set_eq, ← winSet_rawOrbit hgs ⟨j, hj⟩,
      ncard_winSet _ (nodup_rawOrbit gs j) hlt]
  apply le_antisymm
  · rcases h3 with h | ⟨O, hO, he⟩
    · unfold rawMaxOrbit; rw [h]; exact Nat.zero_le _
    · unfold rawMaxOrbit
      rw [he]
      obtain ⟨u, hu⟩ := hcard O hO
      rw [hu]
      exact le_csSup (bddAbove_orbitLengths _) ⟨u, rfl⟩
  · rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have : IsEmpty (Fin 0) := inferInstance
      unfold maxOrbitLength
      have he : {m | ∃ x : Fin 0, Nat.card (orbit (decGroup 0 gs) x) = m} = ∅ := by
        ext m; simp
      rw [he, csSup_empty]
      exact bot_le
    · apply csSup_le (Set.nonempty_of_mem (show Nat.card (orbit (decGroup n gs) (⟨0, hn⟩ : Fin n)) ∈
        {m | ∃ x : Fin n, Nat.card (orbit (decGroup n gs) x) = m} from ⟨⟨0, hn⟩, rfl⟩))
      rintro _ ⟨u, rfl⟩
      have hc := rawOrbits_cover hgs hd u.isLt
      obtain ⟨O, hO, hu⟩ := List.mem_flatten.1 hc
      obtain ⟨j, hj, rfl⟩ := rawOrbits_mem hgs hd hO
      have hlt : ∀ k ∈ rawOrbit (gs, j), k < n := fun k hk =>
        ((mem_rawOrbit_iff hgs hj k).1 hk).1
      have huo : u ∈ orbit (decGroup n gs) (⟨j, hj⟩ : Fin n) :=
        ((mem_rawOrbit_iff hgs hj u).1 hu).2
      have he : orbit (decGroup n gs) u = orbit (decGroup n gs) (⟨j, hj⟩ : Fin n) :=
        orbit_eq_iff.2 huo
      rw [Nat.card_coe_set_eq, he, ← winSet_rawOrbit hgs ⟨j, hj⟩,
        ncard_winSet _ (nodup_rawOrbit gs j) hlt]
      exact h2 _ hO

end MaxOrbit

/-! ## Running time -/

private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd

theorem polyFun_alignDomBig : PolyFun alignDomBig := by
  have i : PolyFun (fun p : ℕ × List ℕ => p) := polyFun_id
  have hl : PolyFun (fun p : ℕ × List ℕ => 3 * p.2.length) :=
    (polyFun_const 3).mul ((psnd i).comp polyFun_length)
  have hr : PolyFun (fun p : ℕ × List ℕ => 2 * p.1 + 1) :=
    ((polyFun_const 2).mul (pfst i)).add (polyFun_const 1)
  exact (hr.le hl).of_eq (fun p => by unfold alignDomBig; simp only [decide_eq_decide]; omega)

theorem polyFun_alignDomFirst : PolyFun alignDomFirst := by
  have i : PolyFun (fun p : ℕ × List (List ℕ) => p) := polyFun_id
  have hb : PolyFun (fun r : ℕ × List ℕ => !alignDomBig r) :=
    (PolyFun.ite polyFun_alignDomBig (polyFun_const false) (polyFun_const true)).of_eq
      (fun r => by cases alignDomBig r <;> rfl)
  have h1 : PolyFun (fun p : ℕ × List (List ℕ) => p.2.filter (fun O => alignDomBig (p.1, O))) :=
    i.comp (PolyFun.filterParam polyFun_alignDomBig)
  have h2 : PolyFun (fun p : ℕ × List (List ℕ) => p.2.filter (fun O => !alignDomBig (p.1, O))) :=
    i.comp (PolyFun.filterParam hb)
  exact ((h1.pair h2).comp polyFun_append).of_eq (fun _ => rfl)

theorem polyFun_alignDomOrbits : PolyFun alignDomOrbits :=
  ((psnd polyFun_id).pair ((pfst polyFun_id).comp polyFun_winOrbits)).comp polyFun_alignDomFirst

private theorem polyFun_listMax : PolyFun (fun l : List ℕ => l.foldl max 0) := by
  have hf : PolyFun (fun z : ℕ × ℕ => max z.1 z.2) := polyFun_max
  have hacc : ∀ (a : ℕ) (l : List ℕ) (j : ℕ),
      Enc.size ((l.take j).foldl max a) ≤ Enc.size (a, l) := by
    intro a l j
    rcases (foldl_max_spec' (l.take j) a).2.2 with he | hm
    · rw [he]; exact Combine.size_fst_le _ _
    · exact le_trans (size_mem_le (List.mem_of_mem_take hm)) (Combine.size_snd_le _ _)
  exact (((polyFun_const (0 : ℕ)).pair polyFun_id).comp
    (PolyFun.foldl hf polyBound_id hacc)).of_eq (fun _ => rfl)

theorem polyFun_rawMaxOrbit : PolyFun rawMaxOrbit :=
  ((polyFun_rawOrbits.comp (PolyFun.map polyFun_length)).comp polyFun_listMax).of_eq
    (fun _ => rfl)

theorem polyFun_rawVeryLarge : PolyFun rawVeryLarge := by
  have i : PolyFun (fun p : ℕ × ℕ => p) := polyFun_id
  have h9 : PolyFun (fun p : ℕ × ℕ => decide (9 ≤ p.1)) := (polyFun_const 9).le (pfst i)
  have hs : PolyFun (fun p : ℕ × ℕ => decide (Nat.size (p.2 * p.2 - 1) ≤ p.1)) :=
    ((PolyFun.sub ((psnd i).mul (psnd i)) (polyFun_const 1)).comp polyFun_natSize).le (pfst i)
  exact polyFun_and h9 hs

end Algo
