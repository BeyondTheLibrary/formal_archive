import Workspace.Refinement.WL
import Workspace.Algo.RefineRaw

/-!
# Named binary WL refinement

Section 4.1.1 replaces each tag by its rank among the tags that occur. We keep that
rank at each round. The count coordinates use the order of `Algo.innerVec` at arity
two: the incoming color comes first. Thus the tags have the order used by the raw
routine, even when the input names have gaps.
-/

namespace Babai.WL

variable {V W : Type*} [Fintype V] [DecidableEq V]

/-- Section 4.1.1: the number of occurring tags smaller than this tag. The comparison
is the explicit lexicographic comparison of equal-length lists of naturals. -/
def namedRank (D : Finset (List ℕ)) (t : List ℕ) : ℕ :=
  (D.filter fun s => Algo.cmpRec s t = 1).card

theorem namedRank_eq_rankIn (D : Finset (List ℕ)) (t : List ℕ) :
    namedRank D t = Algo.rankIn (D.toList, t) := by
  classical
  simp only [namedRank, Algo.rankIn, Algo.lexLtB_eq]
  rw [← List.toFinset_card_of_nodup (D.nodup_toList.filter _)]
  simp only [List.toFinset_filter, Finset.toList_toFinset, decide_eq_true_eq]

theorem namedRank_inj {D : Finset (List ℕ)} {L : ℕ}
    (hlen : ∀ t ∈ D, t.length = L) {s t : List ℕ} (hs : s ∈ D) (ht : t ∈ D) :
    namedRank D s = namedRank D t ↔ s = t := by
  classical
  constructor
  · simpa only [namedRank_eq_rankIn] using
      Algo.rankIn_inj (fun u hu => hlen u (Finset.mem_toList.1 hu))
        (Finset.mem_toList.2 hs) (Finset.mem_toList.2 ht)
  · rintro rfl; rfl

theorem namedRank_lt {D : Finset (List ℕ)} {t : List ℕ} (ht : t ∈ D) :
    namedRank D t < D.card := by
  classical
  simpa only [namedRank_eq_rankIn, Finset.length_toList] using
    Algo.rankIn_lt_length (Finset.mem_toList.2 ht)

theorem namedRank_image {D : Finset (List ℕ)} {L : ℕ}
    (hlen : ∀ t ∈ D, t.length = L) :
    D.image (namedRank D) = Finset.range D.card := by
  apply Finset.eq_of_subset_of_card_le
  · intro i hi
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hi
    exact Finset.mem_range.2 (namedRank_lt ht)
  · rw [Finset.card_range, Finset.card_image_iff.2]
    intro s hs t ht he
    exact (namedRank_inj hlen hs ht).1 he

/-- The two old colors seen through an intermediate vertex, in raw tuple order. -/
def namedVec (c : V → V → ℕ) (u v w : V) : List ℕ := [c w v, c u w]

/-- Only count coordinates that occur somewhere are needed. -/
def namedVecs (c : V → V → ℕ) : Finset (List ℕ) :=
  Finset.univ.image fun p : V × V × V => namedVec c p.1 p.2.1 p.2.2

theorem namedVec_mem (c : V → V → ℕ) (u v w : V) : namedVec c u v w ∈ namedVecs c :=
  Finset.mem_image.2 ⟨(u, v, w), Finset.mem_univ _, rfl⟩

theorem namedVecs_length (c : V → V → ℕ) (t : List ℕ) (ht : t ∈ namedVecs c) :
    t.length = 2 := by
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.1 ht
  rfl

/-- A count is placed at the lexicographic rank of its pair of old names. -/
def namedCount (c : V → V → ℕ) (u v : V) (i : ℕ) : ℕ :=
  (Finset.univ.filter fun w => namedRank (namedVecs c) (namedVec c u v w) = i).card

/-- Section 4.3: the old name followed by all counts, in the raw routine's order. -/
def namedTag (c : V → V → ℕ) (u v : V) : List ℕ :=
  c u v :: (List.range (namedVecs c).card).map (namedCount c u v)

/-- The set of tags on the actual pairs of vertices. -/
def namedTags (c : V → V → ℕ) : Finset (List ℕ) :=
  Finset.univ.image fun p : V × V => namedTag c p.1 p.2

theorem namedTag_mem (c : V → V → ℕ) (u v : V) : namedTag c u v ∈ namedTags c :=
  Finset.mem_image.2 ⟨(u, v), Finset.mem_univ _, rfl⟩

theorem namedTags_length (c : V → V → ℕ) (t : List ℕ) (ht : t ∈ namedTags c) :
    t.length = (namedVecs c).card + 1 := by
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.1 ht
  simp [namedTag]

/-- Sections 4.1.1 and 4.3: one round followed by renaming to an initial segment. -/
def namedStep (c : V → V → ℕ) (u v : V) : ℕ :=
  namedRank (namedTags c) (namedTag c u v)

/-- Sections 4.1.1 and 4.3: keep the new integer names after every round. -/
def namedIter (c : V → V → ℕ) : ℕ → V → V → ℕ
  | 0 => c
  | r + 1 => namedStep (namedIter c r)

theorem namedCount_at_vec (c : V → V → ℕ) (u v : V) {t : List ℕ}
    (ht : t ∈ namedVecs c) :
    namedCount c u v (namedRank (namedVecs c) t) =
      (Finset.univ.filter fun w => namedVec c u v w = t).card := by
  unfold namedCount
  congr 1
  ext w
  simp only [ Finset.mem_filter, Finset.mem_univ, true_and]
  exact namedRank_inj (namedVecs_length c) (namedVec_mem c u v w) ht

theorem namedTag_eq_iff (c : V → V → ℕ) (u v x y : V) :
    namedTag c u v = namedTag c x y ↔ step c u v = step c x y := by
  classical
  rw [step_eq_iff]
  constructor
  · intro he
    have hh : c u v = c x y := List.cons.inj he |>.1
    have ht := List.map_inj_left.1 (List.cons.inj he |>.2)
    refine ⟨hh, fun i j => ?_⟩
    by_cases hv : [j, i] ∈ namedVecs c
    · have hr := ht (namedRank (namedVecs c) [j, i])
        (List.mem_range.2 (namedRank_lt hv))
      rw [namedCount_at_vec c u v hv, namedCount_at_vec c x y hv] at hr
      simpa [namedVec, and_comm, Set.ncard_eq_toFinset_card'] using hr
    · have hz : ∀ a b : V, {w : V | c a w = i ∧ c w b = j} = ∅ := by
        intro a b
        ext w
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro hi hj
        apply hv
        simpa [namedVec, hi, hj] using namedVec_mem c a b w
      rw [hz u v, hz x y]
  · rintro ⟨hh, hc⟩
    unfold namedTag
    rw [hh]
    congr 1
    apply List.map_congr_left
    intro i hi
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1
      (namedRank_image (namedVecs_length c) ▸ Finset.mem_range.2 (List.mem_range.1 hi))
    obtain ⟨⟨a, b, w⟩, _, rfl⟩ := Finset.mem_image.1 ht
    rw [namedCount_at_vec c u v (namedVec_mem c a b w),
      namedCount_at_vec c x y (namedVec_mem c a b w)]
    simpa [namedVec, and_comm, Set.ncard_eq_toFinset_card'] using hc (c a w) (c w b)

/-- Renaming loses no information about one abstract round. -/
theorem namedStep_eq_iff (c : V → V → ℕ) (u v x y : V) :
    namedStep c u v = namedStep c x y ↔ step c u v = step c x y :=
  (namedRank_inj (namedTags_length c) (namedTag_mem c u v) (namedTag_mem c x y)).trans
    (namedTag_eq_iff c u v x y)

/-- Every named round has exactly the classes of the abstract round. -/
theorem namedIter_eq_iff (c : V → V → ℕ) (r : ℕ) (u v x y : V) :
    namedIter c r u v = namedIter c r x y ↔ iter c r u v = iter c r x y := by
  induction r generalizing u v x y with
  | zero => rfl
  | succ r ih =>
    exact (namedStep_eq_iff _ u v x y).trans (step_congr ih u v x y)

/-- After a round, the names are precisely the integers below the number of classes. -/
theorem namedStep_image (c : V → V → ℕ) :
    Finset.univ.image (fun p : V × V => namedStep c p.1 p.2) =
      Finset.range (namedTags c).card := by
  rw [← namedRank_image (namedTags_length c), namedTags, Finset.image_image]
  rfl

/-- At every positive round the names have no gaps. The range size is the number
of color classes, since these are the fibers of the named coloring. -/
theorem namedIter_image (c : V → V → ℕ) {r : ℕ} (hr : 1 ≤ r) :
    let S := Finset.univ.image (fun p : V × V => namedIter c r p.1 p.2)
    S = Finset.range S.card := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  change Finset.univ.image (fun p : V × V => namedStep (namedIter c k) p.1 p.2) = _
  simp only [namedStep_image, namedIter, Finset.card_range]

section Canonical

variable [Fintype W] [DecidableEq W] {c : V → V → ℕ} {d : W → W → ℕ}
    (φ : V ≃ W) (hc : ∀ u v, d (φ u) (φ v) = c u v)

include hc

theorem namedVecs_map : namedVecs d = namedVecs c := by
  ext t
  simp only [namedVecs, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨a, b, w⟩, rfl⟩
    refine ⟨(φ.symm a, φ.symm b, φ.symm w), ?_⟩
    simp only [namedVec, ← hc, Equiv.apply_symm_apply]
  · rintro ⟨⟨a, b, w⟩, rfl⟩
    exact ⟨(φ a, φ b, φ w), by simp only [namedVec, hc]⟩

theorem namedCount_map (u v : V) (i : ℕ) :
    namedCount d (φ u) (φ v) i = namedCount c u v i := by
  unfold namedCount
  rw [namedVecs_map φ hc]
  symm
  refine Finset.card_bij (fun w _ => φ w) ?_ ?_ ?_
  · intro w hw
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, namedVec, hc] using hw
  · intro a _ b _ hab
    exact φ.injective hab
  · intro w hw
    refine ⟨φ.symm w, ?_, φ.apply_symm_apply w⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, namedVec,
      ← hc, Equiv.apply_symm_apply] using hw

theorem namedTag_map (u v : V) : namedTag d (φ u) (φ v) = namedTag c u v := by
  simp only [namedTag, hc, namedVecs_map φ hc]
  congr 1
  exact List.map_congr_left fun i _ => namedCount_map φ hc u v i

theorem namedTags_map : namedTags d = namedTags c := by
  ext t
  simp only [namedTags, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨a, b⟩, rfl⟩
    exact ⟨(φ.symm a, φ.symm b), by simpa using (namedTag_map φ hc (φ.symm a) (φ.symm b)).symm⟩
  · rintro ⟨⟨a, b⟩, rfl⟩
    exact ⟨(φ a, φ b), namedTag_map φ hc a b⟩

/-- An isomorphism preserves the integer names after one round. -/
theorem namedStep_map (u v : V) : namedStep d (φ u) (φ v) = namedStep c u v := by
  rw [namedStep, namedTags_map φ hc, namedTag_map φ hc, namedStep]

/-- An isomorphism preserves the integer names at every round. -/
theorem namedIter_map (r : ℕ) (u v : V) :
    namedIter d r (φ u) (φ v) = namedIter c r u v := by
  induction r generalizing u v with
  | zero => exact hc u v
  | succ r ih => exact namedStep_map φ ih u v

end Canonical

/-- If a stable coloring already uses an initial segment, the next naming is unchanged.
The old name is the first coordinate, so the order of the classes cannot change. -/
theorem namedStep_eq_of_stable {c : V → V → ℕ} (hs : IsStable c) {m : ℕ}
    (hn : Finset.univ.image (fun p : V × V => c p.1 p.2) = Finset.range m) :
    namedStep c = c := by
  funext u v
  have htag : ∀ a b x y, c a b = c x y → namedTag c a b = namedTag c x y :=
    fun a b x y h => (namedTag_eq_iff c a b x y).2 (hs a b x y h)
  have hcmp : ∀ a b, Algo.cmpRec (namedTag c a b) (namedTag c u v) = 1 ↔ c a b < c u v := by
    intro a b
    rcases lt_trichotomy (c a b) (c u v) with h | h | h
    · simp [namedTag, Algo.cmpRec_cons, h]
    · rw [htag a b u v h, Algo.cmpRec_self]
      simp [h]
    · simp [namedTag, Algo.cmpRec_cons, h, Nat.not_lt.2 (Nat.le_of_lt h)]
  have hlt : c u v < m := Finset.mem_range.1 (hn ▸
    Finset.mem_image.2 ⟨(u, v), Finset.mem_univ _, rfl⟩)
  change (Finset.filter _ (namedTags c)).card = c u v
  rw [← Finset.card_range (c u v)]
  refine Finset.card_bij (fun t _ => t.headD 0) ?_ ?_ ?_
  · intro t ht
    obtain ⟨ht, hc⟩ := Finset.mem_filter.1 ht
    obtain ⟨⟨a, b⟩, _, rfl⟩ := Finset.mem_image.1 ht
    exact Finset.mem_range.2 ((hcmp a b).1 hc)
  · intro s hs t ht he
    obtain ⟨⟨a, b⟩, _, rfl⟩ := Finset.mem_image.1 (Finset.mem_filter.1 hs).1
    obtain ⟨⟨x, y⟩, _, rfl⟩ := Finset.mem_image.1 (Finset.mem_filter.1 ht).1
    exact htag a b x y he
  · intro i hi
    have him : i < m := lt_trans (Finset.mem_range.1 hi) hlt
    obtain ⟨⟨a, b⟩, _, he⟩ := Finset.mem_image.1 (hn.symm ▸ Finset.mem_range.2 him)
    refine ⟨namedTag c a b, Finset.mem_filter.2 ⟨namedTag_mem c a b, ?_⟩, he⟩
    exact (hcmp a b).2 (he ▸ Finset.mem_range.1 hi)

/-- Once the partition is stable after a positive number of rounds, the names freeze. -/
theorem namedIter_freeze (c : V → V → ℕ) {r : ℕ} (hr : 1 ≤ r)
    (hs : IsStable (iter c r)) (j : ℕ) : namedIter c (r + j) = namedIter c r := by
  have hsn : IsStable (namedIter c r) := by
    intro u v x y h
    exact (step_congr (namedIter_eq_iff c r) u v x y).2
      (hs u v x y ((namedIter_eq_iff c r u v x y).1 h))
  have hfix : namedStep (namedIter c r) = namedIter c r := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
    exact namedStep_eq_of_stable hsn (namedStep_image (namedIter c k))
  induction j with
  | zero => rfl
  | succ j ih =>
    change namedStep (namedIter c (r + j)) = namedIter c r
    rw [ih, hfix]

end Babai.WL
