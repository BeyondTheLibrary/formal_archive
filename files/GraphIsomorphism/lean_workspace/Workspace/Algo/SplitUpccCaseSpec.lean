import Workspace.Algo.SplitUpccCase

/-!
# Section 9.8: names, color choices, and the outcome

The dictionary names a first-part singleton or a second-part block by one
vertex of the raw table. The raw graph therefore retains block names,
without expanding a block into its points.
-/

namespace Algo
open Babai RAM

section Names
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    (X : UPCCObj s) {n : ℕ} (e : ↥X.vtxSet ≃ Fin n)

/-- The name of a point in the first part. -/
def upccCaseName₁ (x : ↥X.Pt₁) : ℕ := e (X.vtxOfPt x)

/-- The name of a block in the second part. -/
def upccCaseName₂ (B : ↥X.blocks) : ℕ := e (X.vtxOfBlk B)

theorem upccCaseName₁_injective : Function.Injective (upccCaseName₁ X e) := by
  intro x y h
  have hv := congrArg Subtype.val (e.injective (Fin.ext h))
  change ({(x : ↥s)} : Set ↥s) = {(y : ↥s)} at hv
  exact Subtype.ext (Set.singleton_injective hv)

theorem upccCaseName₂_injective : Function.Injective (upccCaseName₂ X e) := by
  intro B C h
  have hv := congrArg Subtype.val (e.injective (Fin.ext h))
  exact Subtype.ext hv

/-- Section 9.8: exact names of both parts and all pair colors. -/
structure UpccCaseNames (r : RawUpccCase) : Prop where
  size : r.1.1.length = n
  color : ∀ u v, binColor (r.1,(e u,e v)) = X.vc u v
  left : upccCaseName₁ X e '' Set.univ = {a | a ∈ r.2.1}
  right : upccCaseName₂ X e '' Set.univ = {a | a ∈ r.2.2}

variable {X e}

theorem upccCaseName₁_mem {r : RawUpccCase} (h : UpccCaseNames X e r) (x : ↥X.Pt₁) :
    upccCaseName₁ X e x ∈ r.2.1 := by
  have := Set.mem_image_of_mem (upccCaseName₁ X e) (Set.mem_univ x)
  rw [h.left] at this
  exact this

theorem upccCaseName₂_mem {r : RawUpccCase} (h : UpccCaseNames X e r) (B : ↥X.blocks) :
    upccCaseName₂ X e B ∈ r.2.2 := by
  have := Set.mem_image_of_mem (upccCaseName₂ X e) (Set.mem_univ B)
  rw [h.right] at this
  exact this

theorem upccCaseName₁_surj {r : RawUpccCase} (h : UpccCaseNames X e r)
    {a : ℕ} (ha : a ∈ r.2.1) : ∃ x : ↥X.Pt₁, upccCaseName₁ X e x = a := by
  have : a ∈ upccCaseName₁ X e '' Set.univ := by rw [h.left]; exact ha
  simpa only [Set.mem_image, Set.mem_univ, true_and] using this

theorem upccCaseName₂_surj {r : RawUpccCase} (h : UpccCaseNames X e r)
    {a : ℕ} (ha : a ∈ r.2.2) : ∃ B : ↥X.blocks, upccCaseName₂ X e B = a := by
  have : a ∈ upccCaseName₂ X e '' Set.univ := by rw [h.right]; exact ha
  simpa only [Set.mem_image, Set.mem_univ, true_and] using this

end Names

/-- A named finite set and its duplicate-free list have the same size. -/
theorem upccCaseSize_image {α : Type*} (S : Set α) (f : α → ℕ)
    (hf : Function.Injective f) (l : List ℕ) (hnd : l.Nodup)
    (he : f '' S = {a | a ∈ l}) : l.length = S.ncard := by
  classical
  have hl : {a | a ∈ l} = (↑l.toFinset : Set ℕ) := by ext a; simp
  rw [← Set.ncard_image_of_injective S hf,he,hl,Set.ncard_coe_finset,
    List.toFinset_card_of_nodup hnd]

section Choices
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    (X : UPCCObj s) {n : ℕ} (e : ↥X.vtxSet ≃ Fin n)
    {r : RawUpccCase} (hw : r.WF) (hn : UpccCaseNames X e r)

include hw hn

theorem upccCaseLeft_size : r.2.1.length = X.Pt₁.ncard := by
  have h := upccCaseSize_image Set.univ _ (upccCaseName₁_injective X e) _ hw.left_nodup hn.left
  simpa [Set.ncard_univ, Nat.card_coe_set_eq] using h

theorem upccCaseRight_size : r.2.2.length = X.blocks.ncard := by
  have h := upccCaseSize_image Set.univ _ (upccCaseName₂_injective X e) _ hw.right_nodup hn.right
  simpa [Set.ncard_univ, Nat.card_coe_set_eq] using h

omit hw in
theorem upccCaseLink_mem (B : ↥X.blocks) (x : ↥X.Pt₁) (k : ℕ) :
    upccCaseName₁ X e x ∈ upccCaseLink ((r,upccCaseName₂ X e B),k) ↔
      X.c B {x.val} = k := by
  simp only [upccCaseLink, upccCaseCell, List.mem_filter, decide_eq_true_eq,
    upccCaseName₁_mem hn x, true_and]
  exact congrArg (· = k) (hn.color (X.vtxOfBlk B) (X.vtxOfPt x)) |>.to_iff

omit hw in
theorem upccCaseBlock_mem (B C : ↥X.blocks) (k : ℕ) :
    upccCaseName₂ X e C ∈ upccCaseBlock ((r,upccCaseName₂ X e B),k) ↔
      X.c B C = k := by
  simp only [upccCaseBlock, upccCaseCell, List.mem_filter, decide_eq_true_eq,
    upccCaseName₂_mem hn C, true_and]
  exact congrArg (· = k) (hn.color (X.vtxOfBlk B) (X.vtxOfBlk C)) |>.to_iff

theorem upccCaseLink_size (B : ↥X.blocks) (k : ℕ) :
    (upccCaseLink ((r,upccCaseName₂ X e B),k)).length = (X.linkClass B k).ncard := by
  have he : upccCaseName₁ X e '' {x : ↥X.Pt₁ | X.c B {x.val} = k} =
      {a | a ∈ upccCaseLink ((r,upccCaseName₂ X e B),k)} := by
    ext a
    constructor
    · rintro ⟨x,hx,rfl⟩; exact (upccCaseLink_mem X e hn B x k).2 hx
    · intro ha
      obtain ⟨x,rfl⟩ := upccCaseName₁_surj hn (List.mem_of_mem_filter ha)
      exact ⟨x,(upccCaseLink_mem X e hn B x k).1 ha,rfl⟩
  rw [upccCaseSize_image _ _ (upccCaseName₁_injective X e)
    (upccCaseLink ((r,upccCaseName₂ X e B),k))
    (hw.left_nodup.filter _) he]
  have hs : Subtype.val '' {x : ↥X.Pt₁ | X.c B {x.val} = k} = X.linkClass B k := by
    ext x
    simp only [Set.mem_image, Set.mem_setOf_eq, BlkCaseObj.linkClass]
    exact ⟨fun ⟨y,hy,hxy⟩ => hxy ▸ ⟨y.2,hy⟩, fun hx => ⟨⟨x,hx.1⟩,hx.2,rfl⟩⟩
  rw [← hs,Set.ncard_image_of_injective _ Subtype.val_injective]

theorem upccCaseBlock_size (B : ↥X.blocks) (k : ℕ) :
    (upccCaseBlock ((r,upccCaseName₂ X e B),k)).length = (X.blkClass B k).ncard := by
  have he : upccCaseName₂ X e '' {C : ↥X.blocks | X.c B C = k} =
      {a | a ∈ upccCaseBlock ((r,upccCaseName₂ X e B),k)} := by
    ext a
    constructor
    · rintro ⟨C,hC,rfl⟩; exact (upccCaseBlock_mem X e hn B C k).2 hC
    · intro ha
      obtain ⟨C,rfl⟩ := upccCaseName₂_surj hn (List.mem_of_mem_filter ha)
      exact ⟨C,(upccCaseBlock_mem X e hn B C k).1 ha,rfl⟩
  rw [upccCaseSize_image _ _ (upccCaseName₂_injective X e)
    (upccCaseBlock ((r,upccCaseName₂ X e B),k))
    (hw.right_nodup.filter _) he]
  have hs : Subtype.val '' {C : ↥X.blocks | X.c B C = k} = X.blkClass B k := by
    ext C
    simp only [Set.mem_image, Set.mem_setOf_eq, BlkCaseObj.blkClass]
    exact ⟨fun ⟨D,hD,hCD⟩ => hCD ▸ ⟨D.2,hD⟩, fun hC => ⟨⟨C,hC.1⟩,hC.2,rfl⟩⟩
  rw [← hs,Set.ncard_image_of_injective _ Subtype.val_injective]

theorem upccCaseBig_spec (B : ↥X.blocks) (k : ℕ) :
    upccCaseBig ((r,upccCaseName₂ X e B),k) = true ↔ X.IsBigColor₂ B k := by
  simp only [upccCaseBig, decide_eq_true_eq, Nat.succ_le_iff,
    upccCaseLeft_size X e hw hn, upccCaseLink_size X e hw hn, BlkCaseObj.IsBigColor₂]
  rfl

theorem upccCaseSmall_spec (B : ↥X.blocks) (k : ℕ) :
    upccCaseSmall ((r,upccCaseName₂ X e B),k) = true ↔ X.IsSmallColor₂ B k := by
  have hex : ((upccCaseBlock ((r,upccCaseName₂ X e B),k)).filter
      (fun y => decide (y ≠ upccCaseName₂ X e B))).isEmpty = false ↔
      ∃ C ∈ X.blocks, C ≠ B.val ∧ X.c B C = k := by
    rw [List.isEmpty_eq_false_iff, List.ne_nil_iff_length_pos]
    constructor
    · intro hpos
      obtain ⟨a,ha⟩ := List.exists_mem_of_length_pos hpos
      obtain ⟨ha,hne⟩ := List.mem_filter.1 ha
      obtain ⟨C,rfl⟩ := upccCaseName₂_surj hn (List.mem_of_mem_filter ha)
      refine ⟨C,C.2,?_,(upccCaseBlock_mem X e hn B C k).1 ha⟩
      intro hCB
      have : C = B := Subtype.ext hCB
      subst C
      simpa using hne
    · rintro ⟨C,hC,hne,hcol⟩
      apply List.length_pos_of_mem (a := upccCaseName₂ X e ⟨C,hC⟩)
      apply List.mem_filter.2
      refine ⟨(upccCaseBlock_mem X e hn B ⟨C,hC⟩ k).2 hcol,?_⟩
      simp only [decide_eq_true_eq]
      intro he
      exact hne (congrArg Subtype.val (upccCaseName₂_injective X e he))
  simp only [upccCaseSmall, Bool.and_eq_true, Bool.not_eq_true', hex,
    decide_eq_true_eq, upccCaseBlock_size X e hw hn, upccCaseRight_size X e hw hn,
    BlkCaseObj.IsSmallColor₂]


theorem upccCaseCandidates_big (B : ↥X.blocks) (k : ℕ) :
    k ∈ upccCaseCandidates upccCaseBig (r,upccCaseName₂ X e B) ↔ X.IsBigColor₂ B k := by
  rw [upccCaseCandidates,List.mem_filter,upccCaseBig_spec X e hw hn]
  refine ⟨And.right,fun hk => ⟨?_,hk⟩⟩
  have hp : 0 < (X.linkClass B k).ncard := by
    have : X.Pt₁.ncard < 2 * (X.linkClass B k).ncard := hk
    omega
  obtain ⟨x,hx⟩ := (Set.ncard_pos (Set.toFinite _)).1 hp
  rw [mem_binaryColorsRaw (hn.size ▸ hw.table)]
  exact ⟨e (X.vtxOfBlk B),e (X.vtxOfPt ⟨x,hx.1⟩),
    (hn.color _ _).trans hx.2⟩

theorem upccCaseCandidates_small (B : ↥X.blocks) (k : ℕ) :
    k ∈ upccCaseCandidates upccCaseSmall (r,upccCaseName₂ X e B) ↔ X.IsSmallColor₂ B k := by
  rw [upccCaseCandidates,List.mem_filter,upccCaseSmall_spec X e hw hn]
  refine ⟨And.right,fun hk => ⟨?_,hk⟩⟩
  obtain ⟨C,hC,_,hcol⟩ := hk.1
  rw [mem_binaryColorsRaw (hn.size ▸ hw.table)]
  exact ⟨e (X.vtxOfBlk B),e (X.vtxOfBlk ⟨C,hC⟩),(hn.color _ _).trans hcol⟩

theorem upccCaseSplits_spec (B : ↥X.blocks) :
    upccCaseSplits (r,upccCaseName₂ X e B) = true ↔
      ∀ k, 2 * (X.linkClass B k).ncard ≤ X.Pt₁.ncard := by
  simp only [upccCaseSplits,List.isEmpty_iff,List.eq_nil_iff_forall_not_mem,
    upccCaseCandidates_big X e hw hn,BlkCaseObj.IsBigColor₂,not_lt]
  rfl

end Choices

/-- The least-list routine returns the least entry, without a numeric search. -/
theorem upccCaseLeast_spec (l : List ℕ) (hne : l ≠ []) :
    upccCaseLeast l ∈ l ∧ ∀ k ∈ l, upccCaseLeast l ≤ k := by
  have hmap : l.map (fun k => (0,k)) ≠ [] := by simpa using hne
  obtain ⟨hm,hle⟩ := upccLeastPair_spec (l.map (fun k => (0,k))) hmap
  obtain ⟨m,hm,he⟩ := List.mem_map.1 hm
  have hout : upccCaseLeast l = m := congrArg Prod.snd he.symm
  rw [hout]
  refine ⟨hm,fun k hk => ?_⟩
  have hh := hle (0,k) (List.mem_map.2 ⟨k,hk,rfl⟩)
  rw [← he] at hh
  have hpair (t : ℕ) : Nat.pair 0 t = t*t := by
    simp [Nat.pair]
    intro ht
    simp [ht]
  simp only [hpair] at hh
  nlinarith

open scoped Classical in
/-- A list scan implements `Nat.find` when it lists exactly the witnesses. -/
theorem upccCaseLeast_find (P : ℕ → Prop) (l : List ℕ)
    (hl : ∀ k, k ∈ l ↔ P k) :
    upccCaseLeast l = (if h : ∃ k, P k then Nat.find h else 0) := by
  classical
  split_ifs with h
  · have hne : l ≠ [] := by
      obtain ⟨k,hk⟩ := h
      exact List.ne_nil_of_mem ((hl k).2 hk)
    obtain ⟨hm,hmin⟩ := upccCaseLeast_spec l hne
    exact le_antisymm (hmin _ ((hl _).2 (Nat.find_spec h)))
      (Nat.find_min' h ((hl _).1 hm))
  · have hn : l = [] := by
      apply List.eq_nil_iff_forall_not_mem.2
      intro k hk
      exact h ⟨k,(hl k).1 hk⟩
    simp [hn,upccCaseLeast,upccLeastPair]

section Selected
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    (X : UPCCObj s) {n : ℕ} (e : ↥X.vtxSet ≃ Fin n)
    {r : RawUpccCase} (hw : r.WF) (hn : UpccCaseNames X e r)

include hw hn

/-- Section 9.8, step 3: the machine selects the mathematical dominant color. -/
theorem upccCaseM_spec (B : ↥X.blocks) :
    upccCaseM (r,upccCaseName₂ X e B) = X.mColor B := by
  classical
  exact upccCaseLeast_find _ _ (upccCaseCandidates_big X e hw hn B)

/-- Section 9.8, step 3: the machine selects the first eligible color of `X₂`. -/
theorem upccCaseL_spec (B : ↥X.blocks) :
    upccCaseL (r,upccCaseName₂ X e B) = X.lColor B := by
  classical
  exact upccCaseLeast_find _ _ (upccCaseCandidates_small X e hw hn B)

end Selected
end Algo
