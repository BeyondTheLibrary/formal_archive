import Workspace.Machine.GIRaw

/-! # Correctness of the raw GI constructor -/

namespace RAM.GIReduction

open Algo Babai Babai.GraphToString Equiv Classical

theorem matrixEntry_graphMatrix {n : ℕ} (X : SimpleGraph (Fin n)) (i j : Fin n) :
    matrixEntry (Targets.graphMatrix X, (i.val, j.val)) =
      (if X.Adj i j then 1 else 0) := by
  classical
  simp [matrixEntry, Targets.graphMatrix, List.getD_eq_getElem, i.isLt, j.isLt]

theorem matrixEntry_listedPair {n : ℕ} (X : SimpleGraph (Fin n))
    (p : {p // p ∈ pairList n}) :
    matrixEntry (Targets.graphMatrix X, p.val) = (edgeString X (listedPair p)).val := by
  classical
  obtain ⟨p, hp⟩ := p
  have h := mem_pairList.mp hp
  have hm := matrixEntry_graphMatrix X (⟨p.1, h.1⟩ : Fin n) (⟨p.2, h.2.1⟩ : Fin n)
  change matrixEntry (Targets.graphMatrix X, p) = _
  rw [hm]
  simp only [listedPair, edgeString, isEdge_pair]
  split <;> rfl

theorem rawString_spec {n : ℕ} (X Y : SimpleGraph (Fin n)) :
    (rawPairs (Targets.graphMatrix X)).map (fun p => matrixEntry (Targets.graphMatrix Y, p)) =
      encStr (edgeString Y ∘ pairEnum n) := by
  apply List.ext_getElem
  · simp [rawPairs, encStr]
  · intro i hi hi'
    have hin : i < (pairList n).length := by simpa [rawPairs] using hi
    simpa [rawPairs, encStr, pairEnum, Function.comp_def] using
      matrixEntry_listedPair Y ⟨(pairList n)[i], List.getElem_mem hin⟩

theorem rotateEntry_spec {n : ℕ} (i : Fin n) :
    rotateEntry (n, i.val) = (finRotate n i).val := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt i.isLt)
  rw [coe_finRotate]
  simp only [rotateEntry, Fin.ext_iff, Fin.val_last]
  split <;> split <;> omega

theorem swapEntry_spec {n : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    swapEntry i.val = (Equiv.swap (⟨0, by omega⟩ : Fin n)
      (finRotate n ⟨0, by omega⟩) i).val := by
  have hrot : finRotate n (⟨0, by omega⟩ : Fin n) = ⟨1, by omega⟩ := by
    apply Fin.ext
    rw [← rotateEntry_spec]
    simp [rotateEntry, hn]
    omega
  rw [hrot]
  by_cases hi : i.val = 0
  · have hi' : i = ⟨0, by omega⟩ := Fin.ext hi
    rw [hi']
    simp [swapEntry]
  · by_cases hi' : i.val = 1
    · have hi'' : i = ⟨1, by omega⟩ := Fin.ext hi'
      rw [hi'']
      simp [swapEntry]
    · have h0 : i ≠ (⟨0, by omega⟩ : Fin n) := fun h => hi (congrArg Fin.val h)
      have h1 : i ≠ (⟨1, by omega⟩ : Fin n) := fun h => hi' (congrArg Fin.val h)
      simp [swapEntry, hi, hi', Equiv.swap_apply_of_ne_of_ne h0 h1]

theorem rawVertexGens_spec {n : ℕ} (X : SimpleGraph (Fin n)) :
    rawVertexGens (Targets.graphMatrix X) = (vertexGens n).map (encPerm n) := by
  by_cases hn : 2 ≤ n
  · simp only [rawVertexGens, Targets.graphMatrix_length, hn, if_true, vertexGens, dif_pos,
      List.map_cons, List.map_nil]
    congr 1
    · apply List.ext_getElem
      · simp [encPerm]
      · intro i hi hi'
        have hin : i < n := by simpa using hi
        simpa only [List.getElem_map, List.getElem_range, encPerm, List.getElem_ofFn] using
          rotateEntry_spec (⟨i, hin⟩ : Fin n)
    · congr 1
      apply List.ext_getElem
      · simp [encPerm]
      · intro i hi hi'
        have hin : i < n := by simpa using hi
        simpa only [List.getElem_map, List.getElem_range, encPerm, List.getElem_ofFn] using
          swapEntry_spec hn (⟨i, hin⟩ : Fin n)
  · simp [rawVertexGens, vertexGens, hn]

theorem rawPairImage_mem {n : ℕ} (σ : Perm (Fin n)) (p : {p // p ∈ pairList n}) :
    rawPairImage (encPerm n σ, p.val) ∈ pairList n := by
  have hp := mem_pairList.mp p.property
  simp only [rawPairImage, rawApply_encPerm n σ hp.1, rawApply_encPerm n σ hp.2.1]
  rw [mem_pairList]
  have h₁ := (σ ⟨p.val.1, hp.1⟩).isLt
  have h₂ := (σ ⟨p.val.2, hp.2.1⟩).isLt
  have hne : (σ ⟨p.val.1, hp.1⟩).val ≠ (σ ⟨p.val.2, hp.2.1⟩).val := by
    intro h
    exact Nat.ne_of_lt hp.2.2 (congrArg Fin.val (σ.injective (Fin.ext h)))
  dsimp only
  omega

theorem listedPair_image {n : ℕ} (σ : Perm (Fin n)) (p : {p // p ∈ pairList n}) :
    listedPair ⟨rawPairImage (encPerm n σ, p.val), rawPairImage_mem σ p⟩ =
      tAction 2 σ (listedPair p) := by
  have hp := mem_pairList.mp p.property
  apply Subtype.ext
  simp only [listedPair, pair, tAction_apply_coe, Finset.image_insert, Finset.image_singleton]
  have h₁ := rawApply_encPerm n σ hp.1
  have h₂ := rawApply_encPerm n σ hp.2.1
  simp only [rawPairImage, h₁, h₂]
  by_cases h : (σ ⟨p.val.1, hp.1⟩).val ≤ (σ ⟨p.val.2, hp.2.1⟩).val
  · simp [min_eq_left h, max_eq_right h]
  · simp [min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge h)),
      max_eq_left (Nat.le_of_lt (Nat.lt_of_not_ge h)), Finset.pair_comm]

theorem numberedAction_get {n : ℕ} (σ : Perm (Fin n)) (i : Fin (pairList n).length) :
    (pairList n)[(numberedAction n σ i).val] =
      rawPairImage (encPerm n σ, (pairList n)[i.val]) := by
  let p : {p // p ∈ pairList n} := ⟨(pairList n)[i.val], List.getElem_mem i.isLt⟩
  let q : {p // p ∈ pairList n} :=
    ⟨(pairList n)[(numberedAction n σ i).val], List.getElem_mem (numberedAction n σ i).isLt⟩
  have h : q = ⟨rawPairImage (encPerm n σ, p.val), rawPairImage_mem σ p⟩ := by
    apply listedPair_injective
    rw [listedPair_image]
    change pairEnum n ((pairEnum n).symm (tAction 2 σ (pairEnum n i))) =
      tAction 2 σ (pairEnum n i)
    exact (pairEnum n).apply_symm_apply _
  exact congrArg Subtype.val h

/-- Lookup in a repetition-free enumeration recovers the index. -/
theorem pairLookup_get (l : List (ℕ × ℕ)) (h : l.Nodup) (i : Fin l.length) :
    pairLookup (l.zipIdx, l[i.val]) = i.val := by
  have hlookup : ∀ (l : List (ℕ × ℕ)), l.Nodup → ∀ (k j : ℕ) (hj : j < l.length),
      (l.zipIdx k).lookup l[j] = some (j + k) := by
    intro l
    induction l with
    | nil => intro _ k j hj; simp at hj
    | cons a l ih =>
      intro h k j hj
      cases j with
      | zero => simp [List.zipIdx_cons, List.lookup]
      | succ j =>
        have hj' : j < l.length := by simpa using hj
        have hne : l[j] ≠ a := fun he => (List.nodup_cons.mp h).1 (he ▸ List.getElem_mem hj')
        have hb : (l[j] == a) = false := by simpa using hne
        simpa [List.zipIdx_cons, List.lookup, hb, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using ih (List.nodup_cons.mp h).2 (k + 1) j hj'
  simp [pairLookup, hlookup l h 0 i.val i.isLt]

theorem rawPairPerm_spec {n : ℕ} (σ : Perm (Fin n)) :
    rawPairPerm (pairList n, encPerm n σ) =
      encPerm (pairList n).length (numberedAction n σ) := by
  apply List.ext_getElem
  · simp [rawPairPerm, encPerm]
  · intro i hi hi'
    have hin : i < (pairList n).length := by simpa [rawPairPerm] using hi
    conv_rhs => simp only [encPerm, List.getElem_ofFn]
    simp only [rawPairPerm, List.getElem_map]
    rw [← numberedAction_get σ ⟨i, hin⟩]
    exact pairLookup_get _ (pairList_nodup n) _

/-- The constructor returns precisely the raw encoding of the mathematical SI instance. -/
theorem build_spec {n : ℕ} (a : Targets.GIInput n) :
    build a.raw = rawOfSI (siInput a.X a.Y) := by
  change build (Targets.graphMatrix a.X, Targets.graphMatrix a.Y) = _
  unfold build
  rw [rawVertexGens_spec, List.map_map, rawString_spec, rawString_spec]
  unfold rawOfSI siInput pairGens
  simp only [List.map_map]
  congr 2
  funext σ
  simpa [rawPairs] using rawPairPerm_spec σ

end RAM.GIReduction

#print axioms RAM.GIReduction.build_spec
