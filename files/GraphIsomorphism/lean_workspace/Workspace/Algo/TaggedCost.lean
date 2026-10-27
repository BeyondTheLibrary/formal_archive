/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 4.1.1: the running time of the tagged refinement process, on the RAM.
-/
import Workspace.Machine.TimeClasses
import Workspace.Refinement.TaggedProcess

/-!
# §4.1.1 — the cost of the tagged refinement process

Lines 2905–2911: *"The cost of each refinement round is `O(m)`, total `O(nm) + |t₁|`. … The
`O(nm)` term can be further reduced to `O(m log n)` as follows (Hopcroft–Tarjan [HoT])."*

The output of the process is `X* = (V, E, c*, t*)`, and it contains the final tag `t*`.  The
same paragraph proves `|t*| = |t₁| + O(n³)`, and this is attained: on the directed path with
`n` vertices, `m = n - 1` and `|t₁| = 2`, but `t*` has at least `(n-1)³/12` letters
(`Babai.TaggedDigraph.pathX_tagLetters_finalTag`).  A RAM changes one register per step, so
it cannot write an output with more nonzero registers than its running time plus its input
length (`nz_output_le`).  Hence both printed bounds are false on the RAM:

* `Section_4_1_1_cost_statement` (`O(nm) + |t₁|`) is refuted by
  `not_Section_4_1_1_cost_statement`;
* `Section_4_1_1_HopcroftTarjan_statement` (`O(m log n) + |t₁|`) implies the former
  (`Section_4_1_1_HopcroftTarjan_statement.toCost`) and is refuted by
  `not_Section_4_1_1_HopcroftTarjan_statement`.

Both statements are made *weaker* than printed before being refuted: the input size is added
to the bound.  The minimal correct bound is `O(n³) + |t₁|` plus the input size;
it is stated as `Section_4_1_1_cost_corrected_statement` and proved in
`Workspace/Algo/TagLinCost.lean` (`Algo.section_4_1_1_cost_corrected`).
See the corrected paper (§4.1.1: running time of the tagged refinement).

No axiom, no `sorry`.
-/

namespace Algo

open RAM Babai Babai.TaggedDigraph

/-! ## A run of `k` steps changes at most `k` registers -/

theorem exec_mem_single (i : Instr) (c : Config) :
    ∃ r, ∀ a, a ≠ r → (exec i c).mem a = c.mem a := by
  obtain ⟨p, m⟩ := c
  cases i with
  | const i v => exact ⟨i, fun a ha => Mem.update_of_ne _ _ ha⟩
  | copy i j => exact ⟨i, fun a ha => Mem.update_of_ne _ _ ha⟩
  | add i j k => exact ⟨i, fun a ha => Mem.update_of_ne _ _ ha⟩
  | sub i j k => exact ⟨i, fun a ha => Mem.update_of_ne _ _ ha⟩
  | load i j => exact ⟨i, fun a ha => Mem.update_of_ne _ _ ha⟩
  | store i j => exact ⟨m i, fun a ha => Mem.update_of_ne _ _ ha⟩
  | jump t => exact ⟨0, fun _ _ => rfl⟩
  | jz i t => exact ⟨0, fun _ _ => rfl⟩
  | halt => exact ⟨0, fun _ _ => rfl⟩

theorem step_mem_single (P : Program) (c : Config) :
    ∃ r, ∀ a, a ≠ r → (step P c).mem a = c.mem a := by
  unfold step
  split
  · exact ⟨0, fun _ _ => rfl⟩
  · exact ⟨0, fun _ _ => rfl⟩
  · exact exec_mem_single _ _

/-- In `k` steps at most `k` registers change. -/
theorem card_changed_le (P : Program) (c : Config) :
    ∀ (k : ℕ) (S : Finset ℕ), (∀ a ∈ S, (run P c k).mem a ≠ c.mem a) → S.card ≤ k
  | 0, S, h => by
    have : S = ∅ := Finset.eq_empty_of_forall_notMem fun a ha => h a ha rfl
    simp [this]
  | k + 1, S, h => by
    obtain ⟨r, hr⟩ := step_mem_single P (run P c k)
    have h' : ∀ a ∈ S.erase r, (run P c k).mem a ≠ c.mem a := fun a ha => by
      rw [Finset.mem_erase] at ha
      have := h a ha.2
      rwa [run_succ, hr a ha.1] at this
    have h1 := card_changed_le P c k _ h'
    have h2 := Finset.pred_card_le_card_erase (s := S) (a := r)
    omega

/-- The number of nonzero entries of a list of registers. -/
def nz (l : List ℕ) : ℕ := l.countP (fun x => x ≠ 0)

theorem nz_eq_sum (l : List ℕ) :
    nz l = ∑ i ∈ Finset.range l.length, if l.getD i 0 ≠ 0 then 1 else 0 := by
  induction l with
  | nil => simp [nz]
  | cons x l ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [← ih]
    simp [nz, List.countP_cons]

/-- **Output lower bound.**  A run of `k` steps on an input of length `|l|` that leaves `out`
in the output convention has `nz(out) ≤ k + |l|`. -/
theorem nz_output_le {P : Program} {l out : List ℕ} {k : ℕ}
    (h : OutputAt (run P (Config.init l) k).mem out) : nz out ≤ k + l.length := by
  classical
  set M := (run P (Config.init l) k).mem
  set A := (Finset.range out.length).filter (fun i => out.getD i 0 ≠ 0)
  set B := (Finset.range out.length).filter (fun i => out.getD i 0 ≠ 0 ∧ l.length ≤ i)
  have hA : nz out = A.card := by rw [nz_eq_sum, Finset.card_filter]
  have hB : B.card ≤ k := by
    rw [← Finset.card_image_of_injective B (add_left_injective 1)]
    apply card_changed_le P (Config.init l) k
    intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ha
    rw [Finset.mem_filter, Finset.mem_range] at hi
    change M (i + 1) ≠ initMem l (i + 1)
    rw [h.2 i hi.1]
    have : initMem l (i + 1) = 0 := by
      simp only [initMem, Nat.add_sub_cancel, if_neg (Nat.succ_ne_zero i)]
      exact List.getD_eq_default _ _ hi.2.2
    rw [this]; exact hi.2.1
  have hsub : A ⊆ B ∪ Finset.range l.length := by
    intro i hi
    rw [Finset.mem_filter, Finset.mem_range] at hi
    by_cases hl : l.length ≤ i
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_range.2 hi.1, hi.2, hl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_range.2 (by omega))
  have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  simp only [Finset.card_range] at this
  omega

/-! ## Nonzero entries of encodings -/

theorem nz_append (l l' : List ℕ) : nz (l ++ l') = nz l + nz l' := List.countP_append ..

theorem nz_frame_ge (xs : List ℕ) : nz xs ≤ nz (frame xs) := by
  rw [frame, nz, nz, List.countP_cons]; exact Nat.le_add_right _ _

theorem nz_encList_ge {α : Type*} (f : α → List ℕ) (l : List α) :
    (l.map (fun a => nz (f a))).sum ≤ nz (encList f l) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, encList, nz_append]
    exact Nat.add_le_add (nz_frame_ge _) ih

theorem length_le_nz_encode (col : List ℕ) : col.length ≤ nz (encode col) := by
  change col.length ≤ nz (encList encode col)
  induction col with
  | nil => simp
  | cons x col ih =>
    rw [encList, nz_append, List.length_cons]
    have : 1 ≤ nz (frame (encode x)) := by
      change 1 ≤ nz [1, x]; simp [nz]
    omega

theorem letters_le_nz_encode (p : List (List ℕ)) : (p.map List.length).sum ≤ nz (encode p) :=
  (List.sum_le_sum (fun col _ => length_le_nz_encode col)).trans (nz_encList_ge _ p)

theorem tagLetters_le_nz_encode (t : List (List (List ℕ))) : tagLetters t ≤ nz (encode t) :=
  (List.sum_le_sum (fun p _ => letters_le_nz_encode p)).trans (nz_encList_ge _ t)

theorem nz_encode_snd_le {α β : Type*} [Enc α] [Enc β] (a : α) (b : β) :
    nz (encode b) ≤ nz (encode (a, b)) := by
  change _ ≤ nz (frame (encode a) ++ frame (encode b))
  rw [nz_append]; exact (nz_frame_ge _).trans (Nat.le_add_left _ _)

/-! ## A weight bounding the size of an encoding -/

/-- `wt l = |l| + Σ l`, an upper bound for `listSize l - 1` and for `|l|`. -/
def wt (l : List ℕ) : ℕ := l.length + l.sum

theorem listSize_le_wt (l : List ℕ) : listSize l ≤ 1 + wt l := by
  induction l with
  | nil => simp [wt]
  | cons x l ih =>
    rw [listSize_cons]
    have := size_le_self x
    simp only [wt, List.length_cons, List.sum_cons] at ih ⊢
    omega

theorem length_le_wt (l : List ℕ) : l.length ≤ wt l := Nat.le_add_right _ _

theorem wt_append (l l' : List ℕ) : wt (l ++ l') = wt l + wt l' := by
  simp [wt]; ring

theorem wt_frame (xs : List ℕ) : wt (frame xs) ≤ 1 + 2 * wt xs := by
  simp only [frame, wt, List.length_cons, List.sum_cons]; omega

theorem wt_encode_pair {α β : Type*} [Enc α] [Enc β] (a : α) (b : β) :
    wt (encode (a, b)) ≤ 2 + 2 * wt (encode a) + 2 * wt (encode b) := by
  change wt (frame (encode a) ++ frame (encode b)) ≤ _
  rw [wt_append]
  have := wt_frame (encode a); have := wt_frame (encode b)
  omega

theorem wt_encList_le {α : Type*} (f : α → List ℕ) (l : List α) (B : ℕ)
    (h : ∀ a ∈ l, wt (f a) ≤ B) : wt (encList f l) ≤ l.length * (2 * B + 1) := by
  induction l with
  | nil => simp [encList, wt]
  | cons a l ih =>
    rw [encList, wt_append, List.length_cons]
    have h1 := (wt_frame (f a)).trans (by have := h a (by simp); omega : 1 + 2 * wt (f a) ≤ 2 * B + 1)
    have h2 := ih (fun b hb => h b (by simp [hb]))
    nlinarith

/-! ## Raw tagged digraphs -/

/-- A tagged colored digraph as the RAM reads it: the list of vertex colors (vertex `i` has
color `r.1[i]`), the list of edges, and the tag. -/
abbrev RawTagged := List (List ℕ) × (List (ℕ × ℕ) × List (List (List ℕ)))

/-- The tagged colored digraph on `Fin n`, `n = |r.1|`, that `r` describes. -/
def decTagged (r : RawTagged) : StrTagged (Fin r.1.length) :=
  ⟨⟨{p | ((p.1 : ℕ), (p.2 : ℕ)) ∈ r.2.1}, fun i => r.1.get i⟩, r.2.2⟩

/-- Well-formed input: no repeated edge, no loop (§4.1: "`E ⊆ (V × V) \ diag(V)`"), and edge
ends are vertices. -/
def RawTagged.WF (r : RawTagged) : Prop :=
  r.2.1.Nodup ∧ ∀ e ∈ r.2.1, e.1 < r.1.length ∧ e.2 < r.1.length ∧ e.1 ≠ e.2

/-- The output `X* = (V, E, c*, t*)` in the same format. -/
noncomputable def taggedOut (r : RawTagged) : RawTagged :=
  (List.ofFn (stableTagged (decTagged r)).c, (r.2.1, finalTag (decTagged r)))

/-! ## The statements -/

/-- §4.1.1, lines 2905–2909, as printed (weakened by adding the input size): *"The cost of each
refinement round is `O(m)`, total `O(nm) + |t₁|`."*  **False**: `not_Section_4_1_1_cost_statement`. -/
def Section_4_1_1_cost_statement : Prop :=
  ∃ (P : Program) (C : ℕ), ∀ r : RawTagged, r.WF →
    ∃ k ≤ C * (r.1.length * r.2.1.length + tagLen (tagIter (decTagged r) 1).tag +
        Enc.size r + 1),
      Halted P (run P (Config.init (encode r)) k) ∧
        OutputAt (run P (Config.init (encode r)) k).mem (encode (taggedOut r))

/-- §4.1.1, line 2910, as printed (weakened by adding the input size): *"The `O(nm)` term can
be further reduced to `O(m log n)`"* (Hopcroft–Tarjan).  **False**:
`not_Section_4_1_1_HopcroftTarjan_statement`. -/
def Section_4_1_1_HopcroftTarjan_statement : Prop :=
  ∃ (P : Program) (C : ℕ), ∀ r : RawTagged, r.WF →
    ∃ k ≤ C * (r.2.1.length * (Nat.log 2 r.1.length + 1) +
        tagLen (tagIter (decTagged r) 1).tag + Enc.size r + 1),
      Halted P (run P (Config.init (encode r)) k) ∧
        OutputAt (run P (Config.init (encode r)) k).mem (encode (taggedOut r))

/-- §4.1.1, the corrected bound: `O(n³) + |t₁|` plus the input size.  The lower bound
`Ω(n³)` is `pathX_tagLetters_finalTag` with `nz_output_le`.  The upper bound is proved in
`Workspace/Algo/TagLinCost.lean` (`Algo.section_4_1_1_cost_corrected`), by a step-exact
program. -/
def Section_4_1_1_cost_corrected_statement : Prop :=
  ∃ (P : Program) (C : ℕ), ∀ r : RawTagged, r.WF →
    ∃ k ≤ C * (r.1.length ^ 3 + tagLen (tagIter (decTagged r) 1).tag + Enc.size r + 1),
      Halted P (run P (Config.init (encode r)) k) ∧
        OutputAt (run P (Config.init (encode r)) k).mem (encode (taggedOut r))

/-- The Hopcroft–Tarjan bound implies the printed `O(nm)` bound, since `log₂ n + 1 ≤ n` when
there is an edge. -/
theorem Section_4_1_1_HopcroftTarjan_statement.toCost
    (h : Section_4_1_1_HopcroftTarjan_statement) : Section_4_1_1_cost_statement := by
  obtain ⟨P, C, hP⟩ := h
  refine ⟨P, C, fun r hr => ?_⟩
  obtain ⟨k, hk, hrun⟩ := hP r hr
  refine ⟨k, hk.trans (Nat.mul_le_mul_left _ ?_), hrun⟩
  have : r.2.1.length * (Nat.log 2 r.1.length + 1) ≤ r.1.length * r.2.1.length := by
    rcases Nat.eq_zero_or_pos r.1.length with h0 | hpos
    · have : r.2.1 = [] := List.eq_nil_iff_forall_not_mem.2 fun e he => by
        have := (hr.2 e he).1; omega
      simp [this]
    · have := Nat.log_lt_self 2 hpos.ne'
      rw [Nat.mul_comm (r.1.length)]
      exact Nat.mul_le_mul_left _ (by omega)
  omega

/-! ## The refutation: the directed path -/

/-- The directed path `0 → 1 → ⋯ → n-1`, colors empty, tag empty. -/
def pathRaw (n : ℕ) : RawTagged :=
  (List.replicate n [], ((List.range (n - 1)).map (fun i => (i, i + 1)), []))

theorem length_pathRaw (n : ℕ) : (pathRaw n).1.length = n := by simp [pathRaw]

theorem wf_pathRaw (n : ℕ) : (pathRaw n).WF := by
  refine ⟨(List.nodup_range).map (fun i j h => by simpa using h), fun e he => ?_⟩
  simp only [pathRaw, List.mem_map, List.mem_range, List.length_replicate] at he ⊢
  obtain ⟨i, hi, rfl⟩ := he
  simp only; omega

theorem isPathLike_decTagged_pathRaw (n : ℕ) : IsPathLike (decTagged (pathRaw n)) := by
  refine ⟨?_, fun a b => by simp [decTagged, pathRaw]⟩
  ext ⟨a, b⟩
  have ha : (a : ℕ) < n := by have := a.2; simpa [pathRaw] using this
  have hb : (b : ℕ) < n := by have := b.2; simpa [pathRaw] using this
  change ((a : ℕ), (b : ℕ)) ∈ (List.range (n - 1)).map (fun i => (i, i + 1)) ↔ (b : ℕ) = a + 1
  rw [List.mem_map]
  constructor
  · rintro ⟨i, hi, he⟩
    simp only [Prod.mk.injEq] at he
    omega
  · intro h
    exact ⟨a, List.mem_range.2 (by omega), by simp [h]⟩

theorem wt_encode_pathRaw (n : ℕ) : wt (encode (pathRaw n)) ≤ 32 * n ^ 2 + 38 * n + 6 := by
  have hc : wt (encode (List.replicate n ([] : List ℕ))) ≤ n := by
    have := wt_encList_le encode (List.replicate n ([] : List ℕ)) 0 (fun a ha => by
      rw [List.eq_of_mem_replicate ha]; simp [wt, encode, Enc.encode, encList])
    simpa using this
  have he : wt (encode ((List.range (n - 1)).map (fun i => (i, i + 1)))) ≤ n * (8 * n + 9) := by
    have := wt_encList_le encode ((List.range (n - 1)).map (fun i => (i, i + 1))) (4 * n + 4)
      (fun e he => by
        simp only [List.mem_map, List.mem_range] at he
        obtain ⟨i, hi, rfl⟩ := he
        refine (wt_encode_pair _ _).trans ?_
        change 2 + 2 * wt [i] + 2 * wt [i + 1] ≤ _
        simp only [wt, List.length_singleton, List.sum_singleton]
        omega)
    simp only [List.length_map, List.length_range] at this
    refine this.trans (Nat.mul_le_mul (Nat.sub_le _ _) (by omega))
  have ht : wt (encode ([] : List (List (List ℕ)))) = 0 := rfl
  have h1 := wt_encode_pair ((List.range (n - 1)).map (fun i => (i, i + 1)))
    ([] : List (List (List ℕ)))
  have h2 := wt_encode_pair (List.replicate n ([] : List ℕ))
    ((List.range (n - 1)).map (fun i => (i, i + 1)), ([] : List (List (List ℕ))))
  change wt (encode (List.replicate n ([] : List ℕ),
    ((List.range (n - 1)).map (fun i => (i, i + 1)), ([] : List (List (List ℕ)))))) ≤ _
  nlinarith

/-- The arithmetic of the refutation: `(n-1)³` output letters cannot be written in
`O(C n²)` steps once `n > 4000 (C + 1)`. -/
theorem refute_arith (n C k S L x : ℕ) (hn : n = 4000 * (C + 1) + 2)
    (hk : k ≤ C * (n * (n - 1) + 2 + S + 1)) (hS : S ≤ 1 + (32 * n ^ 2 + 38 * n + 6))
    (hL : L ≤ 32 * n ^ 2 + 38 * n + 6) (h1 : x ≤ k + L) (h3 : (n - 1) ^ 3 ≤ 12 * x) : False := by
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 1 := ⟨n - 1, by omega⟩
  have hq : 4000 * (C + 1) < q := by omega
  have hq1 : 1 ≤ q := by omega
  simp only [Nat.add_sub_cancel] at hk h3
  have hB : 32 * (q + 1) ^ 2 + 38 * (q + 1) + 7 ≤ 150 * q ^ 2 := by nlinarith
  have hA : (q + 1) * q + 2 + S + 1 ≤ 155 * q ^ 2 := by nlinarith
  have hk' : k ≤ C * (155 * q ^ 2) := hk.trans (Nat.mul_le_mul_left _ hA)
  have hx : x ≤ 155 * (C + 1) * q ^ 2 := by nlinarith
  have hfin : q * q ^ 2 ≤ (1860 * (C + 1)) * q ^ 2 := by
    calc q * q ^ 2 = q ^ 3 := by ring
      _ ≤ 12 * x := h3
      _ ≤ 12 * (155 * (C + 1) * q ^ 2) := Nat.mul_le_mul_left _ hx
      _ = _ := by ring
  have := Nat.le_of_mul_le_mul_right hfin (by positivity)
  omega

/-- **The printed cost `O(nm) + |t₁|` of §4.1.1 is false on the RAM**, even with the input size
added to the bound. -/
theorem not_Section_4_1_1_cost_statement : ¬ Section_4_1_1_cost_statement := by
  rintro ⟨P, C, hP⟩
  obtain ⟨k, hk, -, hout⟩ := hP (pathRaw (4000 * (C + 1) + 2)) (wf_pathRaw _)
  have hX := isPathLike_decTagged_pathRaw (4000 * (C + 1) + 2)
  have hN := length_pathRaw (4000 * (C + 1) + 2)
  -- the output has at least `(n-1)³/12` nonzero registers
  have h1 := nz_output_le hout
  have h2 : tagLetters (finalTag (decTagged (pathRaw (4000 * (C + 1) + 2)))) ≤
      nz (encode (taggedOut (pathRaw (4000 * (C + 1) + 2)))) :=
    (tagLetters_le_nz_encode _).trans ((nz_encode_snd_le _ _).trans (nz_encode_snd_le _ _))
  have h3 := pathX_tagLetters_finalTag hX
  have hN1 : (pathRaw (4000 * (C + 1) + 2)).1.length - 1 = 4000 * (C + 1) + 2 - 1 := by rw [hN]
  rw [hN1] at h3
  -- the bound is `O(C n²)`
  have ht1 : tagLen (tagIter (decTagged (pathRaw (4000 * (C + 1) + 2))) 1).tag = 2 := by
    have hpos : 0 < (pathRaw (4000 * (C + 1) + 2)).1.length := by rw [hN]; omega
    rw [tagLen_tag_tagIter_one_pathLike hX hpos]
    simp [decTagged, pathRaw, tagLen]
  have hm : (pathRaw (4000 * (C + 1) + 2)).2.1.length = 4000 * (C + 1) + 2 - 1 := by
    simp [pathRaw]
  rw [ht1, hm, hN] at hk
  have hw := wt_encode_pathRaw (4000 * (C + 1) + 2)
  exact refute_arith _ C k _ _ _ rfl hk ((listSize_le_wt _).trans (by omega))
    ((length_le_wt _).trans hw) (h2.trans h1) (h3.trans (Nat.mul_le_mul_left _ le_rfl))

/-- **The printed Hopcroft–Tarjan cost `O(m log n) + |t₁|` of §4.1.1 is false on the RAM.** -/
theorem not_Section_4_1_1_HopcroftTarjan_statement :
    ¬ Section_4_1_1_HopcroftTarjan_statement :=
  fun h => not_Section_4_1_1_cost_statement h.toCost

end Algo
