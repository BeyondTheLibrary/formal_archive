import Workspace.Algo.AlignJohnson
import Workspace.Luks.JohnsonBarrier

/-!
# Cameron recognition as an explicit hypothesis

Section 11.2 uses a bijection with a product of sets of subsets. We store all its
values. This lets the validator count the target without listing it. The bounds
on the headers are consequences of the Cameron parameters and the table size.
They also keep the validator polynomial on malformed inputs.

`CameronSpec` makes Theorem 11.2.3 effective. It does not assert a running time.
No recognition axiom is introduced.
-/

namespace Algo

open RAM

/-- Definition 11.2.2, as data: `s`, `t`, `k`, and one tuple of sorted subset rows
per point. The tuple encoding uses the existing RAM product and list encodings. -/
abbrev RawCameron := ℕ × ℕ × ℕ × List (List (List ℕ))

namespace RawCameron

def s (c : RawCameron) : ℕ := c.1
def t (c : RawCameron) : ℕ := c.2.1
def k (c : RawCameron) : ℕ := c.2.2.1
def table (c : RawCameron) : List (List (List ℕ)) := c.2.2.2

/-- The table is a bijection with the product in Definition 11.2.2. -/
structure WF (n : ℕ) (c : RawCameron) : Prop where
  s_pos : 1 ≤ c.s
  t_pos : 1 ≤ c.t
  k_max : max (2 * c.t) 5 ≤ c.k
  k_gt : 2 * c.t < c.k
  table_length : c.table.length = n
  tuple_length : ∀ xs ∈ c.table, xs.length = c.s
  rows : ∀ xs ∈ c.table, ∀ row ∈ xs,
    row.SortedLT ∧ row.length = c.t ∧ ∀ a ∈ row, a < c.k
  nodup : c.table.Nodup
  card : n = (c.k.choose c.t) ^ c.s

/-- The headers are bounded by the number of points, not by their bit lengths. -/
theorem WF.bounds {n : ℕ} {c : RawCameron} (h : WF n c) :
    c.s ≤ n ∧ c.t ≤ n ∧ c.k ≤ n := by
  have hc := Babai.self_le_choose h.t_pos h.k_gt
  have hk : 5 ≤ c.k := (le_max_right _ _).trans h.k_max
  have hp : c.k.choose c.t ≤ (c.k.choose c.t) ^ c.s :=
    le_self_pow (by omega) (by have := h.s_pos; omega)
  have hs : c.s < 2 ^ c.s := Nat.lt_two_pow_self
  have hpow : 2 ^ c.s ≤ (c.k.choose c.t) ^ c.s := Nat.pow_le_pow_left (by omega) _
  rw [← h.card] at hp hpow
  have := h.k_gt
  omega

/-- A tuple in the table, decoded coordinate by coordinate. -/
def WF.tuple {n : ℕ} {c : RawCameron} (h : WF n c) (i : Fin n)
    (j : Fin c.s) : Babai.binom (Fin c.k) c.t :=
  let xs := c.table[i.val]'(by rw [h.table_length]; exact i.isLt)
  have hx : xs ∈ c.table := List.getElem_mem _
  let row := xs[j.val]'(by rw [h.tuple_length xs hx]; exact j.isLt)
  have hr := h.rows xs hx row (List.getElem_mem _)
  ⟨rawJSet c.k row, (card_rawJSet hr.1.nodup hr.2.2).trans hr.2.1⟩

/-- Distinct tuples decode to distinct points of the product. The cardinality
check then proves that every point of the product occurs. -/
theorem WF.tuple_bijective {n : ℕ} {c : RawCameron} (h : WF n c) :
    Function.Bijective h.tuple := by
  classical
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨?_, ?_⟩
  · intro i j hij
    have hi : i.val < c.table.length := by rw [h.table_length]; exact i.isLt
    have hj : j.val < c.table.length := by rw [h.table_length]; exact j.isLt
    have hxi := h.tuple_length _ (List.getElem_mem hi)
    have hxj := h.tuple_length _ (List.getElem_mem hj)
    have heq : c.table[i.val] = c.table[j.val] := by
      apply List.ext_getElem (hxi.trans hxj.symm)
      intro a ha hb
      have has : a < c.s := by omega
      have hv := congrArg Subtype.val (congrFun hij ⟨a, has⟩)
      have hr := h.rows _ (List.getElem_mem hi) _ (List.getElem_mem ha)
      have hr' := h.rows _ (List.getElem_mem hj) _ (List.getElem_mem hb)
      exact rawJSet_injOn hr.1 hr'.1 hr.2.2 hr'.2.2 hv
    exact Fin.ext ((List.Nodup.getElem_inj_iff h.nodup).1 heq)
  · simp only [Fintype.card_fin, Fintype.card_fun, Fintype.card_finset_len]
    exact h.card

end RawCameron

/-- The bijection returned as a table. Choice is used only for its inverse. -/
noncomputable def decCameron {n : ℕ} (c : RawCameron) (h : c.WF n) :
    Fin n ≃ (Fin c.s → Babai.binom (Fin c.k) c.t) :=
  Equiv.ofBijective h.tuple h.tuple_bijective

/-- Check the lengths and subset rows of one tuple. -/
def camTupleOkB (p : (ℕ × ℕ × ℕ) × List (List ℕ)) : Bool :=
  decide (p.2.length = p.1.1) && rawJAllRowsOkB ((p.1.2.2, p.1.2.1), p.2)

theorem camTupleOkB_iff (s t k : ℕ) (xs : List (List ℕ)) :
    camTupleOkB ((s, t, k), xs) = true ↔
      xs.length = s ∧ ∀ row ∈ xs,
        row.SortedLT ∧ row.length = t ∧ ∀ a ∈ row, a < k := by
  simp only [camTupleOkB, Bool.and_eq_true, decide_eq_true_eq, rawJAllRowsOkB_iff]

/-- Check every tuple by scanning the input table. -/
def camAllTuplesB (c : RawCameron) : Bool :=
  (c.table.filter (fun xs => !camTupleOkB ((c.s, c.t, c.k), xs))).isEmpty

theorem camAllTuplesB_iff (c : RawCameron) :
    camAllTuplesB c = true ↔ ∀ xs ∈ c.table,
      xs.length = c.s ∧ ∀ row ∈ xs,
        row.SortedLT ∧ row.length = c.t ∧ ∀ a ∈ row, a < c.k := by
  simp only [camAllTuplesB, List.isEmpty_iff, List.filter_eq_nil_iff,
    Bool.not_eq_true', Bool.not_eq_false]
  exact forall₂_congr fun xs _ => camTupleOkB_iff _ _ _ xs

/-- Duplicate test at the tuple type. -/
def camNodupB (xs : List (List (List ℕ))) : Bool :=
  decide ((dedupG ([], xs)).length = xs.length)

theorem camNodupB_iff (xs : List (List (List ℕ))) :
    camNodupB xs = true ↔ xs.Nodup := by
  rw [camNodupB, decide_eq_true_eq]
  exact rawJ_dedup_nodup xs

/-- A total size calculation. Both loop bounds are capped by the table length. -/
def camCard (c : RawCameron) : ℕ :=
  (Nat.choose (min c.k c.table.length) c.t) ^ min c.s c.table.length

/-- The validator for Definition 11.2.2. Its input includes the whole table. -/
def rawCameronWFb (p : ℕ × RawCameron) : Bool :=
  decide (1 ≤ p.2.s) && decide (1 ≤ p.2.t) &&
  decide (max (2 * p.2.t) 5 ≤ p.2.k) && decide (2 * p.2.t < p.2.k) &&
  decide (p.2.table.length = p.1) && decide (p.2.k ≤ p.2.table.length) &&
  decide (p.2.s ≤ p.2.table.length) && camAllTuplesB p.2 &&
  camNodupB p.2.table && decide (p.1 = camCard p.2)

/-- The bounded test accepts exactly the well-formed tables. -/
theorem rawCameronWFb_iff (n : ℕ) (c : RawCameron) :
    rawCameronWFb (n, c) = true ↔ c.WF n := by
  simp only [rawCameronWFb, Bool.and_eq_true, decide_eq_true_eq,
    camAllTuplesB_iff, camNodupB_iff, and_assoc]
  constructor
  · rintro ⟨hs, ht, hm, hk, hl, hkl, hsl, hr, hnd, hc⟩
    rw [camCard, min_eq_left hkl, min_eq_left hsl] at hc
    exact ⟨hs, ht, hm, hk, hl, fun xs hx => (hr xs hx).1,
      fun xs hx => (hr xs hx).2, hnd, hc⟩
  · intro h
    have hk : c.k ≤ c.table.length := by rw [h.table_length]; exact h.bounds.2.2
    have hs : c.s ≤ c.table.length := by rw [h.table_length]; exact h.bounds.1
    refine ⟨h.s_pos, h.t_pos, h.k_max, h.k_gt, h.table_length, hk, hs,
      fun xs hx => ⟨h.tuple_length xs hx, h.rows xs hx⟩, h.nodup, ?_⟩
    simpa only [camCard, min_eq_left hk, min_eq_left hs] using h.card

theorem camPoly_s : PolyFun RawCameron.s := polyFun_fst
theorem camPoly_t : PolyFun RawCameron.t := polyFun_snd.comp polyFun_fst
theorem camPoly_k : PolyFun RawCameron.k :=
  (polyFun_snd.comp polyFun_snd).comp polyFun_fst
theorem camPoly_table : PolyFun RawCameron.table :=
  (polyFun_snd.comp polyFun_snd).comp polyFun_snd

theorem camTable_length_le_size (c : RawCameron) : c.table.length ≤ Enc.size c := by
  exact (length_le_size _).trans ((Combine.size_snd_le _ _).trans
    ((Combine.size_snd_le _ _).trans (Combine.size_snd_le _ _)))

theorem camPoly_tupleOkB : PolyFun camTupleOkB := by
  have hl : PolyFun (fun p : (ℕ × ℕ × ℕ) × List (List ℕ) =>
      decide (p.2.length = p.1.1)) :=
    ((polyFun_snd.comp polyFun_length).pair
      (polyFun_fst.comp polyFun_fst)).comp polyFun_natEq
  have hr : PolyFun (fun p : (ℕ × ℕ × ℕ) × List (List ℕ) =>
      rawJAllRowsOkB ((p.1.2.2, p.1.2.1), p.2)) :=
    ((((polyFun_fst.comp polyFun_snd).comp polyFun_snd).pair
      ((polyFun_fst.comp polyFun_snd).comp polyFun_fst)).pair polyFun_snd).comp
        polyFun_rawJAllRowsOkB
  exact polyFun_rawJAnd hl hr

theorem camPoly_allTuplesB : PolyFun camAllTuplesB :=
  ((camPoly_s.pair (camPoly_t.pair camPoly_k)).pair camPoly_table).comp
    ((PolyFun.filterParam (polyFun_rawJNot camPoly_tupleOkB)).comp polyFun_isEmpty)

theorem camPoly_nodupB : PolyFun camNodupB :=
  ((((polyFun_nil.pair polyFun_id).comp (polyFun_dedupG polyFun_listListNatEq)).comp
    polyFun_length).pair polyFun_length).comp polyFun_natEq

theorem camPoly_card : PolyFun camCard := by
  have hl := camPoly_table.comp polyFun_length
  have hchoose := PolyFun.choose (camPoly_k.min' hl) camPoly_t
    (q := id) (fun c => (min_le_right _ _).trans (camTable_length_le_size c)) polyBound_id
  exact hchoose.pow (camPoly_s.min' hl)
    (q := id) (fun c => (min_le_right _ _).trans (camTable_length_le_size c)) polyBound_id

/-- The validator runs in polynomial time on every input, including junk. -/
theorem polyFun_rawCameronWFb : PolyFun rawCameronWFb := by
  have hs : PolyFun (fun p : ℕ × RawCameron => p.2.s) := polyFun_snd.comp camPoly_s
  have ht : PolyFun (fun p : ℕ × RawCameron => p.2.t) := polyFun_snd.comp camPoly_t
  have hk : PolyFun (fun p : ℕ × RawCameron => p.2.k) := polyFun_snd.comp camPoly_k
  have hl : PolyFun (fun p : ℕ × RawCameron => p.2.table.length) :=
    (polyFun_snd.comp camPoly_table).comp polyFun_length
  have h1 := (polyFun_const 1).le hs
  have h2 := (polyFun_const 1).le ht
  have h3 := (((polyFun_const 2).mul ht).max' (polyFun_const 5)).le hk
  have h4 : PolyFun (fun p : ℕ × RawCameron => decide (2 * p.2.t < p.2.k)) :=
    ((((polyFun_const 2).mul ht).add (polyFun_const 1)).le hk).of_eq
      (fun _ => decide_eq_decide.2 Nat.add_one_le_iff)
  have h5 := (hl.pair polyFun_fst).comp polyFun_natEq
  have h6 := hk.le hl
  have h7 := hs.le hl
  have h8 : PolyFun (fun p : ℕ × RawCameron => camAllTuplesB p.2) :=
    polyFun_snd.comp camPoly_allTuplesB
  have h9 : PolyFun (fun p : ℕ × RawCameron => camNodupB p.2.table) :=
    (polyFun_snd.comp camPoly_table).comp camPoly_nodupB
  have h10 : PolyFun (fun p : ℕ × RawCameron => decide (p.1 = camCard p.2)) :=
    (polyFun_fst.pair (polyFun_snd.comp camPoly_card)).comp polyFun_natEq
  exact polyFun_rawJAnd (polyFun_rawJAnd (polyFun_rawJAnd (polyFun_rawJAnd
    (polyFun_rawJAnd (polyFun_rawJAnd (polyFun_rawJAnd (polyFun_rawJAnd
      (polyFun_rawJAnd h1 h2) h3) h4) h5) h6) h7) h8) h9) h10

/-- A subset written in increasing order. This map is used to prove existence
of a raw witness, not as the recognition algorithm. -/
def camEncRow {k t : ℕ} (x : Babai.binom (Fin k) t) : List ℕ :=
  (x.val.image Fin.val).sort (· ≤ ·)

theorem camEncRow_spec {k t : ℕ} (x : Babai.binom (Fin k) t) :
    (camEncRow x).SortedLT ∧ (camEncRow x).length = t ∧
      ∀ a ∈ camEncRow x, a < k := by
  refine ⟨Finset.sortedLT_sort _, ?_, ?_⟩
  · simp only [camEncRow, Finset.length_sort,
      Finset.card_image_of_injective _ Fin.val_injective]
    exact x.property
  · intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 (Finset.mem_sort _ |>.1 ha)
    exact i.isLt

@[simp] theorem camRawJSet_encRow {k t : ℕ} (x : Babai.binom (Fin k) t) :
    rawJSet k (camEncRow x) = x.val := by
  ext i
  simp only [mem_rawJSet, camEncRow, Finset.mem_sort, Finset.mem_image]
  constructor
  · rintro ⟨j, hj, heq⟩
    exact Fin.val_injective heq ▸ hj
  · intro hi
    exact ⟨i, hi, rfl⟩

theorem camEncRow_injective {k t : ℕ} :
    Function.Injective (camEncRow (k := k) (t := t)) := by
  intro x y h
  apply Subtype.ext
  simpa only [camRawJSet_encRow] using congrArg (rawJSet k) h

/-- Encode all values of the bijection in Theorem 11.2.3. -/
def camEncode {n s t k : ℕ} (e : Fin n ≃ (Fin s → Babai.binom (Fin k) t)) :
    RawCameron :=
  (s, t, k, List.ofFn (fun i => List.ofFn (fun j => camEncRow (e i j))))

theorem camEncode_wf {n s t k : ℕ}
    (e : Fin n ≃ (Fin s → Babai.binom (Fin k) t))
    (hs : 1 ≤ s) (ht : 1 ≤ t) (hm : max (2 * t) 5 ≤ k) (hk : 2 * t < k) :
    (camEncode e).WF n := by
  refine ⟨hs, ht, hm, hk, ?_, ?_, ?_, ?_, ?_⟩
  · simp [camEncode, RawCameron.table]
  · intro xs hxs
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hxs
    simp [RawCameron.s, camEncode]
  · intro xs hxs row hr
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hxs
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hr
    exact camEncRow_spec (e i j)
  · apply List.nodup_ofFn.2
    intro i j hij
    apply e.injective
    funext a
    apply camEncRow_injective
    exact congrFun (List.ofFn_injective hij) a
  · have hc := Fintype.card_congr e
    simpa only [Fintype.card_fin, Fintype.card_fun, Fintype.card_finset_len] using hc

/-- Decoding an encoded witness recovers the same bijection. -/
theorem camDecode_encode {n s t k : ℕ}
    (e : Fin n ≃ (Fin s → Babai.binom (Fin k) t))
    (h : (camEncode e).WF n) : decCameron (camEncode e) h = e := by
  apply Equiv.ext
  intro i
  funext j
  apply Subtype.ext
  change rawJSet k _ = (e i j).val
  simp only [camEncode, RawCameron.table, List.getElem_ofFn, camRawJSet_encRow]
  rfl

/-- Theorem 11.2.3 made effective. The domain witness may contain any values.
Only its length is used. The socle clause is a proposition, not returned data.
No condition is imposed on the routine outside the theorem's hypotheses. -/
def CameronSpec (cameron : RawGens × List ℕ → Option RawCameron) : Prop :=
  ∀ (n : ℕ) (gs : RawGens) (dom : List ℕ), dom.length = n → RawGens.WF n gs →
    25 ≤ n → Babai.IsPrimitive (decGroup n gs) →
    (n : ℝ) ^ (1 + Real.logb 2 n) ≤ Nat.card (decGroup n gs) →
    ∃ (c : RawCameron) (h : c.WF n), cameron (gs, dom) = some c ∧
      (∃ R : Fin c.s → Subgroup (decGroup n gs),
        Babai.IsSocleFactorization (decGroup n gs) R c.k) ∧
      Babai.basePower (Babai.JohnsonA c.k c.t) c.s ≤
        (decGroup n gs).map (Equiv.permCongrHom (decCameron c h)).toMonoidHom ∧
      (decGroup n gs).map (Equiv.permCongrHom (decCameron c h)).toMonoidHom ≤
        Babai.wreathProduct (Babai.JohnsonS c.k c.t) c.s

/-- The output specification contains all the conjuncts of Definition 11.2.2,
with its final bijection supplied by the returned table. -/
theorem camSpec_isCameronGroup
    (cameron : RawGens × List ℕ → Option RawCameron)
    (hpoly : PolyFun cameron) (hspec : CameronSpec cameron)
    (n : ℕ) (gs : RawGens) (dom : List ℕ) (hd : dom.length = n)
    (hw : RawGens.WF n gs) (hn : 25 ≤ n)
    (hp : Babai.IsPrimitive (decGroup n gs))
    (hb : (n : ℝ) ^ (1 + Real.logb 2 n) ≤ Nat.card (decGroup n gs)) :
    ∃ (c : RawCameron) (_ : c.WF n), cameron (gs, dom) = some c ∧
      Babai.IsCameronGroup (decGroup n gs) c.s c.t c.k := by
  obtain ⟨c, h, heq, hR, hlo, hhi⟩ := hspec n gs dom hd hw hn hp hb
  exact ⟨c, h, heq, h.s_pos, h.t_pos, h.k_max, h.k_gt,
    by simpa using h.card, hR, decCameron c h, hlo, hhi⟩

/-- The existence part of the hypothesis adds nothing to Theorem 11.2.3.
This function is chosen without a time bound. -/
theorem cameronSpec_exists :
    ∃ cameron : RawGens × List ℕ → Option RawCameron, CameronSpec cameron := by
  classical
  let P (q : RawGens × List ℕ) (c : RawCameron) : Prop :=
    ∃ h : c.WF q.2.length,
      (∃ R : Fin c.s → Subgroup (decGroup q.2.length q.1),
        Babai.IsSocleFactorization (decGroup q.2.length q.1) R c.k) ∧
      Babai.basePower (Babai.JohnsonA c.k c.t) c.s ≤
        (decGroup q.2.length q.1).map (Equiv.permCongrHom (decCameron c h)).toMonoidHom ∧
      (decGroup q.2.length q.1).map (Equiv.permCongrHom (decCameron c h)).toMonoidHom ≤
        Babai.wreathProduct (Babai.JohnsonS c.k c.t) c.s
  let f (q : RawGens × List ℕ) : Option RawCameron :=
    if h : ∃ c, P q c then some h.choose else none
  refine ⟨f, ?_⟩
  intro n gs dom hd hw hn hp hb
  subst n
  have hex : ∃ c, P (gs, dom) c := by
    obtain ⟨s, t, k, hs, ht, hm, hk, _, hR, e, hlo, hhi⟩ :=
      Babai.Theorem_11_2_3 (decGroup dom.length gs) (by simpa using hn) hp
        (by simpa using hb)
    let c := camEncode e
    have h : c.WF dom.length := camEncode_wf e hs ht hm hk
    refine ⟨c, h, hR, ?_, ?_⟩
    · simpa only [c, camDecode_encode] using hlo
    · simpa only [c, camDecode_encode] using hhi
  obtain ⟨h, hR, hlo, hhi⟩ := hex.choose_spec
  exact ⟨hex.choose, h, dif_pos hex, hR, hlo, hhi⟩

end Algo
