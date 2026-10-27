/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: Procedure Align (§14.1), lines 1 and 2 (i) — the isomorphism test and
the aligning permutation `σ̄` for Johnson schemes, on the unit-cost RAM.
-/
import Workspace.Algo.AlignJohnson
import Workspace.Algo.AlignPerm

/-!
# §14.1, Procedure Align, lines 1 and 2 (i) for Johnson schemes

> 1. If `X(x)` and `X(y)` are not `G^ϕ`-isomorphic then reject isomorphism, exit.
> 2. Else, let (i) `σ̄ ∈ Iso_{G^ϕ}(X(x), X(y))`

and (§14.1) *"This is trivial in linear time for colored equipartitions, and polynomial time
for Johnson schemes."*

This file does the Johnson half of `σ̄` for `K = S(Γ)`.  The parity correction for
`K = A(Γ)` is the next step; see the DESIGN note "A14 session 4".

## The construction

Two Johnson schemes on `Γ = [0, m)` with the *same* parameters `(m*, t*)` are always
isomorphic, and an isomorphism is written down without any search:

* on `W`, send the point with row `S` to the point of `W'` with the same row `S`.  This is
  well defined and a bijection of `W` with `W'` because, by
  `Algo.RawJohnson.WF.rowBinom_bijective`, the rows on either side are **all** the
  `t*`-subsets of `Γ* = [0, m*)`, each exactly once.  In the words of Prop. 3.2.11 this is
  the isomorphism induced by the identity of the two underlying sets `Γ*`;
* outside `W`, send the `k`-th point of `Γ ∖ W` to the `k`-th point of `Γ ∖ W'`, both in
  increasing order.  The two complements have the same size because
  `|W| = C(m*, t*) = |W'|`.

## Main definitions

* `Algo.alignJOutList`, `Algo.alignJRank` — the complement of `W` and the position of a
  point in it;
* `Algo.alignJMatch`, `Algo.alignJPerm` — **the `σ̄` of line 2 (i)** for Johnson schemes.

## Main results

* `Algo.alignJPerm_wf` — the answer is a permutation of `Γ`;
* `Algo.alignJPerm_smul` — **it is an isomorphism**: it carries the decoded structure of the
  first scheme to the decoded structure of the second;
* `Algo.alignJPerm_mem_structIso` — hence it lies in `Iso_{S(Γ)}(X(x), X(y))`
  (`Babai.structIso`);
* `Algo.polyFun_alignJPerm` — **the running time**.

No axiom, no `sorry`.
-/

namespace Algo

open RAM RAM.Targets
open Equiv (Perm)

/-! ## Looking a key up in a parallel pair of lists -/

/-- `Algo.rawJ_lookup_zip` at an arbitrary key type: the value at the position of the key.
Here the keys are the **rows** and the values are the points of `W'`, the other way round
from `Algo.rawJRow`. -/
theorem alignJ_lookup_zip {α β : Type*} [BEq α] [LawfulBEq α] :
    ∀ (K : List α) (V : List β) (i : ℕ) (k : α) (v : β),
      K.Nodup → K.length = V.length → K[i]? = some k → V[i]? = some v →
      (K.zip V).lookup k = some v := by
  intro K
  induction K with
  | nil => intro V i k v _ _ hk _; simp at hk
  | cons a K ih =>
    intro V i k v hnd hlen hk hv
    cases V with
    | nil => simp at hlen
    | cons b V =>
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hk hv
        subst hk; subst hv
        simp
      | succ j =>
        simp only [List.getElem?_cons_succ] at hk hv
        have hmem : k ∈ K := List.mem_of_getElem? hk
        have hne : ¬ (k = a) := by
          rintro rfl
          exact (List.nodup_cons.1 hnd).1 hmem
        have hb : (k == a) = false := beq_eq_false_iff_ne.2 hne
        simp only [List.zip_cons_cons, List.lookup, hb]
        exact ih V j k v (List.nodup_cons.1 hnd).2 (by simpa using hlen) hk hv

/-! ## The points outside `W` -/

/-- The points of `[0, N)` outside `W`, in increasing order. -/
def alignJOutList (p : List ℕ × List ℕ) : List ℕ :=
  (List.range p.1.length).filter (fun v => !decide (v ∈ p.2))

/-- The position of a point in the increasing list of the points outside `W`: the number of
points below it that are outside `W`. -/
def alignJRank (p : (List ℕ × List ℕ) × ℕ) : ℕ :=
  ((List.range p.1.1.length).filter
    (fun v => decide (v < p.2) && !decide (v ∈ p.1.2))).length

theorem alignJOutList_nodup (dom W : List ℕ) : (alignJOutList (dom, W)).Nodup :=
  List.Nodup.filter _ List.nodup_range

theorem alignJOutList_lt {dom W : List ℕ} {a : ℕ} (ha : a ∈ alignJOutList (dom, W)) :
    a < dom.length := List.mem_range.1 (List.mem_of_mem_filter ha)

theorem alignJOutList_notMem {dom W : List ℕ} {a : ℕ} (ha : a ∈ alignJOutList (dom, W)) :
    a ∉ W := by
  have := List.of_mem_filter ha
  simpa using this

/-- The complement of `W` in `[0, N)` has `N - |W|` points. -/
theorem length_alignJOutList {dom W : List ℕ} {N : ℕ} (hd : dom.length = N) (hnd : W.Nodup)
    (hlt : ∀ a ∈ W, a < N) : (alignJOutList (dom, W)).length = N - W.length := by
  classical
  have hin : ((List.range N).filter (fun v => decide (v ∈ W))).Perm W := by
    refine List.perm_of_nodup_nodup_toFinset_eq (List.Nodup.filter _ List.nodup_range) hnd ?_
    ext a
    simp only [List.mem_toFinset, List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hlt a h, h⟩⟩
  have hsplit : ((List.range N).filter (fun v => decide (v ∈ W))).length
      + (alignJOutList (dom, W)).length = N := by
    rw [alignJOutList]
    show ((List.range N).filter (fun v => decide (v ∈ W))).length
      + ((List.range dom.length).filter (fun v => !decide (v ∈ W))).length = N
    rw [hd, ← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    have h0 := List.length_eq_countP_add_countP (l := List.range N)
      (p := fun v => decide (v ∈ W))
    rw [List.length_range] at h0
    simpa using h0.symm
  rw [hin.length_eq] at hsplit
  omega

/-- The rank is below the size of the complement. -/
theorem alignJRank_lt {dom W : List ℕ} {N u : ℕ} (hd : dom.length = N) (hu : u < N)
    (huW : u ∉ W) : alignJRank ((dom, W), u) < (alignJOutList (dom, W)).length := by
  show ((List.range dom.length).filter (fun v => decide (v < u) && !decide (v ∈ W))).length
    < ((List.range dom.length).filter (fun v => !decide (v ∈ W))).length
  rw [hd]
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  refine countP_lt_countP (a := u) (List.range N) (fun b _ hb => ?_) (List.mem_range.2 hu)
    (by simpa using huW) (by simp)
  simpa using (by simpa using hb : b < u ∧ b ∉ W).2

/-- The rank is strictly monotone on the complement. -/
theorem alignJRank_lt_of_lt {dom W : List ℕ} {N u v : ℕ} (hd : dom.length = N) (huv : u < v)
    (hv : v < N) (huW : u ∉ W) :
    alignJRank ((dom, W), u) < alignJRank ((dom, W), v) := by
  show ((List.range dom.length).filter (fun w => decide (w < u) && !decide (w ∈ W))).length
    < ((List.range dom.length).filter (fun w => decide (w < v) && !decide (w ∈ W))).length
  rw [hd]
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  refine countP_lt_countP (a := u) (List.range N) (fun b _ hb => ?_)
    (List.mem_range.2 (lt_trans huv hv)) (by simpa using ⟨huv, huW⟩) (by simp)
  have hb' : b < u ∧ b ∉ W := by simpa using hb
  simpa using ⟨lt_trans hb'.1 huv, hb'.2⟩

/-! ## The aligning permutation -/

/-- The image of one point of `Γ` under `σ̄`: a point of `W` goes to the point of `W'` with
the same row, a point outside `W` goes to the point of `Γ ∖ W'` at the same position. -/
def alignJMatch (p : (List ℕ × (RawJohnson × RawJohnson)) × ℕ) : ℕ :=
  if p.2 ∈ p.1.2.1.1 then
    ((p.1.2.2.2.2.zip p.1.2.2.1).lookup (rawJRow (p.1.2.1, p.2))).getD 0
  else
    (alignJOutList (p.1.1, p.1.2.2.1)).getD
      (alignJRank ((p.1.1, p.1.2.1.1), p.2)) 0

/-- §14.1, **line 2 (i)** for Johnson schemes: the aligning permutation `σ̄`. -/
def alignJPerm (p : List ℕ × (RawJohnson × RawJohnson)) : RawPerm :=
  (List.range p.1.length).map (fun u => alignJMatch (p, u))

/-! ## Correctness -/

section Spec

variable {m ms ts : ℕ} {dom : List ℕ} {r r' : RawJohnson}

/-- The row map is injective on `W`. -/
theorem rawJRow_inj_of_wf (h : RawJohnson.WF m ms ts r) {u v : ℕ} (hu : u ∈ r.1)
    (hv : v ∈ r.1) (huv : rawJRow (r, u) = rawJRow (r, v)) : u = v := by
  obtain ⟨i, hi, hiu⟩ := List.getElem_of_mem hu
  obtain ⟨j, hj, hjv⟩ := List.getElem_of_mem hv
  rw [← hiu, ← hjv, h.rawJRow_getElem hi, h.rawJRow_getElem hj] at huv
  have : i = j := (List.Nodup.getElem_inj_iff h.rowsNodup).1 huv
  subst this
  rw [← hiu, ← hjv]

/-- **The match on `W`.**  A point of `W` goes to a point of `W'` with the same row. -/
theorem alignJMatch_mem (h : RawJohnson.WF m ms ts r) (h' : RawJohnson.WF m ms ts r')
    {u : ℕ} (hu : u ∈ r.1) :
    alignJMatch ((dom, (r, r')), u) ∈ r'.1 ∧
      rawJRow (r', alignJMatch ((dom, (r, r')), u)) = rawJRow (r, u) := by
  classical
  have hrow : rawJRow (r, u) ∈ r.2.2 := h.rawJRow_mem hu
  obtain ⟨j, hj⟩ := h'.rowBinom_bijective.2
    (⟨rawJSet ms (rawJRow (r, u)), h.card_rowSet hrow⟩ : Babai.binom (Fin ms) ts)
  have hjrow : r'.2.2[(j : ℕ)] = rawJRow (r, u) :=
    rawJSet_injOn (h'.rowSorted _ (List.getElem_mem j.isLt)) (h.rowSorted _ hrow)
      (h'.rowLt _ (List.getElem_mem j.isLt)) (h.rowLt _ hrow) (congrArg Subtype.val hj)
  have hjlt : (j : ℕ) < r'.1.length := by rw [← h'.rowsLen]; exact j.isLt
  have hlk : (r'.2.2.zip r'.1).lookup (rawJRow (r, u)) = some (r'.1[(j : ℕ)]) := by
    refine alignJ_lookup_zip r'.2.2 r'.1 (j : ℕ) (rawJRow (r, u)) _ h'.rowsNodup
      h'.rowsLen ?_ ?_
    · rw [List.getElem?_eq_getElem j.isLt, hjrow]
    · exact List.getElem?_eq_getElem hjlt
  have hM : alignJMatch ((dom, (r, r')), u) = r'.1[(j : ℕ)] := by
    show (if u ∈ r.1 then _ else _) = _
    rw [if_pos hu, hlk]
    rfl
  refine ⟨hM ▸ List.getElem_mem hjlt, ?_⟩
  rw [hM, h'.rawJRow_getElem hjlt, hjrow]

/-- **The match outside `W`.**  A point outside `W` goes to a point outside `W'`. -/
theorem alignJMatch_notMem (hd : dom.length = m) (h : RawJohnson.WF m ms ts r)
    (h' : RawJohnson.WF m ms ts r')
    {u : ℕ} (hu : u < m) (huW : u ∉ r.1) :
    alignJMatch ((dom, (r, r')), u) ∈ alignJOutList (dom, r'.1) := by
  have hlen : r.1.length = r'.1.length := by
    rw [← h.rowsLen, ← h'.rowsLen, h.card, h'.card]
  have hrk : alignJRank ((dom, r.1), u) < (alignJOutList (dom, r'.1)).length := by
    rw [length_alignJOutList hd h'.wNodup h'.wLt, ← hlen,
      ← length_alignJOutList hd h.wNodup h.wLt]
    exact alignJRank_lt hd hu huW
  have hM : alignJMatch ((dom, (r, r')), u)
      = (alignJOutList (dom, r'.1)).getD (alignJRank ((dom, r.1), u)) 0 := by
    show (if u ∈ r.1 then _ else _) = _
    rw [if_neg huW]
  rw [hM, List.getD_eq_getElem _ _ hrk]
  exact List.getElem_mem hrk

/-- `σ̄` is injective. -/
theorem alignJMatch_inj (hd : dom.length = m) (h : RawJohnson.WF m ms ts r)
    (h' : RawJohnson.WF m ms ts r')
    {u v : ℕ} (hu : u < m) (hv : v < m)
    (huv : alignJMatch ((dom, (r, r')), u) = alignJMatch ((dom, (r, r')), v)) : u = v := by
  classical
  by_cases hup : u ∈ r.1 <;> by_cases hvp : v ∈ r.1
  · have h1 := (alignJMatch_mem (dom := dom) h h' hup).2
    have h2 := (alignJMatch_mem (dom := dom) h h' hvp).2
    rw [huv, h2] at h1
    exact rawJRow_inj_of_wf h hup hvp h1.symm
  · exact absurd ((alignJMatch_mem (dom := dom) h h' hup).1)
      (by rw [huv]; exact alignJOutList_notMem (alignJMatch_notMem hd h h' hv hvp))
  · exact absurd ((alignJMatch_mem (dom := dom) h h' hvp).1)
      (by rw [← huv]; exact alignJOutList_notMem (alignJMatch_notMem hd h h' hu hup))
  · have hlen : r.1.length = r'.1.length := by
      rw [← h.rowsLen, ← h'.rowsLen, h.card, h'.card]
    have hbd : ∀ {w : ℕ}, w < m → w ∉ r.1 →
        alignJRank ((dom, r.1), w) < (alignJOutList (dom, r'.1)).length := by
      intro w hw hwW
      rw [length_alignJOutList hd h'.wNodup h'.wLt, ← hlen,
        ← length_alignJOutList hd h.wNodup h.wLt]
      exact alignJRank_lt hd hw hwW
    have hMu : alignJMatch ((dom, (r, r')), u)
        = (alignJOutList (dom, r'.1))[alignJRank ((dom, r.1), u)]'(hbd hu hup) := by
      show (if u ∈ r.1 then _ else _) = _
      rw [if_neg hup, List.getD_eq_getElem _ _ (hbd hu hup)]
    have hMv : alignJMatch ((dom, (r, r')), v)
        = (alignJOutList (dom, r'.1))[alignJRank ((dom, r.1), v)]'(hbd hv hvp) := by
      show (if v ∈ r.1 then _ else _) = _
      rw [if_neg hvp, List.getD_eq_getElem _ _ (hbd hv hvp)]
    rw [hMu, hMv] at huv
    have hrk : alignJRank ((dom, r.1), u) = alignJRank ((dom, r.1), v) :=
      (List.Nodup.getElem_inj_iff (alignJOutList_nodup dom r'.1)).1 huv
    rcases lt_trichotomy u v with hlt | heq | hgt
    · exact absurd hrk (Nat.ne_of_lt (alignJRank_lt_of_lt hd hlt hv hup))
    · exact heq
    · exact absurd hrk.symm (Nat.ne_of_lt (alignJRank_lt_of_lt hd hgt hu hvp))

theorem alignJMatch_lt (hd : dom.length = m) (h : RawJohnson.WF m ms ts r)
    (h' : RawJohnson.WF m ms ts r')
    {u : ℕ} (hu : u < m) : alignJMatch ((dom, (r, r')), u) < m := by
  by_cases hup : u ∈ r.1
  · exact h'.wLt _ (alignJMatch_mem (dom := dom) h h' hup).1
  · exact hd ▸ alignJOutList_lt (alignJMatch_notMem hd h h' hu hup)

/-- **`σ̄` is a permutation of `Γ`.** -/
theorem alignJPerm_wf (hd : dom.length = m) (h : RawJohnson.WF m ms ts r)
    (h' : RawJohnson.WF m ms ts r') :
    RawPerm.WF m (alignJPerm (dom, (r, r'))) := by
  have hlen : (alignJPerm (dom, (r, r'))).length = m := by
    rw [alignJPerm, List.length_map, List.length_range, hd]
  refine ⟨hlen, ?_, ?_⟩
  · intro a ha
    rw [alignJPerm, List.mem_map] at ha
    obtain ⟨u, hu, rfl⟩ := ha
    exact alignJMatch_lt hd h h' (hd ▸ List.mem_range.1 hu)
  · rw [alignJPerm]
    refine List.Nodup.map_on ?_ List.nodup_range
    intro u hu v hv huv
    exact alignJMatch_inj hd h h' (hd ▸ List.mem_range.1 hu) (hd ▸ List.mem_range.1 hv) huv

theorem labAt_alignJPerm (hd : dom.length = m) {u : ℕ} (hu : u < m) :
    labAt (alignJPerm (dom, (r, r'))) u = alignJMatch ((dom, (r, r')), u) := by
  have hlt : u < ((List.range dom.length).map
      (fun w => alignJMatch ((dom, (r, r')), w))).length := by
    rw [List.length_map, List.length_range, hd]; exact hu
  show ((List.range dom.length).map (fun w => alignJMatch ((dom, (r, r')), w))).getD u 0 = _
  rw [List.getD_eq_getElem _ _ hlt, List.getElem_map, List.getElem_range]

/-- `σ̄` carries `W` onto `W'`, and nothing else onto `W'`. -/
theorem alignJMatch_mem_iff (hd : dom.length = m) (h : RawJohnson.WF m ms ts r)
    (h' : RawJohnson.WF m ms ts r') {u : ℕ} (hu : u < m) :
    alignJMatch ((dom, (r, r')), u) ∈ r'.1 ↔ u ∈ r.1 := by
  refine ⟨fun hin => ?_, fun hin => (alignJMatch_mem (dom := dom) h h' hin).1⟩
  by_contra hnot
  exact alignJOutList_notMem (alignJMatch_notMem hd h h' hu hnot) hin

/-- A structure on `Γ` is carried to another by `α` exactly when the two colorings agree
along `α`.  (Lean acts on the left, so `α • X = Y` reads the images backwards; this is the
forward reading.) -/
theorem colStruct_smul_eq {m : ℕ} {α : Perm (Fin m)} {X Y : Babai.ColStruct (Fin m) ℕ}
    (hv : ∀ u, Y.vcol (α u) = X.vcol u) (he : ∀ u v, Y.ecol (α u) (α v) = X.ecol u v) :
    α • X = Y := by
  refine Babai.ColStruct.ext (funext fun u => ?_) (funext fun u => funext fun v => ?_)
  · show X.vcol (α⁻¹ u) = Y.vcol u
    have := hv (α⁻¹ u)
    rw [show α (α⁻¹ u) = u from Equiv.apply_symm_apply α u] at this
    exact this.symm
  · show X.ecol (α⁻¹ u) (α⁻¹ v) = Y.ecol u v
    have := he (α⁻¹ u) (α⁻¹ v)
    rw [show α (α⁻¹ u) = u from Equiv.apply_symm_apply α u,
      show α (α⁻¹ v) = v from Equiv.apply_symm_apply α v] at this
    exact this.symm

/-- §14.1, **line 2 (i)** for Johnson schemes: the computed `σ̄` **is an isomorphism** of the
two decoded structures. -/
theorem alignJPerm_smul (hd : dom.length = m) (h : RawJohnson.WF m ms ts r)
    (h' : RawJohnson.WF m ms ts r') :
    decPerm m (alignJPerm (dom, (r, r'))) • decJohnson m r = decJohnson m r' := by
  have hwf := alignJPerm_wf hd h h'
  have himg : ∀ u : Fin m,
      ((decPerm m (alignJPerm (dom, (r, r'))) u : Fin m) : ℕ)
        = alignJMatch ((dom, (r, r')), (u : ℕ)) := fun u => by
    rw [← labAt_eq_decPerm hwf u.isLt, labAt_alignJPerm hd u.isLt]
  have hmem : ∀ u : Fin m,
      ((decPerm m (alignJPerm (dom, (r, r'))) u : Fin m) : ℕ) ∈ r'.1 ↔ (u : ℕ) ∈ r.1 :=
    fun u => by rw [himg u]; exact alignJMatch_mem_iff hd h h' u.isLt
  refine colStruct_smul_eq (fun u => ?_) (fun u v => ?_)
  · show (if _ ∈ r'.1 then 1 else 0) = (if _ ∈ r.1 then 1 else 0)
    by_cases hc : (u : ℕ) ∈ r.1
    · rw [if_pos ((hmem u).2 hc), if_pos hc]
    · rw [if_neg (fun hx => hc ((hmem u).1 hx)), if_neg hc]
  · by_cases hcu : (u : ℕ) ∈ r.1
    · by_cases hcv : (v : ℕ) ∈ r.1
      · rw [decJohnson_ecol_mem m r' ((hmem u).2 hcu) ((hmem v).2 hcv),
          decJohnson_ecol_mem m r hcu hcv, rawJDiff, rawJDiff, himg u, himg v,
          (alignJMatch_mem (dom := dom) h h' hcu).2,
          (alignJMatch_mem (dom := dom) h h' hcv).2]
      · show (if _ ∈ r'.1 then (if _ ∈ r'.1 then _ else 0) else 0)
          = (if _ ∈ r.1 then (if _ ∈ r.1 then _ else 0) else 0)
        rw [if_pos ((hmem u).2 hcu), if_pos hcu,
          if_neg (fun hx => hcv ((hmem v).1 hx)), if_neg hcv]
    · show (if _ ∈ r'.1 then _ else 0) = (if _ ∈ r.1 then _ else 0)
      rw [if_neg (fun hx => hcu ((hmem u).1 hx)), if_neg hcu]

/-- §14.1, **line 2 (i)** for Johnson schemes: the computed `σ̄` lies in
`Iso_{S(Γ)}(X(x), X(y))`. -/
theorem alignJPerm_mem_structIso (hd : dom.length = m) (h : RawJohnson.WF m ms ts r)
    (h' : RawJohnson.WF m ms ts r') :
    decPerm m (alignJPerm (dom, (r, r')))
      ∈ Babai.structIso (Set.univ : Set (Perm (Fin m))) (decJohnson m r) (decJohnson m r') :=
  ⟨Set.mem_univ _, alignJPerm_smul hd h h'⟩

end Spec

/-! ## The running time -/

theorem polyFun_alignJOutList : PolyFun alignJOutList := by
  have hq : PolyFun (fun z : List ℕ × ℕ => !decide (z.2 ∈ z.1)) :=
    polyFun_rawJNot ((polyFun_snd.pair polyFun_fst).comp polyFun_natListMem)
  have hin : PolyFun (fun p : List ℕ × List ℕ => (p.2, List.range p.1.length)) :=
    polyFun_snd.pair (polyFun_fst.comp polyFun_rangeLength)
  exact (hin.comp (PolyFun.filterParam hq)).of_eq (fun _ => rfl)

theorem polyFun_alignJRank : PolyFun alignJRank := by
  have hq : PolyFun (fun z : (List ℕ × ℕ) × ℕ =>
      decide (z.2 < z.1.2) && !decide (z.2 ∈ z.1.1)) :=
    polyFun_rawJAnd
      ((((polyFun_snd.pair (polyFun_const 1)).comp polyFun_add).pair
        (polyFun_fst.comp polyFun_snd)).comp polyFun_le
          |>.of_eq (fun z => by
            show decide (z.2 + 1 ≤ z.1.2) = decide (z.2 < z.1.2)
            exact decide_eq_decide.2 Nat.add_one_le_iff))
      (polyFun_rawJNot ((polyFun_snd.pair (polyFun_fst.comp polyFun_fst)).comp
        polyFun_natListMem))
  have hin : PolyFun (fun p : (List ℕ × List ℕ) × ℕ =>
      ((p.1.2, p.2), List.range p.1.1.length)) :=
    (((polyFun_fst.comp polyFun_snd).pair polyFun_snd)).pair
      ((polyFun_fst.comp polyFun_fst).comp polyFun_rangeLength)
  exact ((hin.comp (PolyFun.filterParam hq)).comp polyFun_length).of_eq (fun _ => rfl)

/-- Reading the row of a point is a `RAM.PolyFun`. -/
theorem polyFun_rawJRow : PolyFun rawJRow := by
  have htab : PolyFun (fun p : RawJohnson × ℕ => p.1.1.zip p.1.2.2) :=
    ((polyFun_fst.comp polyFun_fst).pair
      ((polyFun_fst.comp polyFun_snd).comp polyFun_snd)).comp polyFun_zip
  exact (((htab.pair polyFun_snd).comp polyFun_natLookup).pair
    (polyFun_const ([] : List ℕ))).comp polyFun_optionGetD

theorem polyFun_alignJMatch : PolyFun alignJMatch := by
  have htest : PolyFun (fun p : (List ℕ × (RawJohnson × RawJohnson)) × ℕ =>
      decide (p.2 ∈ p.1.2.1.1)) :=
    (polyFun_snd.pair (((polyFun_fst.comp polyFun_snd).comp polyFun_fst).comp
      polyFun_fst)).comp polyFun_natListMem
  have hrow : PolyFun (fun p : (List ℕ × (RawJohnson × RawJohnson)) × ℕ =>
      rawJRow (p.1.2.1, p.2)) :=
    ((((polyFun_fst.comp polyFun_snd).comp polyFun_fst).pair polyFun_snd)).comp
      polyFun_rawJRow
  have htab : PolyFun (fun p : (List ℕ × (RawJohnson × RawJohnson)) × ℕ =>
      p.1.2.2.2.2.zip p.1.2.2.1) :=
    (((((polyFun_fst.comp polyFun_snd).comp polyFun_snd).comp polyFun_snd).comp
      polyFun_snd).pair (((polyFun_fst.comp polyFun_snd).comp polyFun_snd).comp
        polyFun_fst)).comp polyFun_zip
  have hyes : PolyFun (fun p : (List ℕ × (RawJohnson × RawJohnson)) × ℕ =>
      ((p.1.2.2.2.2.zip p.1.2.2.1).lookup (rawJRow (p.1.2.1, p.2))).getD 0) :=
    (((htab.pair hrow).comp (polyFun_listLookup (β := ℕ) polyFun_listNatEq)).pair
      (polyFun_const 0)).comp polyFun_optionGetD
  have hno : PolyFun (fun p : (List ℕ × (RawJohnson × RawJohnson)) × ℕ =>
      (alignJOutList (p.1.1, p.1.2.2.1)).getD (alignJRank ((p.1.1, p.1.2.1.1), p.2)) 0) :=
    (((((polyFun_fst.comp polyFun_fst).pair
        (((polyFun_fst.comp polyFun_snd).comp polyFun_snd).comp polyFun_fst)).comp
        polyFun_alignJOutList).pair
      ((((polyFun_fst.comp polyFun_fst).pair
        (((polyFun_fst.comp polyFun_snd).comp polyFun_fst).comp polyFun_fst)).pair
        polyFun_snd).comp polyFun_alignJRank)).pair (polyFun_const 0)).comp polyFun_getD
  exact (PolyFun.ite htest hyes hno).of_eq (fun p => by
    by_cases hc : p.2 ∈ p.1.2.1.1 <;> simp [alignJMatch, hc])

/-- §14.1, **line 2 (i)** for Johnson schemes **runs in polynomial time**. -/
theorem polyFun_alignJPerm : PolyFun alignJPerm :=
  ((polyFun_id.pair (polyFun_fst.comp polyFun_rangeLength)).comp
    (PolyFun.mapParam polyFun_alignJMatch)).of_eq (fun _ => rfl)

end Algo
