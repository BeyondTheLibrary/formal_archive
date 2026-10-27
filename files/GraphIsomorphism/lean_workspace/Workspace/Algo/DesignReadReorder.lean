import Workspace.Algo.DesignReadPipelineRelabel

/-! # The computed coloring does not depend on the listing order

Sec. 5.2 (v2.5) builds the canonical coloring `F3 ∘ F2 ∘ F1` of a `k`-ary relational
structure. The raw routines list the vertices, the tuples and the members of each relation
in some order. This file proves that the colors they compute (read with `tblGet`) depend
only on the vertex set and on which tuples lie in which relation, not on those orders.

Every color name is a rank among the tags that occur, and a rank only counts the distinct
tags that are smaller. So two tables that give every tuple the same color stay so after
each round. The relations enter only through the characteristic vector of a tuple; two
relation lists that agree on every tuple of the table give the same vectors up to trailing
zeros, and trailing zeros do not change a lexicographic comparison.
-/
namespace Algo
open Babai RAM

/-- Two raw tables over the same domain that give every tuple the same color. -/
structure WLSame (n k : ℕ) (p q : RawWL) : Prop where
  left : RawWL.WF n k p
  right : RawWL.WF n k q
  get : ∀ t,tblGet (p.2,t) = tblGet (q.2,t)

theorem tblGet_map_key (l : List (List ℕ × ℕ)) (F : List ℕ → ℕ) (t : List ℕ) :
    tblGet (l.map (fun q => (q.1,F q.1)),t) = if t ∈ l.map Prod.fst then F t else 0 := by
  rw [tblGet,lookup_map_key]
  split <;> rfl

namespace WLSame
variable {n k : ℕ} {p q : RawWL}

theorem key_iff (h : WLSame n k p q) (t : List ℕ) :
    t ∈ p.2.map Prod.fst ↔ t ∈ q.2.map Prod.fst := by
  rw [h.left.keyMem,h.right.keyMem]

theorem dom_perm (h : WLSame n k p q) : p.1.Perm q.1 :=
  (List.perm_ext_iff_of_nodup h.left.domNodup h.right.domNodup).2
    (fun a => by rw [h.left.domMem,h.right.domMem])

theorem length_eq (h : WLSame n k p q) : p.2.length = q.2.length := by
  rw [length_table h.left,length_table h.right]

/-- Recoloring both tables by two rules that agree on the tuples keeps them the same. -/
theorem map {F G : List ℕ → ℕ} (h : WLSame n k p q)
    (hp : RawWL.WF n k (p.1,p.2.map (fun r => (r.1,F r.1))))
    (hq : RawWL.WF n k (q.1,q.2.map (fun r => (r.1,G r.1))))
    (hFG : ∀ t ∈ p.2.map Prod.fst,F t = G t) :
    WLSame n k (p.1,p.2.map (fun r => (r.1,F r.1))) (q.1,q.2.map (fun r => (r.1,G r.1))) := by
  refine ⟨hp,hq,fun t => ?_⟩
  dsimp only
  rw [tblGet_map_key,tblGet_map_key]
  by_cases ht : t ∈ p.2.map Prod.fst
  · rw [if_pos ht,if_pos ((h.key_iff t).1 ht),hFG t ht]
  · rw [if_neg ht,if_neg (fun h' => ht ((h.key_iff t).2 h'))]

/-! ### One round of `k`-ary WL -/

theorem innerVec_eq (h : WLSame n k p q) (t : List ℕ) (y : ℕ) :
    innerVec p.2 t y = innerVec q.2 t y := by
  simp only [innerVec,h.get]

theorem mem_allVecs_iff {p : RawWL} {v : List ℕ} :
    v ∈ allVecs p ↔ ∃ t ∈ p.2.map Prod.fst,∃ y ∈ p.1,innerVec p.2 t y = v := by
  constructor
  · intro hv
    obtain ⟨r,hr,y,hy,rfl⟩ := exists_of_mem_allVecs hv
    exact ⟨r.1,List.mem_map_of_mem hr,y,hy,rfl⟩
  · rintro ⟨t,ht,y,hy,rfl⟩
    obtain ⟨r,hr,rfl⟩ := List.mem_map.1 ht
    exact mem_allVecs hr hy

theorem vecSet_iff (h : WLSame n k p q) (v : List ℕ) : v ∈ vecSet p ↔ v ∈ vecSet q := by
  rw [mem_vecSet,mem_vecSet,mem_allVecs_iff,mem_allVecs_iff]
  constructor
  · rintro ⟨t,ht,y,hy,rfl⟩
    exact ⟨t,(h.key_iff t).1 ht,y,h.dom_perm.subset hy,(h.innerVec_eq t y).symm⟩
  · rintro ⟨t,ht,y,hy,rfl⟩
    exact ⟨t,(h.key_iff t).2 ht,y,h.dom_perm.symm.subset hy,h.innerVec_eq t y⟩

theorem vecSet_rank (h : WLSame n k p q) (v : List ℕ) :
    rankIn (vecSet p,v) = rankIn (vecSet q,v) :=
  rankIn_congr_mem (nodup_vecSet p) (nodup_vecSet q) h.vecSet_iff v

theorem vecSet_length (h : WLSame n k p q) : (vecSet p).length = (vecSet q).length :=
  ((List.perm_ext_iff_of_nodup (nodup_vecSet p) (nodup_vecSet q)).2 h.vecSet_iff).length_eq

theorem wlCount_eq (h : WLSame n k p q) (t : List ℕ) (j : ℕ) :
    wlCount p t j = wlCount q t j := by
  unfold wlCount
  have hf : (fun y => decide (rankIn (vecSet p,innerVec p.2 t y) = j)) =
      (fun y => decide (rankIn (vecSet q,innerVec q.2 t y) = j)) := by
    funext y
    rw [h.vecSet_rank,h.innerVec_eq]
  rw [hf]
  exact (h.dom_perm.filter _).length_eq

theorem wlTagAt_eq (h : WLSame n k p q) (t : List ℕ) : wlTagAt p t = wlTagAt q t := by
  simp only [wlTagAt,h.get t,h.vecSet_length,h.wlCount_eq t]

theorem wlTagSet_iff (h : WLSame n k p q) (u : List ℕ) : u ∈ wlTagSet p ↔ u ∈ wlTagSet q := by
  rw [mem_wlTagSet,mem_wlTagSet,wlTags,wlTags,List.mem_map,List.mem_map]
  constructor
  · rintro ⟨r,hr,rfl⟩
    obtain ⟨r',hr',he⟩ := List.mem_map.1 ((h.key_iff r.1).1 (List.mem_map_of_mem hr))
    exact ⟨r',hr',by rw [he,h.wlTagAt_eq]⟩
  · rintro ⟨r,hr,rfl⟩
    obtain ⟨r',hr',he⟩ := List.mem_map.1 ((h.key_iff r.1).2 (List.mem_map_of_mem hr))
    exact ⟨r',hr',by rw [he,h.wlTagAt_eq]⟩

theorem wlNewCol_eq (h : WLSame n k p q) (t : List ℕ) : wlNewCol p t = wlNewCol q t := by
  rw [wlNewCol,wlNewCol,h.wlTagAt_eq,
    rankIn_congr_mem (nodup_wlTagSet p) (nodup_wlTagSet q) h.wlTagSet_iff]

theorem step (h : WLSame n k p q) : WLSame n k (rawWLStep p) (rawWLStep q) :=
  h.map (rawWLStep_wf h.left) (rawWLStep_wf h.right) (fun t _ => h.wlNewCol_eq t)

theorem iterate (h : WLSame n k p q) (j : ℕ) :
    WLSame n k (rawWLStep^[j] p) (rawWLStep^[j] q) := by
  induction j with
  | zero => exact h
  | succ j ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
    exact ih.step

/-- Sec. 5.4.1: the stable `k`-ary WL refinement of two same tables. -/
theorem stable (h : WLSame n k p q) : WLSame n k (rawWLStable p) (rawWLStable q) := by
  rw [rawWLStable_eq_iterate,rawWLStable_eq_iterate,h.length_eq]
  exact h.iterate _

/-! ### The functor `F2` -/

theorem f2TagAtI_eq (h : WLSame n k p q) (I : IdxP) (t : List ℕ) :
    f2TagAtI I p t = f2TagAtI I q t := by
  simp only [f2TagAtI,h.get]

theorem f2TagSetI_iff (h : WLSame n k p q) (I : IdxP) (u : List ℕ) :
    u ∈ f2TagSetI I p ↔ u ∈ f2TagSetI I q := by
  rw [f2TagSetI,f2TagSetI,RAM.mem_dedupG_nil,RAM.mem_dedupG_nil,f2TagsI,f2TagsI,
    List.mem_map,List.mem_map]
  constructor
  · rintro ⟨r,hr,rfl⟩
    obtain ⟨r',hr',he⟩ := List.mem_map.1 ((h.key_iff r.1).1 (List.mem_map_of_mem hr))
    exact ⟨r',hr',by rw [he,h.f2TagAtI_eq]⟩
  · rintro ⟨r,hr,rfl⟩
    obtain ⟨r',hr',he⟩ := List.mem_map.1 ((h.key_iff r.1).2 (List.mem_map_of_mem hr))
    exact ⟨r',hr',by rw [he,h.f2TagAtI_eq]⟩

/-- Sec. 5.1.5: the functor `F2` on two same tables. -/
theorem f2 (h : WLSame n k p q) (I : IdxP) : WLSame n k (rawF2I I p) (rawF2I I q) := by
  refine h.map (rawF2I_wf h.left) (rawF2I_wf h.right) (fun t _ => ?_)
  rw [f2NewColI,f2NewColI,h.f2TagAtI_eq]
  exact rankIn_congr_mem (RAM.nodup_dedupG _) (RAM.nodup_dedupG _) (h.f2TagSetI_iff I) _

end WLSame

/-! ### The functor `F1` -/

/-- Two relation lists that put the same tuples of the table in the same relations. -/
def RelsAgree (n k : ℕ) (rels rels' : RawRelStruct) : Prop :=
  ∀ (i : ℕ) (t : List ℕ),t.length = k → (∀ a ∈ t,a < n) →
    (t ∈ rels.getD i [] ↔ t ∈ rels'.getD i [])

theorem cmpRec_append_same : ∀ (u v w : List ℕ),u.length = v.length →
    cmpRec (u ++ w) (v ++ w) = cmpRec u v
  | [],[],w,_ => by simp
  | [],_ :: _,_,h => by simp at h
  | _ :: _,[],_,h => by simp at h
  | a :: u,b :: v,w,h => by
    simp only [List.cons_append,cmpRec_cons]
    rw [cmpRec_append_same u v w (by simpa using h)]

/-- Padding every string of one length by the same suffix keeps every rank. -/
theorem rankIn_append_same {D : List (List ℕ)} {t : List ℕ} (w : List ℕ)
    (hD : ∀ u ∈ D,u.length = t.length) :
    rankIn (D.map (· ++ w),t ++ w) = rankIn (D,t) := by
  rw [rankIn_eq_countP,rankIn_eq_countP,List.countP_map]
  apply List.countP_congr
  intro u hu
  simp only [Function.comp_apply,lexLtB_eq,cmpRec_append_same u t w (hD u hu)]

theorem getElem_membVec {rels : RawRelStruct} {t : List ℕ} {i : ℕ}
    (hi : i < (membVec (rels,t)).length) :
    (membVec (rels,t))[i] = if t ∈ rels.getD i [] then 1 else 0 := by
  simp only [membVec,List.getElem_map]
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]

theorem membVec_pad {n k : ℕ} {rels rels' : RawRelStruct} (h : RelsAgree n k rels rels')
    {t : List ℕ} (hl : t.length = k) (ht : ∀ a ∈ t,a < n) :
    membVec (rels,t) ++ List.replicate rels'.length 0 =
      membVec (rels',t) ++ List.replicate rels.length 0 := by
  apply List.ext_getElem (by simp [Nat.add_comm])
  intro i h1 h2
  have hc : ∀ (R S : RawRelStruct) (hi : i < R.length + S.length),
      (membVec (R,t) ++ List.replicate S.length 0)[i]'(by simpa using hi) =
        if t ∈ R.getD i [] then 1 else 0 := by
    intro R S hi
    by_cases hr : i < R.length
    · rw [List.getElem_append_left (by simpa using hr),getElem_membVec]
    · rw [List.getElem_append_right (by simpa using hr),List.getElem_replicate,
        getD_of_length_le (by omega)]
      simp
  simp only [List.length_append,length_membVec,List.length_replicate] at h1 h2
  rw [hc rels rels' h1,hc rels' rels h2]
  simp only [h i t hl ht]

theorem membVec_length_eq {rels : RawRelStruct} {u : List ℕ} {a : RawF1In}
    (hu : u ∈ f1TagSet a) (h : a.2 = rels) : u.length = rels.length := by
  obtain ⟨r,-,rfl⟩ := List.mem_map.1 (mem_f1TagSet.1 hu)
  rw [length_membVec,h]

/-- Sec. 5.1.3: the functor `F1` on the same tuples with agreeing relations. -/
theorem wlSame_rawF1 {n k : ℕ} {p q : RawWL} {rels rels' : RawRelStruct}
    (hp : RawWL.WF n k p) (hq : RawWL.WF n k q) (h : RelsAgree n k rels rels') :
    WLSame n k (rawF1 (p,rels)) (rawF1 (q,rels')) := by
  have hkey : ∀ t,t ∈ p.2.map Prod.fst ↔ t ∈ q.2.map Prod.fst := by
    intro t; rw [hp.keyMem,hq.keyMem]
  have hs : WLSame n k (p.1,p.2.map (fun r => (r.1,f1NewCol (p,rels) r.1)))
      (q.1,q.2.map (fun r => (r.1,f1NewCol (q,rels') r.1))) := by
    let w := List.replicate rels'.length 0
    let w' := List.replicate rels.length 0
    have hpad : ∀ t ∈ p.2.map Prod.fst,membVec (rels,t) ++ w = membVec (rels',t) ++ w' := by
      intro t ht
      obtain ⟨hl,hlt⟩ := (hp.keyMem t).1 ht
      exact membVec_pad h hl hlt
    have hA : ∀ t ∈ p.2.map Prod.fst,f1NewCol (p,rels) t =
        rankIn ((f1TagSet (p,rels)).map (· ++ w),membVec (rels,t) ++ w) := by
      intro t _
      rw [f1NewCol,rankIn_append_same w]
      intro u hu
      rw [membVec_length_eq hu rfl,length_membVec]
    have hB : ∀ t ∈ q.2.map Prod.fst,f1NewCol (q,rels') t =
        rankIn ((f1TagSet (q,rels')).map (· ++ w'),membVec (rels',t) ++ w') := by
      intro t _
      rw [f1NewCol,rankIn_append_same w']
      intro u hu
      rw [membVec_length_eq hu rfl,length_membVec]
    have hmem : ∀ u,u ∈ (f1TagSet (p,rels)).map (· ++ w) ↔
        u ∈ (f1TagSet (q,rels')).map (· ++ w') := by
      intro u
      simp only [List.mem_map,mem_f1TagSet,f1Tags]
      constructor
      · rintro ⟨_,⟨r,hr,rfl⟩,rfl⟩
        obtain ⟨r',hr',he⟩ := List.mem_map.1 ((hkey r.1).1 (List.mem_map_of_mem hr))
        refine ⟨_,⟨r',hr',rfl⟩,?_⟩
        dsimp only
        rw [he,hpad r.1 (List.mem_map_of_mem hr)]
      · rintro ⟨_,⟨r,hr,rfl⟩,rfl⟩
        obtain ⟨r',hr',he⟩ := List.mem_map.1 ((hkey r.1).2 (List.mem_map_of_mem hr))
        refine ⟨_,⟨r',hr',rfl⟩,?_⟩
        dsimp only
        rw [hpad r'.1 (List.mem_map_of_mem hr'),he]
    have hinj : ∀ z : List ℕ,Function.Injective (· ++ z) :=
      fun z _ _ he => List.append_cancel_right he
    refine ⟨rawF1_wf (a := (p,rels)) hp,rawF1_wf (a := (q,rels')) hq,fun t => ?_⟩
    dsimp only
    rw [tblGet_map_key,tblGet_map_key]
    by_cases ht : t ∈ p.2.map Prod.fst
    · rw [if_pos ht,if_pos ((hkey t).1 ht),hA t ht,hB t ((hkey t).1 ht),hpad t ht]
      exact rankIn_congr_mem ((nodup_f1TagSet _).map (hinj w))
        ((nodup_f1TagSet _).map (hinj w')) hmem _
    · rw [if_neg ht,if_neg (fun h' => ht ((hkey t).2 h'))]
  exact hs

/-! ### The whole pipeline -/

/-- The start table: every tuple over the domain, all with color `0`. -/
theorem wlSame_tupleTable {n k : ℕ} {dom dom' : List ℕ} (hnd : dom.Nodup)
    (hmem : ∀ a,a ∈ dom ↔ a < n) (hnd' : dom'.Nodup) (hmem' : ∀ a,a ∈ dom' ↔ a < n) :
    WLSame n k (tupleTable dom k) (tupleTable dom' k) := by
  refine ⟨wf_tupleTable hnd hmem,wf_tupleTable hnd' hmem',fun t => ?_⟩
  have e : ∀ d : List ℕ,(tupleTable d k).2 = (tuplesOf d k).map (fun t => (t,0)) := fun _ => rfl
  have e' : ∀ d : List ℕ,(tuplesOf d k).map (fun t => (t,(0 : ℕ))) =
      ((tuplesOf d k).map (fun t => (t,0))).map (fun r => (r.1,(fun _ => (0 : ℕ)) r.1)) := by
    intro d; simp [List.map_map,Function.comp_def]
  rw [e,e,e' dom,e' dom']
  rw [tblGet_map_key _ (fun _ => 0),tblGet_map_key _ (fun _ => 0)]
  split <;> split <;> rfl

/-- **Sec. 5.2, the pipeline `F3 ∘ F2 ∘ F1` does not see the listing orders.** Two ambient
inputs with the same arity list and guard string, the same domain up to order, and relations
that agree on every tuple of the domain get the same color on every tuple. -/
theorem wlSame_ambientPipeline321 {n c : ℕ} {ks base dom dom' : List ℕ}
    {rels rels' : RawRelStruct} (hnd : dom.Nodup) (hmem : ∀ i,i ∈ dom ↔ i < n)
    (hnd' : dom'.Nodup) (hmem' : ∀ i,i ∈ dom' ↔ i < n)
    (hg : ks.length ≤ guardBound c base.length) (hr : RelsAgree n ks.length rels rels') :
    WLSame n ks.length (ambientPipeline321 c ((ks,base,dom),rels))
      (ambientPipeline321 c ((ks,base,dom'),rels')) := by
  rw [ambientPipeline321_of_guard hg,ambientPipeline321_of_guard hg]
  have h0 := wlSame_tupleTable (k := ks.length) hnd hmem hnd' hmem'
  exact ((wlSame_rawF1 h0.left h0.right hr).f2 _).stable

/-- The decoded structures of two same tables are equal. -/
theorem WLSame.decWL_eq {n k : ℕ} {p q : RawWL} (h : WLSame n k p q) :
    decWL n k p = decWL n k q := by
  unfold decWL
  congr 1
  funext x
  exact h.get _

end Algo
