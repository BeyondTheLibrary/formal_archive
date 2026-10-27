import Workspace.Algo.DesignReadReorder
import Workspace.Algo.DesignReadFamilyRelabel

/-! # The Design Lemma read family does not depend on the listing orders

Procedure "Design Lemma" (Sec. 8.1, v2.5) individualizes the shortest strings at which its
test fires. The RAM scan lists strings over the domain in the order of the domain list and
stops at the first length where some string fires. Here we prove that the length it stops at,
the set of all firing strings at that length and every output read at such a string depend
only on the colors of Sec. 5.2, hence (by `wlSame_ambientPipeline321`) not on the order of the
domain list nor on the order of the tuples inside each relation.
-/
namespace Algo
open Babai RAM
open scoped Classical

section Table
variable {n k a b : ℕ} {ks : List ℕ} {p q : RawWL} (h : WLSame n k p q)
    (hk : ks.length = k) (hb : 0 < b)
include h hk hb

/-- The test of lines 04–08 reads only the colors of the table. -/
theorem WLSame.returnsB_eq {ys : List ℕ} (hl : ys.length ≤ k) (hlt : ∀ i ∈ ys,i < n) :
    returnsB (((ks,ys),p),(a,b)) = returnsB (((ks,ys),q),(a,b)) := by
  obtain ⟨x,hx⟩ := exists_tupleOf (n := n) (rfl : ys.length = ys.length) hlt
  have e1 := returnsB_spec (a := a) h.left hk hl x hb (α := (a:ℝ)/b) rfl
  have e2 := returnsB_spec (a := a) h.right hk hl x hb (α := (a:ℝ)/b) rfl
  rw [h.decWL_eq,hx] at e1
  rw [hx] at e2
  rw [Bool.eq_iff_iff,e1,e2]

theorem WLSame.scanLen_none {l : ℕ} (hl : l ≤ k) {x₀ x₀' : List ℕ} :
    scanLen l (((ks,x₀),p),(a,b)) = none ↔ scanLen l (((ks,x₀'),q),(a,b)) = none := by
  rw [Algo.scanLen_none_iff h.left hk hl hb rfl,Algo.scanLen_none_iff h.right hk hl hb rfl,
    h.decWL_eq]

omit h hk hb in
theorem scanLen_length {l : ℕ} {z : DIn} {xs : List ℕ} (hs : scanLen l z = some xs) :
    xs.length = l := by
  have hm := List.mem_of_mem_head? hs
  exact ((mem_tuplesOf _ _ _).1 (List.mem_filter.1 hm).1).1

/-- The scan of line 03 stops at the same length. -/
theorem WLSame.ansUpTo_length {x₀ x₀' : List ℕ} :
    ∀ j ≤ k,(ansUpTo (((ks,x₀),p),(a,b)) j).map List.length =
      (ansUpTo (((ks,x₀'),q),(a,b)) j).map List.length := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    have ih := ih (by omega)
    simp only [ansUpTo]
    cases hA : ansUpTo (((ks,x₀),p),(a,b)) j <;>
      cases hA' : ansUpTo (((ks,x₀'),q),(a,b)) j <;> rw [hA,hA'] at ih
    · simp only [Option.elim_none]
      have hiff := h.scanLen_none hk hb (a := a) (l := j) (by omega) (x₀ := x₀) (x₀' := x₀')
      cases hs : scanLen j (((ks,x₀),p),(a,b)) <;>
        cases hs' : scanLen j (((ks,x₀'),q),(a,b))
      · rfl
      · rw [hs,hs'] at hiff; simp at hiff
      · rw [hs,hs'] at hiff; simp at hiff
      · simp only [Option.map_some,scanLen_length hs,scanLen_length hs']
    · simp at ih
    · simp at ih
    · exact ih

end Table

theorem option_elim_mem_congr {α : Type*} {ys : α} {F F' : List ℕ → List α}
    (hF : ∀ xs xs' : List ℕ,xs.length = xs'.length → (ys ∈ F xs ↔ ys ∈ F' xs')) :
    ∀ o o' : Option (List ℕ),o.map List.length = o'.map List.length →
      (ys ∈ o.elim [] F ↔ ys ∈ o'.elim [] F')
  | none,none,_ => Iff.rfl
  | none,some _,h => by simp at h
  | some _,none,h => by simp at h
  | some xs,some xs',h => hF xs xs' (by simpa using h)

section Family
variable {n a b c : ℕ} {ks base dom dom' : List ℕ} {rels rels' : RawRelStruct}
    (hnd : dom.Nodup) (hmem : ∀ i,i ∈ dom ↔ i < n)
    (hnd' : dom'.Nodup) (hmem' : ∀ i,i ∈ dom' ↔ i < n)
    (hg : ks.length ≤ guardBound c base.length)
    (hr : RelsAgree n ks.length rels rels') (hb : 0 < b)
local notation "g" => (((ks,base,dom),rels),(a,b))
local notation "g'" => (((ks,base,dom'),rels'),(a,b))
include hnd hmem hnd' hmem' hg hr hb

theorem ambientDesignProcedure_reorder :
    (ambientDesignProcedure c g).map List.length =
      (ambientDesignProcedure c g').map List.length := by
  have h := wlSame_ambientPipeline321 (c := c) hnd hmem hnd' hmem' hg hr
  rw [ambientDesignProcedure,ambientDesignProcedure,ambientDesignScan_of_guard hg,
    ambientDesignScan_of_guard hg]
  exact h.ansUpTo_length rfl hb _ le_rfl

/-- **Every returning string at the least returning length is kept, in either order.** -/
theorem mem_ambientDesignVersions_reorder (ys : List ℕ) :
    ys ∈ ambientDesignVersions c g ↔ ys ∈ ambientDesignVersions c g' := by
  have h := wlSame_ambientPipeline321 (c := c) hnd hmem hnd' hmem' hg hr
  have hp := ambientDesignProcedure_reorder hnd hmem hnd' hmem' hg hr hb (c := c) (a := a)
  have key : ∀ l,(ys ∈ tuplesOf dom (min l ks.length) ∧
        returnsB (ambientDesignAt c g ys) = true) ↔
      (ys ∈ tuplesOf dom' (min l ks.length) ∧
        returnsB (ambientDesignAt c g' ys) = true) := by
    intro l
    rw [mem_tuplesOf,mem_tuplesOf]
    constructor
    · rintro ⟨⟨hl,hin⟩,hret⟩
      have hlt : ∀ i ∈ ys,i < n := fun i hi => (hmem i).1 (hin i hi)
      refine ⟨⟨hl,fun i hi => (hmem' i).2 (hlt i hi)⟩,?_⟩
      have e : returnsB (ambientDesignAt c g ys) = returnsB (ambientDesignAt c g' ys) :=
        h.returnsB_eq rfl hb (by rw [hl]; exact min_le_right _ _) hlt
      exact e.symm.trans hret
    · rintro ⟨⟨hl,hin⟩,hret⟩
      have hlt : ∀ i ∈ ys,i < n := fun i hi => (hmem' i).1 (hin i hi)
      refine ⟨⟨hl,fun i hi => (hmem i).2 (hlt i hi)⟩,?_⟩
      have e : returnsB (ambientDesignAt c g ys) = returnsB (ambientDesignAt c g' ys) :=
        h.returnsB_eq rfl hb (by rw [hl]; exact min_le_right _ _) hlt
      exact e.trans hret
  rw [ambientDesignVersions,ambientDesignVersions]
  refine option_elim_mem_congr (fun xs xs' he => ?_) _ _ hp
  simp only [ambientDesignVersionsAt,List.mem_filter,ambientDesignVersionRows_prefix hg,he]
  exact key _

/-- **The read family of the Design Lemma does not depend on the listing orders**: every entry
has an entry with the same string at the reordered input, and their outputs are related by
the identity of `Fin n`. -/
theorem ambientDesignReadFamily_reorder {u : List ℕ × RawDesignReadOut}
    (hu : u ∈ ambientDesignReadFamily c g) :
    ∃ v ∈ ambientDesignReadFamily c g',v.1 = u.1 ∧ DesignReadOutIso n 1 u.2 v.2 := by
  have h := wlSame_ambientPipeline321 (c := c) hnd hmem hnd' hmem' hg hr
  obtain ⟨ys,hys,rfl⟩ := List.mem_map.1 hu
  have hys' := (mem_ambientDesignVersions_reorder hnd hmem hnd' hmem' hg hr hb ys).1 hys
  refine ⟨_,List.mem_map.2 ⟨ys,hys',rfl⟩,rfl,?_⟩
  obtain ⟨l,hl,x,rfl,_⟩ := ambientDesignVersions_witness hnd hmem rfl hg hb rfl hys
  have hf : (1 : Equiv.Perm (Fin n)) ∈ KAryPartStruct.Iso
      (decWL n ks.length (ambientPipeline321 c ((ks,base,dom),rels)))
      (decWL n ks.length (ambientPipeline321 c ((ks,base,dom'),rels'))) := by
    intro y
    rw [h.decWL_eq]
    rfl
  exact designReadIso_exit h.left h.right rfl hl.le x hb rfl 1 hf

end Family
end Algo
