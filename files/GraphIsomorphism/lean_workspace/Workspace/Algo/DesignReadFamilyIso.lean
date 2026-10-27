import Workspace.Algo.DesignReadFamilyReorder

/-! # The Design Lemma read family moves along any isomorphism of the input

Theorem 8.1.2 and Procedure "Design Lemma" (Sec. 8.1, v2.5) produce canonical objects:
an isomorphism `f` of two `k`-ary relational structures carries each individualized output
of the first to one of the second. On the RAM two isomorphic inputs may list the domain, the
relations and the members of each relation in unrelated orders. We split `f` into three
moves: drop the tuples that are not tuples of the domain, relabel along `f`
(`ambientDesignReadFamily_relabel`), and reorder (`ambientDesignReadFamily_reorder`).
-/
namespace Algo
open Babai RAM Equiv
open scoped Classical

/-- Outputs related by `f` and then by `g` are related by `g * f`. -/
theorem DesignReadOutIso.trans {n : ℕ} {f g : Perm (Fin n)} {o o₁ o₂ : RawDesignReadOut}
    (h₁ : DesignReadOutIso n f o o₁) (h₂ : DesignReadOutIso n g o₁ o₂) :
    DesignReadOutIso n (g * f) o o₂ := by
  rcases h₁ with ⟨P,P₁,rfl,rfl,hc,hp⟩ | ⟨L,L₁,q,q₁,rfl,rfl,hw,hq⟩
  · rcases h₂ with ⟨P₁',P₂,he,rfl,hc',hp'⟩ | ⟨L₁',L₂,q₁',q₂,he,rfl,_,_⟩
    · obtain rfl : P₁ = P₁' := by simpa using he
      refine Or.inl ⟨P,P₂,rfl,rfl,fun u => ?_,fun u v => ?_⟩
      · rw [Perm.mul_apply,hc',hc]
      · rw [Perm.mul_apply,Perm.mul_apply,hp,hp']
    · simp at he
  · rcases h₂ with ⟨P₁',P₂,he,rfl,_,_⟩ | ⟨L₁',L₂,q₁',q₂,he,rfl,hw',hq'⟩
    · simp at he
    · simp only [Prod.mk.injEq,Option.some.injEq,true_and] at he
      obtain ⟨rfl,rfl⟩ := he
      refine Or.inr ⟨L,L₂,q,q₂,rfl,rfl,?_,fun u v hu hv => ?_⟩
      · rw [Perm.coe_mul,Set.image_comp,hw,hw']
      · have hmem : ∀ w : Fin n,w.val ∈ L → (f w).val ∈ L₁ := by
          intro w hw0
          have : f w ∈ f '' winSet n L := ⟨w,hw0,rfl⟩
          rw [hw] at this
          exact this
        rw [Perm.mul_apply,Perm.mul_apply,hq' _ _ (hmem u hu) (hmem v hv),hq u v hu hv]

theorem List.Forall₂.exists_of_mem {α β : Type*} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β},List.Forall₂ R l₁ l₂ → ∀ a ∈ l₁,∃ b ∈ l₂,R a b
  | _,_,.nil,_,ha => by simp at ha
  | _,_,.cons hab h,a,ha => by
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨_,List.mem_cons_self ..,hab⟩
    · obtain ⟨b,hb,h'⟩ := List.Forall₂.exists_of_mem h a ha
      exact ⟨b,List.mem_cons_of_mem _ hb,h'⟩

/-- Keep only the tuples of the domain in each relation. -/
def keyRels (n k : ℕ) (rels : RawRelStruct) : RawRelStruct :=
  rels.map (List.filter (fun t => t.length == k && t.all (· < n)))

theorem getD_keyRels (n k : ℕ) (rels : RawRelStruct) (i : ℕ) :
    (keyRels n k rels).getD i [] = (rels.getD i []).filter (fun t => t.length == k && t.all (· < n)) := by
  unfold keyRels
  by_cases hi : i < rels.length
  · rw [List.getD_eq_getElem _ _ (by simpa using hi),List.getD_eq_getElem _ _ hi,
      List.getElem_map]
  · rw [getD_of_length_le (by simpa using hi),getD_of_length_le (by omega)]
    rfl

theorem relsAgree_keyRels (n k : ℕ) (rels : RawRelStruct) :
    RelsAgree n k rels (keyRels n k rels) := by
  intro i t hl ht
  rw [getD_keyRels,List.mem_filter]
  simp only [Bool.and_eq_true,beq_iff_eq,List.all_eq_true,decide_eq_true_eq]
  exact ⟨fun h => ⟨h,hl,ht⟩,fun h => h.1⟩

theorem keyRels_lt {n k : ℕ} {rels : RawRelStruct} :
    ∀ R ∈ keyRels n k rels,∀ t ∈ R,∀ i ∈ t,i < n := by
  intro R hR t ht i hi
  obtain ⟨R₀,-,rfl⟩ := List.mem_map.1 hR
  have := (List.mem_filter.1 ht).2
  simp only [Bool.and_eq_true,beq_iff_eq,List.all_eq_true,decide_eq_true_eq] at this
  exact this.2 i hi

theorem getD_relabelRels (π : RawPerm) (rels : RawRelStruct) (i : ℕ) :
    (relabelRels (π,rels)).getD i [] = (rels.getD i []).map (permList π) := by
  unfold relabelRels
  by_cases hi : i < rels.length
  · rw [List.getD_eq_getElem _ _ (by simpa using hi),List.getD_eq_getElem _ _ hi,
      List.getElem_map]
  · rw [getD_of_length_le (by simpa using hi),getD_of_length_le (by omega)]
    rfl

theorem nodup_permList {n : ℕ} {π : RawPerm} (hπ : RawPerm.WF n π) {dom : List ℕ}
    (hnd : dom.Nodup) (hmem : ∀ i,i ∈ dom ↔ i < n) : (permList π dom).Nodup :=
  hnd.map_on (fun x hx y hy he =>
    rawApply_inj hπ ((hmem x).1 hx) ((hmem y).1 hy) he)

theorem mem_permList_dom {n : ℕ} {π : RawPerm} (hπ : RawPerm.WF n π) {dom : List ℕ}
    (hmem : ∀ i,i ∈ dom ↔ i < n) (i : ℕ) : i ∈ permList π dom ↔ i < n := by
  constructor
  · exact fun hi => permList_lt hπ (fun a ha => (hmem a).1 ha) i hi
  · intro hi
    rw [permList,List.mem_map]
    exact ⟨invAt π i,(hmem _).2 (invAt_lt hπ hi),rawApply_invAt hπ hi⟩

section
variable {n a b c : ℕ} {ks base dom dom' : List ℕ} {rels rels' : RawRelStruct}
    (hnd : dom.Nodup) (hmem : ∀ i,i ∈ dom ↔ i < n)
    (hnd' : dom'.Nodup) (hmem' : ∀ i,i ∈ dom' ↔ i < n)
    (hg : ks.length ≤ guardBound c base.length) (hb : 0 < b)
local notation "g" => (((ks,base,dom),rels),(a,b))
local notation "g'" => (((ks,base,dom'),rels'),(a,b))
include hnd hmem hnd' hmem' hg hb

/-- The relabeled key relations agree with the relations of an isomorphic input. -/
theorem relsAgree_relabel_of_iso {f : Perm (Fin n)}
    (hf : f ∈ KAryRelStruct.Iso (decRel n ks.length rels) (decRel n ks.length rels')) :
    RelsAgree n ks.length (relabelRels (encPerm n f,keyRels n ks.length rels)) rels' := by
  have hπ := wf_encPerm n f
  intro i t hl ht
  obtain ⟨y,rfl⟩ := exists_tupleOf (n := n) hl ht
  have hx : permList (encPerm n f) (tupleOf (tupleMap f.symm y)) = tupleOf y := by
    rw [← designTupleOf_relabel hπ,decPerm_encPerm]
    congr 1
    funext j
    simp [tupleMap]
  have hR : ∀ s ∈ (keyRels n ks.length rels).getD i [],∀ c ∈ s,c < n := by
    intro s hs c hc
    rw [getD_keyRels] at hs
    have := (List.mem_filter.1 hs).2
    simp only [Bool.and_eq_true,beq_iff_eq,List.all_eq_true,decide_eq_true_eq] at this
    exact this.2 c hc
  rw [getD_relabelRels,← hx,mem_relabel_rel hπ hR (fun _ h => tupleOf_lt _ h),
    ← relsAgree_keyRels n ks.length rels i _ (by simp) (fun _ h => tupleOf_lt _ h)]
  have := hf i (tupleMap f.symm y)
  simp only [mem_decRel_rel] at this
  rw [this]
  have hy : tupleMap f (tupleMap f.symm y) = y := by
    funext j; simp [tupleMap]
  rw [hy,hx]

/-- **Sec. 8.1, canonicity of the Design Lemma read-off on the RAM.** An isomorphism `f` of the
two relational structures carries every entry of the computed read family of the first input
to an entry of the second, with outputs related by `f`. The two inputs may list the domain and
the relations in any orders. -/
theorem ambientDesignReadFamily_iso {f : Perm (Fin n)}
    (hf : f ∈ KAryRelStruct.Iso (decRel n ks.length rels) (decRel n ks.length rels'))
    {u : List ℕ × RawDesignReadOut} (hu : u ∈ ambientDesignReadFamily c g) :
    ∃ v ∈ ambientDesignReadFamily c g',DesignReadOutIso n f u.2 v.2 := by
  have hπ := wf_encPerm n f
  -- drop the tuples that are not tuples of the domain
  obtain ⟨v₀,hv₀,-,h₀⟩ := ambientDesignReadFamily_reorder hnd hmem hnd hmem hg
    (relsAgree_keyRels n ks.length rels) hb hu
  -- relabel along `f`
  have hrel := ambientDesignReadFamily_relabel (c := c) (ks := ks) (base := base)
    (rels := keyRels n ks.length rels) (a := a) hπ hnd hmem hg keyRels_lt hb rfl
  obtain ⟨v₁,hv₁,-,h₁⟩ := List.Forall₂.exists_of_mem hrel v₀ hv₀
  -- reorder to the listing of the second input
  obtain ⟨v,hv,-,h₂⟩ := ambientDesignReadFamily_reorder (nodup_permList hπ hnd hmem)
    (mem_permList_dom hπ hmem) hnd' hmem' hg
    (relsAgree_relabel_of_iso hnd hmem hnd' hmem' hg hb hf) hb hv₁
  refine ⟨v,hv,?_⟩
  have := (h₀.trans h₁).trans h₂
  simpa only [decPerm_encPerm,mul_one,one_mul] using this

end
end Algo
