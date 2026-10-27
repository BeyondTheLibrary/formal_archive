/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 9.7, Case 2: the twin class `C` acts on the traces of the neighborhoods on `C`.
-/
import Workspace.SplitOrJohnson.BlkTwinClass

/-!
# §9.7, Case 2  The orbit of a hyperedge under the transpositions inside `C`

Version 2.5, lines 4270-4272:

> *"Since `Aut(H*)` acts on `C` as the symmetric group, all edges of `H*` have the same
> multiplicity.  In other words, `A` is equipartitioned by the twin equivalence classes in
> `X*`."*

`Aut(H)` contains the transposition of any two blocks of the twin class `C`, and such a
transposition moves no block outside `C`.  So for a point `v` of `V₁` the neighborhood
`X(v)` may have its trace `X(v) ∩ C` replaced by **any** set of the same size inside `C`,
the part `X(v) ∖ C` staying put, and the result is again a hyperedge
(`Babai.BlkCaseObj.mem_edgeFam_of_twinSet`, the induction of
`Babai.isCase1_mem_edgeFam` run inside `C`).

That is the whole content of the two sentences quoted above.  Read on the points of `V₁`
it says that the *fibers* of `v ↦ X(v) ∩ C` over the subsets of `C` of one given size all
have the same number of points (`Babai.BlkCaseObj.ncard_traceClass_eq`) and are all
nonempty (`Babai.BlkCaseObj.exists_traceClass`): the fiber over `T` is carried onto the
fiber over `T'` by the bijection that replaces the trace, whose inverse replaces it back.
The bijection is made explicit through `Babai.BlkCaseObj.outerFam`, the set of the parts
`X(v) ∖ C` that occur with a given trace, which is literally the same set for `T` and `T'`.
-/

namespace Babai

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-! ### Swapping two members of `C` moves nothing outside `C` -/

theorem swapIn_subset_of_subset {α : Type*} {B B' : α} {S T : Set α} (hB : B ∈ T)
    (hB' : B' ∈ T) (hS : S ⊆ T) : swapIn B B' S ⊆ T := by
  rintro A (⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨-, -, hA⟩)
  · exact hB
  · exact hB'
  · exact hS hA

namespace BlkCaseObj

variable {s : Set Ω} {Case : (Set ↥s → Set ↥s → ℕ) → Set (Set ↥s) → Set (Set ↥s) → Prop}

/-! ### The orbit of a hyperedge -/

/-- §9.7, Case 2.  **The transpositions inside a twin class `C` reach every trace**: if
`S` is a hyperedge of `H` and `T` is a family of blocks with the same part outside `C` and
a trace on `C` of the same size, then `T` is a hyperedge of `H`.

The proof is the induction of `Babai.isCase1_mem_edgeFam` run inside `C`: one transposition
of a member of `S ∩ C ∖ T` with a member of `T ∩ C ∖ S` lowers `|(S ∩ C) ∖ T|` by one, and
`Babai.BlkCaseObj.IsHTwin` says that every such transposition preserves
`Babai.BlkCaseObj.edgeFam`. -/
theorem mem_edgeFam_of_twinSet {X : BlkCaseObj s Case} {C : Set (Set ↥s)}
    (hC : C ⊆ X.blocks) (htw : ∀ B ∈ C, ∀ B' ∈ C, X.IsHTwin B B') (n : ℕ) :
    ∀ S T : Set (Set ↥s), S ∈ X.edgeFam → T ⊆ X.blocks → S \ C = T \ C →
      (T ∩ C).ncard = (S ∩ C).ncard → ((S ∩ C) \ T).ncard = n → T ∈ X.edgeFam := by
  induction n with
  | zero =>
      intro S T hS hTb hdiff hcard hn
      have hsub : S ∩ C ⊆ T := by
        have : (S ∩ C) \ T = ∅ := by rwa [Set.ncard_eq_zero (Set.toFinite _)] at hn
        exact Set.diff_eq_empty.1 this
      have hsub' : S ∩ C ⊆ T ∩ C := fun A hA => ⟨hsub hA, hA.2⟩
      have heq : S ∩ C = T ∩ C :=
        (Set.eq_of_subset_of_ncard_le hsub' (le_of_eq hcard) (Set.toFinite _))
      have : S = T := by
        rw [← Set.diff_union_inter S C, ← Set.diff_union_inter T C, hdiff, heq]
      exact this ▸ hS
  | succ n ih =>
      intro S T hS hTb hdiff hcard hn
      -- a member of `(S ∩ C) ∖ T` and a member of `(T ∩ C) ∖ S`
      have hne : ((S ∩ C) \ T).Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
      obtain ⟨B, hBS, hBT⟩ := hne
      have hBC : B ∈ C := hBS.2
      have hsymm : ((T ∩ C) \ (S ∩ C)).ncard = ((S ∩ C) \ (T ∩ C)).ncard := by
        have h1 := Set.ncard_inter_add_ncard_diff_eq_ncard (S ∩ C) (T ∩ C) (Set.toFinite _)
        have h2 := Set.ncard_inter_add_ncard_diff_eq_ncard (T ∩ C) (S ∩ C) (Set.toFinite _)
        rw [Set.inter_comm] at h2
        omega
      have hdiffT : (S ∩ C) \ (T ∩ C) = (S ∩ C) \ T := by
        ext A
        simp only [Set.mem_diff, Set.mem_inter_iff]
        constructor
        · rintro ⟨hA, hA'⟩; exact ⟨hA, fun hc => hA' ⟨hc, hA.2⟩⟩
        · rintro ⟨hA, hA'⟩; exact ⟨hA, fun hc => hA' hc.1⟩
      have hne' : ((T ∩ C) \ (S ∩ C)).Nonempty := by
        refine Set.nonempty_of_ncard_ne_zero ?_
        rw [hsymm, hdiffT, hn]; omega
      obtain ⟨B', hB'T, hB'S⟩ := hne'
      have hB'C : B' ∈ C := hB'T.2
      have hB'notS : B' ∉ S := fun hc => hB'S ⟨hc, hB'C⟩
      -- the swapped family
      have hswap : swapIn B B' S = insert B' (S \ {B}) := swapIn_eq_insert hBS.1 hB'notS
      have hS' : swapIn B B' S ∈ X.edgeFam := htw B hBC B' hB'C S hS
      have hBnotS : B ∉ S \ {B} := fun hc => hc.2 rfl
      have hinter : swapIn B B' S ∩ C = insert B' ((S ∩ C) \ {B}) := by
        rw [hswap]
        ext A
        simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_diff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨rfl | ⟨h1, h2⟩, hAC⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨⟨h1, hAC⟩, h2⟩
        · rintro (rfl | ⟨⟨h1, h2⟩, h3⟩)
          · exact ⟨Or.inl rfl, hB'C⟩
          · exact ⟨Or.inr ⟨h1, h3⟩, h2⟩
      have hdiff' : swapIn B B' S \ C = S \ C := by
        rw [hswap]
        ext A
        simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨rfl | ⟨h1, h2⟩, hAC⟩
          · exact absurd hB'C hAC
          · exact ⟨h1, hAC⟩
        · rintro ⟨h1, h2⟩
          exact ⟨Or.inr ⟨h1, fun hc => h2 (hc ▸ hBC)⟩, h2⟩
      have hcard' : (swapIn B B' S ∩ C).ncard = (S ∩ C).ncard := by
        rw [hinter, Set.ncard_insert_of_notMem (fun hc => hB'S hc.1) (Set.toFinite _),
          Set.ncard_diff_singleton_of_mem hBS]
        have : 0 < (S ∩ C).ncard := (Set.ncard_pos (Set.toFinite _)).2 ⟨B, hBS⟩
        omega
      have hn' : ((swapIn B B' S ∩ C) \ T).ncard = n := by
        have hset : (swapIn B B' S ∩ C) \ T = ((S ∩ C) \ T) \ {B} := by
          rw [hinter]
          ext A
          simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff]
          constructor
          · rintro ⟨rfl | ⟨h1, h2⟩, h3⟩
            · exact absurd hB'T.1 h3
            · exact ⟨⟨h1, h3⟩, h2⟩
          · rintro ⟨⟨h1, h2⟩, h3⟩
            exact ⟨Or.inr ⟨h1, h3⟩, h2⟩
        rw [hset, Set.ncard_diff_singleton_of_mem (show B ∈ (S ∩ C) \ T from ⟨hBS, hBT⟩), hn]
        omega
      exact ih (swapIn B B' S) T hS' hTb (by rw [hdiff', hdiff]) (by rw [hcard, hcard']) hn'

/-! ### The fibers of `v ↦ X(v) ∩ C` -/

/-- §9.7, Case 2.  The parts `X(v) ∖ C` of the neighborhoods whose trace on `C` is `T`.
Two fibers of `v ↦ X(v) ∩ C` over sets of the same size have literally the same set of
parts (`Babai.BlkCaseObj.outerFam_eq`), which is why they have the same number of
points. -/
def outerFam (X : BlkCaseObj s Case) (T : Set (Set ↥s)) : Set (Set (Set ↥s)) :=
  {O | ∃ x, X.part₁ x ∧ X.nbhd x \ X.bigTwin = O ∧ X.nbhd x ∩ X.bigTwin = T}

/-- §9.7, Case 2.  *"the trace class of `v`"*: the points of `V₁` whose neighborhood meets
`C` in `T`.  Under the branch condition these are the twin classes of `X*` inside the
dominant `c'`-color class `A`. -/
def traceClass (X : BlkCaseObj s Case) (T : Set (Set ↥s)) : Set ↥s :=
  {x | X.part₁ x ∧ X.nbhd x ∩ X.bigTwin = T}

/-- §9.7, Case 2.  **The sets of parts are the same for two traces of the same size.**
This is *"`Aut(H*)` acts on `C` as the symmetric group"*, read on `V₁`. -/
theorem outerFam_eq {X : BlkCaseObj s Case}
    (htw : ∀ B ∈ X.bigTwin, ∀ B' ∈ X.bigTwin, X.IsHTwin B B') {T T' : Set (Set ↥s)}
    (hT : T ⊆ X.bigTwin) (hT' : T' ⊆ X.bigTwin) (hcard : T.ncard = T'.ncard) :
    X.outerFam T = X.outerFam T' := by
  have key : ∀ U U' : Set (Set ↥s), U ⊆ X.bigTwin → U' ⊆ X.bigTwin → U.ncard = U'.ncard →
      X.outerFam U ⊆ X.outerFam U' := by
    rintro U U' hU hU' hc O ⟨x, hx, hO, hUx⟩
    have hSb : X.nbhd x ⊆ X.blocks := X.nbhd_subset_blocks x
    have hOC : Disjoint O X.bigTwin := by
      rw [← hO, Set.disjoint_left]; rintro A ⟨-, hA⟩ hA'; exact hA hA'
    set T₂ : Set (Set ↥s) := O ∪ U' with hT₂
    have hT₂b : T₂ ⊆ X.blocks := by
      refine Set.union_subset ?_ (hU'.trans X.bigTwin_subset_blocks)
      rw [← hO]; exact fun A hA => hSb hA.1
    have hT₂diff : T₂ \ X.bigTwin = O := by
      ext A
      simp only [hT₂, Set.mem_diff, Set.mem_union]
      constructor
      · rintro ⟨hA | hA, hA'⟩
        · exact hA
        · exact absurd (hU' hA) hA'
      · intro hA
        exact ⟨Or.inl hA, fun hc => (Set.disjoint_left.1 hOC hA) hc⟩
    have hT₂inter : T₂ ∩ X.bigTwin = U' := by
      ext A
      simp only [hT₂, Set.mem_inter_iff, Set.mem_union]
      constructor
      · rintro ⟨hA | hA, hA'⟩
        · exact absurd hA' (Set.disjoint_left.1 hOC hA)
        · exact hA
      · intro hA; exact ⟨Or.inr hA, hU' hA⟩
    have hmem : T₂ ∈ X.edgeFam :=
      mem_edgeFam_of_twinSet X.bigTwin_subset_blocks htw _ (X.nbhd x) T₂ ⟨x, hx, rfl⟩ hT₂b
        (by rw [hT₂diff, hO]) (by rw [hT₂inter, hUx, hc]) rfl
    obtain ⟨y, hy, hny⟩ := hmem
    exact ⟨y, hy, by rw [hny, hT₂diff], by rw [hny, hT₂inter]⟩
  exact Set.Subset.antisymm (key T T' hT hT' hcard) (key T' T hT' hT hcard.symm)

/-- §9.7, Case 2.  A trace class has as many points as its set of parts: a point of `V₁` is
determined by its neighborhood (*"no multiple edges"*,
`Babai.BlkCaseObj.nbhd_injective`), which inside one trace class is determined by its part
outside `C`. -/
theorem ncard_traceClass (X : BlkDesignObj s) (T : Set (Set ↥s)) :
    (X.traceClass T).ncard = (X.outerFam T).ncard := by
  have himg : (fun x => X.nbhd x \ X.bigTwin) '' X.traceClass T = X.outerFam T := by
    ext O
    constructor
    · rintro ⟨x, ⟨hx, hTx⟩, rfl⟩; exact ⟨x, hx, rfl, hTx⟩
    · rintro ⟨x, hx, hO, hTx⟩; exact ⟨x, ⟨hx, hTx⟩, hO⟩
  have hinj : Set.InjOn (fun x => X.nbhd x \ X.bigTwin) (X.traceClass T) := by
    rintro u ⟨hu, hTu⟩ v ⟨hv, hTv⟩ huv
    have huv' : X.nbhd u \ X.bigTwin = X.nbhd v \ X.bigTwin := huv
    refine X.nbhd_injective hu hv ?_
    rw [← Set.diff_union_inter (X.nbhd u) X.bigTwin,
      ← Set.diff_union_inter (X.nbhd v) X.bigTwin, huv', hTu, hTv]
  rw [← himg, Set.InjOn.ncard_image hinj]

/-- §9.7, Case 2.  ***"all edges of `H*` have the same multiplicity"***: two trace classes
over subsets of `C` of the same size have the same number of points. -/
theorem ncard_traceClass_eq (X : BlkDesignObj s)
    (htw : ∀ B ∈ X.bigTwin, ∀ B' ∈ X.bigTwin, X.IsHTwin B B') {T T' : Set (Set ↥s)}
    (hT : T ⊆ X.bigTwin) (hT' : T' ⊆ X.bigTwin) (hcard : T.ncard = T'.ncard) :
    (X.traceClass T).ncard = (X.traceClass T').ncard := by
  rw [X.ncard_traceClass T, X.ncard_traceClass T', outerFam_eq htw hT hT' hcard]

/-- §9.7, Case 2.  Every subset of `C` of the right size is the trace of a neighborhood:
the trace classes over the `d*`-subsets of `C` are all nonempty. -/
theorem exists_traceClass (X : BlkDesignObj s)
    (htw : ∀ B ∈ X.bigTwin, ∀ B' ∈ X.bigTwin, X.IsHTwin B B') {x : ↥s} (hx : X.part₁ x)
    {T : Set (Set ↥s)} (hT : T ⊆ X.bigTwin) (hcard : T.ncard = X.localSize x) :
    (X.traceClass T).Nonempty := by
  have hmem : X.nbhd x \ X.bigTwin ∈ X.outerFam (X.nbhd x ∩ X.bigTwin) := ⟨x, hx, rfl, rfl⟩
  rw [outerFam_eq htw Set.inter_subset_right hT hcard.symm] at hmem
  obtain ⟨y, hy, -, hTy⟩ := hmem
  exact ⟨y, hy, hTy⟩

end BlkCaseObj

end Babai
