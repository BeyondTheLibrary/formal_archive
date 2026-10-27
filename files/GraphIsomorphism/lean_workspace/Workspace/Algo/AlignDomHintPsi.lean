/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: Procedure Align, line 8 (§14.1) — the machine's `ψ : H → S(Γ*)` is the
natural epimorphism, up to the numbering of `Γ*`.
-/
import Workspace.Algo.AlignDomHint

/-!
# The machine's `ψ` is the natural epimorphism

`Algo.alignDomPsi` computes `ψ(σ)` for a permutation `σ` of `Γ` from the marking of `Γ` by
the points of `Γ*` (`Algo.alignDomMark`).  This file shows that it returns the permutation of
`Γ*` that `σ` induces, read through a fixed numbering `f` of `Γ*`:

* case (A) (`Algo.alignDomPsi_partition`): given a block map `blk : Γ → Γ*` of the dominant
  class (two dominant points have the same block exactly when they are in the same cell of
  the colored partition, and every point of `Γ*` is a block), and `σ` permuting the blocks
  by `π`, the machine returns `f⁻¹ π f`;
* case (B) (`Algo.alignDomPsi_johnson`): given the identification of the Johnson scheme's
  vertices with `t*`-subsets of `Γ*` read through a bijection `e`, and `σ` inducing `π` on
  them, the machine returns `f⁻¹ π f`.

The numbering `f` depends only on the raw data, not on `σ`.  Both proofs check the two
hypotheses of `Algo.markFirstExpr_eq`.
-/

namespace Algo
open RAM RAM.Targets Babai Equiv

/-- The point `w` of `Γ` is in the dominant class of line 6. -/
def alignDomIn (p : RawAction × RawAlignOutcome) (w : ℕ) : Prop :=
  labAt (alignRColorOf p).2 w = alignRDomColor (alignRColorOf p)

instance (p : RawAction × RawAlignOutcome) (w : ℕ) : Decidable (alignDomIn p w) :=
  inferInstanceAs (Decidable (_ = _))

/-! ## Case (A): the blocks of the dominant class -/

section CaseA

variable {A : RawAction} {m : ℕ} (hg : A.2.1.length = m) (P : RawColPart)
    (hhd : alignRHasDom (alignRColorOf (A, rawAlignPartition P)) = true)

include hg hhd in
/-- The dominant points are the points of `Γ` in the dominant class. -/
theorem mem_alignRDomPoints_iff {w : ℕ} :
    w ∈ alignRDomPoints (alignRColorOf (A, rawAlignPartition P)) ↔
      w < m ∧ alignDomIn (A, rawAlignPartition P) w := by
  have e := alignRDomPoints_eq (lab := (alignRColorOf (A, rawAlignPartition P)).2) hg hhd
  have : alignRColorOf (A, rawAlignPartition P) =
      (A, (alignRColorOf (A, rawAlignPartition P)).2) := rfl
  rw [this, e, List.mem_filter, List.mem_range, decide_eq_true_iff]
  rfl

include hg hhd in
/-- **Every dominant point has exactly one listed point in its block** (existence). -/
theorem exists_mem_alignDomKeys {γ : ℕ} (hγm : γ < m)
    (hγ : alignDomIn (A, rawAlignPartition P) γ) :
    ∃ r ∈ alignDomKeys (A, rawAlignPartition P), cellOf P r = cellOf P γ := by
  set D := alignRDomPoints (alignRColorOf (A, rawAlignPartition P)) with hD
  have hγD : γ ∈ D := (mem_alignRDomPoints_iff hg P hhd).2 ⟨hγm, hγ⟩
  set B := alignDomBlockOf ((P, D), γ) with hB
  have hγB : γ ∈ B := by
    rw [hB, alignDomBlockOf, List.mem_filter, decide_eq_true_iff]
    exact ⟨hγD, rfl⟩
  have hlen : 0 < B.length := List.length_pos_iff_exists_mem.2 ⟨γ, hγB⟩
  set r := rawGet (B, 0) with hr
  have hrB : r ∈ B := by
    rw [hr, rawGet, List.getD_eq_getElem _ _ hlen]
    exact List.getElem_mem hlen
  have hrB' := hrB
  rw [hB, alignDomBlockOf, List.mem_filter, decide_eq_true_iff] at hrB'
  obtain ⟨hrD, hrc⟩ := hrB'
  have hBr : alignDomBlockOf ((P, D), r) = B := by
    rw [hB, alignDomBlockOf, alignDomBlockOf]
    refine List.filter_congr fun δ _ => ?_
    simp only [hrc]
  refine ⟨r, ?_, hrc⟩
  show r ∈ alignDomRepsA (P, D)
  rw [alignDomRepsA, List.mem_filter, alignDomIsRep, decide_eq_true_iff, hBr]
  exact ⟨hrD, hr.symm⟩

include hg hhd in
/-- **Two listed points in the same cell are equal** (uniqueness). -/
theorem eq_of_mem_alignDomKeys {r r' : ℕ} (hr : r ∈ alignDomKeys (A, rawAlignPartition P))
    (hr' : r' ∈ alignDomKeys (A, rawAlignPartition P)) (hc : cellOf P r = cellOf P r') :
    r = r' := by
  set D := alignRDomPoints (alignRColorOf (A, rawAlignPartition P)) with hD
  have h1 : r ∈ alignDomRepsA (P, D) := hr
  have h2 : r' ∈ alignDomRepsA (P, D) := hr'
  rw [alignDomRepsA, List.mem_filter, alignDomIsRep, decide_eq_true_iff] at h1 h2
  have hBB : alignDomBlockOf ((P, D), r) = alignDomBlockOf ((P, D), r') := by
    rw [alignDomBlockOf, alignDomBlockOf]
    refine List.filter_congr fun δ _ => ?_
    simp only [hc]
  have e1 : rawGet (alignDomBlockOf ((P, D), r), 0) = r := h1.2
  have e2 : rawGet (alignDomBlockOf ((P, D), r'), 0) = r' := h2.2
  calc r = _ := e1.symm
    _ = _ := by rw [hBB]
    _ = r' := e2

include hg hhd in
/-- A listed point is a dominant point of `Γ`. -/
theorem lt_and_in_of_mem_alignDomKeys {r : ℕ} (hr : r ∈ alignDomKeys (A, rawAlignPartition P)) :
    r < m ∧ alignDomIn (A, rawAlignPartition P) r := by
  have h1 : r ∈ alignDomRepsA (P, alignRDomPoints (alignRColorOf (A, rawAlignPartition P))) := hr
  rw [alignDomRepsA, List.mem_filter] at h1
  exact (mem_alignRDomPoints_iff hg P hhd).1 h1.1

theorem nodup_alignDomKeys_partition :
    (alignDomKeys (A, rawAlignPartition P)).Nodup := by
  show (alignDomRepsA (P, alignRDomPoints (alignRColorOf (A, rawAlignPartition P)))).Nodup
  exact List.Nodup.filter _ (List.Nodup.filter _ List.nodup_range)

/-- The marking of case (A), read. -/
theorem alignDomMark_partition (i w : ℕ) :
    alignDomMark ((A, rawAlignPartition P), i, w) =
      (decide (alignDomIn (A, rawAlignPartition P) w) &&
        decide (cellOf P w = cellOf P (rawGet (alignDomKeys (A, rawAlignPartition P), i)))) :=
  rfl

include hg hhd in
/-- §14.1, line 8, case (A): **the machine's `ψ` is the action on the blocks.**  Given a
block map `blk` of the dominant class onto `Γ*` (two dominant points have the same block
exactly when they lie in the same cell of `P`), there is a numbering `f` of `Γ*` by the listed
points such that, for every `σ` preserving the dominant class and permuting the blocks by
`π`, the machine returns `f⁻¹ π f`. -/
theorem alignDomPsi_partition {ms : ℕ} (blk : Fin m → Fin ms)
    (hblk : ∀ γ δ : Fin m, alignDomIn (A, rawAlignPartition P) γ →
      alignDomIn (A, rawAlignPartition P) δ → (blk γ = blk δ ↔ cellOf P γ = cellOf P δ))
    (hsurj : ∀ i, ∃ γ : Fin m, alignDomIn (A, rawAlignPartition P) γ ∧ blk γ = i) :
    ∃ f : Fin (alignDomKeys (A, rawAlignPartition P)).length ≃ Fin ms,
      ∀ (σ : Perm (Fin m)) (π : Perm (Fin ms)),
        (∀ γ : Fin m, alignDomIn (A, rawAlignPartition P) (σ γ) ↔
          alignDomIn (A, rawAlignPartition P) γ) →
        (∀ γ : Fin m, alignDomIn (A, rawAlignPartition P) γ → blk (σ γ) = π (blk γ)) →
        alignDomPsi ((A, rawAlignPartition P), encPerm m σ) =
          encPerm _ (Equiv.permCongr f.symm π) := by
  classical
  set p : RawAction × RawAlignOutcome := (A, rawAlignPartition P) with hp
  set K := alignDomKeys p with hK
  have hKnd : K.Nodup := nodup_alignDomKeys_partition P
  have hKlt : ∀ i : Fin K.length, K[(i : ℕ)] < m := fun i =>
    (lt_and_in_of_mem_alignDomKeys hg P hhd (List.getElem_mem i.isLt)).1
  have hKin : ∀ i : Fin K.length, alignDomIn p K[(i : ℕ)] := fun i =>
    (lt_and_in_of_mem_alignDomKeys hg P hhd (List.getElem_mem i.isLt)).2
  let key : Fin K.length → Fin m := fun i => ⟨K[(i : ℕ)], hKlt i⟩
  let f₀ : Fin K.length → Fin ms := fun i => blk (key i)
  have hf₀ : Function.Bijective f₀ := by
    constructor
    · intro i j hij
      have hc := (hblk (key i) (key j) (hKin i) (hKin j)).1 hij
      have := eq_of_mem_alignDomKeys hg P hhd (List.getElem_mem i.isLt)
        (List.getElem_mem j.isLt) hc
      exact Fin.ext ((List.Nodup.getElem_inj_iff hKnd).1 this)
    · intro x
      obtain ⟨γ, hγ, hγx⟩ := hsurj x
      obtain ⟨r, hr, hrc⟩ := exists_mem_alignDomKeys hg P hhd γ.isLt hγ
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
      refine ⟨⟨i, hi⟩, ?_⟩
      rw [← hγx]
      exact (hblk (key ⟨i, hi⟩) γ (hKin ⟨i, hi⟩) hγ).2 hrc
  let f : Fin K.length ≃ Fin ms := Equiv.ofBijective f₀ hf₀
  -- the marking through `blk`
  have hmark : ∀ (i : Fin K.length) (w : Fin m),
      alignDomMark (p, i, w) = decide (alignDomIn p w ∧ blk w = f i) := by
    intro i w
    rw [alignDomMark_partition]
    have hk : rawGet (K, (i : ℕ)) = K[(i : ℕ)] := by
      rw [rawGet, List.getD_eq_getElem _ _ i.isLt]
    rw [hk]
    apply Bool.eq_iff_iff.2
    simp only [Bool.and_eq_true, decide_eq_true_iff]
    exact ⟨fun h => ⟨h.1, (hblk w (key i) h.1 (hKin i)).2 h.2⟩,
      fun h => ⟨h.1, (hblk w (key i) h.1 (hKin i)).1 h.2⟩⟩
  refine ⟨f, fun σ π hσ hπ => ?_⟩
  refine alignDomPsi_eq_encPerm rfl hg σ _ (fun i w => ?_) (fun a b hab => ?_)
  · rw [hmark, hmark]
    refine decide_eq_decide.2 ?_
    show alignDomIn p w ∧ blk w = f i ↔ alignDomIn p (σ w) ∧ blk (σ w) = f (f.symm (π (f i)))
    rw [Equiv.apply_symm_apply, hσ w]
    constructor
    · rintro ⟨hw, he⟩
      exact ⟨hw, by rw [hπ w hw, he]⟩
    · rintro ⟨hw, he⟩
      exact ⟨hw, π.injective (by rw [← hπ w hw, he])⟩
  · obtain ⟨γ, hγ, hγx⟩ := hsurj (f b)
    have h1 : alignDomMark (p, b, γ) = true := by
      rw [hmark]; exact decide_eq_true ⟨hγ, hγx⟩
    have h2 := hab γ h1
    rw [hmark, decide_eq_true_iff] at h2
    exact f.injective (h2.2.symm.trans hγx)

end CaseA

/-! ## Case (B): the Johnson scheme -/

section CaseB

variable {A : RawAction} {m ms ts : ℕ} {J : RawJohnson} (hJ : J.WF m ms ts)

/-- The marking of case (B), read. -/
theorem alignDomMark_johnson (i w : ℕ) :
    alignDomMark ((A, rawAlignJohnson J), i, w) =
      (decide (w ∈ J.1) && decide (i ∈ rawJRow (J, w))) := rfl

include hJ in
theorem length_alignDomKeys_johnson :
    (alignDomKeys (A, rawAlignJohnson J)).length = ms :=
  hJ.rawJDeg_eq

include hJ in
/-- §14.1, line 8, case (B): **the machine's `ψ` is the permutation of `Γ*` that induces the
automorphism.**  Let `e : [m*] → Fin M` be a bijection, and read the vertex `w` of the scheme
as the set `e(S_w)`, `S_w` its row.  For every `σ` preserving the vertex set and moving
`e(S_w)` to `π(e(S_w))`, the machine returns `f⁻¹ π f` with `f` the numbering by `e`. -/
theorem alignDomPsi_johnson {M : ℕ} (e : Fin ms → Fin M) (he : Function.Bijective e) :
    ∃ f : Fin (alignDomKeys (A, rawAlignJohnson J)).length ≃ Fin M,
      ∀ (σ : Perm (Fin m)) (π : Perm (Fin M)), A.2.1.length = m →
        (∀ w : Fin m, ((σ w : Fin m) : ℕ) ∈ J.1 ↔ (w : ℕ) ∈ J.1) →
        (∀ w : Fin m, (w : ℕ) ∈ J.1 → ∀ a : Fin ms,
          (a : ℕ) ∈ rawJRow (J, σ w) ↔ ∃ b : Fin ms, (b : ℕ) ∈ rawJRow (J, w) ∧ π (e b) = e a) →
        alignDomPsi ((A, rawAlignJohnson J), encPerm m σ) =
          encPerm _ (Equiv.permCongr f.symm π) := by
  classical
  set p : RawAction × RawAlignOutcome := (A, rawAlignJohnson J) with hp
  have hN : (alignDomKeys p).length = ms := length_alignDomKeys_johnson hJ
  let f : Fin (alignDomKeys p).length ≃ Fin M :=
    (finCongr hN).trans (Equiv.ofBijective e he)
  have hf : ∀ i : Fin (alignDomKeys p).length, f i = e ⟨i, by rw [← hN]; exact i.isLt⟩ :=
    fun _ => rfl
  refine ⟨f, fun σ π hm hσ hrow => ?_⟩
  have hts := hJ.two_le
  have hks := hJ.params
  refine alignDomPsi_eq_encPerm rfl hm σ _ (fun i w => ?_) (fun a b hab => ?_)
  · rw [alignDomMark_johnson, alignDomMark_johnson]
    apply Bool.eq_iff_iff.2
    simp only [Bool.and_eq_true, decide_eq_true_iff]
    rw [hσ w]
    constructor
    · rintro ⟨hw, hi⟩
      refine ⟨hw, ?_⟩
      set a' : Fin ms := ⟨((f.symm (π (f i)) : Fin _) : ℕ), by
        rw [← hN]; exact (f.symm (π (f i))).isLt⟩ with ha'
      have := (hrow w hw a').2 ⟨⟨i, by rw [← hN]; exact i.isLt⟩, hi, ?_⟩
      · exact this
      · rw [ha', ← hf, ← hf]
        show π (f i) = f (f.symm (π (f i)))
        rw [Equiv.apply_symm_apply]
    · rintro ⟨hw, hi⟩
      refine ⟨hw, ?_⟩
      set a' : Fin ms := ⟨((f.symm (π (f i)) : Fin _) : ℕ), by
        rw [← hN]; exact (f.symm (π (f i))).isLt⟩ with ha'
      obtain ⟨b, hb, hbe⟩ := (hrow w hw a').1 hi
      have hfa : e a' = π (f i) := by
        rw [ha', ← hf]
        show f (f.symm (π (f i))) = π (f i)
        rw [Equiv.apply_symm_apply]
      rw [hfa, hf] at hbe
      have := he.1 (π.injective hbe)
      rw [this] at hb
      exact hb
  · -- two different points of `Γ*` are told apart by a `t*`-subset containing one of them
    by_contra hne
    set x : Fin ms := ⟨a, by rw [← hN]; exact a.isLt⟩ with hx
    set y : Fin ms := ⟨b, by rw [← hN]; exact b.isLt⟩ with hy
    have hxy : x ≠ y := fun h => by
      have h' : (x : ℕ) = y := by rw [h]
      exact hne (Fin.ext h')
    have h1 : ({y} : Finset (Fin ms)).card ≤ ts := by rw [Finset.card_singleton]; omega
    have h2 : ts ≤ ((Finset.univ : Finset (Fin ms)).erase x).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ, Fintype.card_fin]
      omega
    have hsub : ({y} : Finset (Fin ms)) ⊆ (Finset.univ : Finset (Fin ms)).erase x := by
      intro z hz
      rw [Finset.mem_singleton] at hz
      rw [hz]
      exact Finset.mem_erase.2 ⟨hxy.symm, Finset.mem_univ _⟩
    obtain ⟨S, hyS, hSx, hScard⟩ := Finset.exists_subsuperset_card_eq hsub h1 h2
    obtain ⟨⟨w, hwJ⟩, hw⟩ := hJ.toBinom_bijective.2 ⟨S, hScard⟩
    have hwS : rawJSet ms (rawJRow (J, (w : ℕ))) = S := congrArg Subtype.val hw
    have hyw : (b : ℕ) ∈ rawJRow (J, (w : ℕ)) := by
      have : y ∈ rawJSet ms (rawJRow (J, (w : ℕ))) := by
        rw [hwS]; exact hyS (Finset.mem_singleton_self y)
      exact (mem_rawJSet (i := y)).1 this
    have hxw : (a : ℕ) ∉ rawJRow (J, (w : ℕ)) := by
      intro hmem
      have : x ∈ rawJSet ms (rawJRow (J, (w : ℕ))) := (mem_rawJSet (i := x)).2 hmem
      rw [hwS] at this
      exact (Finset.mem_erase.1 (hSx this)).1 rfl
    have hb' : alignDomMark (p, b, w) = true := by
      rw [alignDomMark_johnson]
      simp only [Bool.and_eq_true, decide_eq_true_iff]
      exact ⟨hwJ, hyw⟩
    have ha' := hab w hb'
    rw [alignDomMark_johnson] at ha'
    simp only [Bool.and_eq_true, decide_eq_true_iff] at ha'
    exact hxw ha'.2

end CaseB

end Algo
