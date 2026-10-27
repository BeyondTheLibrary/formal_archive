import Workspace.Algo.SplitUpcc

/-!
# The outcome specification for Lemma 9.3.1

`UpccOutcomeRep` describes decoding by a relation: the stored names, colors,
blocks, matrix entries and threshold must all agree with the mathematical
object. This avoids choosing names on an abstract carrier during decoding.
The main result is `Upcc.versionF_spec`. It gives a valid outcome, as requested
when the mathematical construction contains `Classical.choose`.
-/

namespace Algo

open Babai RAM

section Encoding

variable {Ω : Type} {s : Set Ω} {n : ℕ}

/-- The ambient name of a vertex of the returned graph. -/
def upccSubName (e : ↥s ≃ Fin n) {t : Set Ω} (ht : t ⊆ s) (w : ↥t) : ℕ :=
  e ⟨w,ht w.2⟩

open scoped Classical in
/-- The raw graph represents exactly these parts, edges and vertex colors.
The two image equalities also rule out extra or missing vertex names. -/
def UpccBipRep (e : ↥s ≃ Fin n) (lab : RawLab) (g : RawUpccBip)
    {t : Set Ω} (ht : t ⊆ s) (Y : VColBip ↥t ℕ) : Prop :=
  g.1.Nodup ∧ g.2.1.Nodup ∧
    upccSubName e ht '' Y.V₁ = {u | u ∈ g.1} ∧
    upccSubName e ht '' Y.V₂ = {u | u ∈ g.2.1} ∧
    (∀ w, labAt lab (upccSubName e ht w) = Y.f w) ∧
    g.2.2 = g.1.map (fun u => g.2.1.map (fun v =>
      if ∃ w z : ↥t, upccSubName e ht w = u ∧ upccSubName e ht z = v ∧
        (w,z) ∈ Y.E then 1 else 0))

/-- The decoding relation for the tagged outcome. In the partition branch,
the equivalence is the identity on ambient vertices. In the graph branch,
the inclusion names every retained vertex. -/
def UpccOutcomeRep [Fintype Ω] [DecidableEq Ω] (e : ↥s ≃ Fin n) (q : RawUpccOutcome)
    (Z : Pt (Cat.sum (ColoredPartitions Ω ℕ) (BipInputs Ω))) : Prop :=
  q.1.1.length = n ∧ q.1.2.length = n ∧
    match q.2, Z.obj with
    | none, Sum.inl P => ∃ f : ↥Z.car ≃ ↥s,
        (∀ w, (f w : Ω) = (w : Ω)) ∧
        (∀ w, labAt q.1.1 (e (f w)) = P.color w) ∧
        (∀ u v, LabRel q.1.2 (e (f u)) (e (f v)) ↔ P.part u v)
    | some (ab,g), Sum.inr Y => ∃ ht : Z.car ⊆ s,
        UpccBipRep e q.1.1 g ht Y.1.1 ∧ (ab.1 : ℝ) / ab.2 = Y.1.2
    | _, _ => False

end Encoding

section GraphSpec

variable {Ω : Type} [Fintype Ω] {s : Set Ω} {n : ℕ} {p : RawConfig}
    {c : ↥s → ↥s → ℕ}

theorem upccBipRaw_rep (h : RawWL.WF n 2 p) (e : ↥s ≃ Fin n)
    (he : UpccNames e p c) (x : ↥s) (k i j : ℕ) (hik : i ≠ k) :
    UpccBipRep e (upccCellsRaw (p,e x)) (upccBipRaw ((p,e x),(k,i,j)))
      (bipCarrier_subset c x k i) (bipGraph c x k i j) := by
  classical
  have hname : ∀ w : ↥(bipCarrier c x k i),
      upccSubName e (bipCarrier_subset c x k i) w = (e (bipIota w) : ℕ) := fun _ => rfl
  have himg₁ : upccSubName e (bipCarrier_subset c x k i) '' (bipGraph c x k i j).V₁ =
      {u | u ∈ upccCellRaw ((p,e x),k)} := by
    ext u
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact (upccCellRaw_spec h e he x (bipIota w) k).2 hw
    · intro hu
      have hlt : u < n := (h.domMem u).1 (List.mem_of_mem_filter hu)
      let y := e.symm ⟨u,hlt⟩
      have hy : y ∈ cellOf c x k :=
        (upccCellRaw_spec h e he x y k).1 (by simpa [y] using hu)
      refine ⟨bipPt (Or.inl hy),hy,?_⟩
      simp [hname, y]
  have himg₂ : upccSubName e (bipCarrier_subset c x k i) '' (bipGraph c x k i j).V₂ =
      {u | u ∈ upccCellRaw ((p,e x),i)} := by
    rw [bipGraph_V₂_eq hik]
    ext u
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact (upccCellRaw_spec h e he x (bipIota w) i).2 hw
    · intro hu
      have hlt : u < n := (h.domMem u).1 (List.mem_of_mem_filter hu)
      let y := e.symm ⟨u,hlt⟩
      have hy : y ∈ cellOf c x i :=
        (upccCellRaw_spec h e he x y i).1 (by simpa [y] using hu)
      refine ⟨bipPt (Or.inr hy),hy,?_⟩
      simp [hname, y]
  refine ⟨h.domNodup.filter _,h.domNodup.filter _,himg₁,himg₂,?_,?_⟩
  · intro w
    exact upccCellsRaw_spec h e he x (bipIota w)
  · change upccBipRows _ = _
    unfold upccBipRows upccBipRow
    apply List.map_congr_left
    intro u hu
    apply List.map_congr_left
    intro v hv
    have hu' : u < n := (h.domMem u).1 (List.mem_of_mem_filter hu)
    have hv' : v < n := (h.domMem v).1 (List.mem_of_mem_filter hv)
    let u' := e.symm ⟨u,hu'⟩
    let v' := e.symm ⟨v,hv'⟩
    have huk : u' ∈ cellOf c x k :=
      (upccCellRaw_spec h e he x u' k).1 (by simpa [u'] using hu)
    have hvi : v' ∈ cellOf c x i :=
      (upccCellRaw_spec h e he x v' i).1 (by simpa [v'] using hv)
    have hedge : binColor (p,(u,v)) = j ↔
        ∃ w z : ↥(bipCarrier c x k i),
          upccSubName e (bipCarrier_subset c x k i) w = u ∧
          upccSubName e (bipCarrier_subset c x k i) z = v ∧
          (w,z) ∈ (bipGraph c x k i j).E := by
      constructor
      · intro huv
        refine ⟨bipPt (Or.inl huk),bipPt (Or.inr hvi),?_,?_,huk,?_,?_⟩
        · simp [hname,u']
        · simp [hname,v']
        · exact fun hk => hik (hvi.symm.trans hk)
        · have hcol := he u' v'
          simpa [u',v',huv] using hcol.symm
      · rintro ⟨w,z,hw,hz,hE⟩
        have hcol := he (bipIota w) (bipIota z)
        rw [← hname w, ← hname z, hw, hz] at hcol
        exact hcol.trans hE.2.2
    simp only [hedge]
    split <;> simp_all

end GraphSpec

section Validity

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {c : ↥s → ↥s → ℕ} {β : ℝ} {x : ↥s} {k : ℕ}

omit [DecidableEq Ω] in
/-- Lemma 9.3.1: any color passing the strict big-cell test gives an admissible
bipartite input with the least middle pair. -/
theorem upccBipCond_of_big (hc : IsUPCCColoring c) (hβ : 2 / 3 ≤ β)
    (hk : β * s.ncard < ((cellOf c x k).ncard : ℝ)) :
    upccBipCond β c x k (midI c x k) (midJ c x k) := by
  classical
  obtain ⟨_,hsr,hnt,h2,hlt,_,hαβ,hα1,_⟩ := bipCase hc hβ hk
  refine ⟨by linarith,hα1,h2,hlt,?_⟩
  have key : ∀ (iF : Fintype ↥(bipCarrier c x k (midI c x k)))
      (iD : DecidableEq ↥(bipCarrier c x k (midI c x k))),
      (1 : ℚ) / 2 ≤ @VColBip.defect₁ _ _
        (bipGraph c x k (midI c x k) (midJ c x k)) iF iD :=
    fun iF iD => @VColBip.half_le_defect₁ _ _ iF iD _ hsr hnt
  have hle : 1 - bipAlpha β c x k ≤ ((1 / 2 : ℚ) : ℝ) := by
    push_cast
    linarith
  exact hle.trans (Rat.cast_le.2 (key _ _))

/-- Lemma 9.3.1: the selected big color need only satisfy its size test. -/
theorem upccBigOutcome_good (X : Pt (UPCCs Ω)) {x : ↥X.car} {k : ℕ}
    (hβ : 2 / 3 ≤ β) (hk : β * X.car.ncard < ((cellOf X.obj.1 x k).ncard : ℝ)) :
    IsUPCCToBipOutcome β X
      ⟨bipCarrier X.obj.1 x k (midI X.obj.1 x k),
        Sum.inr ⟨(bipGraph X.obj.1 x k (midI X.obj.1 x k) (midJ X.obj.1 x k),
          bipAlpha β X.obj.1 x k),upccBipCond_of_big X.obj.2 hβ hk⟩⟩ := by
  obtain ⟨_,hsr,_,_,_,hge,_,hα1,hαe⟩ := bipCase X.obj.2 hβ hk
  exact ⟨bipCarrier_subset _ _ _ _,hsr,hge,hα1.le,hαe⟩

end Validity

namespace Upcc

/-- Lemma 9.3.1 on the RAM: the indexed raw value represents a valid outcome
on the named abstract carrier. The specification does not identify a
`Classical.choose` witness with a computed value. -/
theorem versionF_spec {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (X : Pt (UPCCs Ω)) {n a b : ℕ} {p : RawConfig}
    (h : RawWL.WF n 2 p) (e : ↥X.car ≃ Fin n) (he : UpccNames e p X.obj.1)
    (hb : 0 < b) (hβ : (2 : ℝ) / 3 ≤ (a : ℝ) / b) (x : ↥X.car) :
    ∃ Z : Pt (Cat.sum (ColoredPartitions Ω ℕ) (BipInputs Ω)),
      UpccOutcomeRep e (versionF ((p,(a,b)),e x)) Z ∧
        IsUPCCToBipOutcome ((a : ℝ) / b) X Z := by
  classical
  have hlen : (upccCellsRaw (p,e x)).length = n := by
    simp [card_eq_length_dom h]
  cases hk : upccBigColor ((p,(a,b)),e x) with
  | none =>
      have hnil : upccBigColors ((p,(a,b)),e x) = [] := by
        simpa [upccBigColor] using hk
      have hsmall := (upccCellSmall_spec h e he hb x).1
        (show upccCellSmall ((p,(a,b)),e x) = true by simp [upccCellSmall,hnil])
      refine ⟨⟨X.car,Sum.inl (cellPartition X.obj.1 x)⟩,?_,?_⟩
      · simp only [versionF,hk,Option.elim_none,UpccOutcomeRep]
        exact ⟨hlen,hlen,Equiv.refl _,fun _ => rfl,
          upccCellsRaw_spec h e he x,upccCellsRaw_blocks h e he x⟩
      · refine ⟨rfl,?_⟩
        have key : ∀ iF : Fintype ↥X.car,
            @ColoredPartition.IsAlphaPartition _ _ (cellPartition X.obj.1 x) iF
              ((a : ℝ) / b) := by
          intro iF
          apply cellPartition_isAlphaPartition
          intro k
          simpa only [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] using hsmall k
        exact key _
  | some k =>
      have hbig := upccBigColor_spec h e he hb x hk
      let i := midI X.obj.1 x k
      let j := midJ X.obj.1 x k
      let Z : Pt (Cat.sum (ColoredPartitions Ω ℕ) (BipInputs Ω)) :=
        ⟨bipCarrier X.obj.1 x k i,Sum.inr ⟨(bipGraph X.obj.1 x k i j,
          bipAlpha ((a : ℝ) / b) X.obj.1 x k),upccBipCond_of_big X.obj.2 hβ hbig⟩⟩
      refine ⟨Z,?_,upccBigOutcome_good X hβ hbig⟩
      have hik : i ≠ k := (bipCase X.obj.2 hβ hbig).1
      have hij := upccMidIJRaw_spec h e he x k
      change upccMidIJRaw ((p,e x),k) = (i,j) at hij
      simp only [versionF,hk,Option.elim_some,UpccOutcomeRep,upccBipBranch,hij,Z]
      refine ⟨hlen,hlen,bipCarrier_subset _ _ _ _,upccBipRaw_rep h e he x k i j hik,?_⟩
      rw [upccCellRaw_size h e he,card_eq_length_dom h,bipAlpha,upccNaming_card e]
      push_cast
      ring

/-- The same outcome specification for a raw version index below `widthF`. -/
theorem versionF_spec_index {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (X : Pt (UPCCs Ω)) {n a b : ℕ} {p : RawConfig}
    (h : RawWL.WF n 2 p) (e : ↥X.car ≃ Fin n) (he : UpccNames e p X.obj.1)
    (hb : 0 < b) (hβ : (2 : ℝ) / 3 ≤ (a : ℝ) / b) {i : ℕ}
    (hi : i < widthF (p,(a,b))) :
    ∃ Z : Pt (Cat.sum (ColoredPartitions Ω ℕ) (BipInputs Ω)),
      UpccOutcomeRep e (versionF ((p,(a,b)),i)) Z ∧
        IsUPCCToBipOutcome ((a : ℝ) / b) X Z := by
  have hi' : i < n := by simpa only [widthF,card_eq_length_dom h] using hi
  simpa only [e.apply_symm_apply] using versionF_spec X h e he hb hβ (e.symm ⟨i,hi'⟩)

/-- Lemma 9.3.1: the indexed raw family has at most `n` members.
This set is used only in the specification and is never materialized by the routine. -/
theorem versionFamily_card_le (r : RawUpcc) :
    (Set.range (fun i : Fin (widthF r) => versionF (r,i))).ncard ≤ widthF r := by
  rw [← Set.image_univ]
  simpa only [Set.ncard_univ,Nat.card_fin] using
    Set.ncard_image_le (s := (Set.univ : Set (Fin (widthF r))))
      (f := fun i => versionF (r,i)) Set.finite_univ

end Upcc

end Algo
