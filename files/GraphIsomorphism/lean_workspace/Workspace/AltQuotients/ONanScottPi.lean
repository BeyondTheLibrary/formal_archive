/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Direct powers of a nonabelian simple group, used in the proof of Theorem 10.2.4.
-/
import Workspace.AltQuotients.ONanScottConstr

/-!
# Direct powers `T^ι` of a nonabelian simple group

Background for the proof of Theorem 10.2.4 (Dixon–Mortimer, GTM 163, §4.3 and §4.6).  For a
nonabelian simple group `T` and a finite index type `ι`:

* `Babai.ONS.coord i`, the `i`-th coordinate subgroup of `T^ι`;
* `Babai.ONS.coord_le_of_normal`: a normal subgroup of `T^ι` with an element whose `i`-th
  coordinate is nontrivial contains the `i`-th coordinate subgroup ([DiM, Thm. 4.3A (iii)]);
* `Babai.ONS.sigma`, `Babai.ONS.theta`: an automorphism of `T^ι` permutes the coordinate
  subgroups ([DiM, Thm. 4.3A (iii)]), `σ`, and acts between them by isomorphisms `θ`, with
  `(γ f)(σ i) = θ (f i)`;
* `Babai.ONS.diagGroup`: the primitive group of diagonal type with socle `T^k`
  ([DiM, Lemma 4.5A, Thm. 4.5A]), of degree `|T|^{k-1}`.
-/

namespace Babai

namespace ONS

open Subgroup

section Coord

variable {ι : Type*} [DecidableEq ι] {R : Type*} [Group R]

/-- The `i`-th coordinate subgroup of `R^ι`. -/
def coord (i : ι) : Subgroup (ι → R) := (MonoidHom.mulSingle (fun _ : ι => R) i).range

theorem mem_coord {i : ι} {f : ι → R} : f ∈ coord i ↔ ∀ j, j ≠ i → f j = 1 := by
  constructor
  · rintro ⟨r, rfl⟩ j hj
    simp [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne hj]
  · intro h
    refine ⟨f i, funext fun j => ?_⟩
    by_cases hj : j = i
    · subst hj; simp
    · simp [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne hj, h j hj]

theorem mulSingle_mem_coord (i : ι) (r : R) : Pi.mulSingle i r ∈ coord i := ⟨r, rfl⟩

theorem eq_mulSingle_of_mem_coord {i : ι} {f : ι → R} (hf : f ∈ coord i) :
    f = Pi.mulSingle i (f i) := by
  obtain ⟨r, rfl⟩ := hf
  simp [MonoidHom.mulSingle_apply]

instance coord_normal (i : ι) : (coord (R := R) i).Normal := by
  constructor
  intro f hf g
  rw [mem_coord] at hf ⊢
  intro j hj
  simp [hf j hj]

/-- A function supported on `S` lies in every subgroup containing the coordinate subgroups
of `S`. -/
theorem mem_of_coord_le (Y : Subgroup (ι → R)) (S : Finset ι)
    (hS : ∀ i ∈ S, coord i ≤ Y) (f : ι → R) (hf : ∀ i ∉ S, f i = 1) : f ∈ Y := by
  induction S using Finset.induction_on generalizing f with
  | empty =>
    have : f = 1 := funext fun i => hf i (Finset.notMem_empty i)
    rw [this]; exact Y.one_mem
  | insert a S haS ih =>
    have hsplit : f = Pi.mulSingle a (f a) * Function.update f a 1 := by
      funext j
      by_cases hj : j = a
      · subst hj; simp
      · simp [Pi.mulSingle_eq_of_ne hj, Function.update_of_ne hj]
    rw [hsplit]
    refine mul_mem (hS a (Finset.mem_insert_self a S) (mulSingle_mem_coord a _)) ?_
    refine ih (fun i hi => hS i (Finset.mem_insert_of_mem hi)) _ ?_
    intro i hi
    by_cases hia : i = a
    · subst hia; simp
    · rw [Function.update_of_ne hia]
      exact hf i (by simp [hia, hi])

theorem eq_top_of_coord_le [Fintype ι] (Y : Subgroup (ι → R)) (h : ∀ i, coord i ≤ Y) :
    Y = ⊤ :=
  eq_top_iff.2 fun f _ => mem_of_coord_le Y Finset.univ (fun i _ => h i) f (by simp)

theorem coord_le_coord_iff [Nontrivial R] {i j : ι} : coord (R := R) i ≤ coord j ↔ i = j := by
  constructor
  · intro h
    obtain ⟨r, hr⟩ := exists_ne (1 : R)
    have := h (mulSingle_mem_coord i r)
    rw [mem_coord] at this
    by_contra hij
    have := this i hij
    simp at this
    exact hr this
  · rintro rfl; exact le_rfl

end Coord

section Simple

variable {R : Type*} [Group R] [IsSimpleGroup R] (hR : ¬ ∀ a b : R, a * b = b * a)

include hR in
/-- A nontrivial element of a nonabelian simple group is not central. -/
theorem exists_not_commute {r : R} (hr : r ≠ 1) : ∃ t : R, r * t ≠ t * r := by
  by_contra h
  push Not at h
  have hc : r ∈ Subgroup.center R := Subgroup.mem_center_iff.2 fun t => (h t).symm
  rw [center_eq_bot_of_simple_nonabelian hR, Subgroup.mem_bot] at hc
  exact hr hc

include hR in
/-- A nontrivial element of a nonabelian simple group does not commute with some conjugate
of itself: otherwise it would commute with its normal closure, the whole group. -/
theorem exists_not_commute_conj {r : R} (hr : r ≠ 1) :
    ∃ t : R, r * (t * r * t⁻¹) ≠ (t * r * t⁻¹) * r := by
  by_contra h
  push Not at h
  have hncl : Subgroup.normalClosure ({r} : Set R) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal _
      (Subgroup.normalClosure_normal (s := ({r} : Set R))) with h' | h'
    · exfalso
      have : r ∈ Subgroup.normalClosure ({r} : Set R) :=
        Subgroup.subset_normalClosure (Set.mem_singleton r)
      rw [h', Subgroup.mem_bot] at this
      exact hr this
    · exact h'
  obtain ⟨t, ht⟩ := exists_not_commute hR hr
  apply ht
  have ht' : t ∈ Subgroup.normalClosure ({r} : Set R) := by rw [hncl]; trivial
  rw [Subgroup.normalClosure, Subgroup.mem_closure] at ht'
  let C : Subgroup R := Subgroup.centralizer {r}
  have hsub : Group.conjugatesOfSet ({r} : Set R) ⊆ C := by
    intro x hx
    rw [Group.mem_conjugatesOfSet_iff] at hx
    obtain ⟨a, ha, hx⟩ := hx
    rw [Set.mem_singleton_iff] at ha
    subst ha
    obtain ⟨c, rfl⟩ := isConj_iff.1 hx
    show c * _ * c⁻¹ ∈ C
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (h c)
  have := ht' C hsub
  rw [Subgroup.mem_centralizer_iff] at this
  exact (this r (Set.mem_singleton r))

end Simple

section Normal

variable {ι : Type*} [DecidableEq ι] {R : Type*} [Group R] [IsSimpleGroup R]
  (hR : ¬ ∀ a b : R, a * b = b * a)

/-- The subgroup of `R` of the `i`-th coordinates of `Y ∩ coord i`. -/
def coordPart (Y : Subgroup (ι → R)) (i : ι) : Subgroup R :=
  Y.comap (MonoidHom.mulSingle (fun _ : ι => R) i)

omit [IsSimpleGroup R] in
theorem coord_le_of_coordPart_eq_top {Y : Subgroup (ι → R)} {i : ι}
    (h : coordPart Y i = ⊤) : coord i ≤ Y := by
  rintro _ ⟨r, rfl⟩
  have : r ∈ coordPart Y i := by rw [h]; trivial
  exact this

/-- If `Y` is normalized by the constant functions and contains a nontrivial element of the
`i`-th coordinate subgroup, then it contains that subgroup. -/
theorem coord_le_of_const_normal {Y : Subgroup (ι → R)} {i : ι}
    (hY : ∀ t : R, ∀ y ∈ Y, (fun _ => t) * y * (fun _ => t⁻¹) ∈ Y)
    {r : R} (hr : r ≠ 1) (hrY : Pi.mulSingle i r ∈ Y) : coord i ≤ Y := by
  apply coord_le_of_coordPart_eq_top
  have hn : (coordPart Y i).Normal := by
    constructor
    intro z hz t
    have := hY t _ hz
    show Pi.mulSingle i (t * z * t⁻¹) ∈ Y
    convert this using 1
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Pi.mulSingle_eq_of_ne hj]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal _ hn with h | h
  · exfalso
    have : r ∈ coordPart Y i := hrY
    rw [h, Subgroup.mem_bot] at this
    exact hr this
  · exact h

include hR in
/-- **[DiM, Thm. 4.3A (iii)]**, the step used here: a normal subgroup of `R^ι` that has an
element with nontrivial `i`-th coordinate contains the `i`-th coordinate subgroup. -/
theorem coord_le_of_normal (Y : Subgroup (ι → R)) [hYn : Y.Normal] {y : ι → R} (hy : y ∈ Y)
    {i : ι} (hyi : y i ≠ 1) : coord i ≤ Y := by
  obtain ⟨t, ht⟩ := exists_not_commute hR hyi
  set m : ι → R := Pi.mulSingle i t with hm
  have hc : y * m * y⁻¹ * m⁻¹ ∈ Y := by
    have h1 : m * y⁻¹ * m⁻¹ ∈ Y := hYn.conj_mem _ (inv_mem hy) m
    have := mul_mem hy h1
    simpa [mul_assoc] using this
  have hceq : y * m * y⁻¹ * m⁻¹ = Pi.mulSingle i (y i * t * (y i)⁻¹ * t⁻¹) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp [hm]
    · simp [hm, Pi.mulSingle_eq_of_ne hj]
  rw [hceq] at hc
  refine coord_le_of_const_normal (fun t' z hz => ?_) ?_ hc
  · have := hYn.conj_mem z hz (fun _ => t')
    simpa using this
  · intro h
    apply ht
    have : y i * t * (y i)⁻¹ = t := by
      calc y i * t * (y i)⁻¹ = y i * t * (y i)⁻¹ * t⁻¹ * t := by group
        _ = t := by rw [h, one_mul]
    calc y i * t = y i * t * (y i)⁻¹ * y i := by group
      _ = t * y i := by rw [this]

include hR in
/-- A nontrivial normal subgroup of `R^ι` contains a coordinate subgroup. -/
theorem exists_coord_le_of_normal (Y : Subgroup (ι → R)) [Y.Normal] (hY : Y ≠ ⊥) :
    ∃ i, coord i ≤ Y := by
  obtain ⟨y, hy, hy1⟩ : ∃ y ∈ Y, y ≠ 1 := by
    by_contra h
    push Not at h
    exact hY (eq_bot_iff.2 fun y hy => Subgroup.mem_bot.2 (h y hy))
  obtain ⟨i, hi⟩ : ∃ i, y i ≠ 1 := by
    by_contra h
    push Not at h
    exact hy1 (funext h)
  exact ⟨i, coord_le_of_normal hR Y hy hi⟩

include hR in
/-- An element that commutes with the `j`-th coordinate subgroup has trivial `j`-th
coordinate. -/
theorem apply_eq_one_of_commute {g : ι → R} {j : ι}
    (h : ∀ f ∈ coord (R := R) j, g * f = f * g) : g j = 1 := by
  by_contra hg
  obtain ⟨t, ht⟩ := exists_not_commute hR hg
  have := congrFun (h _ (mulSingle_mem_coord j t)) j
  simp at this
  exact ht this

end Normal

section Aut

variable {ι : Type*} [DecidableEq ι] {R : Type*} [Group R] [IsSimpleGroup R]
  (hR : ¬ ∀ a b : R, a * b = b * a)

theorem coord_ne_bot (i : ι) : coord (R := R) i ≠ ⊥ := by
  obtain ⟨r, hr⟩ := exists_ne (1 : R)
  intro h
  have := mulSingle_mem_coord i r
  rw [h, Subgroup.mem_bot] at this
  exact hr (by simpa using congrFun this i)

include hR in
/-- **[DiM, Thm. 4.3A (iii)]**: an automorphism of `R^ι` permutes the coordinate
subgroups. -/
theorem exists_map_coord (γ : MulAut (ι → R)) (i : ι) :
    ∃ j, (coord (R := R) i).map γ.toMonoidHom = coord j := by
  set Y := (coord (R := R) i).map γ.toMonoidHom with hY
  haveI : Y.Normal := (coord_normal i).map _ γ.surjective
  have hYne : Y ≠ ⊥ := by
    intro h
    exact coord_ne_bot i ((Subgroup.map_eq_bot_iff_of_injective _ γ.injective).1 h)
  obtain ⟨j, hj⟩ := exists_coord_le_of_normal hR Y hYne
  refine ⟨j, le_antisymm ?_ hj⟩
  set Z := (coord (R := R) j).comap γ.toMonoidHom with hZ
  haveI : Z.Normal := (coord_normal j).comap _
  have hZle : Z ≤ coord i := by
    have := Subgroup.comap_mono (f := γ.toMonoidHom) hj
    rwa [Subgroup.comap_map_eq_self_of_injective γ.injective] at this
  have hZne : Z ≠ ⊥ := by
    intro h
    apply coord_ne_bot (R := R) j
    have hmap : Z.map γ.toMonoidHom = coord j :=
      Subgroup.map_comap_eq_self_of_surjective γ.surjective _
    rw [← hmap, h, Subgroup.map_bot]
  obtain ⟨l, hl⟩ := exists_coord_le_of_normal hR Z hZne
  have hli : l = i := coord_le_coord_iff.1 (hl.trans hZle)
  subst hli
  rw [Subgroup.map_le_iff_le_comap]
  exact hl

/-- The permutation of the coordinates induced by an automorphism of `R^ι`. -/
noncomputable def sigma (γ : MulAut (ι → R)) (i : ι) : ι := by
  classical exact if h : ∃ j, (coord (R := R) i).map γ.toMonoidHom = coord j then h.choose else i

include hR in
theorem map_coord_sigma (γ : MulAut (ι → R)) (i : ι) :
    (coord (R := R) i).map γ.toMonoidHom = coord (sigma γ i) := by
  have h := exists_map_coord hR γ i
  rw [sigma, dif_pos h]
  exact h.choose_spec

omit [IsSimpleGroup R] in
theorem sigma_eq_of_map [Nontrivial R] {γ : MulAut (ι → R)} {i j : ι}
    (h : (coord (R := R) i).map γ.toMonoidHom = coord j) : sigma γ i = j := by
  have h' : ∃ j, (coord (R := R) i).map γ.toMonoidHom = coord j := ⟨j, h⟩
  rw [sigma, dif_pos h']
  exact coord_le_coord_iff.1 (h'.choose_spec.symm.trans h).le

omit [DecidableEq ι] [IsSimpleGroup R] in
theorem toMonoidHom_mul (γ δ : MulAut (ι → R)) :
    (γ * δ).toMonoidHom = γ.toMonoidHom.comp δ.toMonoidHom := rfl

include hR in
theorem sigma_mul (γ δ : MulAut (ι → R)) (i : ι) : sigma (γ * δ) i = sigma γ (sigma δ i) := by
  apply sigma_eq_of_map
  rw [toMonoidHom_mul, ← Subgroup.map_map, map_coord_sigma hR, map_coord_sigma hR]

theorem sigma_one (i : ι) : sigma (1 : MulAut (ι → R)) i = i := by
  apply sigma_eq_of_map
  convert Subgroup.map_id (coord (R := R) i)

/-- The isomorphism from the `i`-th to the `σ(i)`-th coordinate induced by `γ`. -/
noncomputable def theta (γ : MulAut (ι → R)) (i : ι) : R →* R :=
  (Pi.evalMonoidHom (fun _ : ι => R) (sigma γ i)).comp
    (γ.toMonoidHom.comp (MonoidHom.mulSingle (fun _ : ι => R) i))

omit [IsSimpleGroup R] in
theorem theta_apply (γ : MulAut (ι → R)) (i : ι) (r : R) :
    theta γ i r = γ (Pi.mulSingle i r) (sigma γ i) := rfl

include hR in
theorem apply_mulSingle (γ : MulAut (ι → R)) (i : ι) (r : R) :
    γ (Pi.mulSingle i r) = Pi.mulSingle (sigma γ i) (theta γ i r) := by
  have hmem : γ (Pi.mulSingle i r) ∈ coord (R := R) (sigma γ i) := by
    rw [← map_coord_sigma hR]
    exact ⟨_, mulSingle_mem_coord i r, rfl⟩
  exact eq_mulSingle_of_mem_coord hmem

include hR in
/-- The coordinate formula `(γ f)(σ i) = θ (f i)`. -/
theorem apply_sigma (γ : MulAut (ι → R)) (f : ι → R) (i : ι) :
    γ f (sigma γ i) = theta γ i (f i) := by
  set f' := Function.update f i 1 with hf'
  have hsplit : f = Pi.mulSingle i (f i) * f' := by
    funext j
    by_cases hj : j = i
    · subst hj; simp [hf']
    · simp [hf', Pi.mulSingle_eq_of_ne hj, Function.update_of_ne hj]
  have h1 : γ f' (sigma γ i) = 1 := by
    apply apply_eq_one_of_commute hR
    intro g hg
    rw [← map_coord_sigma hR] at hg
    obtain ⟨h, hh, rfl⟩ := hg
    have hc : f' * h = h * f' := by
      rw [SetLike.mem_coe, mem_coord] at hh
      funext j
      by_cases hj : j = i
      · subst hj; simp [hf']
      · simp [hh j hj]
    show γ f' * γ h = γ h * γ f'
    rw [← map_mul, ← map_mul, hc]
  conv_lhs => rw [hsplit]
  rw [map_mul, Pi.mul_apply, h1, mul_one, theta_apply]

include hR in
theorem theta_mul (γ δ : MulAut (ι → R)) (i : ι) (r : R) :
    theta (γ * δ) i r = theta γ (sigma δ i) (theta δ i r) := by
  rw [theta_apply, sigma_mul hR, MulAut.mul_apply, apply_sigma hR, apply_sigma hR]
  simp

theorem theta_one (i : ι) (r : R) : theta (1 : MulAut (ι → R)) i r = r := by
  rw [theta_apply, sigma_one]
  simp

include hR in
theorem sigma_inv_sigma (γ : MulAut (ι → R)) (i : ι) : sigma γ⁻¹ (sigma γ i) = i := by
  rw [← sigma_mul hR, inv_mul_cancel, sigma_one]

include hR in
theorem sigma_sigma_inv (γ : MulAut (ι → R)) (i : ι) : sigma γ (sigma γ⁻¹ i) = i := by
  rw [← sigma_mul hR, mul_inv_cancel, sigma_one]

/-- `θ` as an isomorphism. -/
noncomputable def thetaEquiv (γ : MulAut (ι → R)) (i : ι) : R ≃* R :=
  MulEquiv.ofBijective (theta γ i) (by
    refine ⟨fun a b hab => ?_, fun r => ⟨theta γ⁻¹ (sigma γ i) r, ?_⟩⟩
    · have ha := theta_mul hR γ⁻¹ γ i a
      have hb := theta_mul hR γ⁻¹ γ i b
      rw [inv_mul_cancel, theta_one] at ha hb
      rw [ha, hb, hab]
    · have h := theta_mul hR γ γ⁻¹ (sigma γ i) r
      rw [mul_inv_cancel, theta_one, sigma_inv_sigma hR] at h
      exact h.symm)

theorem thetaEquiv_apply (γ : MulAut (ι → R)) (i : ι) (r : R) :
    thetaEquiv hR γ i r = theta γ i r := rfl

end Aut

end ONS

end Babai
