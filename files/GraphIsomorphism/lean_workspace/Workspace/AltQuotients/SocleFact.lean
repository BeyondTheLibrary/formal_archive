/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Fact 10.2.2 (ii), proved (it was an axiom citing the O'Nan–Scott theorem).
-/
import Workspace.AltQuotients.Defs
import Workspace.Prelim.PrimitiveSocleRegular

/-!
# Fact 10.2.2 (ii): the socle of a primitive group

The paper cites Fact 10.2.2 from the literature (`[Sco]`, `[AsS]`, cf. `[DiM, Thm. 4.3B]`)
and remarks that "the proof of this theorem is elementary".  It is proved here along the
standard proof, Dixon–Mortimer, *Permutation Groups*, GTM 163, Springer 1996:

* **[DiM, Thm. 4.3A (ii)]** (`Babai.exists_simple_decomp_of_gammaSimple`): a finite group
  `N` that has no proper nontrivial normal subgroup invariant under a group `Γ` of
  automorphisms is the direct product of `Γ`-conjugate, hence isomorphic, simple
  subgroups.  Applied with `N` a minimal normal subgroup of a finite group and `Γ` the
  conjugations, this is "a minimal normal subgroup is a direct product of isomorphic
  simple groups".
* **[DiM, Thm. 4.3B]**: a primitive group has at most two minimal normal subgroups, and if
  it has two, `M₁` and `M₂`, both are regular and `M₁ ≅ M₂`
  (`Babai.isMinimalNormal_eq_of_three`, `Babai.nonempty_mulEquiv_of_two_minimalNormal`).

Together these give Fact 10.2.2 (ii), `Babai.fact_10_2_2_ii`, with the statement of the
former axiom unchanged.
-/

universe u

namespace Babai

open Subgroup MulAction

/-! ### Independence of normal subgroups -/

section Indep

variable {N : Type*} [Group N]

/-- Two normal subgroups with trivial intersection commute elementwise. -/
theorem commute_of_disjoint_normal {A B : Subgroup N} [A.Normal] [B.Normal]
    (h : Disjoint A B) {x y : N} (hx : x ∈ A) (hy : y ∈ B) : Commute x y := by
  have h1 : x * y * x⁻¹ * y⁻¹ ∈ B :=
    mul_mem (Normal.conj_mem inferInstance y hy x) (inv_mem hy)
  have h2 : x * y * x⁻¹ * y⁻¹ ∈ A := by
    have hmem : y * x⁻¹ * y⁻¹ ∈ A := Normal.conj_mem inferInstance x⁻¹ (inv_mem hx) y
    simpa [mul_assoc] using mul_mem hx hmem
  have hone : x * y * x⁻¹ * y⁻¹ = 1 := Subgroup.disjoint_def.1 h h2 h1
  rw [← commutatorElement_eq_one_iff_commute, commutatorElement_def]
  exact hone

/-- A supremum of normal subgroups is normal. -/
theorem normal_sSup {S : Set (Subgroup N)} (hS : ∀ K ∈ S, K.Normal) : (sSup S).Normal := by
  constructor
  intro x hx g
  rw [sSup_eq_iSup'] at hx ⊢
  refine Subgroup.iSup_induction (fun K : S => (K : Subgroup N))
    (C := fun z => g * z * g⁻¹ ∈ ⨆ K : S, (K : Subgroup N)) hx ?_ ?_ ?_
  · intro K z hz
    exact le_iSup (fun K : S => (K : Subgroup N)) K ((hS K K.2).conj_mem z hz g)
  · simp
  · intro a b ha hb
    have h : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [h]
    exact mul_mem ha hb

/-- If `Q` and `T` are normal and `T` meets `Q ⊔ R` trivially, where `R` meets `Q`
trivially, then ... : the basic step of extending an independent family of normal
subgroups.  `x ∈ R ⊓ (Q ⊔ T)` with `R ⊔ Q ≤ P` and `P ⊓ T = ⊥` forces `x ∈ R ⊓ Q`. -/
theorem disjoint_sup_of_normal {R Q T P : Subgroup N} [T.Normal] (hRP : R ≤ P) (hQP : Q ≤ P)
    (hRQ : Disjoint R Q) (hTP : Disjoint T P) : Disjoint R (Q ⊔ T) := by
  rw [Subgroup.disjoint_def]
  intro x hxR hxQT
  rw [← SetLike.mem_coe, Subgroup.mul_normal Q T] at hxQT
  obtain ⟨q, hq, t, ht, rfl⟩ := hxQT
  have htP : t ∈ P := by
    have : t = q⁻¹ * (q * t) := by group
    rw [this]
    exact mul_mem (inv_mem (hQP hq)) (hRP hxR)
  have ht1 : t = 1 := Subgroup.disjoint_def.1 hTP ht htP
  subst ht1
  simp only [mul_one] at hxR ⊢
  exact Subgroup.disjoint_def.1 hRQ hxR hq

/-- Adding a normal subgroup that meets the supremum trivially to an independent set of
normal subgroups keeps it independent. -/
theorem sSupIndep_insert_of_normal {S : Set (Subgroup N)}
    (hind : sSupIndep S) {T : Subgroup N} [T.Normal] (hTS : T ∉ S)
    (hdisj : Disjoint T (sSup S)) : sSupIndep (insert T S) := by
  intro a ha
  rcases ha with rfl | haS
  · have : insert a S \ {a} = S := by
      ext K
      simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨h1 | h1, h2⟩
        · exact absurd h1 h2
        · exact h1
      · intro hK
        exact ⟨Or.inr hK, fun h => hTS (h ▸ hK)⟩
    rw [this]
    exact hdisj
  · have hne : a ≠ T := fun h => hTS (h ▸ haS)
    have : insert T S \ {a} = insert T (S \ {a}) := by
      ext K
      simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨h1 | h1, h2⟩
        · exact Or.inl h1
        · exact Or.inr ⟨h1, h2⟩
      · rintro (h1 | ⟨h1, h2⟩)
        · exact ⟨Or.inl h1, fun h => hne (h ▸ h1)⟩
        · exact ⟨Or.inr h1, h2⟩
    rw [this, sSup_insert, sup_comm]
    exact disjoint_sup_of_normal (P := sSup S) (le_sSup haS)
      (sSup_le_sSup Set.diff_subset) (hind haS) hdisj

/-- Two independent families of subgroups, lying in two normal subgroups `M₁`, `M₂` that
meet trivially, together form an independent family. -/
theorem iSupIndep_sum_elim {ι κ : Type*} {A : ι → Subgroup N} {B : κ → Subgroup N}
    {M₁ M₂ : Subgroup N} [M₁.Normal] [M₂.Normal] (hA : iSupIndep A) (hB : iSupIndep B)
    (hA1 : ∀ i, A i ≤ M₁) (hB2 : ∀ j, B j ≤ M₂) (hd : Disjoint M₁ M₂) :
    iSupIndep (Sum.elim A B) := by
  rw [iSupIndep_def] at hA hB ⊢
  rintro (i | j)
  · have hle : (⨆ x, ⨆ (_ : x ≠ Sum.inl i), Sum.elim A B x) ≤
        (⨆ k, ⨆ (_ : k ≠ i), A k) ⊔ M₂ := by
      refine iSup₂_le ?_
      rintro (k | k) hk
      · exact le_sup_of_le_left (le_iSup₂_of_le (f := fun k (_ : k ≠ i) => A k) k
          (fun h => hk (h ▸ rfl)) le_rfl)
      · exact le_sup_of_le_right (hB2 k)
    exact (disjoint_sup_of_normal (P := M₁) (hA1 i) (iSup₂_le fun k _ => hA1 k) (hA i)
      hd.symm).mono_right hle
  · have hle : (⨆ x, ⨆ (_ : x ≠ Sum.inr j), Sum.elim A B x) ≤
        (⨆ k, ⨆ (_ : k ≠ j), B k) ⊔ M₁ := by
      refine iSup₂_le ?_
      rintro (k | k) hk
      · exact le_sup_of_le_right (hA1 k)
      · exact le_sup_of_le_left (le_iSup₂_of_le (f := fun k (_ : k ≠ j) => B k) k
          (fun h => hk (h ▸ rfl)) le_rfl)
    exact (disjoint_sup_of_normal (P := M₂) (hB2 j) (iSup₂_le fun k _ => hB2 k) (hB j)
      hd).mono_right hle

end Indep

/-! ### [DiM, Thm. 4.3A (ii)]: characteristically simple groups -/

section CharSimple

variable {N : Type*} [Group N]

/-- **[DiM, Thm. 4.3A (ii)]** (Dixon–Mortimer, *Permutation Groups*, GTM 163, p. 113), in
the form with a group `Γ` of automorphisms.  Let `N` be a nontrivial finite group whose
only `Γ`-invariant normal subgroups are `1` and `N`.  Then `N` is the internal direct
product of simple normal subgroups, all isomorphic.

The proof is the standard one: take a minimal normal subgroup `T₀` of `N`; its images
under `Γ` are minimal normal subgroups of `N` and generate a `Γ`-invariant normal
subgroup, which is `N`; a maximal independent set of them generates `N`, because every
image meets that product in `1` or lies in it; and a factor is simple, because a normal
subgroup of a factor is normalized by the other factors, which centralize it. -/
theorem exists_simple_decomp_of_gammaSimple [Finite N] [Nontrivial N]
    (Γ : Subgroup (MulAut N))
    (hmin : ∀ K : Subgroup N, K.Normal →
      (∀ γ ∈ Γ, K.map (γ : MulAut N).toMonoidHom ≤ K) → K = ⊥ ∨ K = ⊤) :
    ∃ (a : ℕ) (U : Fin a → Subgroup N), iSupIndep U ∧ ⨆ i, U i = ⊤ ∧
      (∀ i, (U i).Normal) ∧ (∀ i, IsSimpleGroup (U i)) ∧ ∀ i j, Nonempty (U i ≃* U j) := by
  classical
  haveI : Finite (Subgroup N) :=
    Finite.of_injective (fun H : Subgroup N => (H : Set N)) SetLike.coe_injective
  haveI : WellQuasiOrderedLE (Subgroup N) := Finite.to_wellQuasiOrderedLE
  set P : Subgroup N → Prop := fun K => K.Normal ∧ K ≠ ⊥ with hP
  have hPtop : P ⊤ := ⟨inferInstance, top_ne_bot⟩
  obtain ⟨T0, -, hT0⟩ := exists_minimal_le_of_wellFoundedLT P ⊤ hPtop
  -- the images of `T₀`
  set cj : MulAut N → Subgroup N := fun γ => T0.map γ.toMonoidHom with hcj
  have hcjP : ∀ γ : MulAut N, P (cj γ) := by
    intro γ
    refine ⟨hT0.1.1.map _ γ.surjective, ?_⟩
    intro h
    exact hT0.1.2 ((Subgroup.map_eq_bot_iff_of_injective _ γ.injective).1 h)
  have hcjmin : ∀ γ : MulAut N, ∀ K, P K → K ≤ cj γ → K = cj γ := by
    intro γ K hK hKle
    have hK' : P (K.map γ.symm.toMonoidHom) :=
      ⟨hK.1.map _ γ.symm.surjective,
        fun h => hK.2 ((Subgroup.map_eq_bot_iff_of_injective _ γ.symm.injective).1 h)⟩
    have hle : K.map γ.symm.toMonoidHom ≤ T0 := by
      intro x hx
      rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm] at hx
      have := hKle hx
      rw [hcj, Subgroup.mem_map_equiv] at this
      simpa using this
    have hge := hT0.2 hK' hle
    refine le_antisymm hKle ?_
    intro x hx
    rw [hcj, Subgroup.mem_map_equiv] at hx
    have := hge hx
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm] at this
    simpa using this
  set C : Set (Subgroup N) := cj '' (Γ : Set (MulAut N)) with hC
  have hCfin : C.Finite := Set.toFinite _
  set F : Finset (Finset (Subgroup N)) :=
    hCfin.toFinset.powerset.filter (fun S => sSupIndep (S : Set (Subgroup N))) with hF
  have hFne : F.Nonempty := ⟨∅, by simp [hF, sSupIndep_empty]⟩
  obtain ⟨S, hSF, hSmax⟩ := F.exists_max_image Finset.card hFne
  rw [hF, Finset.mem_filter, Finset.mem_powerset] at hSF
  obtain ⟨hSC, hSind⟩ := hSF
  have hSC' : ∀ T ∈ S, T ∈ C := fun T hT => (hCfin.mem_toFinset).1 (hSC hT)
  have hSnorm : ∀ T ∈ (S : Set (Subgroup N)), T.Normal := by
    intro T hT
    obtain ⟨γ, -, rfl⟩ := hSC' T hT
    exact (hcjP γ).1
  -- every image of `T₀` lies in the product of `S`
  have hall : ∀ T ∈ C, T ≤ sSup (S : Set (Subgroup N)) := by
    intro T hT
    obtain ⟨γ, hγ, rfl⟩ := hT
    by_cases hmem : cj γ ∈ S
    · exact le_sSup hmem
    · haveI := (hcjP γ).1
      haveI : (sSup (S : Set (Subgroup N))).Normal := normal_sSup hSnorm
      by_cases hbot : cj γ ⊓ sSup (S : Set (Subgroup N)) = ⊥
      · exfalso
        have hind' : sSupIndep (insert (cj γ) (S : Set (Subgroup N))) :=
          sSupIndep_insert_of_normal hSind (by simpa using hmem) (disjoint_iff.2 hbot)
        have hmemF : insert (cj γ) S ∈ F := by
          rw [hF, Finset.mem_filter, Finset.mem_powerset]
          refine ⟨?_, by simpa using hind'⟩
          intro x hx
          rw [Finset.mem_insert] at hx
          rcases hx with rfl | hx
          · exact (hCfin.mem_toFinset).2 ⟨γ, hγ, rfl⟩
          · exact hSC hx
        have := hSmax _ hmemF
        rw [Finset.card_insert_of_notMem hmem] at this
        omega
      · have hPi : P (cj γ ⊓ sSup (S : Set (Subgroup N))) := ⟨inferInstance, hbot⟩
        have := hcjmin γ _ hPi inf_le_left
        rw [← this]
        exact inf_le_right
  -- the images of `T₀` generate `N`
  have hCtop : sSup C = ⊤ := by
    have hnorm : (sSup C).Normal := normal_sSup (by
      rintro T ⟨γ, -, rfl⟩
      exact (hcjP γ).1)
    have hinv : ∀ γ ∈ Γ, (sSup C).map (γ : MulAut N).toMonoidHom ≤ sSup C := by
      intro γ hγ
      rw [(Subgroup.gc_map_comap _).l_sSup]
      refine iSup₂_le ?_
      rintro _ ⟨δ, hδ, rfl⟩
      refine le_sSup ⟨γ * δ, mul_mem hγ hδ, ?_⟩
      simp only [hcj, Subgroup.map_map]
      rfl
    rcases hmin _ hnorm hinv with h | h
    · exfalso
      have h1 : cj 1 ≤ sSup C := le_sSup ⟨1, one_mem _, rfl⟩
      rw [h] at h1
      exact (hcjP 1).2 (le_bot_iff.1 h1)
    · exact h
  have hStop : sSup (S : Set (Subgroup N)) = ⊤ := by
    rw [eq_top_iff, ← hCtop]
    exact sSup_le hall
  -- each member of `S` is simple and isomorphic to `T₀`
  have hiso : ∀ T ∈ S, Nonempty (T0 ≃* T) := by
    intro T hT
    obtain ⟨γ, -, rfl⟩ := hSC' T hT
    exact ⟨T0.equivMapOfInjective γ.toMonoidHom γ.injective⟩
  have hsimple : ∀ T ∈ S, IsSimpleGroup T := by
    intro T hT
    obtain ⟨γ, -, hγT⟩ := hSC' T hT
    haveI hTn : T.Normal := hSnorm T hT
    have hTne : T ≠ ⊥ := hγT ▸ (hcjP γ).2
    set Q := sSup ((S : Set (Subgroup N)) \ {T}) with hQ
    haveI : Q.Normal := normal_sSup (fun K hK => hSnorm K hK.1)
    have hTQ : Disjoint T Q := hSind hT
    have hTQtop : T ⊔ Q = ⊤ := by
      rw [← hStop, hQ, ← sSup_insert, Set.insert_diff_singleton,
        Set.insert_eq_of_mem (Finset.mem_coe.2 hT)]
    haveI : Nontrivial T := (Subgroup.nontrivial_iff_ne_bot T).2 hTne
    refine ⟨fun K hK => ?_⟩
    set K' := K.map T.subtype with hK'
    have hK'T : K' ≤ T := by
      rw [hK']
      exact (Subgroup.map_le_range _ _).trans_eq T.range_subtype
    have hK'n : K'.Normal := by
      constructor
      intro k hk g
      have hg : g ∈ ((T ⊔ Q : Subgroup N) : Set N) := by rw [hTQtop]; trivial
      rw [Subgroup.mul_normal T Q] at hg
      obtain ⟨t, ht, q, hq, rfl⟩ := hg
      have hcomm : Commute q k := commute_of_disjoint_normal hTQ.symm hq (hK'T hk)
      have heq : t * q * k * (t * q)⁻¹ = t * k * t⁻¹ := by
        rw [mul_inv_rev, show t * q * k * (q⁻¹ * t⁻¹) = t * (q * k * q⁻¹) * t⁻¹ by group,
          hcomm.eq, mul_inv_cancel_right]
      rw [heq]
      obtain ⟨k0, hk0, rfl⟩ := Subgroup.mem_map.1 hk
      refine Subgroup.mem_map.2 ⟨⟨t, ht⟩ * k0 * ⟨t, ht⟩⁻¹, hK.conj_mem k0 hk0 _, ?_⟩
      simp
    by_cases hK'bot : K' = ⊥
    · left
      exact (Subgroup.map_eq_bot_iff_of_injective _ T.subtype_injective).1 hK'bot
    · right
      have hK'eq : K' = T := by
        have := hcjmin γ K' ⟨hK'n, hK'bot⟩ (hγT ▸ hK'T)
        rw [this, hγT]
      apply Subgroup.map_injective T.subtype_injective
      rw [← hK', hK'eq, ← MonoidHom.range_eq_map, T.range_subtype]
  -- index `S` by `Fin a`
  set e := S.equivFin with he
  refine ⟨S.card, fun i => (e.symm i : Subgroup N), ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : iSupIndep (fun x : ↥(S : Set (Subgroup N)) => x.1) :=
      (sSupIndep_iff _).1 hSind
    exact h1.comp (f := fun i => (⟨(e.symm i).1, (e.symm i).2⟩ : ↥(S : Set (Subgroup N))))
      (fun i j h => e.symm.injective (Subtype.ext (congrArg Subtype.val h)))
  · rw [← hStop, sSup_eq_iSup']
    exact e.symm.surjective.iSup_comp (fun x : {x // x ∈ S} => x.1)
  · intro i
    exact hSnorm _ (e.symm i).2
  · intro i
    exact hsimple _ (e.symm i).2
  · intro i j
    obtain ⟨fi⟩ := hiso _ (e.symm i).2
    obtain ⟨fj⟩ := hiso _ (e.symm j).2
    exact ⟨fi.symm.trans fj⟩

end CharSimple

/-! ### Transporting a decomposition along an injective homomorphism -/

section Transport

variable {K L : Type*} [Group K] [Group L]

/-- An injective homomorphism preserves independence of subgroups. -/
theorem iSupIndep_map_of_injective {ι : Type*} {U : ι → Subgroup K} (f : K →* L)
    (hf : Function.Injective f) (hU : iSupIndep U) : iSupIndep (fun i => (U i).map f) := by
  rw [iSupIndep_def] at hU ⊢
  intro i
  have h := Subgroup.disjoint_map hf (hU i)
  have heq : (⨆ j, ⨆ (_ : j ≠ i), (U j).map f) = (⨆ j, ⨆ (_ : j ≠ i), U j).map f := by
    rw [Subgroup.map_iSup]
    congr 1
    funext j
    rw [Subgroup.map_iSup]
  rw [heq]
  exact h

/-- The image of a decomposition of `K` into independent normal subgroups, under an
injective homomorphism `f`, is a decomposition of `f(K)` into independent subgroups that
are normal in `f(K)`, each isomorphic to its preimage. -/
theorem map_decomp {ι : Type*} {U : ι → Subgroup K} (f : K →* L) (hf : Function.Injective f)
    (hind : iSupIndep U) (hsup : ⨆ i, U i = ⊤) (hnorm : ∀ i, (U i).Normal) :
    iSupIndep (fun i => (U i).map f) ∧ ⨆ i, (U i).map f = f.range ∧
      (∀ i, (U i).map f ≤ f.range) ∧
      (∀ i, ∀ g ∈ f.range, ∀ x ∈ (U i).map f, g * x * g⁻¹ ∈ (U i).map f) ∧
      ∀ i, Nonempty (U i ≃* (U i).map f) := by
  refine ⟨iSupIndep_map_of_injective f hf hind, ?_, fun i => Subgroup.map_le_range _ _, ?_,
    fun i => ⟨(U i).equivMapOfInjective f hf⟩⟩
  · rw [← Subgroup.map_iSup, hsup, MonoidHom.range_eq_map]
  · rintro i g ⟨k, rfl⟩ x hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hx
    refine Subgroup.mem_map.2 ⟨k * u * k⁻¹, (hnorm i).conj_mem u hu k, ?_⟩
    simp

end Transport

/-! ### A minimal normal subgroup is a product of isomorphic simple groups -/

section MinNormal

variable {H : Type*} [Group H]

/-- **[DiM, Thm. 4.3A (ii)]**, the case used for Fact 10.2.2 (ii): a minimal normal
subgroup `M` of a finite group `H` is the direct product of isomorphic simple subgroups.
Here the factors are subgroups of `M` itself (as a group). -/
theorem exists_simple_decomp_of_isMinimalNormal [Finite H] {M : Subgroup H}
    (hM : IsMinimalNormal M) :
    ∃ (a : ℕ) (U : Fin a → Subgroup M), iSupIndep U ∧ ⨆ i, U i = ⊤ ∧
      (∀ i, (U i).Normal) ∧ (∀ i, IsSimpleGroup (U i)) ∧ ∀ i j, Nonempty (U i ≃* U j) := by
  haveI : M.Normal := hM.1
  haveI : Nontrivial M := (Subgroup.nontrivial_iff_ne_bot M).2 hM.2.1
  refine exists_simple_decomp_of_gammaSimple (MulAut.conjNormal (H := M)).range ?_
  intro K hK hinv
  -- the image of `K` in `H` is normal in `H`
  have hKn : (K.map M.subtype).Normal := by
    constructor
    intro x hx g
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hx
    have hmem : MulAut.conjNormal g k ∈ K :=
      hinv _ ⟨g, rfl⟩ (Subgroup.mem_map.2 ⟨k, hk, rfl⟩)
    refine Subgroup.mem_map.2 ⟨_, hmem, ?_⟩
    simp [MulAut.conjNormal_apply]
  by_cases hbot : K.map M.subtype = ⊥
  · left
    exact (Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective).1 hbot
  · right
    have hle : K.map M.subtype ≤ M :=
      (Subgroup.map_le_range _ _).trans_eq M.range_subtype
    have heq := hM.2.2 _ hKn hbot hle
    apply Subgroup.map_injective M.subtype_injective
    rw [heq, ← MonoidHom.range_eq_map, M.range_subtype]

end MinNormal

/-! ### [DiM, Thm. 4.3B]: minimal normal subgroups of a primitive group -/

section Primitive

variable {Ω : Type*} [Finite Ω] {G : Subgroup (Equiv.Perm Ω)}

/-- Two distinct minimal normal subgroups meet trivially. -/
theorem disjoint_of_isMinimalNormal {H : Type*} [Group H] {M₁ M₂ : Subgroup H}
    (h₁ : IsMinimalNormal M₁) (h₂ : IsMinimalNormal M₂) (hne : M₁ ≠ M₂) : Disjoint M₁ M₂ := by
  haveI := h₁.1
  haveI := h₂.1
  rw [disjoint_iff]
  by_contra hbot
  have h1 := h₁.2.2 _ inferInstance hbot inf_le_left
  have h2 := h₂.2.2 _ inferInstance hbot inf_le_right
  exact hne (h1.symm.trans h2)

omit [Finite Ω] in
/-- A transitive subgroup has order at least `n`. -/
theorem card_le_of_isPretransitive {M : Subgroup ↥G} [Finite M] (hM : IsPretransitive ↥M Ω)
    (x : Ω) : Nat.card Ω ≤ Nat.card M := by
  refine Nat.card_le_card_of_surjective (fun m : ↥M => m • x) ?_
  intro y
  exact hM.exists_smul_eq x y

/-- **[DiM, Thm. 4.3B]**: if a primitive group has two distinct minimal normal subgroups
`M₁ ≠ M₂`, then `M₂` is the centralizer of `M₁`. -/
theorem eq_centralizer_of_isMinimalNormal (hG : IsPrimitive G) {M₁ M₂ : Subgroup ↥G}
    (h₁ : IsMinimalNormal M₁) (h₂ : IsMinimalNormal M₂) (hne : M₁ ≠ M₂) :
    M₂ = Subgroup.centralizer (M₁ : Set ↥G) := by
  haveI := h₁.1
  haveI := h₂.1
  have hd := disjoint_of_isMinimalNormal h₁ h₂ hne
  have hle : M₂ ≤ Subgroup.centralizer (M₁ : Set ↥G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (commute_of_disjoint_normal hd hx hy).eq
  have ht₁ := isPretransitive_of_normal_of_isPrimitive hG M₁ h₁.2.1
  have ht₂ := isPretransitive_of_normal_of_isPrimitive hG M₂ h₂.2.1
  obtain ⟨x⟩ := hG.nonempty_dom
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  exact (card_centralizer_le ht₁ x).trans (card_le_of_isPretransitive ht₂ x)

/-- **[DiM, Thm. 4.3B]**: a primitive group has at most two minimal normal subgroups. -/
theorem isMinimalNormal_eq_of_three (hG : IsPrimitive G) {M₁ M₂ M₃ : Subgroup ↥G}
    (h₁ : IsMinimalNormal M₁) (h₂ : IsMinimalNormal M₂) (h₃ : IsMinimalNormal M₃)
    (h₁₂ : M₁ ≠ M₂) (h₁₃ : M₁ ≠ M₃) : M₂ = M₃ :=
  (eq_centralizer_of_isMinimalNormal hG h₁ h₂ h₁₂).trans
    (eq_centralizer_of_isMinimalNormal hG h₁ h₃ h₁₃).symm

/-- **[DiM, Thm. 4.3B]**: if a primitive group has two distinct minimal normal subgroups,
they are isomorphic.  Both are regular and centralize each other; fixing a point `α`, the
map sending `m ∈ M₁` to the unique `m' ∈ M₂` with `m' α = m⁻¹ α` is an isomorphism. -/
theorem nonempty_mulEquiv_of_two_minimalNormal (hG : IsPrimitive G) {M₁ M₂ : Subgroup ↥G}
    (h₁ : IsMinimalNormal M₁) (h₂ : IsMinimalNormal M₂) (hne : M₁ ≠ M₂) :
    Nonempty (M₁ ≃* M₂) := by
  classical
  haveI := h₁.1
  haveI := h₂.1
  have hd := disjoint_of_isMinimalNormal h₁ h₂ hne
  have ht₁ := isPretransitive_of_normal_of_isPrimitive hG M₁ h₁.2.1
  have ht₂ := isPretransitive_of_normal_of_isPrimitive hG M₂ h₂.2.1
  obtain ⟨α⟩ := hG.nonempty_dom
  -- elements of `M₂` are determined by the image of `α`
  have huniq₂ : ∀ a b : ↥M₂, (a : Equiv.Perm Ω) α = (b : Equiv.Perm Ω) α → a = b := by
    intro a b hab
    have hc : ∀ m ∈ M₁, ((b⁻¹ * a : ↥M₂) : ↥G) * m = m * ((b⁻¹ * a : ↥M₂) : ↥G) := fun m hm =>
      (commute_of_disjoint_normal hd hm (b⁻¹ * a).2).eq.symm
    have hfix : (((b⁻¹ * a : ↥M₂) : ↥G) : Equiv.Perm Ω) α = α := by
      simp [hab]
    have h1 := eq_one_of_centralizes_of_fixed ht₁ hc hfix
    have h2 : b⁻¹ * a = 1 := Subtype.ext h1
    rw [inv_mul_eq_one] at h2
    exact h2.symm
  have huniq₁ : ∀ a b : ↥M₁, (a : Equiv.Perm Ω) α = (b : Equiv.Perm Ω) α → a = b := by
    intro a b hab
    have hc : ∀ m ∈ M₂, ((b⁻¹ * a : ↥M₁) : ↥G) * m = m * ((b⁻¹ * a : ↥M₁) : ↥G) := fun m hm =>
      (commute_of_disjoint_normal hd (b⁻¹ * a).2 hm).eq
    have hfix : (((b⁻¹ * a : ↥M₁) : ↥G) : Equiv.Perm Ω) α = α := by
      simp [hab]
    have h1 := eq_one_of_centralizes_of_fixed ht₂ hc hfix
    have h2 : b⁻¹ * a = 1 := Subtype.ext h1
    rw [inv_mul_eq_one] at h2
    exact h2.symm
  have hex : ∀ m : ↥M₁, ∃ m' : ↥M₂,
      (m' : Equiv.Perm Ω) α = ((m⁻¹ : ↥M₁) : Equiv.Perm Ω) α := fun m =>
    ht₂.exists_smul_eq α _
  choose φ hφ using hex
  have hmul : ∀ m n : ↥M₁, φ (m * n) = φ m * φ n := by
    intro m n
    apply huniq₂
    rw [hφ]
    have hcomm : ((φ m : ↥G) : Equiv.Perm Ω) * ((n⁻¹ : ↥M₁) : Equiv.Perm Ω) =
        ((n⁻¹ : ↥M₁) : Equiv.Perm Ω) * ((φ m : ↥G) : Equiv.Perm Ω) := by
      have := (commute_of_disjoint_normal hd (n⁻¹).2 (φ m).2).eq
      exact (congrArg Subtype.val this).symm
    have e1 : ((φ m * φ n : ↥M₂) : Equiv.Perm Ω) α =
        ((φ m : ↥G) : Equiv.Perm Ω) (((φ n : ↥G) : Equiv.Perm Ω) α) := rfl
    rw [e1, hφ n]
    have e2 : ((φ m : ↥G) : Equiv.Perm Ω) (((n⁻¹ : ↥M₁) : Equiv.Perm Ω) α) =
        (((φ m : ↥G) : Equiv.Perm Ω) * ((n⁻¹ : ↥M₁) : Equiv.Perm Ω)) α := rfl
    rw [e2, hcomm, Equiv.Perm.mul_apply, hφ m]
    simp only [mul_inv_rev, Subgroup.coe_mul, Equiv.Perm.mul_apply]
  have hinj : Function.Injective φ := by
    intro m n h
    have : ((m⁻¹ : ↥M₁) : Equiv.Perm Ω) α = ((n⁻¹ : ↥M₁) : Equiv.Perm Ω) α := by
      rw [← hφ, ← hφ, h]
    exact inv_injective (huniq₁ _ _ this)
  have hsurj : Function.Surjective φ := by
    intro m'
    obtain ⟨m, hm⟩ := ht₁.exists_smul_eq α ((m' : ↥G) • α)
    refine ⟨m⁻¹, huniq₂ _ _ ?_⟩
    rw [hφ, inv_inv]
    exact hm
  exact ⟨MulEquiv.ofBijective (MulHom.mk φ hmul) ⟨hinj, hsurj⟩⟩

end Primitive

/-! ### Fact 10.2.2 (ii) -/

/-- **Fact 10.2.2 (ii)**, §10.2: "The socle of a primitive permutation group is a direct
product of isomorphic simple groups."

Formerly an axiom citing `[Sco]`, `[AsS]`, `[DiM, Thm. 4.3B]`; the statement is unchanged.
The proof follows Dixon–Mortimer, *Permutation Groups*, GTM 163: by [DiM, Thm. 4.3B] a
primitive group has one minimal normal subgroup `M₁`, or two, `M₁ ≅ M₂`; the socle is `M₁`
or `M₁ × M₂`; and by [DiM, Thm. 4.3A (ii)] `M₁` is a direct product of isomorphic simple
groups. -/
theorem fact_10_2_2_ii {Ω : Type u} [Finite Ω] (G : Subgroup (Equiv.Perm Ω))
    (hG : IsPrimitive G) :
    ∃ (s : ℕ) (R : Fin s → Subgroup G),
      IsInternalDirectProduct (socle G) R ∧ (∀ i, IsSimpleGroup (R i)) ∧
        ∀ i j, Nonempty (R i ≃* R j) := by
  classical
  haveI : Nontrivial G := Finite.one_lt_card_iff_nontrivial.1 (by have := hG.1; omega)
  obtain ⟨M₁, h₁, -⟩ := exists_isMinimalNormal_le (C := (⊤ : Subgroup G))
    (fun _ _ _ => trivial) top_ne_bot
  haveI := h₁.1
  obtain ⟨a, U, hind, hsup, hnorm, hsimp, hiso⟩ := exists_simple_decomp_of_isMinimalNormal h₁
  obtain ⟨hAind, hAsup, hAle, hAnorm, hAiso⟩ :=
    map_decomp M₁.subtype M₁.subtype_injective hind hsup hnorm
  rw [M₁.range_subtype] at hAsup hAle hAnorm
  set A : Fin a → Subgroup G := fun i => (U i).map M₁.subtype with hA
  have hAsimp : ∀ i, IsSimpleGroup (A i) := fun i =>
    haveI := hsimp i
    (hAiso i).some.symm.isSimpleGroup
  by_cases h2 : ∃ M₂ : Subgroup G, IsMinimalNormal M₂ ∧ M₂ ≠ M₁
  · obtain ⟨M₂, h₂, hne⟩ := h2
    haveI := h₂.1
    obtain ⟨ψ⟩ := nonempty_mulEquiv_of_two_minimalNormal hG h₁ h₂ hne.symm
    set f₂ : M₁ →* G := M₂.subtype.comp ψ.toMonoidHom with hf₂
    have hf₂inj : Function.Injective f₂ := M₂.subtype_injective.comp ψ.injective
    have hf₂range : f₂.range = M₂ := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact (ψ y).2
      · intro hx
        exact ⟨ψ.symm ⟨x, hx⟩, by simp [hf₂]⟩
    obtain ⟨hBind, hBsup, hBle, hBnorm, hBiso⟩ := map_decomp f₂ hf₂inj hind hsup hnorm
    rw [hf₂range] at hBsup hBle hBnorm
    set B : Fin a → Subgroup G := fun i => (U i).map f₂ with hB
    have hBsimp : ∀ i, IsSimpleGroup (B i) := fun i =>
      haveI := hsimp i
      (hBiso i).some.symm.isSimpleGroup
    have hd := disjoint_of_isMinimalNormal h₁ h₂ hne.symm
    -- the socle is `M₁ ⊔ M₂`
    have hset : {N : Subgroup G | IsMinimalNormal N} = {M₁, M₂} := by
      ext N
      simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro hN
        by_cases hN1 : N = M₁
        · exact Or.inl hN1
        · exact Or.inr (isMinimalNormal_eq_of_three hG h₁ hN h₂ (Ne.symm hN1) hne.symm)
      · rintro (rfl | rfl)
        · exact h₁
        · exact h₂
    have hsoc : socle G = M₁ ⊔ M₂ := by rw [socle, hset, sSup_pair]
    set e := (finSumFinEquiv (m := a) (n := a)).symm with he
    refine ⟨a + a, fun k => Sum.elim A B (e k), ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · intro k
      rw [hsoc]
      rcases e k with i | i
      · exact (hAle i).trans le_sup_left
      · exact (hBle i).trans le_sup_right
    · intro k g hg x hx
      rw [hsoc, ← SetLike.mem_coe, Subgroup.mul_normal M₁ M₂] at hg
      obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := hg
      revert hx
      rcases e k with i | i
      · intro hx
        have hxM : x ∈ M₁ := hAle i hx
        have hc : Commute m₂ x := commute_of_disjoint_normal hd.symm hm₂ hxM
        have : m₁ * m₂ * x * (m₁ * m₂)⁻¹ = m₁ * x * m₁⁻¹ := by
          rw [mul_inv_rev, show m₁ * m₂ * x * (m₂⁻¹ * m₁⁻¹) = m₁ * (m₂ * x * m₂⁻¹) * m₁⁻¹ by
            group, hc.eq, mul_inv_cancel_right]
        rw [this]
        exact hAnorm i m₁ hm₁ x hx
      · intro hx
        have hy := hBnorm i m₂ hm₂ x hx
        have hc : Commute m₁ (m₂ * x * m₂⁻¹) := commute_of_disjoint_normal hd hm₁ (hBle i hy)
        have : m₁ * m₂ * x * (m₁ * m₂)⁻¹ = m₂ * x * m₂⁻¹ := by
          rw [mul_inv_rev, show m₁ * m₂ * x * (m₂⁻¹ * m₁⁻¹) = m₁ * (m₂ * x * m₂⁻¹) * m₁⁻¹ by
            group, hc.eq, mul_inv_cancel_right]
        rw [this]
        exact hy
    · exact (iSupIndep_sum_elim hAind hBind hAle hBle hd).comp e.injective
    · rw [hsoc, e.iSup_comp (g := Sum.elim A B), iSup_sum]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [hAsup, hBsup]
    · intro k
      show IsSimpleGroup ↥(Sum.elim A B (e k))
      rcases e k with i | i
      · exact hAsimp i
      · exact hBsimp i
    · have key : ∀ k, ∃ i, Nonempty (U i ≃* ↥(Sum.elim A B (e k) : Subgroup G)) := by
        intro k
        rcases e k with i | i
        · exact ⟨i, hAiso i⟩
        · exact ⟨i, hBiso i⟩
      intro k l
      obtain ⟨i, ⟨fi⟩⟩ := key k
      obtain ⟨j, ⟨fj⟩⟩ := key l
      obtain ⟨g⟩ := hiso i j
      exact ⟨fi.symm.trans (g.trans fj)⟩
  · push Not at h2
    have hset : {N : Subgroup G | IsMinimalNormal N} = {M₁} := by
      ext N
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      exact ⟨h2 N, fun h => h ▸ h₁⟩
    have hsoc : socle G = M₁ := by rw [socle, hset, sSup_singleton]
    refine ⟨a, A, ⟨?_, ?_, hAind, ?_⟩, hAsimp, ?_⟩
    · intro i
      rw [hsoc]
      exact hAle i
    · intro i g hg x hx
      rw [hsoc] at hg
      exact hAnorm i g hg x hx
    · rw [hsoc]
      exact hAsup
    · intro i j
      obtain ⟨fi⟩ := hAiso i
      obtain ⟨fj⟩ := hAiso j
      obtain ⟨g⟩ := hiso i j
      exact ⟨fi.symm.trans (g.trans fj)⟩

end Babai
