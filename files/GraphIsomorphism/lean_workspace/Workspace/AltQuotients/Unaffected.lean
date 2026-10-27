/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 10.3 (Alternating quotients versus stabilizers: the Unaffected Stabilizers Lemma).
-/
import Workspace.AltQuotients.PrimitiveQuotient
import Workspace.AltQuotients.SmallIndex
import Workspace.Prelim.BlockActionPrimitive

/-!
# §10.3 Alternating quotients versus stabilizers

Lemma 10.3.1, Lemma 10.3.3, Definition 10.3.4, Theorem 10.3.5 (Unaffected Stabilizers
Lemma), Proposition 10.3.6 and Corollary 10.3.7 (Affected Orbit Lemma).
-/

universe u

namespace Babai

open MulAction Equiv Equiv.Perm

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-! ### The restriction of `G` to an invariant subset -/

section Restrict

variable {G : Subgroup (Equiv.Perm Ω)} {Δ : Set Ω} (hΔ : IsInvariant G Δ)

/-- The restriction `G → G^Δ`, as an epimorphism. -/
def restrictOnto : G →* restrictTo G Δ hΔ := (restrictHom G Δ hΔ).rangeRestrict

theorem restrictOnto_surjective : Function.Surjective (restrictOnto hΔ) :=
  MonoidHom.rangeRestrict_surjective _

theorem restrictOnto_smul (g : G) (x : ↥Δ) :
    ((restrictOnto hΔ g • x : ↥Δ) : Ω) = (g : Equiv.Perm Ω) (x : Ω) := rfl

/-- The kernel of the restriction `G → G^Δ` is the pointwise stabilizer `G_(Δ)`. -/
theorem ker_restrictOnto : (restrictOnto hΔ).ker = pointwiseStab G Δ := by
  ext g
  rw [MonoidHom.mem_ker, mem_pointwiseStab]
  constructor
  · intro h x hx
    have h1 : restrictHom G Δ hΔ g = 1 := Subtype.ext_iff.1 h
    have := congrArg (fun p : Equiv.Perm ↥Δ => ((p ⟨x, hx⟩ : ↥Δ) : Ω)) h1
    simpa [restrictHom] using this
  · intro h
    refine Subtype.ext (Equiv.ext fun x => Subtype.ext ?_)
    exact h (x : Ω) x.2

/-- The stabilizer of `x ∈ Δ` in `G^Δ` pulls back to the stabilizer of `x` in `G`. -/
theorem comap_stabilizer_restrictOnto (x : ↥Δ) :
    (stabilizer (restrictTo G Δ hΔ) x).comap (restrictOnto hΔ) = stabilizer G ((x : Ω)) := by
  ext g
  rw [Subgroup.mem_comap, mem_stabilizer_iff, mem_stabilizer_iff]
  constructor
  · intro h
    have h2 := Subtype.ext_iff.1 h
    rwa [restrictOnto_smul] at h2
  · intro h
    exact Subtype.ext (by rw [restrictOnto_smul]; exact h)

/-- If `ϕ` factors across the restriction as `ψ`, then the two groups attach the same image
to the stabilizer of a point of `Δ`. -/
theorem map_stabilizer_of_restrict_factor {k : ℕ} {ϕ : G →* Equiv.Perm (Fin k)}
    {ψ : restrictTo G Δ hΔ →* Equiv.Perm (Fin k)} (hψ : ψ.comp (restrictOnto hΔ) = ϕ)
    (x : ↥Δ) :
    (stabilizer (restrictTo G Δ hΔ) x).map ψ = (stabilizer G ((x : Ω))).map ϕ := by
  conv_rhs => rw [← comap_stabilizer_restrictOnto hΔ x, ← hψ, ← Subgroup.map_map,
    Subgroup.map_comap_eq_self_of_surjective (restrictOnto_surjective hΔ)]

/-- The orbits of `G^Δ` are orbits of `G`, so `n₀(G^Δ) ≤ n₀(G)`. -/
theorem maxOrbitLength_restrictTo_le [Fintype ↥Δ] :
    maxOrbitLength (restrictTo G Δ hΔ) ≤ maxOrbitLength G := by
  refine maxOrbitLength_le fun x => ?_
  have hmap : ∀ y : ↥(orbit (restrictTo G Δ hΔ) x), ((y : ↥Δ) : Ω) ∈ orbit G ((x : ↥Δ) : Ω) := by
    rintro ⟨y, hy⟩
    obtain ⟨p, hp⟩ := mem_orbit_iff.1 hy
    obtain ⟨g, rfl⟩ := restrictOnto_surjective hΔ p
    refine mem_orbit_iff.2 ⟨g, ?_⟩
    have := restrictOnto_smul hΔ g x
    rw [hp] at this
    exact this.symm
  have hinj : Function.Injective
      (fun y : ↥(orbit (restrictTo G Δ hΔ) x) =>
        (⟨((y : ↥Δ) : Ω), hmap y⟩ : ↥(orbit G ((x : ↥Δ) : Ω)))) := by
    intro a b hab
    exact Subtype.ext (Subtype.ext (by simpa using hab))
  exact le_trans (Nat.card_le_card_of_injective _ hinj) (card_orbit_le_maxOrbitLength G _)

/-- `G^Δ` is transitive when `Δ` is a `G`-orbit. -/
theorem isTransitive_restrictTo_orbit {z : Ω} (hΔ : IsInvariant G (orbit G z)) :
    IsTransitive (restrictTo G (orbit G z) hΔ) := by
  refine (isTransitiveAction_iff _ _).2 ⟨⟨⟨z, mem_orbit_self z⟩⟩, ⟨fun x y => ?_⟩⟩
  have hx : orbit G ((x : ↥(orbit G z)) : Ω) = orbit G z := orbit_eq_iff.2 x.2
  have hy : ((y : ↥(orbit G z)) : Ω) ∈ orbit G ((x : ↥(orbit G z)) : Ω) := by rw [hx]; exact y.2
  obtain ⟨g, hg⟩ := mem_orbit_iff.1 hy
  exact ⟨restrictOnto hΔ g, Subtype.ext (by rw [restrictOnto_smul]; exact hg)⟩

end Restrict

/-! ### Lemma 10.3.1 and Lemma 10.3.3 -/

/-- **Lemma 10.3.1**, §10.3, as an induction on `|G|` over all domains at once.

The paper's proof is an induction on `|G|`, and the inductive step passes from `G ≤ S(Ω)`
to the restriction of a normal subgroup of `G` to one of *its* orbits, so the domain
shrinks as well; the statement is therefore quantified over the domain too. -/
theorem lemma_10_3_1_forall :
    ∀ (Nb : ℕ) (Ω : Type u) (_ : Fintype Ω) (_ : DecidableEq Ω)
      (G : Subgroup (Equiv.Perm Ω)), Nat.card ↥G ≤ Nb → IsTransitive G →
      ∀ (k : ℕ) (ϕ : ↥G →* Equiv.Perm (Fin k)), ϕ.range = alternatingGroup (Fin k) →
        LargeK k (Nat.card Ω) → ∀ x : Ω,
          (stabilizer ↥G x).map ϕ ≠ alternatingGroup (Fin k) := by
  intro Nb
  induction Nb using Nat.strong_induction_on with
  | _ Nb ih =>
  intro Ω instF instD G hGcard hG k ϕ hϕ hk x hcon
  haveI := instF
  haveI := instD
  classical
  have hk8 := hk.eight_lt
  have hn := hk.lt_two_pow
  have h5 : 5 ≤ Fintype.card (Fin k) := by simp only [Fintype.card_fin]; omega
  haveI : IsSimpleGroup (alternatingGroup (Fin k)) := isSimpleGroup_alternatingGroup h5
  haveI : Nontrivial (Fin k) := ⟨⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff]⟩⟩
  have hpk : Nat.card (Equiv.Perm (Fin k)) = Nat.factorial k := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  have halt : 2 * Nat.card (alternatingGroup (Fin k)) = Nat.card (Equiv.Perm (Fin k)) :=
    two_mul_nat_card_alternatingGroup
  rw [hpk] at halt
  have hfac : 2 ^ k ≤ Nat.factorial k := two_pow_le_factorial (by omega)
  have hsplit : (2 : ℕ) ^ k = 4 * 2 ^ (k - 2) := by
    conv_lhs => rw [show k = 2 + (k - 2) by omega]
    rw [pow_add]
    norm_num
  -- `G` is transitive, so the image of *every* point stabilizer is `A_k`
  haveI : Nonempty Ω := ⟨x⟩
  have horbu : ∀ z : Ω, orbit ↥G z = Set.univ := (isTransitive_iff_orbit_eq_univ G).1 hG
  have hstabany : ∀ z : Ω, (stabilizer ↥G z).map ϕ = alternatingGroup (Fin k) := by
    intro z
    have hz : z ∈ orbit ↥G x := by rw [horbu x]; trivial
    obtain ⟨σ, rfl⟩ := mem_orbit_iff.1 hz
    rw [stabilizer_smul_eq_stabilizer_map_conj, map_map_conj, hcon,
      map_conj_alternatingGroup]
  -- `|Ω| ≥ 2`, since otherwise `G = 1` could not have `A_k` as a quotient
  have h2Ω : 2 ≤ Fintype.card Ω := by
    by_contra hcard
    push_neg at hcard
    haveI : Subsingleton Ω := Fintype.card_le_one_iff_subsingleton.1 (by omega)
    have hGsub : ∀ g : ↥G, g = 1 := fun g =>
      Subtype.ext (Equiv.ext fun y => Subsingleton.elim _ _)
    have hbot : ϕ.range = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨g, rfl⟩
      rw [Subgroup.mem_bot, hGsub g, map_one]
    rw [hϕ] at hbot
    have h1 : Nat.card ↥(alternatingGroup (Fin k)) = 1 := by rw [hbot]; simp
    omega
  -- a maximal block `B ∋ x` and the system `Ω'` of its `G`-images
  obtain ⟨ℬ, B, hℬ, hBmem, hxB, hBne⟩ :=
    exists_minimalSystemOfImprimitivity_mem hG h2Ω x
  haveI : Fintype ↥ℬ := Fintype.ofFinite _
  haveI : DecidableEq ↥ℬ := Classical.decEq _
  have hKmem : ∀ t : ↥G, t ∈ (blockHom G ℬ hℬ.permutes).ker ↔
      ∀ C ∈ ℬ, (t : Equiv.Perm Ω) '' C = C := fun _ => mem_ker_blockHom
  set K : Subgroup ↥G := (blockHom G ℬ hℬ.permutes).ker with hKdef
  haveI hKnorm : K.Normal := by rw [hKdef]; infer_instance
  -- "`N` is a maximal normal subgroup of `G`, so `K ≤ N` or `K N = G`"
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((K.map ϕ).subgroupOf (alternatingGroup (Fin k)))
      (normal_subgroupOf_of_map hϕ hKnorm) with hbot | htop
  · -- `K ≤ ker ϕ`: `ϕ` factors through the *primitive* group `G^Ω'`, so by Lemma 10.2.5
    -- `ker ϕ = K`, whence `G_B = G` and `Ω'` has only one block
    have hle : K.map ϕ ≤ alternatingGroup (Fin k) := by
      rw [← hϕ]; rintro _ ⟨t, -, rfl⟩; exact ⟨t, rfl⟩
    have hmapbot : K.map ϕ = ⊥ := by
      rw [Subgroup.subgroupOf_eq_bot] at hbot
      rw [eq_bot_iff, ← inf_eq_left.2 hle]
      exact hbot.le_bot
    have hKker : K ≤ ϕ.ker := (Subgroup.map_eq_bot_iff _).1 hmapbot
    have hsurj : Function.Surjective (blockHom G ℬ hℬ.permutes).rangeRestrict :=
      MonoidHom.rangeRestrict_surjective _
    have hkerle : (blockHom G ℬ hℬ.permutes).rangeRestrict.ker ≤ ϕ.ker := by
      rw [MonoidHom.ker_rangeRestrict]; exact hKker
    obtain ⟨ψ, hψ⟩ := exists_factor_of_ker_le hsurj ϕ hkerle
    have hcomp : ∀ g : ↥G, ψ ((blockHom G ℬ hℬ.permutes).rangeRestrict g) = ϕ g :=
      fun g => DFunLike.congr_fun hψ g
    have hψr : ψ.range = alternatingGroup (Fin k) := by
      rw [range_of_factor hsurj hψ, hϕ]
    -- `|Ω'| ≤ |Ω|`: the blocks are nonempty and pairwise disjoint
    have hcardB : Nat.card ↥ℬ ≤ Nat.card Ω := by
      have hne : ∀ C : ↥ℬ, ((C : Set Ω)).Nonempty := fun C => hℬ.nonempty _ C.2
      refine Nat.card_le_card_of_injective (fun C : ↥ℬ => (hne C).choose) ?_
      intro C D hCD
      refine Subtype.ext ?_
      by_contra hne2
      have hdisj := hℬ.pairwiseDisjoint _ C.2 _ D.2 hne2
      have h1 : (hne C).choose ∈ (C : Set Ω) := (hne C).choose_spec
      have hCD' : (hne C).choose = (hne D).choose := hCD
      have h2 : (hne C).choose ∈ (D : Set Ω) := by rw [hCD']; exact (hne D).choose_spec
      exact Set.disjoint_left.1 hdisj h1 h2
    have hinj := lemma_10_2_5 (isPrimitive_onBlocks hℬ) ψ hψr (hk.mono hcardB)
    have hkereq : ϕ.ker = K := by
      refine le_antisymm (fun g hg => ?_) hKker
      rw [MonoidHom.mem_ker] at hg
      have h1 : ψ ((blockHom G ℬ hℬ.permutes).rangeRestrict g) = ψ 1 := by
        rw [hcomp, hg, map_one]
      have h2 : g ∈ (blockHom G ℬ hℬ.permutes).rangeRestrict.ker :=
        MonoidHom.mem_ker.2 (hinj h1)
      rwa [MonoidHom.ker_rangeRestrict] at h2
    -- `G_x ≤ G_B`, so `G_B^ϕ = A_k`, and `ker ϕ = K ≤ G_B` gives `G_B = G`
    have hstabB : stabilizer ↥G x ≤ setwiseStab G B := by
      intro g hg
      rw [mem_setwiseStab]
      have hgx : (g : Equiv.Perm Ω) x = x := hg
      rcases eq_or_ne ((g : Equiv.Perm Ω) '' B) B with h | h
      · exact h
      · exfalso
        have hmem := hℬ.permutes _ g.2 _ hBmem
        exact Set.disjoint_left.1 (hℬ.pairwiseDisjoint _ hmem _ hBmem h) ⟨x, hxB, hgx⟩ hxB
    have hSA : (setwiseStab G B).map ϕ = alternatingGroup (Fin k) := by
      refine le_antisymm ?_ ?_
      · rw [← hϕ]; rintro _ ⟨t, -, rfl⟩; exact ⟨t, rfl⟩
      · rw [← hcon]; exact Subgroup.map_mono hstabB
    have hKsub : K ≤ setwiseStab G B := by
      intro t ht
      rw [mem_setwiseStab]
      exact (hKmem t).1 ht B hBmem
    have hStop : setwiseStab G B = ⊤ := by
      refine (Subgroup.eq_top_iff' _).2 fun g => ?_
      have hmem : ϕ g ∈ (setwiseStab G B).map ϕ := by rw [hSA, ← hϕ]; exact ⟨g, rfl⟩
      obtain ⟨h, hh, hhg⟩ := hmem
      have hmul : g * h⁻¹ ∈ ϕ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hhg, mul_inv_cancel]
      rw [hkereq] at hmul
      have := (setwiseStab G B).mul_mem (hKsub hmul) hh
      simpa using this
    -- every block equals `B`, contradicting `|Ω'| ≥ 2`
    obtain ⟨B₁, hB₁, B₂, hB₂, hne12⟩ := (Set.one_lt_ncard (Set.toFinite _)).1 hℬ.two_blocks
    have hfix : ∀ C ∈ ℬ, C = B := by
      intro C hC
      obtain ⟨σ, hσ, hσB⟩ := hℬ.transitiveOnBlocks B hBmem C hC
      have hmem : (⟨σ, hσ⟩ : ↥G) ∈ setwiseStab G B := by rw [hStop]; trivial
      rw [mem_setwiseStab] at hmem
      exact (hmem.symm.trans hσB).symm
    exact hne12 ((hfix B₁ hB₁).trans (hfix B₂ hB₂).symm)
  · -- `K N = G`, i.e. `K^ϕ = A_k`.  Lemma 10.1.1 makes `ϕ|_K` factor through the
    -- restriction of `K` to one of its orbits, and the induction hypothesis applies there
    rw [Subgroup.subgroupOf_eq_top] at htop
    have hleK : K.map ϕ ≤ alternatingGroup (Fin k) := by
      rw [← hϕ]; rintro _ ⟨t, -, rfl⟩; exact ⟨t, rfl⟩
    have hKmapA : K.map ϕ = alternatingGroup (Fin k) := le_antisymm hleK htop
    set Kp : Subgroup (Equiv.Perm Ω) := K.map G.subtype with hKpdef
    have hKple : Kp ≤ G := by rintro _ ⟨g, -, rfl⟩; exact g.2
    set incl : ↥Kp →* ↥G := Subgroup.inclusion hKple with hincldef
    have hinclcoe : ∀ y : ↥Kp, ((incl y : ↥G) : Equiv.Perm Ω) = (y : Equiv.Perm Ω) :=
      fun _ => rfl
    have hinclmem : ∀ y : ↥Kp, incl y ∈ K := by
      intro y
      obtain ⟨g, hg, hgy⟩ := y.2
      have h1 : incl y = g := Subtype.ext hgy.symm
      rw [h1]; exact hg
    have hinclsurj : ∀ g : ↥G, g ∈ K → ∃ y : ↥Kp, incl y = g :=
      fun g hg => ⟨⟨(g : Equiv.Perm Ω), ⟨g, hg, rfl⟩⟩, rfl⟩
    set ϕK : ↥Kp →* Equiv.Perm (Fin k) := ϕ.comp incl with hϕKdef
    have hϕKapp : ∀ y : ↥Kp, ϕK y = ϕ (incl y) := fun _ => rfl
    have hϕKrange : ϕK.range = alternatingGroup (Fin k) := by
      rw [← hKmapA]
      ext a
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨incl y, hinclmem y, rfl⟩
      · rintro ⟨g, hg, rfl⟩
        obtain ⟨y, hy⟩ := hinclsurj g hg
        exact ⟨y, by rw [hϕKapp, hy]⟩
    -- `K ≠ G`, because `G` moves the blocks
    have hcardle : Nat.card ↥Kp ≤ Nat.card ↥G :=
      Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hKple)
    obtain ⟨B₁, hB₁, B₂, hB₂, hne12⟩ := (Set.one_lt_ncard (Set.toFinite _)).1 hℬ.two_blocks
    have hKlt : Nat.card ↥Kp < Nat.card ↥G := by
      rcases lt_or_eq_of_le hcardle with h | h
      · exact h
      exfalso
      have hKG : Kp = G := eq_of_le_of_card_le hKple h.ge
      obtain ⟨σ, hσ, hσB⟩ := hℬ.transitiveOnBlocks B₁ hB₁ B₂ hB₂
      have hσKp : σ ∈ Kp := by rw [hKG]; exact hσ
      obtain ⟨g, hg, hgσ⟩ := hσKp
      have hgσ' : (g : Equiv.Perm Ω) = σ := hgσ
      have hfix := (hKmem g).1 hg B₁ hB₁
      rw [hgσ'] at hfix
      exact hne12 (hfix.symm.trans hσB)
    -- `K` is a subdirect product of its restrictions to its orbits (Lemma 10.1.1)
    have hinv : ∀ z : Ω, IsInvariant Kp (orbit ↥Kp z) := fun z => isInvariant_orbit Kp z
    have hsub : IsSubdirectProduct (fun z : Ω => restrictOnto (hinv z)) := by
      constructor
      · intro g hg
        refine Subtype.ext (Equiv.ext fun y => ?_)
        have h2 : g ∈ (restrictOnto (hinv y)).ker := hg y
        rw [ker_restrictOnto, mem_pointwiseStab] at h2
        exact h2 y (mem_orbit_self y)
      · exact fun z => restrictOnto_surjective _
    have hmemA : ∀ g : ↥Kp, ϕK g ∈ alternatingGroup (Fin k) := fun g => by
      rw [← hϕKrange]; exact ⟨g, rfl⟩
    set ϕK' : ↥Kp →* alternatingGroup (Fin k) :=
      ϕK.codRestrict (alternatingGroup (Fin k)) hmemA with hϕK'def
    have hϕK'surj : Function.Surjective ϕK' := by
      intro a
      have ha : (a : Equiv.Perm (Fin k)) ∈ ϕK.range := by rw [hϕKrange]; exact a.2
      obtain ⟨g, hg⟩ := ha
      exact ⟨g, Subtype.ext hg⟩
    have hϕK'ker : ϕK'.ker = ϕK.ker := by
      ext g
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
      exact ⟨fun h => Subtype.ext_iff.1 h, fun h => Subtype.ext h⟩
    obtain ⟨z, hz⟩ := lemma_10_1_1 hsub (alternatingGroup_nonabelian h5) hϕK'surj
    rw [hϕK'ker] at hz
    obtain ⟨χ, hχ⟩ := exists_factor_of_ker_le (restrictOnto_surjective (hinv z)) ϕK hz
    haveI : Fintype ↥(orbit ↥Kp z) := Fintype.ofFinite _
    haveI : Nonempty ↥(orbit ↥Kp z) := ⟨⟨z, mem_orbit_self z⟩⟩
    have hχrange : χ.range = alternatingGroup (Fin k) := by
      rw [range_of_factor (restrictOnto_surjective (hinv z)) hχ, hϕKrange]
    -- the induction hypothesis, applied to `K^Δ` where `Δ` is the orbit of `z`
    have hcardres : Nat.card ↥(restrictTo Kp (orbit ↥Kp z) (hinv z)) < Nb := by
      have h1 : Nat.card ↥(restrictTo Kp (orbit ↥Kp z) (hinv z)) ≤ Nat.card ↥Kp :=
        Nat.card_le_card_of_surjective _ (restrictOnto_surjective (hinv z))
      omega
    have hΔcard : Nat.card ↥(orbit ↥Kp z) ≤ Nat.card Ω :=
      Nat.card_le_card_of_injective _ Subtype.val_injective
    have hIH := ih _ hcardres ↥(orbit ↥Kp z) inferInstance (Classical.decEq _)
      (restrictTo Kp (orbit ↥Kp z) (hinv z)) le_rfl
      (isTransitive_restrictTo_orbit (hinv z)) k χ hχrange (hk.mono hΔcard)
      ⟨z, mem_orbit_self z⟩
    rw [map_stabilizer_of_restrict_factor (hinv z) hχ ⟨z, mem_orbit_self z⟩] at hIH
    -- `K_z^ϕ ⊴ G_z^ϕ = A_k`, and it is not `A_k`, so it is trivial
    have hstabnorm :
        (((stabilizer ↥Kp z).map ϕK).subgroupOf (alternatingGroup (Fin k))).Normal := by
      constructor
      intro m hm a
      rw [Subgroup.mem_subgroupOf] at hm ⊢
      obtain ⟨t, ht, htm⟩ := hm
      have htm' : ϕ (incl t) = (m : Equiv.Perm (Fin k)) := htm
      have htz : (t : Equiv.Perm Ω) z = z := ht
      have ha : (a : Equiv.Perm (Fin k)) ∈ (stabilizer ↥G z).map ϕ := by
        rw [hstabany z]; exact a.2
      obtain ⟨g, hgstab, hga⟩ := ha
      have hgz : (g : Equiv.Perm Ω) z = z := hgstab
      have hginv : (g : Equiv.Perm Ω)⁻¹ z = z := by
        conv_lhs => rw [← hgz]
        simp
      have hu : g * incl t * g⁻¹ ∈ K := hKnorm.conj_mem _ (hinclmem t) g
      refine ⟨⟨((g * incl t * g⁻¹ : ↥G) : Equiv.Perm Ω), ⟨_, hu, rfl⟩⟩, ?_, ?_⟩
      · show ((g * incl t * g⁻¹ : ↥G) : Equiv.Perm Ω) z = z
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply]
        rw [hginv, hinclcoe, htz, hgz]
      · show ϕ (g * incl t * g⁻¹) = ((a * m * a⁻¹ : ↥(alternatingGroup (Fin k))) :
          Equiv.Perm (Fin k))
        push_cast
        rw [map_mul, map_mul, map_inv, hga, htm']
    have hle2 : (stabilizer ↥Kp z).map ϕK ≤ alternatingGroup (Fin k) := by
      rw [← hϕKrange]; rintro _ ⟨t, -, rfl⟩; exact ⟨t, rfl⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal _ hstabnorm with hbot2 | htop2
    swap
    · rw [Subgroup.subgroupOf_eq_top] at htop2
      exact hIH (le_antisymm hle2 htop2)
    have hmapbot2 : (stabilizer ↥Kp z).map ϕK = ⊥ := by
      rw [Subgroup.subgroupOf_eq_bot] at hbot2
      rw [eq_bot_iff, ← inf_eq_left.2 hle2]
      exact hbot2.le_bot
    have hstabker : stabilizer ↥Kp z ≤ ϕK.ker := (Subgroup.map_eq_bot_iff _).1 hmapbot2
    -- `|A_k| = |K : ker ϕ_K|` divides `|K : K_z| = |z^K|`
    have hdvd : Nat.card ↥(alternatingGroup (Fin k)) ∣ Nat.card ↥(orbit ↥Kp z) := by
      have h1 : ϕK.ker.index ∣ (stabilizer ↥Kp z).index := Subgroup.index_dvd_of_le hstabker
      rw [Subgroup.index_ker, hϕKrange] at h1
      rwa [card_orbit_eq_index]
    have hAle : Nat.card ↥(alternatingGroup (Fin k)) ≤ Nat.card ↥(orbit ↥Kp z) :=
      Nat.le_of_dvd Nat.card_pos hdvd
    -- but the orbits of `K` lie inside blocks, which are proper subsets of `Ω`
    have hzC : ∃ C ∈ ℬ, z ∈ C := by
      have hmem : z ∈ ⋃₀ ℬ := by rw [hℬ.covers]; trivial
      obtain ⟨C, hC, hzC⟩ := hmem
      exact ⟨C, hC, hzC⟩
    obtain ⟨C, hC, hzC⟩ := hzC
    have horbsub : orbit ↥Kp z ⊆ C := by
      rintro y ⟨g, rfl⟩
      obtain ⟨t, ht, htg⟩ := g.2
      have htg' : (t : Equiv.Perm Ω) = (g : Equiv.Perm Ω) := htg
      have hfix := (hKmem t).1 ht C hC
      rw [htg'] at hfix
      show (g : Equiv.Perm Ω) z ∈ C
      rw [← hfix]
      exact ⟨z, hzC, rfl⟩
    obtain ⟨D, hD, hDC⟩ : ∃ D ∈ ℬ, D ≠ C := by
      by_cases h : B₁ = C
      · exact ⟨B₂, hB₂, fun hh => hne12 (h.trans hh.symm)⟩
      · exact ⟨B₁, hB₁, h⟩
    obtain ⟨y, hy⟩ := hℬ.nonempty D hD
    have hyC : y ∉ C := Set.disjoint_left.1 (hℬ.pairwiseDisjoint _ hD _ hC hDC) hy
    have horblt : Nat.card ↥(orbit ↥Kp z) < Nat.card Ω := by
      have hss : orbit ↥Kp z ⊂ Set.univ :=
        ⟨Set.subset_univ _, fun h => hyC (horbsub (h (Set.mem_univ y)))⟩
      have hlt := Set.ncard_lt_ncard hss (Set.toFinite _)
      rw [Set.ncard_univ] at hlt
      rwa [Nat.card_coe_set_eq]
    omega

/-- **Lemma 10.3.1**, §10.3.

> Let `G ≤ S(Ω)` be a transitive permutation group and `ϕ : G → A_k` an epimorphism where
> `k > max{8, 2 + log₂ n}`.  Then `G_x^ϕ ≠ A_k` for any `x ∈ Ω`.

The paper's proof, an induction on `|G|`: let `B` be a maximal block of imprimitivity
containing `x`, let `Ω'` be the system of its `G`-images (on which `G` acts primitively,
`Babai.isPrimitive_onBlocks`) and `K` the kernel of the action on `Ω'`.  Since `ker ϕ` is
a maximal normal subgroup of `G`, either `K ≤ ker ϕ` or `K^ϕ = A_k`.

In the first case `ϕ` factors through the primitive group `G^{Ω'}`, so Lemma 10.2.5 makes
that factor injective, `ker ϕ = K`; as `G_x ≤ G_B` we get `G_B^ϕ = A_k` and hence
`G = K G_B = G_B`, so `Ω'` has one block, contradicting its definition.

In the second case `K` is a subdirect product of its restrictions to its orbits, so by
Lemma 10.1.1 `ϕ|_K` factors through the restriction `K^Δ` to one orbit `Δ = z^K`, and
`|K| < |G|` lets the induction hypothesis apply to `K^Δ`: `K_z^ϕ ≠ A_k`.  As `K ⊴ G` we
have `K_z ⊴ G_z`, so `K_z^ϕ ⊴ G_z^ϕ = A_k` and therefore `K_z^ϕ = 1`.  Then
`|A_k|` divides `|K : K_z| = |z^K| ≤ |B| < n < 2^{k-2} < |A_k|`, a contradiction. -/
theorem lemma_10_3_1 {G : Subgroup (Equiv.Perm Ω)} (hG : IsTransitive G) {k : ℕ}
    (ϕ : G →* Equiv.Perm (Fin k)) (hϕ : ϕ.range = alternatingGroup (Fin k))
    (hk : LargeK k (Nat.card Ω)) (x : Ω) :
    (stabilizer G x).map ϕ ≠ alternatingGroup (Fin k) :=
  lemma_10_3_1_forall (Nat.card ↥G) Ω inferInstance inferInstance G le_rfl hG k ϕ hϕ hk x

/-- **Lemma 10.3.3**, §10.3, proved. -/
theorem lemma_10_3_3_proof {G : Subgroup (Equiv.Perm Ω)} {k : ℕ}
    (ϕ : G →* Equiv.Perm (Fin k)) (hϕ : ϕ.range = alternatingGroup (Fin k))
    (hk : LargeK k (maxOrbitLength G)) :
    ∃ x : Ω, (stabilizer G x).map ϕ ≠ alternatingGroup (Fin k) := by
  classical
  have hk8 := hk.eight_lt
  have h5 : 5 ≤ Fintype.card (Fin k) := by simp only [Fintype.card_fin]; omega
  haveI : IsSimpleGroup (alternatingGroup (Fin k)) := isSimpleGroup_alternatingGroup h5
  -- `G` is a subdirect product of its restrictions to its orbits
  set hinv : ∀ z : Ω, IsInvariant G (orbit G z) := fun z => isInvariant_orbit G z with hinvdef
  have hsub : IsSubdirectProduct (fun z : Ω => restrictOnto (hinv z)) := by
    constructor
    · intro g hg
      refine Subtype.ext (Equiv.ext fun y => ?_)
      have h2 : g ∈ (restrictOnto (hinv y)).ker := hg y
      rw [ker_restrictOnto, mem_pointwiseStab] at h2
      exact h2 y (mem_orbit_self y)
    · exact fun z => restrictOnto_surjective _
  -- `ϕ` as an epimorphism onto `A_k`
  have hmemA : ∀ g : G, ϕ g ∈ alternatingGroup (Fin k) := fun g => by
    rw [← hϕ]; exact ⟨g, rfl⟩
  set ϕ' : G →* alternatingGroup (Fin k) :=
    ϕ.codRestrict (alternatingGroup (Fin k)) hmemA with hϕ'
  have hϕ'coe : ∀ g : G, ((ϕ' g : alternatingGroup (Fin k)) : Equiv.Perm (Fin k)) = ϕ g :=
    fun g => rfl
  have hϕ'surj : Function.Surjective ϕ' := by
    intro a
    have : (a : Equiv.Perm (Fin k)) ∈ ϕ.range := by rw [hϕ]; exact a.2
    obtain ⟨g, hg⟩ := this
    exact ⟨g, Subtype.ext (by rw [hϕ'coe]; exact hg)⟩
  have hϕ'ker : ϕ'.ker = ϕ.ker := by
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro h
      have h2 : ((ϕ' g : alternatingGroup (Fin k)) : Equiv.Perm (Fin k)) = 1 :=
        Subtype.ext_iff.1 h
      rw [hϕ'coe] at h2
      exact h2
    · intro h
      exact Subtype.ext (by rw [hϕ'coe]; simpa using h)
  obtain ⟨z, hz⟩ := lemma_10_1_1 hsub (alternatingGroup_nonabelian h5) hϕ'surj
  rw [hϕ'ker] at hz
  -- `ϕ` factors across the restriction to the orbit of `z`
  obtain ⟨ψ, hψ⟩ := exists_factor_of_ker_le (restrictOnto_surjective (hinv z)) ϕ hz
  haveI : Fintype ↥(orbit G z) := Fintype.ofFinite _
  have hψrange : ψ.range = alternatingGroup (Fin k) := by
    rw [range_of_factor (restrictOnto_surjective (hinv z)) hψ, hϕ]
  set x : ↥(orbit G z) := ⟨z, mem_orbit_self z⟩ with hxdef
  have hx := lemma_10_3_1 (isTransitive_restrictTo_orbit (hinv z)) ψ hψrange
    (hk.mono (card_orbit_le_maxOrbitLength G z)) x
  exact ⟨(x : Ω), by rwa [← map_stabilizer_of_restrict_factor (hinv z) hψ x]⟩

/-- **Lemma 10.3.3**, §10.3.

> Let `G ≤ S(Ω)` be a permutation group and `ϕ : G → A_k` an epimorphism.  Assume
> `k > max{8, 2 + log₂ n₀}` where `n₀ = n₀(G)` denotes the length of the largest orbit of
> `G`.  Then `G_x^ϕ ≠ A_k` for some `x ∈ Ω`.

The paper's proof: `G` is a subdirect product of its restrictions `Gᵢ` to its orbits, so by
Lemma 10.1.1 `ϕ` factors through some `Gᵢ`, and Lemma 10.3.1 applies to `Gᵢ`. -/
theorem lemma_10_3_3 {G : Subgroup (Equiv.Perm Ω)} {k : ℕ}
    (ϕ : G →* Equiv.Perm (Fin k)) (hϕ : ϕ.range = alternatingGroup (Fin k))
    (hk : LargeK k (maxOrbitLength G)) :
    ∃ x : Ω, (stabilizer G x).map ϕ ≠ alternatingGroup (Fin k) :=
  lemma_10_3_3_proof ϕ hϕ hk

/-- **Remark 10.3.2**, §10.3.

> Again, the assumption `k > 2 + log₂ n` is tight; the Lemma fails infinitely often if
> `k = 2 + log₂ n` is permitted.  This is shown by the same examples as in Remark 10.2.6.

Recorded as a statement only (it asserts that Lemma 10.3.1 fails at the boundary, by the
construction of Remark 10.2.6, which the paper does not use). -/
def Remark_10_3_2_statement : Prop :=
  ∀ k : ℕ, 9 ≤ k → Even k →
    ∃ (Ω : Type) (G : Subgroup (Equiv.Perm Ω)) (ϕ : G →* Equiv.Perm (Fin k)) (x : Ω),
      IsTransitive G ∧ Nat.card Ω = 2 ^ (k - 2) ∧
        ϕ.range = alternatingGroup (Fin k) ∧
          (stabilizer G x).map ϕ = alternatingGroup (Fin k)

/-! ### Theorem 10.3.5 (Unaffected Stabilizers Lemma) -/

/-- The unaffected set is `G`-invariant. -/
theorem isInvariant_unaffectedSet {G : Subgroup (Equiv.Perm Ω)} {k : ℕ}
    (ϕ : G →* Equiv.Perm (Fin k)) : IsInvariant G (unaffectedSet ϕ) := by
  rw [isInvariant_iff_mem]
  intro σ hσ x
  have hkey : ((stabilizer G ((⟨σ, hσ⟩ : G) • x)).map ϕ)
      = ((stabilizer G x).map ϕ).map (MulAut.conj (ϕ ⟨σ, hσ⟩)).toMonoidHom := by
    rw [stabilizer_smul_eq_stabilizer_map_conj, map_map_conj]
  show (¬ Affected ϕ x) ↔ (¬ Affected ϕ (σ x))
  have hsx : σ x = (⟨σ, hσ⟩ : G) • x := rfl
  simp only [Affected, not_not, hsx, hkey, alternating_le_map_conj_iff]

/-- **Theorem 10.3.5**, §10.3, the paper's first case: `G^ϕ = A_k`.

> First assume `G^ϕ = A_k`.  The set `D` is `G`-invariant and `G_(D)` is the kernel of the
> restriction map `G → S(D)`.  Let `P ≤ S(D)` be the image of this map (restriction of `G`
> to `D`), so `P ≅ G/G_(D)`.  Since `G_(D) ⊴ G`, we have `G_(D)^ϕ ⊴ G^ϕ = A_k`.  Assume for
> a contradiction that `G_(D)^ϕ ≠ A_k`; it follows that `|G_(D)^ϕ| = 1`, i.e.
> `G_(D) ≤ ker(ϕ)`.  Hence `ϕ` factors across `P` as `G → P → A_k`.  It follows that
> `P^ψ = G^ϕ = A_k` so `ψ` is an epimorphism.  By Lemma 10.3.3 we have `P_x^ψ ≠ A_k` for
> some `x ∈ D`.  But `P_x^ψ = G_x^ϕ = A_k` (because `x ∈ D` is not affected by `ϕ`), a
> contradiction. -/
theorem theorem_10_3_5_aux {G : Subgroup (Equiv.Perm Ω)} {k : ℕ}
    (ϕ : G →* Equiv.Perm (Fin k)) (hϕ : ϕ.range = alternatingGroup (Fin k))
    (hk : LargeK k (maxOrbitLength G)) :
    alternatingGroup (Fin k) ≤ (pointwiseStab G (unaffectedSet ϕ)).map ϕ := by
  classical
  set D := unaffectedSet ϕ with hDdef
  have hDinv : IsInvariant G D := isInvariant_unaffectedSet ϕ
  haveI hnormal := pointwiseStab_normal hDinv
  set N := (pointwiseStab G D).map ϕ with hNdef
  have hNle : N ≤ alternatingGroup (Fin k) := by
    rw [← hϕ]; rintro _ ⟨t, -, rfl⟩; exact ⟨t, rfl⟩
  -- `G_(D) ⊴ G`, so `G_(D)^ϕ ⊴ G^ϕ = A_k`
  have hNnormal : (N.subgroupOf (alternatingGroup (Fin k))).Normal := by
    constructor
    intro n hn a
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨s, hs, hsn⟩ := hn
    have ha : (a : Equiv.Perm (Fin k)) ∈ ϕ.range := by rw [hϕ]; exact a.2
    obtain ⟨g, hg⟩ := ha
    refine ⟨g * s * g⁻¹, hnormal.conj_mem s hs g, ?_⟩
    push_cast
    rw [map_mul, map_mul, map_inv, hg, hsn]
  haveI : IsSimpleGroup (alternatingGroup (Fin k)) :=
    isSimpleGroup_alternatingGroup (by
      have := hk.eight_lt
      simp only [Fintype.card_fin]; omega)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (N.subgroupOf (alternatingGroup (Fin k))) hNnormal with hbot | htop
  swap
  · rw [Subgroup.subgroupOf_eq_top] at htop; exact htop
  -- `N = 1`, i.e. `G_(D) ≤ ker ϕ`
  exfalso
  have hNbot : N = ⊥ := by
    rw [Subgroup.subgroupOf_eq_bot] at hbot
    rw [eq_bot_iff, ← inf_eq_left.2 hNle]
    exact hbot.le_bot
  have hkerle : pointwiseStab G D ≤ ϕ.ker := (Subgroup.map_eq_bot_iff _).1 hNbot
  -- the restriction `G → S(D)`, with image `P`
  haveI : Fintype ↥D := Fintype.ofFinite _
  set ρ := restrictHom G D hDinv with hρdef
  have hρapply : ∀ (g : G) (x : ↥D), ((ρ g) x : Ω) = (g : Equiv.Perm Ω) (x : Ω) := by
    intro g x; rfl
  have hρker : ρ.ker = pointwiseStab G D := by
    ext g
    rw [MonoidHom.mem_ker, mem_pointwiseStab]
    constructor
    · intro h x hx
      have := congrArg (fun p : Equiv.Perm ↥D => ((p ⟨x, hx⟩ : ↥D) : Ω)) h
      simpa [hρapply] using this
    · intro h
      refine Equiv.ext fun x => Subtype.ext ?_
      rw [hρapply]
      exact h (x : Ω) x.2
  set P := ρ.range with hPdef
  set ρ' := ρ.rangeRestrict with hρ'def
  have hρ'surj : Function.Surjective ρ' := ρ.rangeRestrict_surjective
  have hρ'apply : ∀ (g : G) (x : ↥D), ((ρ' g • x : ↥D) : Ω) = (g : Equiv.Perm Ω) (x : Ω) :=
    fun g x => rfl
  have hρ'ker : ρ'.ker ≤ ϕ.ker := by
    rw [hρ'def, MonoidHom.ker_rangeRestrict, hρker]; exact hkerle
  set ψ : ↥P →* Equiv.Perm (Fin k) :=
    (QuotientGroup.lift ρ'.ker ϕ hρ'ker).comp
      (QuotientGroup.quotientKerEquivOfSurjective ρ' hρ'surj).symm.toMonoidHom with hψdef
  have hψρ : ∀ g : G, ψ (ρ' g) = ϕ g := by
    intro g
    show (QuotientGroup.lift ρ'.ker ϕ hρ'ker)
      ((QuotientGroup.quotientKerEquivOfSurjective ρ' hρ'surj).symm (ρ' g)) = ϕ g
    rw [show (QuotientGroup.quotientKerEquivOfSurjective ρ' hρ'surj).symm (ρ' g)
        = (QuotientGroup.mk g : G ⧸ ρ'.ker) from by rw [MulEquiv.symm_apply_eq]; rfl]
    rfl
  have hψcomp : ψ.comp ρ' = ϕ := MonoidHom.ext hψρ
  have hψrange : ψ.range = alternatingGroup (Fin k) := by
    rw [← hϕ]
    ext a
    constructor
    · rintro ⟨p, rfl⟩
      obtain ⟨g, rfl⟩ := hρ'surj p
      exact ⟨g, (hψρ g).symm⟩
    · rintro ⟨g, rfl⟩
      exact ⟨ρ' g, hψρ g⟩
  -- the orbits of `P` are the orbits of `G` inside `D`
  have horb : maxOrbitLength P ≤ maxOrbitLength G := by
    refine maxOrbitLength_le fun x => ?_
    have hmap : ∀ y : ↥(orbit P x), ((y : ↥D) : Ω) ∈ orbit G ((x : ↥D) : Ω) := by
      rintro ⟨y, hy⟩
      obtain ⟨p, hp⟩ := mem_orbit_iff.1 hy
      obtain ⟨g, rfl⟩ := hρ'surj p
      refine mem_orbit_iff.2 ⟨g, ?_⟩
      have : ((ρ' g • x : ↥D) : Ω) = (g : Equiv.Perm Ω) ((x : ↥D) : Ω) := hρ'apply g x
      rw [hp] at this
      exact this.symm
    have hinj : Function.Injective
        (fun y : ↥(orbit P x) => (⟨((y : ↥D) : Ω), hmap y⟩ : ↥(orbit G ((x : ↥D) : Ω)))) := by
      intro a b hab
      exact Subtype.ext (Subtype.ext (by simpa using hab))
    exact le_trans (Nat.card_le_card_of_injective _ hinj)
      (card_orbit_le_maxOrbitLength G _)
  -- Lemma 10.3.3 applied to `(P, ψ)`
  obtain ⟨x, hx⟩ := lemma_10_3_3 ψ hψrange (hk.mono horb)
  apply hx
  have hstab : stabilizer G ((x : ↥D) : Ω) = (stabilizer P x).comap ρ' := by
    ext g
    rw [Subgroup.mem_comap, mem_stabilizer_iff, mem_stabilizer_iff]
    constructor
    · intro h
      exact Subtype.ext (by rw [hρ'apply]; exact h)
    · intro h
      have h2 := Subtype.ext_iff.1 h
      rwa [hρ'apply] at h2
  have hmapstab : (stabilizer P x).map ψ = (stabilizer G ((x : ↥D) : Ω)).map ϕ := by
    conv_rhs => rw [hstab, ← hψcomp, ← Subgroup.map_map,
      Subgroup.map_comap_eq_self_of_surjective hρ'surj]
  rw [hmapstab]
  refine le_antisymm ?_ ?_
  · rw [← hϕ]; rintro _ ⟨t, -, rfl⟩; exact ⟨t, rfl⟩
  · have hxD : ((x : ↥D) : Ω) ∈ D := x.2
    simpa [hDdef, unaffectedSet, Affected] using hxD

/-! #### The paper's second case: `G^ϕ = S_k`, handled through `G₁ = ϕ⁻¹(A_k)`

> Now if `G^ϕ = S_k` then let `G₁ = ϕ⁻¹(A_k)`.  Let `ϕ₁` be the restriction of `ϕ` to
> `G₁`, so `ϕ₁ : G₁ → A_k` is an epimorphism.  Moreover, `x ∈ Ω` is affected by `ϕ` if
> and only if `x` is affected by `ϕ₁` (because `A_k` has no subgroup of index 2).  An
> application of the previous case to `(G₁, ϕ₁)` completes the proof. -/

section CaseTwo

variable {G : Subgroup (Equiv.Perm Ω)} {k : ℕ} (ϕ : G →* Equiv.Perm (Fin k))

/-- `G₁ = ϕ⁻¹(A_k)` of the proof of Theorem 10.3.5, as a subgroup of `S(Ω)`. -/
def preimageAlt : Subgroup (Equiv.Perm Ω) :=
  ((alternatingGroup (Fin k)).comap ϕ).map G.subtype

theorem preimageAlt_le : preimageAlt ϕ ≤ G := by
  rintro _ ⟨g, -, rfl⟩
  exact g.2

theorem mem_preimageAlt {σ : Equiv.Perm Ω} :
    σ ∈ preimageAlt ϕ ↔ ∃ g : G, ϕ g ∈ alternatingGroup (Fin k) ∧ (g : Equiv.Perm Ω) = σ := by
  constructor
  · rintro ⟨g, hg, rfl⟩; exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩; exact ⟨g, hg, rfl⟩

/-- `ϕ₁`, the restriction of `ϕ` to `G₁ = ϕ⁻¹(A_k)`. -/
def restrictAlt : preimageAlt ϕ →* Equiv.Perm (Fin k) :=
  ϕ.comp (Subgroup.inclusion (preimageAlt_le ϕ))

theorem restrictAlt_apply (y : preimageAlt ϕ) (g : G)
    (h : (g : Equiv.Perm Ω) = (y : Equiv.Perm Ω)) : restrictAlt ϕ y = ϕ g := by
  have : (Subgroup.inclusion (preimageAlt_le ϕ)) y = g := Subtype.ext h.symm
  rw [restrictAlt, MonoidHom.comp_apply, this]

theorem map_stabilizer_restrictAlt (x : Ω) :
    (stabilizer (preimageAlt ϕ) x).map (restrictAlt ϕ)
      = ((stabilizer G x).map ϕ) ⊓ alternatingGroup (Fin k) := by
  ext a
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨g, hgA, hgy⟩ := (mem_preimageAlt ϕ).1 y.2
    have hval : restrictAlt ϕ y = ϕ g := restrictAlt_apply ϕ y g hgy
    have hstab : g ∈ stabilizer G x := by
      have : (y : Equiv.Perm Ω) x = x := hy
      rw [mem_stabilizer_iff]
      show (g : Equiv.Perm Ω) x = x
      rw [hgy]; exact this
    exact ⟨⟨g, hstab, hval.symm⟩, by rw [hval]; exact hgA⟩
  · rintro ⟨⟨g, hg, rfl⟩, hA⟩
    have hmem : (g : Equiv.Perm Ω) ∈ preimageAlt ϕ := (mem_preimageAlt ϕ).2 ⟨g, hA, rfl⟩
    refine ⟨⟨(g : Equiv.Perm Ω), hmem⟩, ?_, ?_⟩
    · show (g : Equiv.Perm Ω) x = x
      exact hg
    · exact (restrictAlt_apply ϕ ⟨(g : Equiv.Perm Ω), hmem⟩ g rfl)

theorem unaffectedSet_restrictAlt (hϕ : IsGiantRep ϕ) :
    unaffectedSet (restrictAlt ϕ) = unaffectedSet ϕ := by
  ext x
  simp only [unaffectedSet, Set.mem_setOf_eq, Affected, not_not,
    map_stabilizer_restrictAlt ϕ x, le_inf_iff, and_iff_left (le_refl _)]

end CaseTwo

/-- **Theorem 10.3.5** (Unaffected Stabilizers Lemma), §10.3, proved. -/
theorem theorem_10_3_5_proof {G : Subgroup (Equiv.Perm Ω)} {k : ℕ} (ϕ : G →* Equiv.Perm (Fin k))
    (hϕ : IsGiantRep ϕ) (hk : LargeK k (maxOrbitLength G)) :
    alternatingGroup (Fin k) ≤ (pointwiseStab G (unaffectedSet ϕ)).map ϕ := by
  classical
  have hk8 := hk.eight_lt
  rcases eq_alternating_or_top (K := ϕ.range) hϕ
      (by simp only [Nat.card_eq_fintype_card, Fintype.card_fin]; omega) with hrange | hrange
  · exact theorem_10_3_5_aux ϕ hrange hk
  -- `G^ϕ = S_k`: apply the previous case to `G₁ = ϕ⁻¹(A_k)`
  set G₁ := preimageAlt ϕ with hG₁
  set ϕ₁ := restrictAlt ϕ with hϕ₁
  have hrange₁ : ϕ₁.range = alternatingGroup (Fin k) := by
    ext a
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨g, hgA, hgy⟩ := (mem_preimageAlt ϕ).1 y.2
      rw [restrictAlt_apply ϕ y g hgy]
      exact hgA
    · intro ha
      have : a ∈ ϕ.range := by rw [hrange]; trivial
      obtain ⟨g, rfl⟩ := this
      have hmem : (g : Equiv.Perm Ω) ∈ G₁ := (mem_preimageAlt ϕ).2 ⟨g, ha, rfl⟩
      exact ⟨⟨(g : Equiv.Perm Ω), hmem⟩, restrictAlt_apply ϕ ⟨_, hmem⟩ g rfl⟩
  have hkey := theorem_10_3_5_aux ϕ₁ hrange₁
    (hk.mono (maxOrbitLength_mono (preimageAlt_le ϕ)))
  rw [unaffectedSet_restrictAlt ϕ hϕ] at hkey
  refine le_trans hkey ?_
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨g, hgA, hgy⟩ := (mem_preimageAlt ϕ).1 y.2
  refine ⟨g, ?_, (restrictAlt_apply ϕ y g hgy).symm ▸ rfl⟩
  simp only [SetLike.mem_coe, mem_pointwiseStab]
  intro z hz
  have : (y : Equiv.Perm Ω) z = z := (mem_pointwiseStab.1 hy) z hz
  rw [hgy]; exact this

/-- **Theorem 10.3.5** (Unaffected Stabilizers Lemma), §10.3.

> Let `G ≤ S(Ω)` be a permutation group and `ϕ : G → S_k` a giant representation.  Assume
> `k > max{8, 2 + log₂ n₀}` where `n₀ = n₀(G)` denotes the length of the largest orbit of
> `G`.  Let `D` be the set of elements of `Ω` not affected by `ϕ`.  Then `G_(D)^ϕ ≥ A_k`.

The paper's proof: for `G^ϕ = A_k`, `D` is `G`-invariant and `G_(D)` is the kernel of the
restriction `G → S(D)` with image `P`; if `G_(D)^ϕ ≠ A_k` then `G_(D) ≤ ker ϕ`, so `ϕ`
factors as `G → P → A_k`, and Lemma 10.3.3 gives `x ∈ D` with `P_x^ψ ≠ A_k`, contradicting
that `x` is unaffected.  For `G^ϕ = S_k` apply this to `G₁ = ϕ⁻¹(A_k)` (the notion of
"affected" is the same for `ϕ` and `ϕ₁` because `A_k` has no subgroup of index 2). -/
theorem theorem_10_3_5 {G : Subgroup (Equiv.Perm Ω)} {k : ℕ} (ϕ : G →* Equiv.Perm (Fin k))
    (hϕ : IsGiantRep ϕ) (hk : LargeK k (maxOrbitLength G)) :
    alternatingGroup (Fin k) ≤ (pointwiseStab G (unaffectedSet ϕ)).map ϕ :=
  theorem_10_3_5_proof ϕ hϕ hk

/-! ### Proposition 10.3.6 -/

section Index

variable {A : Type*} [Group A] [Finite A]

/-- `H.subgroupOf K` and `H ⊓ K` have the same elements. -/
def subgroupOfEquivInf (H K : Subgroup A) : (H.subgroupOf K) ≃ (H ⊓ K : Subgroup A) where
  toFun x := ⟨((x : K) : A), ⟨x.2, (x : K).2⟩⟩
  invFun y := ⟨⟨(y : A), y.2.2⟩, y.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The finite-group counting identity behind the paper's computation
`|N : Nₓ| = |N : (N ∩ Gₓ)| = |N Gₓ : Gₓ|`: for `N` normal and any `S`,
`|N S : S| = |N : N ∩ S|`. -/
theorem relIndex_sup_left_of_normal (N S : Subgroup A) [N.Normal] :
    S.relIndex (N ⊔ S) = S.relIndex N := by
  classical
  have hcard : ∀ (H K : Subgroup A), H.relIndex K * Nat.card (H ⊓ K : Subgroup A)
      = Nat.card K := by
    intro H K
    have h1 : (H.subgroupOf K).index * Nat.card (H.subgroupOf K) = Nat.card K :=
      Subgroup.index_mul_card _
    rwa [Nat.card_congr (subgroupOfEquivInf H K)] at h1
  have hS : S.relIndex (N ⊔ S) * Nat.card (S ⊓ (N ⊔ S) : Subgroup A) = Nat.card (N ⊔ S : Subgroup A) :=
    hcard S (N ⊔ S)
  have hN : N.relIndex (N ⊔ S) * Nat.card (N ⊓ (N ⊔ S) : Subgroup A) = Nat.card (N ⊔ S : Subgroup A) :=
    hcard N (N ⊔ S)
  rw [inf_eq_left.2 (le_sup_right : S ≤ N ⊔ S)] at hS
  rw [inf_eq_left.2 (le_sup_left : N ≤ N ⊔ S)] at hN
  have hNsup : N.relIndex (N ⊔ S) = N.relIndex S := by
    rw [sup_comm]
    exact Subgroup.relIndex_sup_right S N
  have hNS : N.relIndex S * Nat.card (N ⊓ S : Subgroup A) = Nat.card S := hcard N S
  have hSN : S.relIndex N * Nat.card (S ⊓ N : Subgroup A) = Nat.card N := hcard S N
  have hinf : (S ⊓ N : Subgroup A) = (N ⊓ S : Subgroup A) := inf_comm _ _
  rw [hinf] at hSN
  -- `|NS| = |N| * |S| / |N ∩ S|`, in multiplicative form
  have hpos : 0 < Nat.card (N ⊓ S : Subgroup A) := Nat.card_pos
  have hposS : 0 < N.relIndex S := by
    rcases Nat.eq_zero_or_pos (N.relIndex S) with h | h
    · rw [h, zero_mul] at hNS
      exact absurd hNS.symm (Nat.card_pos).ne'
    · exact h
  -- multiply both sides of the goal by `N.relIndex S * |N ∩ S|`
  refine Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hposS hpos) ?_
  calc S.relIndex (N ⊔ S) * (N.relIndex S * Nat.card (N ⊓ S : Subgroup A))
      = S.relIndex (N ⊔ S) * Nat.card S := by rw [hNS]
    _ = Nat.card (N ⊔ S : Subgroup A) := hS
    _ = N.relIndex S * Nat.card N := by rw [← hNsup, hN]
    _ = N.relIndex S * (S.relIndex N * Nat.card (N ⊓ S : Subgroup A)) := by rw [hSN]
    _ = S.relIndex N * (N.relIndex S * Nat.card (N ⊓ S : Subgroup A)) := by ring

end Index

/-- The stabilizer of `x` in a subgroup `H` of `G` is the stabilizer in `G`, cut down. -/
theorem stabilizer_subgroupOf {A : Type*} [Group A] [MulAction A Ω] (H : Subgroup A) (x : Ω) :
    stabilizer H x = (stabilizer A x).subgroupOf H := by
  ext h
  simp [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff, Subgroup.smul_def]

/-- **Proposition 10.3.6**, §10.3, at the point `x` itself.

> Let `G ≤ S(Ω)` be a permutation group and `ϕ : G → H` an epimorphism.  Let `Δ ⊆ Ω` be an
> orbit of `G` and `x ∈ ∆`.  Let `L = G_x^ϕ`.  Then each orbit of `ker(ϕ)` in `∆` has
> length `|∆|/k` where `k = |H : L|`.

Stated multiplicatively (`k * |orbit| = |Δ|`) to avoid truncated division.  The paper's
computation: `|G : N G_x| = |G^ϕ : G_x^ϕ| = k` and `|N : N_x| = |N : (N ∩ G_x)| =
|N G_x : G_x| = d/k`. -/
theorem proposition_10_3_6_self {G : Subgroup (Equiv.Perm Ω)} {H : Type*} [Group H]
    (ϕ : G →* H) (hϕ : Function.Surjective ϕ) (x : Ω) :
    ((stabilizer G x).map ϕ).index * Nat.card (orbit ϕ.ker x) = Nat.card (orbit G x) := by
  classical
  set N := ϕ.ker with hNdef
  set S := stabilizer G x with hSdef
  -- `|G : N G_x| = |G^ϕ : G_x^ϕ| = k`
  have hmap : (N ⊔ S).map ϕ = S.map ϕ := by
    rw [Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).2 (le_refl _), bot_sup_eq]
  have hindex : ((S.map ϕ)).index = (N ⊔ S).index := by
    rw [← hmap, Subgroup.index_map_eq _ hϕ le_sup_left]
  -- `|N : N_x| = |N : N ∩ G_x| = |N G_x : G_x|`
  have horbN : Nat.card (orbit ϕ.ker x) = S.relIndex N := by
    have h1 : Nat.card (orbit ϕ.ker x) = (stabilizer ϕ.ker x).index :=
      Nat.card_congr (orbitEquivQuotientStabilizer _ x)
    rw [h1, stabilizer_subgroupOf]
    rfl
  have hsplit : S.relIndex (N ⊔ S) * (N ⊔ S).index = S.index :=
    Subgroup.relIndex_mul_index le_sup_right
  have horbG : Nat.card (orbit G x) = S.index := card_orbit_eq_index G x
  rw [hindex, horbN, horbG, ← hsplit, relIndex_sup_left_of_normal N S]
  ring

/-- **Proposition 10.3.6**, §10.3, as the paper states it: the conclusion holds at every
point `y` of the orbit `Δ` of `x`, with `k = |H : G_x^ϕ|` computed at `x`.

"First we note that `k` only depends on `Δ`, not on the specific element `x ∈ Δ` because
if `y ∈ Δ` then `Gₓ` and `G_y` are conjugates in `G`." -/
theorem proposition_10_3_6 {G : Subgroup (Equiv.Perm Ω)} {H : Type*} [Group H]
    (ϕ : G →* H) (hϕ : Function.Surjective ϕ) (x y : Ω) (hy : y ∈ orbit G x) :
    ((stabilizer G x).map ϕ).index * Nat.card (orbit ϕ.ker y) = Nat.card (orbit G x) := by
  obtain ⟨σ, rfl⟩ := mem_orbit_iff.1 hy
  have hconj : stabilizer G (σ • x) = (stabilizer G x).map (MulAut.conj σ).toMonoidHom :=
    stabilizer_smul_eq_stabilizer_map_conj σ x
  have hcomp : ((stabilizer G x).map (MulAut.conj σ).toMonoidHom).map ϕ
      = ((stabilizer G x).map ϕ).map ((MulAut.conj (ϕ σ)) : H →* H) := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext g
    simp [MulAut.conj, map_mul, map_inv]
  have hindex : ((stabilizer G (σ • x)).map ϕ).index = ((stabilizer G x).map ϕ).index := by
    rw [hconj, hcomp, Subgroup.index_map_equiv]
  have horb : orbit G (σ • x) = orbit G x := orbit_eq_iff.2 hy
  rw [← hindex, ← horb]
  exact proposition_10_3_6_self ϕ hϕ (σ • x)

/-! ### Corollary 10.3.7 (Affected Orbit Lemma) -/

/-- The image of a subgroup under the corestriction `ϕ : G → G^ϕ` is the image under `ϕ`,
viewed inside `G^ϕ`. -/
theorem map_rangeRestrict_eq_subgroupOf {G : Subgroup (Equiv.Perm Ω)} {H : Type*} [Group H]
    (ϕ : G →* H) (T : Subgroup G) :
    T.map ϕ.rangeRestrict = (T.map ϕ).subgroupOf ϕ.range := by
  ext g
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, rfl⟩
  · rintro ⟨t, ht, hgt⟩
    exact ⟨t, ht, Subtype.ext hgt⟩

/-- **Corollary 10.3.7** (Affected Orbit Lemma), §10.3.

> Let `G ≤ S(Ω)` be a permutation group and `ϕ : G → S_k` a giant representation.  Assume
> `k ≥ 5`.  Then, if `∆` is an affected `G`-orbit, i.e. `∆ ∩ D = ∅`, then `ker(ϕ)` is not
> transitive on `∆`; in fact, each orbit of `ker(ϕ)` in `∆` has length `≤ |∆|/k`.

Proof (the paper's): "For `k ≥ 5`, the largest proper subgroup of `A_k` has index `k`, and
the largest subgroup of `S_k` not containing `A_k` also has index `k`.  So the statement
follows from Prop. 10.3.6."  (The index fact is
`Babai.card_le_relIndex_of_not_alternating_le`.) -/
theorem corollary_10_3_7 {G : Subgroup (Equiv.Perm Ω)} {k : ℕ}
    (ϕ : G →* Equiv.Perm (Fin k)) (hϕ : IsGiantRep ϕ) (hk5 : 5 ≤ k) (x : Ω)
    (hΔ : ∀ z ∈ orbit G x, Affected ϕ z) (y : Ω) (hy : y ∈ orbit G x) :
    k * Nat.card (orbit ϕ.ker y) ≤ Nat.card (orbit G x) ∧
      Nat.card (orbit ϕ.ker y) < Nat.card (orbit G x) := by
  classical
  -- corestrict `ϕ` to its image, so that Prop. 10.3.6 applies
  set ψ := ϕ.rangeRestrict with hψdef
  have hψsurj : Function.Surjective ψ := ϕ.rangeRestrict_surjective
  have hker : ψ.ker = ϕ.ker := MonoidHom.ker_rangeRestrict ϕ
  have hmain := proposition_10_3_6 ψ hψsurj x y hy
  rw [hker] at hmain
  -- "the largest subgroup of `S_k` not containing `A_k` has index `k`"
  have hcard : Fintype.card (Fin k) = k := Fintype.card_fin k
  have hnotle : ¬ alternatingGroup (Fin k) ≤ (stabilizer G x).map ϕ :=
    hΔ x (mem_orbit_self x)
  have hle : (stabilizer G x).map ϕ ≤ ϕ.range := by
    rintro _ ⟨t, -, rfl⟩
    exact ⟨t, rfl⟩
  have hk_le : k ≤ ((stabilizer G x).map ψ).index := by
    rw [map_rangeRestrict_eq_subgroupOf]
    have := card_le_relIndex_of_not_alternating_le (Ω := Fin k) (by omega) hϕ hle hnotle
    rw [hcard] at this
    exact this
  have hmul : k * Nat.card (orbit ϕ.ker y) ≤ Nat.card (orbit G x) := by
    calc k * Nat.card (orbit ϕ.ker y)
        ≤ ((stabilizer G x).map ψ).index * Nat.card (orbit ϕ.ker y) :=
          Nat.mul_le_mul_right _ hk_le
      _ = Nat.card (orbit G x) := hmain
  refine ⟨hmul, ?_⟩
  haveI : Nonempty (orbit ϕ.ker y) := ⟨⟨y, mem_orbit_self y⟩⟩
  have hpos : 0 < Nat.card (orbit ϕ.ker y) := Nat.card_pos
  have h5 : 5 * Nat.card (orbit ϕ.ker y) ≤ k * Nat.card (orbit ϕ.ker y) :=
    Nat.mul_le_mul_right _ hk5
  omega

end Babai
