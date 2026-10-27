import Workspace.Algo.CameronDescent
import Workspace.Algo.TopParity

/-!
# The signed coordinate action in Section 11.2

A wreath element has one permutation of the underlying points at each output
coordinate. Its action on subsets determines these permutations. We keep the
coordinate permutation and the sign at each coordinate. The kernel is exactly
the alternating base group of Theorem 11.2.1.
-/

namespace Algo

open Equiv (Perm)

/-- A subset can contain one given point and omit another. -/
theorem camSubset_separates {k t : ℕ} (ht : 1 ≤ t) (hk : t < k)
    {a b : Fin k} (hab : a ≠ b) :
    ∃ S : Babai.binom (Fin k) t, a ∈ S.val ∧ b ∉ S.val := by
  classical
  have hs : ({a} : Finset (Fin k)) ⊆ Finset.univ.erase b := by
    simpa using hab
  have hc : t ≤ (Finset.univ.erase b : Finset (Fin k)).card := by
    simp only [Finset.card_erase_of_mem (Finset.mem_univ b), Finset.card_univ,
      Fintype.card_fin]
    omega
  obtain ⟨S, ha, hS, hcard⟩ := Finset.exists_subsuperset_card_eq hs (by simpa using ht) hc
  exact ⟨⟨S, hcard⟩, ha (by simp), fun hb => (Finset.mem_erase.1 (hS hb)).1 rfl⟩

/-- There are two distinct subsets when the subset size is positive and proper. -/
theorem camBinom_nontrivial {k t : ℕ} (ht : 1 ≤ t) (hk : t < k) :
    Nontrivial (Babai.binom (Fin k) t) := by
  have hk2 : 2 ≤ k := by omega
  let a : Fin k := ⟨0, by omega⟩
  let b : Fin k := ⟨1, by omega⟩
  have hab : a ≠ b := by intro h; have := congrArg Fin.val h; simp [a, b] at this
  obtain ⟨S, ha, hb⟩ := camSubset_separates ht hk hab
  obtain ⟨T, _, hna⟩ := camSubset_separates ht hk hab.symm
  exact ⟨⟨S, T, fun h => hna (h ▸ ha)⟩⟩

/-- A product action on a nontrivial alphabet determines all its factors. -/
theorem camWreathPerm_injective {Γ : Type*} [Nontrivial Γ] {s : ℕ}
    {h h' : Fin s → Perm Γ} {σ σ' : Perm (Fin s)}
    (he : Babai.wreathPerm h σ = Babai.wreathPerm h' σ') : h = h' ∧ σ = σ' := by
  classical
  have hh : h = h' := by
    funext i
    apply Equiv.ext
    intro a
    exact congrArg (fun w : Perm (Fin s → Γ) => w (fun _ => a) i) he
  refine ⟨hh, ?_⟩
  subst h'
  have hinv : σ⁻¹ = σ'⁻¹ := by
    apply Equiv.ext
    intro i
    by_contra hn
    obtain ⟨a, b, hab⟩ := exists_pair_ne Γ
    have hv := congrArg
      (fun w : Perm (Fin s → Γ) => w (Function.update (fun _ => b) (σ⁻¹ i) a) i) he
    have hf := (h i).injective hv
    simp only [Babai.wreathPerm_apply, Function.update_self,
      Function.update_of_ne (Ne.symm hn)] at hf
    exact hab hf
  exact inv_injective hinv

/-- The point permutations and the coordinate permutation of a Johnson wreath element. -/
theorem camWreath_lift {k t s : ℕ}
    (w : Babai.wreathProduct (Babai.JohnsonS k t) s) :
    ∃ (p : Fin s → Perm (Fin k)) (σ : Perm (Fin s)),
      w.val = Babai.wreathPerm (fun i => Babai.tAction t (p i)) σ := by
  obtain ⟨h, σ, hh, he⟩ := w.property
  have hl : ∀ i, ∃ p : Perm (Fin k), Babai.tAction t p = h i := by
    intro i
    obtain ⟨p, _, hp⟩ := hh i
    exact ⟨p, hp⟩
  choose p hp using hl
  exact ⟨p, σ, he.trans (by congr; funext i; exact (hp i).symm)⟩

/-- Faithfulness on nonempty proper subsets, proved by separating two points. -/
theorem camTAction_injective {k t : ℕ} (ht : 1 ≤ t) (hk : t < k) :
    Function.Injective (Babai.tAction (Ω := Fin k) t) := by
  rw [injective_iff_map_eq_one]
  intro π hπ
  apply Equiv.ext
  intro a
  by_contra hn
  obtain ⟨S, ha, hpa⟩ := camSubset_separates ht hk (Ne.symm hn)
  have hv : Babai.tAction t π S = S := by rw [hπ]; rfl
  have hm : π a ∈ (Babai.tAction t π S).val := Finset.mem_image.2 ⟨a, ha, rfl⟩
  rw [hv] at hm
  exact hpa hm

/-- The lift is unique because the action on proper nonempty subsets is faithful. -/
theorem camWreath_lift_unique {k t s : ℕ} (ht : 1 ≤ t) (hk : t < k)
    {p q : Fin s → Perm (Fin k)} {σ τ : Perm (Fin s)}
    (he : Babai.wreathPerm (fun i => Babai.tAction t (p i)) σ =
      Babai.wreathPerm (fun i => Babai.tAction t (q i)) τ) : p = q ∧ σ = τ := by
  letI := camBinom_nontrivial ht hk
  obtain ⟨hp, hs⟩ := camWreathPerm_injective he
  exact ⟨funext fun i => camTAction_injective ht hk (congrFun hp i), hs⟩

/-- The signs act on two copies of every coordinate. -/
def camSignedPerm {k s : ℕ} (p : Fin s → Perm (Fin k)) (σ : Perm (Fin s)) :
    Perm (Fin s × ℤˣ) where
  toFun x := (σ x.1, (p (σ x.1)).sign * x.2)
  invFun x := (σ⁻¹ x.1, (p x.1).sign⁻¹ * x.2)
  left_inv := by intro x; simp [← mul_assoc]
  right_inv := by intro x; simp [← mul_assoc]

@[simp] theorem camSignedPerm_apply {k s : ℕ} (p : Fin s → Perm (Fin k))
    (σ : Perm (Fin s)) (x : Fin s × ℤˣ) :
    camSignedPerm p σ x = (σ x.1, (p (σ x.1)).sign * x.2) := rfl

theorem camSignedPerm_one (k s : ℕ) :
    camSignedPerm (fun _ : Fin s => (1 : Perm (Fin k))) 1 = 1 := by
  ext x <;> simp

theorem camSignedPerm_mul {k s : ℕ} (p q : Fin s → Perm (Fin k))
    (σ τ : Perm (Fin s)) :
    camSignedPerm (fun i => p i * q (σ⁻¹ i)) (σ * τ) =
      camSignedPerm p σ * camSignedPerm q τ := by
  apply Equiv.ext
  intro x
  simp [Perm.mul_apply, mul_assoc]

/-- Fixing both copies forces the coordinates to be fixed and all point signs to be even. -/
theorem camSignedPerm_eq_one {k s : ℕ} (p : Fin s → Perm (Fin k))
    (σ : Perm (Fin s)) :
    camSignedPerm p σ = 1 ↔ σ = 1 ∧ ∀ i, p i ∈ alternatingGroup (Fin k) := by
  constructor
  · intro he
    have hs : σ = 1 := Equiv.ext fun i => congrArg Prod.fst (Equiv.congr_fun he (i, 1))
    refine ⟨hs, fun i => ?_⟩
    have hv := congrArg Prod.snd (Equiv.congr_fun he (i, 1))
    simpa [camSignedPerm, hs, Perm.mem_alternatingGroup] using hv
  · rintro ⟨rfl, hp⟩
    apply Equiv.ext
    intro x
    have hx := Perm.mem_alternatingGroup.1 (hp x.1)
    simp [hx]

/-- Choice supplies only a specification of the recovered factors. -/
noncomputable def camWreathPoints {k t s : ℕ}
    (w : Babai.wreathProduct (Babai.JohnsonS k t) s) : Fin s → Perm (Fin k) :=
  (camWreath_lift w).choose

noncomputable def camWreathCoords {k t s : ℕ}
    (w : Babai.wreathProduct (Babai.JohnsonS k t) s) : Perm (Fin s) :=
  (camWreath_lift w).choose_spec.choose

theorem camWreath_decomp {k t s : ℕ}
    (w : Babai.wreathProduct (Babai.JohnsonS k t) s) :
    w.val = Babai.wreathPerm (fun i => Babai.tAction t (camWreathPoints w i))
      (camWreathCoords w) := (camWreath_lift w).choose_spec.choose_spec

theorem camWreath_parts {k t s : ℕ} (ht : 1 ≤ t) (hk : t < k)
    (w : Babai.wreathProduct (Babai.JohnsonS k t) s)
    {p : Fin s → Perm (Fin k)} {σ : Perm (Fin s)}
    (he : w.val = Babai.wreathPerm (fun i => Babai.tAction t (p i)) σ) :
    camWreathPoints w = p ∧ camWreathCoords w = σ :=
  camWreath_lift_unique ht hk ((camWreath_decomp w).symm.trans he)

/-- The signed coordinate homomorphism used to compute the subgroup in Theorem 11.2.1. -/
noncomputable def camWreathSign {k t s : ℕ} (ht : 1 ≤ t) (hk : t < k) :
    Babai.wreathProduct (Babai.JohnsonS k t) s →* Perm (Fin s × ℤˣ) where
  toFun w := camSignedPerm (camWreathPoints w) (camWreathCoords w)
  map_one' := by
    have he : (1 : Babai.wreathProduct (Babai.JohnsonS k t) s).val =
        Babai.wreathPerm (fun _ => Babai.tAction t (1 : Perm (Fin k))) 1 := by
      ext f i; simp
    obtain ⟨hp, hs⟩ := camWreath_parts ht hk 1 he
    rw [hp, hs, camSignedPerm_one]
  map_mul' w v := by
    have he : (w * v).val = Babai.wreathPerm
        (fun i => Babai.tAction t (camWreathPoints w i *
          camWreathPoints v ((camWreathCoords w)⁻¹ i)))
        (camWreathCoords w * camWreathCoords v) := by
      change w.val * v.val = _
      rw [camWreath_decomp w, camWreath_decomp v]
      ext f i
      simp [Perm.mul_apply]
    obtain ⟨hp, hs⟩ := camWreath_parts ht hk (w * v) he
    rw [hp, hs, camSignedPerm_mul]

/-- The kernel is the alternating base group, with no condition on the signs on subsets. -/
theorem camWreathSign_eq_one {k t s : ℕ} (ht : 1 ≤ t) (hk : t < k)
    (w : Babai.wreathProduct (Babai.JohnsonS k t) s) :
    camWreathSign ht hk w = 1 ↔ w.val ∈ Babai.basePower (Babai.JohnsonA k t) s := by
  change camSignedPerm _ _ = 1 ↔ _
  rw [camSignedPerm_eq_one]
  constructor
  · rintro ⟨hs, hp⟩
    exact ⟨fun i => Babai.tAction t (camWreathPoints w i),
      fun i => Subgroup.mem_map_of_mem _ (hp i), by rw [← hs]; exact camWreath_decomp w⟩
  · rintro ⟨h, hh, he⟩
    have hl : ∀ i, ∃ p : Perm (Fin k), p ∈ alternatingGroup (Fin k) ∧
        Babai.tAction t p = h i := fun i => hh i
    choose p hp heq using hl
    have hd : w.val = Babai.wreathPerm (fun i => Babai.tAction t (p i)) 1 := by
      rw [he]; congr; funext i; exact (heq i).symm
    obtain ⟨hpoints, hcoords⟩ := camWreath_parts ht hk w hd
    exact ⟨hcoords, by rwa [hpoints]⟩

/-- Read the wreath element through the returned Cameron bijection. -/
noncomputable def camIntoWreath {n : ℕ} {c : RawCameron} (h : c.WF n)
    (G : Subgroup (Perm (Fin n)))
    (hhi : G.map (Equiv.permCongrHom (decCameron c h)).toMonoidHom ≤
      Babai.wreathProduct (Babai.JohnsonS c.k c.t) c.s) :
    G →* Babai.wreathProduct (Babai.JohnsonS c.k c.t) c.s :=
  ((Equiv.permCongrHom (decCameron c h)).toMonoidHom.comp G.subtype).codRestrict _
    (fun g => hhi (Subgroup.mem_map_of_mem _ g.property))

/-- The signed action of the recognized group, before numbering its two-point fibres. -/
noncomputable def camSignAction {n : ℕ} {c : RawCameron} (h : c.WF n)
    (G : Subgroup (Perm (Fin n)))
    (hhi : G.map (Equiv.permCongrHom (decCameron c h)).toMonoidHom ≤
      Babai.wreathProduct (Babai.JohnsonS c.k c.t) c.s) : G →* Perm (Fin c.s × ℤˣ) :=
  (camWreathSign h.t_pos (by have := h.k_gt; omega)).comp (camIntoWreath h G hhi)

/-- Membership in the kernel is precisely membership in the session 1 subgroup. -/
theorem camSignAction_eq_one {n : ℕ} {c : RawCameron} (h : c.WF n)
    (G : Subgroup (Perm (Fin n)))
    (hhi : G.map (Equiv.permCongrHom (decCameron c h)).toMonoidHom ≤
      Babai.wreathProduct (Babai.JohnsonS c.k c.t) c.s) (g : G) :
    camSignAction h G hhi g = 1 ↔ g.val ∈ camNbar c h :=
  camWreathSign_eq_one h.t_pos (by have := h.k_gt; omega) _

/-- Number the two signs by zero and one. -/
def camUnitBit : ℤˣ ≃ Fin 2 where
  toFun u := if u = 1 then 0 else 1
  invFun b := if b = 0 then 1 else -1
  left_inv := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl <;> norm_num
  right_inv := by
    intro b
    fin_cases b <;> norm_num

/-- The signed domain has exactly twice the number of coordinates. -/
def camSignNumbering (s : ℕ) : Fin s × ℤˣ ≃ Fin (s * 2) :=
  (Equiv.prodCongr (Equiv.refl _) camUnitBit).trans finProdFinEquiv

theorem camUnitBit_mul (u v : ℤˣ) :
    (camUnitBit (u * v)).val =
      if u = 1 then (camUnitBit v).val else 1 - (camUnitBit v).val := by
  rcases Int.units_eq_one_or u with rfl | rfl <;>
    rcases Int.units_eq_one_or v with rfl | rfl <;> norm_num [camUnitBit]

/-- Numbered form of the signed action, ready for the raw kernel routine. -/
noncomputable def camSignActionFin {n : ℕ} {c : RawCameron} (h : c.WF n)
    (G : Subgroup (Perm (Fin n)))
    (hhi : G.map (Equiv.permCongrHom (decCameron c h)).toMonoidHom ≤
      Babai.wreathProduct (Babai.JohnsonS c.k c.t) c.s) : G →* Perm (Fin (c.s * 2)) :=
  (Equiv.permCongrHom (camSignNumbering c.s)).toMonoidHom.comp (camSignAction h G hhi)

theorem camSignActionFin_eq_one {n : ℕ} {c : RawCameron} (h : c.WF n)
    (G : Subgroup (Perm (Fin n)))
    (hhi : G.map (Equiv.permCongrHom (decCameron c h)).toMonoidHom ≤
      Babai.wreathProduct (Babai.JohnsonS c.k c.t) c.s) (g : G) :
    camSignActionFin h G hhi g = 1 ↔ g.val ∈ camNbar c h := by
  change (Equiv.permCongrHom (camSignNumbering c.s)) (camSignAction h G hhi g) = 1 ↔ _
  rw [map_eq_one_iff _ (Equiv.permCongrHom (camSignNumbering c.s)).injective]
  exact camSignAction_eq_one h G hhi g

end Algo
