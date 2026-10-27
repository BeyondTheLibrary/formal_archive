/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 11.2: elementary facts about the Johnson groups `S_k^(t)` and `A_k^(t)`.
-/
import Workspace.Luks.PrelimExtra

/-!
# Facts about the Johnson groups

The proof of Theorem 11.2.1 (§11.2) uses three elementary facts about the Johnson groups
of §2.2.1, none of which is a numbered item of the paper:

* `Babai.johnsonA_le_johnsonS` and `Babai.johnsonA_conj_mem`: `A_k^(t)` is a normal
  subgroup of `S_k^(t)` (it is the image of `A_k ◁ S_k` under the induced action on
  `t`-sets);
* `Babai.card_johnsonS_le_two_mul`: `|S_k^(t)| ≤ 2·|A_k^(t)|`, the paper's
  "`|S_k^(t) : A_k^(t)| ≤ 2`";
* `Babai.johnsonA_exists_smul`: `A_k^(t)` is transitive on the `t`-subsets of `[k]`, for
  `1 ≤ t` and `2t < k`.
-/

namespace Babai

open MulAction Equiv Equiv.Perm

/-! ### `A_k^(t)` is normal in `S_k^(t)` -/

/-- `A_k^(t) ≤ S_k^(t)`. -/
theorem johnsonA_le_johnsonS (k t : ℕ) : JohnsonA k t ≤ JohnsonS k t :=
  Subgroup.map_mono le_top

/-- `A_k^(t)` is closed under conjugation by `S_k^(t)`: it is the image of the normal
subgroup `A_k ◁ S_k` under the homomorphism `tAction`. -/
theorem johnsonA_conj_mem (k t : ℕ) :
    ∀ σ ∈ JohnsonS k t, ∀ a ∈ JohnsonA k t, σ * a * σ⁻¹ ∈ JohnsonA k t := by
  rintro _ ⟨σ, -, rfl⟩ _ ⟨a, ha, rfl⟩
  refine ⟨σ * a * σ⁻¹, ?_, by simp⟩
  exact (alternatingGroup (Fin k)).normal_of_characteristic.conj_mem a ha σ

/-! ### `|S_k^(t) : A_k^(t)| ≤ 2` -/

/-- The relative index of `A_k^(t)` in `S_k^(t)` divides `2`: relative indices of images
are relative indices of the subgroups joined with the kernel
(`Subgroup.relIndex_map_map`), and `|S_k : A_k| = 2`. -/
theorem relIndex_johnsonA_johnsonS_dvd_two {k : ℕ} (hk : 2 ≤ k) (t : ℕ) :
    (JohnsonA k t).relIndex (JohnsonS k t) ∣ 2 := by
  haveI : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.2 hk
  have hmap := Subgroup.relIndex_map_map (tAction (Ω := Fin k) t)
    (alternatingGroup (Fin k)) ⊤
  have htop : (⊤ : Subgroup (Equiv.Perm (Fin k))) ⊔ (tAction (Ω := Fin k) t).ker = ⊤ :=
    top_sup_eq _
  rw [htop, Subgroup.relIndex_top_right] at hmap
  have hdvd : (alternatingGroup (Fin k) ⊔ (tAction (Ω := Fin k) t).ker).index ∣
      (alternatingGroup (Fin k)).index := Subgroup.index_dvd_of_le le_sup_left
  rw [alternatingGroup.index_eq_two] at hdvd
  exact hmap ▸ hdvd

/-- §11.2, the bound "`|S_k^(t) : A_k^(t)| ≤ 2`" used in the proof of Theorem 11.2.1,
stated on orders. -/
theorem card_johnsonS_le_two_mul {k : ℕ} (hk : 2 ≤ k) (t : ℕ) :
    Nat.card (JohnsonS k t) ≤ 2 * Nat.card (JohnsonA k t) := by
  have hle := johnsonA_le_johnsonS k t
  have hcard := relIndex_mul_card_of_le hle
  have hdvd := relIndex_johnsonA_johnsonS_dvd_two hk t
  have h2 : (JohnsonA k t).relIndex (JohnsonS k t) ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  calc Nat.card (JohnsonS k t)
      = (JohnsonA k t).relIndex (JohnsonS k t) * Nat.card (JohnsonA k t) := hcard.symm
    _ ≤ 2 * Nat.card (JohnsonA k t) := Nat.mul_le_mul_right _ h2

/-! ### `A_k^(t)` is transitive on `t`-sets -/

/-- There is a `t`-subset of `[k]` whenever `t ≤ k`. -/
theorem binom_nonempty {k t : ℕ} (h : t ≤ k) : Nonempty (binom (Fin k) t) := by
  classical
  obtain ⟨u, -, hu⟩ := Finset.exists_subset_card_eq
    (show t ≤ (Finset.univ : Finset (Fin k)).card by simpa using h)
  exact ⟨⟨u, hu⟩⟩

/-- The Johnson group `A_k^(t)` is transitive on the `t`-subsets of `[k]`, for `1 ≤ t` and
`2t < k`: the alternating group is `(k-2)`-transitive and `t ≤ k - 2`. -/
theorem johnsonA_exists_smul {k t : ℕ} (ht : 1 ≤ t) (hk : 2 * t < k)
    (c c' : binom (Fin k) t) : ∃ a ∈ JohnsonA k t, a c = c' := by
  classical
  haveI : IsMultiplyPretransitive (alternatingGroup (Fin k)) (Fin k)
      (Nat.card (Fin k) - 2) := alternatingGroup.isMultiplyPretransitive (Fin k)
  haveI : IsMultiplyPretransitive (alternatingGroup (Fin k)) (Fin k) t := by
    refine MulAction.isMultiplyPretransitive_of_le (n := Nat.card (Fin k) - 2) ?_ ?_
    · simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
      omega
    · simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
      omega
  haveI : IsPretransitive (alternatingGroup (Fin k)) (Set.powersetCard (Fin k) t) :=
    Set.powersetCard.isPretransitive_of_isMultiplyPretransitive
      (alternatingGroup (Fin k)) (n := t) inferInstance
  obtain ⟨g, hg⟩ := (‹IsPretransitive (alternatingGroup (Fin k))
      (Set.powersetCard (Fin k) t)›).exists_smul_eq
    (⟨(c : Finset (Fin k)), c.2⟩ : Set.powersetCard (Fin k) t)
    (⟨(c' : Finset (Fin k)), c'.2⟩ : Set.powersetCard (Fin k) t)
  refine ⟨tAction t (g : Equiv.Perm (Fin k)), ⟨(g : Equiv.Perm (Fin k)), g.2, rfl⟩, ?_⟩
  refine Subtype.ext ?_
  have hg' := congrArg Subtype.val hg
  simp only [Set.powersetCard.coe_smul] at hg'
  rw [tAction_apply_coe, ← hg']
  simp [Finset.smul_finset_def, Subgroup.smul_def, Equiv.Perm.smul_def]

end Babai
