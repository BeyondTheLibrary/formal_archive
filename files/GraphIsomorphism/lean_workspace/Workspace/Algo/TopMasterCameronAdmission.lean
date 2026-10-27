import Workspace.Algo.TopMasterCameronWindowLink

/-! # Admission of the transitive Cameron children
The computed subgroup generators and coordinate images already have
polynomial size. Keeping their window dictionary unchanged preserves
the exact image rows and block labels proved for the Cameron child.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv

def masterCameronChildBound (n : ℕ) : ℕ :=
  16 * (aggnCheckedWindowBound n + gensBound n + strBound n + n + 2)

theorem polyBound_masterCameronChildBound : PolyBound masterCameronChildBound :=
  (polyBound_const 16).mul (((((aggnPolyBound_checkedWindow.add polyBound_gensBound).add
    polyBound_strBound).add polyBound_id).add (polyBound_const 2)))

section Child
variable {n m : ℕ} {p : MasterDescInput} {c : RawCameron}
    {φ : decGroup n p.1.2.1 →* Perm (Fin m)}
    (hp : RawAction.WF n m (masterDescAction p) φ) (h : c.WF m)
    (hhi : (decGroup m p.2.2).map (permCongrHom (decCameron c h)).toMonoidHom ≤
      wreathProduct (JohnsonS c.k c.t) c.s)
    (hW : AggnCheckedWindowWF n p.1) (hm : m ≤ p.1.1.length)
    (hinv : IsInvariant (decGroup n p.1.2.1) (winSet n p.1.1))

include hp hW in
theorem masterCameronChildInput_window_wf (j : ℕ) :
    AggnCheckedWindowWF n (masterCameronChildInput ((c, p), j)).1 := by
  refine ⟨hW.1, hW.2.1, camLiftGens_wf (p := masterDescAction p) hp, camLiftGens_length (p := masterDescAction p) hp, ?_,
    hW.2.2.2.2.2.1, hW.2.2.2.2.2.2⟩
  exact wf_rawMul (wf_normPerm hp.1 _) (wf_normPerm hp.1 _)

include hp h hhi hW hm in
theorem masterCameronChildInput_size (j : ℕ) :
    Enc.size (((masterCameronChildInput ((c, p), j)).1,
      some (masterCameronChildInput ((c, p), j)).2) : RawMasterSI) ≤
      masterCameronChildBound n := by
  have hn := length_le_of_nodup_lt hW.1 hW.2.1
  have hkn : c.k ≤ n := h.bounds.2.2.trans (hm.trans hn)
  have htn : c.t ≤ n := h.bounds.2.1.trans (hm.trans hn)
  have hwin := aggnCheckedWindow_size (masterCameronChildInput_window_wf (c := c) hp hW j)
  have hact := camLiftAction_wf (p := masterDescAction p) hp h hhi
  have hlen : (camLiftImages (c, masterDescAction p)).length ≤ n * n := by
    simpa only [camLiftImages, List.length_map] using camLiftGens_length (c := c) hp
  have himg : Enc.size (camLiftImages (c, masterDescAction p)) ≤ gensBound n := by
    have hs := size_list_le_of_entries (camLiftImages (c, masterDescAction p)) (strBound n)
      (fun g hg => size_perm_le' hkn (hact.2.2.2.1 g hg))
    have hl := Nat.mul_le_mul_right (2 * strBound n + 1) hlen
    dsimp [gensBound]
    omega
  have hdom : Enc.size (camPointDom c) ≤ strBound n := by
    rw [camPointDom_eq h]
    apply size_natList_le
    · simpa using hkn
    · intro i hi
      exact (List.mem_range.mp hi).trans_le hkn
  have ht : Enc.size c.t ≤ n + 2 := (size_nat_le_self c.t).trans (by omega)
  have h1 := size_pair_le' (((masterCameronChildInput ((c, p), j)).1,
    some (masterCameronChildInput ((c, p), j)).2) : RawMasterSI)
  have h2 := size_pair_le' ((camPointDom c, camLiftImages (c, masterDescAction p)), c.t)
  have h3 := size_pair_le' (camPointDom c, camLiftImages (c, masterDescAction p))
  dsimp only [Prod.fst, Prod.snd] at h1 h2 h3
  rw [size_some_eq] at h1
  change Enc.size _ ≤ _
  dsimp only [masterCameronChildInput, camLiftHint, camLiftAction] at h1 hwin ⊢
  unfold masterCameronChildBound
  omega

include h hW hm in
theorem masterCameronChildInput_measure (j : ℕ) :
    masterRawMeasure ((masterCameronChildInput ((c, p), j)).1,
      some (masterCameronChildInput ((c, p), j)).2) < masterRawMeasure (p.1, none) := by
  have hk : c.k ≤ p.1.1.length := h.bounds.2.2.trans hm
  have hpos : 0 < p.1.1.length := by have := h.k_max; omega
  have hn := length_le_of_nodup_lt hW.1 hW.2.1
  apply masterRawMeasure_lt (p := (p.1, none))
    (q := ((masterCameronChildInput ((c, p), j)).1,
      some (masterCameronChildInput ((c, p), j)).2)) rfl (le_refl _) _ (Or.inr ?_)
  · change (camPointDom c).length ≤ 2 * p.1.2.2.2.1.length
    rw [camPointDom_eq h, List.length_range, hW.2.2.2.2.2.1.1]
    omega
  · change (camPointDom c).length < 2 * p.1.1.length
    rw [camPointDom_eq h, List.length_range]
    omega

include hp hhi hW hinv in
/-- The Cameron child passes the invariance check: its group, the lift of the subgroup of
Theorem 11.2.1, lies in the parent's group, which preserves the window. -/
theorem masterCameronChildInput_rawIsInvariant (j : ℕ) :
    rawIsInvariant ((masterCameronChildInput ((c, p), j)).1.2.1,
      (masterCameronChildInput ((c, p), j)).1.1) = true := by
  have hw := masterCameronChildInput_window_wf (c := c) hp hW j
  rw [rawIsInvariant_eq_true_iff hw.2.2.1 hw.2.1]
  change IsInvariant (decGroup n (camLiftGens (c, masterDescAction p))) (winSet n p.1.1)
  rw [camLiftGens_spec hp h hhi]
  intro σ hσ
  exact hinv σ ((mem_camLiftSubgroup h).mp hσ).1

include hp h hhi hW hm hinv in
theorem masterCameronChildInput_admitted {a b : ℕ}
    (hcap : masterCameronChildBound n ≤ masterInputCap a b n) (j : ℕ) :
    masterAdmitChild a b ((p.1, none),
      some ((masterCameronChildInput ((c, p), j)).1,
        some (masterCameronChildInput ((c, p), j)).2)) =
      some ((masterCameronChildInput ((c, p), j)).1,
        some (masterCameronChildInput ((c, p), j)).2) := by
  have hn := length_le_of_nodup_lt hW.1 hW.2.1
  have hk := h.bounds.2.2.trans hm
  refine masterAdmitChild_some.mpr ⟨rfl, ⟨?_, ?_, ?_⟩, rfl,
    masterCameronChildInput_measure h hW hm j,
    masterCameronChildInput_rawIsInvariant hp h hhi hW hinv j⟩
  · change Enc.size _ ≤ masterInputCap a b p.1.2.2.2.1.length
    rw [hW.2.2.2.2.2.1.1]
    exact (masterCameronChildInput_size hp h hhi hW hm j).trans hcap
  · change p.1.1.length ≤ p.1.2.2.2.1.length
    rwa [hW.2.2.2.2.2.1.1]
  · change (camPointDom c).length ≤ 2 * p.1.1.length
    rw [camPointDom_eq h, List.length_range]
    omega
end Child

theorem exists_masterCameronChild_cap : ∃ a b : ℕ,
    ∀ n, masterCameronChildBound n ≤ masterInputCap a b n := by
  obtain ⟨a, b, hab⟩ := polyBound_masterCameronChildBound
  refine ⟨a, b, fun n => (hab n).trans ?_⟩
  change topcsContextCap a b n ≤ _
  unfold masterInputCap
  omega
end Algo
