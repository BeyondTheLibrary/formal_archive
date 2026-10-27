import Workspace.Algo.TopMasterCameronSelect

/-! # The Cameron select carrier runs the exact step-6 tree
Section 11.3, step 6 descends to the preimage of the Cameron subgroup.
When that subgroup is transitive on the window, each coset call keeps the
Johnson hint of step 7. Otherwise step 3 applies to the new group: the same
node runs the Chain Rule over its orbits after each representative.
The one carrier `masterCamSelectOps` follows both trees exactly.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv

/-- The computed test of the select carrier is the single-orbit test. -/
theorem masterCamHasHint_eq (c : RawCameron) (p : MasterDescInput) :
    masterCamHasHint (c, p) =
      decide ((winOrbits (camLiftGens (c, masterDescAction p), p.1.1)).length = 1) := rfl

/-- The tree of step 6: coset calls with the hint when the descended group is
transitive on the window, and the orbit chains otherwise. -/
noncomputable def masterCamSelectTree (n : ℕ) (c : RawCameron) (p : MasterDescInput) :
    SIReduction (Fin n) ℕ (Set (Perm (Fin n))) :=
  if (winOrbits (camLiftGens (c, masterDescAction p), p.1.1)).length = 1 then
    masterDescTree n (masterCameronDescInput (c, p))
  else masterCamStrongTree n (c, p)

section Match
variable {n m a b : ℕ} {p : MasterDescInput} {c : RawCameron}
    {φ : decGroup n p.1.2.1 →* Perm (Fin m)}
    (hp : RawAction.WF n m (masterDescAction p) φ) (h : c.WF m)
    (hhi : (decGroup m p.2.2).map (permCongrHom (decCameron c h)).toMonoidHom ≤
      wreathProduct (JohnsonS c.k c.t) c.s)
    (hW : AggnCheckedWindowWF n p.1) (hm : m ≤ p.1.1.length)
    (hidx : (camNbar c h).relIndex (decGroup m p.2.2) ≤ m)
    (hinv : IsInvariant (decGroup n p.1.2.1) (winSet n p.1.1))
    (hcap : masterCameronChildBound n ≤ masterInputCap a b n)
    (f : RawMasterSI → RawCameron × MasterDescInput) (hfp : f (p.1, none) = (c, p))

include hp h hW hm in
/-- The window is nonempty on the Cameron branch, so it has at least one orbit. -/
theorem masterCam_orbits_pos :
    0 < (winOrbits (camLiftGens (c, masterDescAction p), p.1.1)).length := by
  have hk : c.k ≤ p.1.1.length := h.bounds.2.2.trans hm
  have hpos : 0 < p.1.1.length := by have := h.k_max; omega
  obtain ⟨u, hu⟩ := List.exists_mem_of_length_pos hpos
  have hflat := winOrbits_cover (gs := camLiftGens (c, masterDescAction p))
    (n := n) (camLiftGens_wf (p := masterDescAction p) (c := c) hp) hW.2.1 hu
  rcases hlen : winOrbits (camLiftGens (c, masterDescAction p), p.1.1) with _ | ⟨v, vs⟩
  · rw [hlen] at hflat
    simp at hflat
  · simp

variable (P : RawMasterSI) (hP1 : P.1.1 = p.1.1) (hPx : P.1.2.2.2.1 = p.1.2.2.2.1)
    (hP2 : P.2 = none) (hfP : f P = (c, p))

include hp h hhi hW hm hidx hinv hcap hP1 hPx hP2 hfP in
/-- **Section 11.3, steps 6–7, on the RAM.** The select carrier at a Cameron node
matches the transitive coset tree or the orbit-chain tree, as the computed
single-orbit test says. The node may differ from `p.1` outside its window,
source and hint. -/
theorem masterCamSelect_match_at :
    LoopMatch (masterAdmittedRound a b (masterCamSelectOps f)) (fun J => decWinSI n J.1)
      (decCoset n) P ((masterCamSelectOps f).width P) 0
      ((masterCamSelectOps f).init P) (masterCamSelectTree n c p) := by
  unfold masterCamSelectTree
  by_cases h1 : (winOrbits (camLiftGens (c, masterDescAction p), p.1.1)).length = 1
  · have hh : masterCamHasHint (f P) = true := by
      rw [hfP, masterCamHasHint_eq, decide_eq_true_eq]
      exact h1
    rw [if_pos h1]
    refine masterCamOpen_match_at hp h hhi hW hm hidx hinv hcap masterCamFoldEmbed P hP1 hPx hP2
      ?_ ?_ ?_ ?_ ?_
    · change (if masterCamHasHint (f P) then _ else _) = _
      rw [if_pos hh, hfP]
    · intro j s
      change (if masterCamHasHint (f P) then _ else _) = _
      rw [if_pos hh, hfP]
      rfl
    · change (if masterCamHasHint (f P) then _ else _) = _
      rw [if_pos hh]
    · intro j s A
      change (if masterCamHasHint (f P) then _ else _) = _
      rw [if_pos hh, hPx]
      rfl
    · intro s
      change top2NormC P.1.2.2.2.1 s = _
      rw [hPx]
  · have hh : masterCamHasHint (f P) = false := by
      rw [hfP, masterCamHasHint_eq, decide_eq_false_iff_not]
      exact h1
    have h2 : 1 < (winOrbits (camLiftGens (c, masterDescAction p), p.1.1)).length := by
      have := masterCam_orbits_pos hp h hW hm
      omega
    rw [if_neg h1]
    refine masterCamChain_match_at hp h hhi hW hm hidx hinv h2 id P hP1 hPx ?_ ?_ ?_ ?_ ?_
    · change (if masterCamHasHint (f P) then _ else _) = _
      rw [if_neg (by simp [hh]), hfP]
    · intro j s
      change (if masterCamHasHint (f P) then _ else _) = _
      rw [if_neg (by simp [hh]), hfP]
      rfl
    · change (if masterCamHasHint (f P) then _ else _) = _
      rw [if_neg (by simp [hh]), hfP]
      rfl
    · intro j s A
      change (if masterCamHasHint (f P) then _ else _) = _
      rw [if_neg (by simp [hh]), hfP]
      rfl
    · intro s
      change top2NormC P.1.2.2.2.1 s.2.2.2 = _
      rw [hPx]
      rfl

include hp h hhi hW hm hidx hinv hcap hfp in
/-- The select carrier at the node `p.1` itself. -/
theorem masterCamSelect_match :
    LoopMatch (masterAdmittedRound a b (masterCamSelectOps f)) (fun J => decWinSI n J.1)
      (decCoset n) (p.1, none) ((masterCamSelectOps f).width (p.1, none)) 0
      ((masterCamSelectOps f).init (p.1, none)) (masterCamSelectTree n c p) :=
  masterCamSelect_match_at hp h hhi hW hm hidx hinv hcap f (p.1, none) rfl rfl rfl hfp
end Match
end Algo
