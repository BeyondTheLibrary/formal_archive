import Workspace.Algo.TopMasterCameronStepSix

/-! # The computed coset list drives the live step-6 record
Eq. (62) needs a list of coset representatives of `K₁` in `K`. The machine
computes one from the signed Cameron action. It is installed as the record's
ambient enumeration. Its restriction to the window is the window enumeration,
and the machine's orbit windows of the kernel are the orbit enumeration of
`G₁`. The descended group is transitive exactly when the computed kernel has a
single orbit on the window. In both cases the machine's tree and the record's
coset branch have the same calls and the same value. In the intransitive case
this is the window lift of the descent to `G₁` expanded by the Chain Rule. So
the prepared carrier runs the paper's branch of step 6, followed by the shift
back to the node's coset.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Classical Pointwise

theorem restrictTo_congr {Ω : Type*} {K K' : Subgroup (Perm Ω)} {Δ : Set Ω} (hK : K = K')
    (h : IsInvariant K Δ) (h' : IsInvariant K' Δ) : restrictTo K Δ h = restrictTo K' Δ h' := by
  subst hK
  rfl

theorem siInstance_ext {Ω A : Type*} {a b : SIInstance Ω A} (hK : a.K = b.K) (hΔ : a.Δ = b.Δ)
    (hx : a.x = b.x) (hy : a.y = b.y) : a = b := by
  cases a
  cases b
  simp only at hK hΔ hx hy
  subst hK hΔ hx hy
  rfl

/-- The restriction of a permutation to an invariant window, and `1` off the group. -/
noncomputable def masterWindowRestrict {Ω : Type*} (K : Subgroup (Perm Ω)) (Δ : Set Ω)
    (hK : IsInvariant K Δ) (σ : Perm Ω) : Perm Δ :=
  if hσ : σ ∈ K then restrictHom K Δ hK ⟨σ, hσ⟩ else 1

/-- The coset of a restricted representative pulls back to the coset upstairs. -/
theorem windowPreim_restrict_smul {Ω : Type*} {K : Subgroup (Perm Ω)} {Δ : Set Ω}
    (hK : IsInvariant K Δ) (G₁ : Subgroup (Perm Δ)) {σ : Perm Ω} (hσ : σ ∈ K) :
    windowPreim K Δ hK (masterWindowRestrict K Δ hK σ • (G₁ : Set (Perm Δ))) =
      σ • (windowPreimSubgroup K Δ hK G₁ : Set (Perm Ω)) := by
  ext τ
  rw [mem_windowPreim, Set.mem_smul_set_iff_inv_smul_mem]
  change _ ↔ σ⁻¹ * τ ∈ windowPreimSubgroup K Δ hK G₁
  rw [mem_windowPreimSubgroup]
  constructor
  · rintro ⟨hτ, hr⟩
    refine ⟨mul_mem (inv_mem hσ) hτ, ?_⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem] at hr
    have he : restrictHom K Δ hK ⟨σ⁻¹ * τ, mul_mem (inv_mem hσ) hτ⟩ =
        (masterWindowRestrict K Δ hK σ)⁻¹ * restrictHom K Δ hK ⟨τ, hτ⟩ := by
      rw [masterWindowRestrict, dif_pos hσ, ← map_inv, ← map_mul]
      rfl
    rw [he]
    exact hr
  · rintro ⟨hτ', hr⟩
    have hτ : τ ∈ K := by
      have := mul_mem hσ hτ'
      rwa [← mul_assoc, mul_inv_cancel, one_mul] at this
    refine ⟨hτ, ?_⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    have he : restrictHom K Δ hK ⟨σ⁻¹ * τ, hτ'⟩ =
        (masterWindowRestrict K Δ hK σ)⁻¹ * restrictHom K Δ hK ⟨τ, hτ⟩ := by
      rw [masterWindowRestrict, dif_pos hσ, ← map_inv, ← map_mul]
      rfl
    rw [he] at hr
    exact hr

/-- A coset cover of `K` by cosets of the window preimage of `G₁`, restricted to
the window, is a coset cover of the window group by cosets of `G₁`. -/
noncomputable def CosetRepEnum.restrictWindow {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {K : Subgroup (Perm Ω)} {Δ : Set Ω} (hK : IsInvariant K Δ) {G₁ : Subgroup (Perm Δ)}
    (hG : G₁ ≤ restrictTo K Δ hK) (E : CosetRepEnum (windowPreimSubgroup K Δ hK G₁) K) :
    CosetRepEnum G₁ (restrictTo K Δ hK) where
  reps := E.reps.map (masterWindowRestrict K Δ hK)
  cover := by
    ext τ
    simp only [Set.mem_iUnion, List.mem_map, exists_prop]
    constructor
    · intro hτ
      obtain ⟨⟨k, hk⟩, rfl⟩ := hτ
      have hk' : k ∈ (K : Set (Perm Ω)) := hk
      rw [E.cover] at hk'
      obtain ⟨σ, hσ, hkσ⟩ := Set.mem_iUnion₂.mp hk'
      have hσK : σ ∈ K := E.mem hσ
      obtain ⟨k₁, hk₁, rfl⟩ := hkσ
      obtain ⟨hk₁K, hk₁G⟩ := mem_windowPreimSubgroup.mp hk₁
      refine ⟨_, ⟨σ, hσ, rfl⟩, ⟨_, hk₁G, ?_⟩⟩
      rw [masterWindowRestrict, dif_pos hσK]
      change restrictHom K Δ hK ⟨σ, hσK⟩ * restrictHom K Δ hK ⟨k₁, hk₁K⟩ = _
      rw [← map_mul]
      rfl
    · rintro ⟨_, ⟨σ, hσ, rfl⟩, ⟨g₁, hg₁, rfl⟩⟩
      have hσK : σ ∈ K := E.mem hσ
      refine mul_mem ?_ (hG hg₁)
      rw [masterWindowRestrict, dif_pos hσK]
      exact ⟨_, rfl⟩
  length := by
    rw [List.length_map, ← relIndex_windowPreimSubgroup hK G₁]
    exact E.length

/-- Expanding the coset descent of Eq. (62) substitutes a sub-reduction for each
coset call, and unites the answers in the same order. -/
theorem expand_cosetDescent {Ω A : Type*} (H : Subgroup (Perm Ω)) (Δ : Set Ω) (x y : Ω → A)
    (f : SIInstance Ω A → SIReduction Ω A (Set (Perm Ω))) :
    ∀ L : List (Perm Ω), (cosetDescent H Δ x y L).expand f =
      unionAnswers (L.map fun σ => f ⟨σ • (H : Set (Perm Ω)), Δ, x, y⟩) := by
  intro L
  induction L with
  | nil => rfl
  | cons σ rest ih =>
    rw [cosetDescent, List.map_cons, unionAnswers]
    change (f _).bind (fun ans => (((cosetDescent H Δ x y rest).bind
      fun s => .done (ans ∪ s)).expand f)) = _
    congr 1
    funext ans
    rw [masterExpand_bind, ih]
    rfl

/-- **Step 6, intransitive case, on the ambient domain.** The descent to `G₁`
on the window, expanded by the Chain Rule over the orbits of `G₁` and lifted
to `Ω`, makes the calls of the orbit chains of the cosets `σ K₁` upstairs,
in the same order, with the same value. -/
theorem liftWindow_descent_trace {Ω A : Type*} [Fintype Ω] [DecidableEq Ω]
    {K : Subgroup (Perm Ω)} {Δ : Set Ω} (hinv : IsInvariant K Δ) {G₁ : Subgroup (Perm Δ)}
    (hG : G₁ ≤ restrictTo K Δ hinv) (x y : Ω → A) (L : List (Perm Ω)) (hL : ∀ σ ∈ L, σ ∈ K)
    (E : OrbitEnum G₁) :
    let T := liftWindow K Δ hinv x ((cosetDescent G₁ Set.univ (restrictStr Δ x) (restrictStr Δ y)
      (L.map (masterWindowRestrict K Δ hinv))).expand E.chain)
    let U := unionAnswers (L.map fun σ => Babai.cosetChain x (extendStr Δ x (restrictStr Δ y))
      (E.windows.map (Subtype.val '' ·)) (σ • (windowPreimSubgroup K Δ hinv G₁ : Set (Perm Ω))))
    T.calls = U.calls ∧ T.run = U.run := by
  intro T U
  let C := (L.map (masterWindowRestrict K Δ hinv)).map fun σ => σ • (G₁ : Set (Perm Δ))
  have hC : ∀ S ∈ C, S ⊆ (restrictTo K Δ hinv : Set (Perm Δ)) := by
    intro S hS
    obtain ⟨_, hσ', rfl⟩ := List.mem_map.mp hS
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hσ'
    rintro _ ⟨g, hg, rfl⟩
    refine mul_mem ?_ (hG hg)
    rw [masterWindowRestrict, dif_pos (hL σ hσ)]
    exact ⟨_, rfl⟩
  have h := masterWindowImageChains_trace hinv x (restrictStr Δ y) E.windows C hC
  dsimp only at h
  have hT : T = liftWindow K Δ hinv x
      (unionAnswers (C.map (Babai.cosetChain (restrictStr Δ x) (restrictStr Δ y) E.windows))) := by
    change liftWindow K Δ hinv x _ = _
    rw [expand_cosetDescent]
    simp only [C, List.map_map]
    rfl
  have hU : unionAnswers (C.map fun S => Babai.cosetChain x (extendStr Δ x (restrictStr Δ y))
      (E.windows.map (Subtype.val '' ·)) (windowPreim K Δ hinv S)) = U := by
    change _ = unionAnswers _
    congr 1
    rw [List.map_map, List.map_map]
    refine List.map_congr_left fun σ hσ => ?_
    change Babai.cosetChain _ _ _ (windowPreim K Δ hinv
      (masterWindowRestrict K Δ hinv σ • (G₁ : Set (Perm Δ)))) = _
    rw [windowPreim_restrict_smul hinv G₁ (hL σ hσ)]
  rw [hT, ← hU]
  exact h

section Descent
variable {n : ℕ} {W : RawWinSI} (hx : W.2.2.2.1.length = n) (hw : RawGens.WF n W.2.1)
    (hnd : W.1.Nodup) (hlt : ∀ u ∈ W.1, u < n)
    (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1))
    (htr : IsTransitive (decGroup W.1.length (primitiveWindowInput W).1)) (hn : 2 ≤ W.1.length)
    {c : RawCameron} (h : c.WF (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length)
    (hlo : basePower (JohnsonA c.k c.t) c.s ≤
      (decGroup (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length
        (masterWindowBlockAction W).2.2).map (permCongrHom (decCameron c h)).toMonoidHom)
    (hhi : (decGroup (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length
        (masterWindowBlockAction W).2.2).map (permCongrHom (decCameron c h)).toMonoidHom ≤
      wreathProduct (JohnsonS c.k c.t) c.s)
    (hwindow : 64 ≤ (masterGroupInstance n W).windowSize)

/-- The group-frame input the prepared carrier runs at the node `W`. -/
def masterCamFrameInput (c : RawCameron) (W : RawWinSI) : MasterDescInput :=
  (masterCamPrepared (c, masterWindowBlockInput W)).2

/-- The machine's coset representatives of `K₁` in `K`, in its own order. -/
noncomputable def masterCamAmbientPerms (n : ℕ) (c : RawCameron) (W : RawWinSI) : List (Perm (Fin n)) :=
  masterDescPerms n (masterCameronDescInput (c, masterCamFrameInput c W))

include hx in
theorem masterCamFrame_K : (decWinSI n (masterCamFrameInput c W).1).K =
    (decGroup n W.2.1 : Set (Perm (Fin n))) := by
  change decCoset n (some (W.2.1, rawOne W.2.2.2.1)) = _
  rw [decCoset_some, decPerm_rawOne hx, one_smul]

include hx in
/-- **Eq. (62), the cover of step 6.** The machine's representatives cover `K`
by cosets of `K₁`, and there are `|K : K₁|` of them. -/
noncomputable def masterCamAmbientReps :
    CosetRepEnum (masterCamDescentBase hw hnd hlt hinv htr hn h hlo hhi hwindow).K₁
      (masterCamDescentBase hw hnd hlt hinv htr hn h hlo hhi hwindow).blocks.K where
  reps := masterCamAmbientPerms n c W
  cover := by
    have hp := masterWindowBlockAction_wf hx hw hnd hlt hinv htr hn
    have hc := masterDesc_cover (p := masterCameronDescInput (c, masterCamFrameInput c W))
      (camLiftSign_wf (p := masterWindowBlockAction W) hp h hhi)
    have hK : (decWinSI n (masterCameronDescInput (c, masterCamFrameInput c W)).1).K =
        (decGroup n W.2.1 : Set (Perm (Fin n))) := masterCamFrame_K hx
    rw [hK] at hc
    rw [masterCamDescentBase_K₁ hx hw hnd hlt hinv htr hn h hlo hhi hwindow]
    exact hc
  length := by
    have hp := masterWindowBlockAction_wf hx hw hnd hlt hinv htr hn
    rw [masterCamDescentBase_K₁ hx hw hnd hlt hinv htr hn h hlo hhi hwindow]
    have hi : (decGroup n (camLiftGens (c, masterWindowBlockAction W))).relIndex
        (decGroup n W.2.1) = _ := camLiftGens_index hp h hhi
    change (masterDescPerms n _).length ≤
      (decGroup n (camLiftGens (c, masterWindowBlockAction W))).relIndex (decGroup n W.2.1)
    rw [hi]
    simp only [masterDescPerms, List.length_map, List.length_range]
    exact (masterCameronDesc_width (p := masterCamFrameInput c W) hp h hhi).le

include hx in
/-- The descended group on the window is the window group of the computed kernel. -/
theorem masterCamBase_G₁ (hinv' : IsInvariant (decGroup n (camLiftGens (c, masterWindowBlockAction W)))
      (winSet n W.1)) :
    (masterCamDescentBase hw hnd hlt hinv htr hn h hlo hhi hwindow).G₁ =
      restrictTo (decGroup n (camLiftGens (c, masterWindowBlockAction W))) (winSet n W.1) hinv' :=
  (masterCamDescentBase hw hnd hlt hinv htr hn h hlo hhi hwindow).restrictTo_K₁.symm.trans
    (restrictTo_congr (masterCamDescentBase_K₁ hx hw hnd hlt hinv htr hn h hlo hhi hwindow) _ _)

/-- **Eq. (62) on the window.** The machine's representatives, restricted to the
window, cover the window group by cosets of `G₁`. -/
noncomputable def masterCamWindowReps :
    CosetRepEnum (masterCamDescentBase hw hnd hlt hinv htr hn h hlo hhi hwindow).G₁
      (masterCamDescentBase hw hnd hlt hinv htr hn h hlo hhi hwindow).blocks.windowGroup :=
  Algo.CosetRepEnum.restrictWindow
    (masterCamDescentBase hw hnd hlt hinv htr hn h hlo hhi hwindow).blocks.invariant
    (masterCamDescentBase hw hnd hlt hinv htr hn h hlo hhi hwindow).G₁_le
    (masterCamAmbientReps hx hw hnd hlt hinv htr hn h hlo hhi hwindow)

/-- The machine's orbit windows of the computed kernel, as the orbits of `G₁`. -/
noncomputable def masterCamOrbits :
    OrbitEnum (masterCamDescentBase hw hnd hlt hinv htr hn h hlo hhi hwindow).G₁ :=
  let hp := masterWindowBlockAction_wf hx hw hnd hlt hinv htr hn
  let hinv' : IsInvariant (decGroup n (camLiftGens (c, masterWindowBlockAction W)))
      (winSet n W.1) := isInvariant_of_le hinv (camLiftGens_le hp h hhi)
  ⟨masterOrbitWindows n (W.1, camLiftGens (c, masterWindowBlockAction W), W.2.2), by
    rw [masterCamBase_G₁ hx hw hnd hlt hinv htr hn h hlo hhi hwindow hinv']
    exact masterOrbitWindows_perm (W := (W.1, camLiftGens (c, masterWindowBlockAction W), W.2.2))
      (camLiftGens_wf (c := c) hp) hlt hinv'⟩

/-- **The live step-6 record of a raw node**, with the machine's coset lists and
orbit order. -/
noncomputable def masterCamDescentData : DescentData (masterGroupInstance n W) :=
  { masterCamDescentBase hw hnd hlt hinv htr hn h hlo hhi hwindow with
    ambientReps := masterCamAmbientReps hx hw hnd hlt hinv htr hn h hlo hhi hwindow
    windowReps := masterCamWindowReps hx hw hnd hlt hinv htr hn h hlo hhi hwindow
    orbits := masterCamOrbits hx hw hnd hlt hinv htr hn h hlo hhi hwindow }

set_option maxHeartbeats 1000000 in
include hx in
theorem masterCamDescentData_K₁ :
    (masterCamDescentData hx hw hnd hlt hinv htr hn h hlo hhi hwindow).K₁ =
      decGroup n (camLiftGens (c, masterWindowBlockAction W)) :=
  masterCamDescentBase_K₁ hx hw hnd hlt hinv htr hn h hlo hhi hwindow

include hx in
/-- **The test of step 3 on the descended group.** `G₁` is transitive exactly
when the computed kernel has a single orbit on the window. -/
theorem masterCamDescentData_transitive_iff :
    IsTransitive (masterCamDescentData hx hw hnd hlt hinv htr hn h hlo hhi hwindow).G₁ ↔
      (winOrbits (camLiftGens (c, masterWindowBlockAction W), W.1)).length = 1 := by
  let D := masterCamDescentData hx hw hnd hlt hinv htr hn h hlo hhi hwindow
  have hp := masterWindowBlockAction_wf hx hw hnd hlt hinv htr hn
  have hw' := camLiftGens_wf (c := c) hp
  have hinv' : IsInvariant (decGroup n (camLiftGens (c, masterWindowBlockAction W)))
      (winSet n W.1) := isInvariant_of_le hinv (camLiftGens_le hp h hhi)
  have hG : D.G₁ = restrictTo (decGroup n (camLiftGens (c, masterWindowBlockAction W)))
      (winSet n W.1) hinv' :=
    D.restrictTo_K₁.symm.trans (restrictTo_congr
      (masterCamDescentData_K₁ hx hw hnd hlt hinv htr hn h hlo hhi hwindow) _ _)
  have hne : Nonempty (masterGroupInstance n W).Δ := by
    obtain ⟨u, hu⟩ := List.exists_mem_of_length_pos (show 0 < W.1.length by omega)
    exact ⟨⟨⟨u, hlt u hu⟩, hu⟩⟩
  haveI := hne
  rw [hG, isTransitive_iff_orbitList_length]
  have hperm : (masterOrbitWindows n (W.1, camLiftGens (c, masterWindowBlockAction W), W.2.2)).Perm
      (orbitList (restrictTo (decGroup n (camLiftGens (c, masterWindowBlockAction W)))
        (winSet n W.1) hinv')) :=
    masterOrbitWindows_perm (W := (W.1, camLiftGens (c, masterWindowBlockAction W), W.2.2)) hw' hlt hinv'
  have hl := hperm.length_eq
  rw [masterOrbitWindows, List.length_map] at hl
  rw [hl]
  convert Iff.rfl using 3

/-- In the transitive case the prepared target is the target of the instance. -/
theorem masterCamFrame_y (h1 : (winOrbits (camLiftGens (c, masterWindowBlockAction W),
      W.1)).length = 1) :
    decStrN n (masterCamFrameInput c W).1.2.2.2.2 = (masterGroupInstance n W).y :=
  masterCamPrepared_target_hint c _ (by
    rw [masterCamHasHint_eq, decide_eq_true_eq]
    exact h1)

include hx in
/-- **Step 6, transitive case: the machine's tree is the paper's branch.** The
coset calls of the machine are those of Eq. (62) in the record, in the same
order, and both return `Iso^Δ_K(x, y)`. -/
theorem masterCamDescentData_trace_transitive
    (h1 : (winOrbits (camLiftGens (c, masterWindowBlockAction W), W.1)).length = 1) :
    let D := masterCamDescentData hx hw hnd hlt hinv htr hn h hlo hhi hwindow
    (masterCamSelectTree n c (masterCamFrameInput c W)).calls = D.cosetBranch.calls ∧
      (masterCamSelectTree n c (masterCamFrameInput c W)).run = D.cosetBranch.run := by
  intro D
  have hp := masterWindowBlockAction_wf hx hw hnd hlt hinv htr hn
  have htrD : IsTransitive D.G₁ :=
    (masterCamDescentData_transitive_iff hx hw hnd hlt hinv htr hn h hlo hhi hwindow).mpr h1
  have hsel : masterCamSelectTree n c (masterCamFrameInput c W) =
      masterDescTree n (masterCameronDescInput (c, masterCamFrameInput c W)) := by
    unfold masterCamSelectTree
    exact if_pos h1
  have hbr : D.cosetBranch = cosetDescent D.K₁ (masterGroupInstance n W).Δ
      (masterGroupInstance n W).x (masterGroupInstance n W).y (masterCamAmbientPerms n c W) := by
    unfold DescentData.cosetBranch
    rw [if_pos htrD]
    rfl
  rw [hsel, hbr]
  have hK : (decGroup n (camLiftGens (c, masterWindowBlockAction W)) : Set (Perm (Fin n))) =
      (D.K₁ : Set (Perm (Fin n))) := by
    rw [masterCamDescentData_K₁ hx hw hnd hlt hinv htr hn h hlo hhi hwindow]
  have hy := masterCamFrame_y (n := n) (c := c) h1
  have hr1 := masterDescTree_spec (n := n) (p := masterCameronDescInput (c, masterCamFrameInput c W))
    (camLiftSign_wf (p := masterWindowBlockAction W) hp h hhi) hinv
  constructor
  · rw [masterDescTree, masterDescChain_calls, calls_cosetDescent,
      show masterCamAmbientPerms n c W =
        masterDescPerms n (masterCameronDescInput (c, masterCamFrameInput c W)) from rfl]
    refine List.map_congr_left (fun σ _ => ?_)
    exact siInstance_ext (congrArg (fun S : Set (Perm (Fin n)) => σ • S) hK) rfl rfl hy
  · rw [hr1, ← hbr, D.run_cosetBranch]
    exact congrArg SIInstance.answer (siInstance_ext (masterCamFrame_K (c := c) hx) rfl rfl hy)

set_option maxHeartbeats 1000000 in
include hx in
/-- **Step 6, intransitive case: the machine's tree is the paper's branch.** The
orbit chains the machine runs after each representative are the calls of the
record's window descent, expanded by the Chain Rule over the orbits of `G₁`
and lifted to the ambient domain, in the same order and with the same value. -/
theorem masterCamDescentData_trace_intransitive (hW : AggnCheckedWindowWF n W)
    (hidx : (camNbar c h).relIndex (decGroup (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length
      (masterWindowBlockAction W).2.2) ≤ (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length)
    (h1 : ¬ (winOrbits (camLiftGens (c, masterWindowBlockAction W), W.1)).length = 1) :
    let D := masterCamDescentData hx hw hnd hlt hinv htr hn h hlo hhi hwindow
    (masterCamSelectTree n c (masterCamFrameInput c W)).calls = D.cosetBranch.calls ∧
      (masterCamSelectTree n c (masterCamFrameInput c W)).run = D.cosetBranch.run := by
  intro D
  have hp := masterWindowBlockAction_wf hx hw hnd hlt hinv htr hn
  have hw' := camLiftGens_wf (c := c) hp
  have hinv' : IsInvariant (decGroup n (camLiftGens (c, masterWindowBlockAction W)))
      (winSet n W.1) := isInvariant_of_le hinv (camLiftGens_le hp h hhi)
  have hm : (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length ≤ W.1.length :=
    (blocksWF_rawMinBlocks (rfl : W.1.length = W.1.length) (primitiveWindowInput W).1).length_le
  have htrD : ¬ IsTransitive D.G₁ := fun ht =>
    h1 ((masterCamDescentData_transitive_iff hx hw hnd hlt hinv htr hn h hlo hhi hwindow).mp ht)
  have hsel : masterCamSelectTree n c (masterCamFrameInput c W) =
      masterCamStrongTree n (c, masterCamFrameInput c W) := by
    unfold masterCamSelectTree
    exact if_neg h1
  have hL : ∀ σ ∈ masterCamAmbientPerms n c W, σ ∈ decGroup n W.2.1 :=
    fun σ hσ => (masterCamAmbientReps hx hw hnd hlt hinv htr hn h hlo hhi hwindow).mem hσ
  have ht := liftWindow_descent_trace hinv D.G₁_le (masterGroupInstance n W).x
    (masterGroupInstance n W).y (masterCamAmbientPerms n c W) hL D.orbits
  dsimp only at ht
  have hbr : D.cosetBranch = liftWindow (decGroup n W.2.1) (winSet n W.1) hinv
      (masterGroupInstance n W).x ((cosetDescent D.G₁ Set.univ
        (restrictStr (winSet n W.1) (masterGroupInstance n W).x)
        (restrictStr (winSet n W.1) (masterGroupInstance n W).y)
        ((masterCamAmbientPerms n c W).map (masterWindowRestrict _ _ hinv))).expand
        D.orbits.chain) := by
    unfold DescentData.cosetBranch
    rw [if_neg htrD]
    rfl
  have hK : (windowPreimSubgroup (decGroup n W.2.1) (winSet n W.1) hinv D.G₁ : Set (Perm (Fin n))) =
      (decGroup n (camLiftGens (c, masterWindowBlockAction W)) : Set (Perm (Fin n))) := by
    change ((D.K₁ : Subgroup (Perm (Fin n))) : Set (Perm (Fin n))) = _
    rw [masterCamDescentData_K₁ hx hw hnd hlt hinv htr hn h hlo hhi hwindow]
  have hD : D.orbits.windows.map (Subtype.val '' ·) =
      (winOrbits (camLiftGens (c, masterWindowBlockAction W), W.1)).map (winSet n) :=
    masterOrbitWindows_image (W := (W.1, camLiftGens (c, masterWindowBlockAction W), W.2.2))
      hw' hlt hinv'
  have hy := masterCamPrepared_target_chain hx hnd hlt c (masterWindowBlockInput W).2
    (by rw [masterCamHasHint_eq, decide_eq_false_iff_not]; exact h1)
  have hWf := masterCamPrepared_wf hx c (masterWindowBlockInput W).2 hW
  have hreps := masterCamLists_reps (p := masterCamFrameInput c W) hp h hhi hWf hm hidx
  have hU : masterCamStrongTree n (c, masterCamFrameInput c W) =
      unionAnswers ((masterCamAmbientPerms n c W).map fun σ => Babai.cosetChain
        (masterGroupInstance n W).x (extendStr (winSet n W.1) (masterGroupInstance n W).x
          (restrictStr (winSet n W.1) (masterGroupInstance n W).y))
        (D.orbits.windows.map (Subtype.val '' ·))
        (σ • (windowPreimSubgroup (decGroup n W.2.1) (winSet n W.1) hinv D.G₁ :
          Set (Perm (Fin n))))) := by
    rw [hK, hD, ← hy]
    unfold masterCamStrongTree strongDescent
    rw [hreps]
    rfl
  rw [hsel, hbr, hU]
  exact ⟨ht.1.symm, ht.2.symm⟩

/-- A trace equation survives the final shift back to the node's coset. -/
theorem trace_bind_shift {Ω A : Type*} {T U : SIReduction Ω A (Set (Perm Ω))}
    (f : Set (Perm Ω) → SIReduction Ω A (Set (Perm Ω)))
    (h : T.calls = U.calls ∧ T.run = U.run) :
    (T.bind f).calls = (U.bind f).calls ∧ (T.bind f).run = (U.bind f).run := by
  rw [SIReduction.calls_bind, SIReduction.calls_bind, SIReduction.run_bind,
    SIReduction.run_bind, h.1, h.2]
  exact ⟨rfl, rfl⟩

include hx in
/-- **Section 11.3, steps 6–7, transitive case, at a raw node.** The prepared
carrier runs the coset branch of the live step-6 record, in the group frame of
the node, and shifts the answer back to the node's candidate coset. -/
theorem masterCamPrepared_match_transitive {a b : ℕ} (hW : AggnCheckedWindowWF n W)
    (hidx : (camNbar c h).relIndex (decGroup (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length
      (masterWindowBlockAction W).2.2) ≤ (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length)
    (hcap : masterCameronChildBound n ≤ masterInputCap a b n)
    (g : RawMasterSI → RawCameron × MasterDescInput) (hgp : g (W, none) = (c, masterWindowBlockInput W))
    (h1 : (winOrbits (camLiftGens (c, masterWindowBlockAction W), W.1)).length = 1) :
    LoopMatch (masterAdmittedRound a b (masterCamPreparedOps g)) (fun J => decWinSI n J.1)
      (decCoset n) (W, none) ((masterCamPreparedOps g).width (W, none)) 0
      ((masterCamPreparedOps g).init (W, none))
      ((masterCamDescentData hx hw hnd hlt hinv htr hn h hlo hhi hwindow).cosetBranch.bind
        (fun A => .done (decPerm n W.2.2.1 • A))) := by
  have hp := masterWindowBlockAction_wf hx hw hnd hlt hinv htr hn
  have hm : (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length ≤ W.1.length :=
    (blocksWF_rawMinBlocks (rfl : W.1.length = W.1.length) (primitiveWindowInput W).1).length_le
  have hM := masterCamPrepared_match (p := masterWindowBlockInput W) hp h hhi hW hm hidx hinv
    hcap g hgp
  exact loopMatch_of_trace hM
    (trace_bind_shift _ (masterCamDescentData_trace_transitive hx hw hnd hlt hinv htr hn h hlo hhi
      hwindow h1)).1
    (trace_bind_shift _ (masterCamDescentData_trace_transitive hx hw hnd hlt hinv htr hn h hlo hhi
      hwindow h1)).2
include hx in
/-- **Section 11.3, steps 6–7, at a raw node, both cases.** The prepared
carrier runs the coset branch of the live step-6 record in the group frame of
the node: the coset calls with the Johnson hint when `G₁` is transitive, and
the lifted orbit chains of the cosets of `G₁` otherwise. It then shifts the
answer back to the node's candidate coset. -/
theorem masterCamPrepared_match_descent {a b : ℕ} (hW : AggnCheckedWindowWF n W)
    (hidx : (camNbar c h).relIndex (decGroup (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length
      (masterWindowBlockAction W).2.2) ≤ (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length)
    (hcap : masterCameronChildBound n ≤ masterInputCap a b n)
    (g : RawMasterSI → RawCameron × MasterDescInput)
    (hgp : g (W, none) = (c, masterWindowBlockInput W)) :
    LoopMatch (masterAdmittedRound a b (masterCamPreparedOps g)) (fun J => decWinSI n J.1)
      (decCoset n) (W, none) ((masterCamPreparedOps g).width (W, none)) 0
      ((masterCamPreparedOps g).init (W, none))
      ((masterCamDescentData hx hw hnd hlt hinv htr hn h hlo hhi hwindow).cosetBranch.bind
        (fun A => .done (decPerm n W.2.2.1 • A))) := by
  have hp := masterWindowBlockAction_wf hx hw hnd hlt hinv htr hn
  have hm : (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length ≤ W.1.length :=
    (blocksWF_rawMinBlocks (rfl : W.1.length = W.1.length) (primitiveWindowInput W).1).length_le
  have hM := masterCamPrepared_match (p := masterWindowBlockInput W) hp h hhi hW hm hidx hinv
    hcap g hgp
  have htr' : (masterCamSelectTree n c (masterCamFrameInput c W)).calls =
        (masterCamDescentData hx hw hnd hlt hinv htr hn h hlo hhi hwindow).cosetBranch.calls ∧
      (masterCamSelectTree n c (masterCamFrameInput c W)).run =
        (masterCamDescentData hx hw hnd hlt hinv htr hn h hlo hhi hwindow).cosetBranch.run := by
    by_cases h1 : (winOrbits (camLiftGens (c, masterWindowBlockAction W), W.1)).length = 1
    · exact masterCamDescentData_trace_transitive hx hw hnd hlt hinv htr hn h hlo hhi hwindow h1
    · exact masterCamDescentData_trace_intransitive hx hw hnd hlt hinv htr hn h hlo hhi hwindow
        hW hidx h1
  exact loopMatch_of_trace hM (trace_bind_shift _ htr').1 (trace_bind_shift _ htr').2
end Descent
end Algo
