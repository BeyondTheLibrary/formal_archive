import Workspace.Algo.AggNodeCosetCanon
import Workspace.Algo.LocalCertAff
import Workspace.LocalCertificates.StrongCompare

/-! # The initial transporter in the certificate comparison

Proposition 13.1.11, line 01 needs an element carrying one test set to
the other. Reorder the two equal-sized sets first. If the resulting top
permutation is odd, a swap within the source set changes its parity.
The giant contains the resulting even permutation. Lift a successful
candidate and choose the canonical element of its coset of `G_T`.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Pointwise

abbrev AggnTransportInput := RawAction × (List ℕ × List ℕ)

/-- The orderings of the source and target define a permutation between them. -/
def aggnTransportBase (p : List ℕ × (List ℕ × List ℕ)) : RawPerm :=
  rawMul (rawOrd (p.1, p.2.2), rawInv (rawOrd (p.1, p.2.1)))

/-- One parity correction from any same-part swap suffices in a giant. -/
def aggnTransportCandidates (p : List ℕ × (List ℕ × List ℕ)) : RawGens :=
  aggnTransportBase p :: rawGensMul (aggnTransportBase p, topPartSwaps (p.1, p.2.1))

/-- Select a candidate in the image group using the polynomial membership test. -/
def aggnTransportTop (p : AggnTransportInput) : Option RawPerm :=
  ((aggnTransportCandidates (p.1.2.1, p.2)).filter
    (fun r => rawMem (p.1.2, r))).head?

def aggnTransportLift (p : AggnTransportInput) : Option RawPerm :=
  (aggnTransportTop p).bind fun r => actPreimage (p.1, r)

/-- Proposition 13.1.11, line 01, with the ambient lift chosen canonically. -/
def aggnTransport (p : AggnTransportInput) : Option RawPerm :=
  (aggnTransportLift p).map fun r =>
    aggnCanonCoset ((p.1.1.1, topStab (p.1, p.2.1)), r)

theorem aggnPolyFun_transportBase : PolyFun aggnTransportBase := by
  have hs : PolyFun (fun p : List ℕ × (List ℕ × List ℕ) => rawOrd (p.1, p.2.1)) := (polyFun_fst.pair (polyFun_snd.comp polyFun_fst)).comp polyFun_rawOrd
  have ht : PolyFun (fun p : List ℕ × (List ℕ × List ℕ) => rawOrd (p.1, p.2.2)) := (polyFun_fst.pair (polyFun_snd.comp polyFun_snd)).comp polyFun_rawOrd
  exact (ht.pair (hs.comp polyFun_rawInv)).comp polyFun_rawMul

theorem aggnPolyFun_transportCandidates : PolyFun aggnTransportCandidates :=
  (aggnPolyFun_transportBase.pair
    ((aggnPolyFun_transportBase.pair
      ((polyFun_fst.pair (polyFun_snd.comp polyFun_fst)).comp polyFun_topPartSwaps)).comp
      polyFun_rawGensMul)).comp polyFun_cons

theorem aggnPolyFun_transportTop : PolyFun aggnTransportTop := by
  have hc : PolyFun (fun p : AggnTransportInput => aggnTransportCandidates (p.1.2.1, p.2)) :=
    (((polyFun_fst.comp polyFun_snd).comp polyFun_fst).pair polyFun_snd).comp
      aggnPolyFun_transportCandidates
  exact (((polyFun_fst.comp polyFun_snd).pair hc).comp
    (PolyFun.filterParam polyFun_rawMem)).comp polyFun_headOption

theorem aggnPolyFun_transportLift : PolyFun aggnTransportLift := by
  exact ((aggnPolyFun_transportTop.pair polyFun_id).comp
    (PolyFun.optionElim (polyFun_const none)
      (((polyFun_snd.comp polyFun_fst).pair polyFun_fst).comp polyFun_actPreimage))).of_eq
        (fun p => by unfold aggnTransportLift; cases aggnTransportTop p <;> rfl)

theorem aggnPolyFun_transport : PolyFun aggnTransport := by
  have hs : PolyFun (fun p : RawPerm × AggnTransportInput =>
      some (aggnCanonCoset ((p.2.1.1.1, topStab (p.2.1, p.2.2.1)), p.1))) :=
    (((((polyFun_snd.comp polyFun_fst).comp polyFun_fst).comp polyFun_fst).pair
      (((polyFun_snd.comp polyFun_fst).pair
        ((polyFun_snd.comp polyFun_snd).comp polyFun_fst)).comp polyFun_topStab)).pair
      polyFun_fst |>.comp aggnPolyFun_canonCoset).comp polyFun_some
  exact ((aggnPolyFun_transportLift.pair polyFun_id).comp
    (PolyFun.optionElim (polyFun_const none) hs)).of_eq
      (fun p => by unfold aggnTransport; cases aggnTransportLift p <;> rfl)

section Top
variable {m : ℕ} {dom row row' : List ℕ}
  (hd : dom.length = m) (hn : row.Nodup) (hn' : row'.Nodup)
  (hlt : ∀ u ∈ row, u < m) (hlt' : ∀ u ∈ row', u < m)
  (hlen : row.length = row'.length)

include hd hn hn' hlt hlt' hlen in
theorem aggnTransportBase_spec :
    RawPerm.WF m (aggnTransportBase (dom, row, row')) ∧
    (decPerm m (aggnTransportBase (dom, row, row'))) '' winSet m row = winSet m row' := by
  have hs := wf_rawOrd hd hn hlt
  have ht := wf_rawOrd hd hn' hlt'
  refine ⟨wf_rawMul ht (wf_rawInv hs), ?_⟩
  rw [aggnTransportBase, rawMul_of_wf ht (wf_rawInv hs), decPerm_encPerm,
    rawInv_of_wf hs, decPerm_encPerm]
  have hims := image_decPerm_rawOrd hd hn hlt
  have himt := image_decPerm_rawOrd hd hn' hlt'
  change _ '' {x : Fin m | x.val ∈ row} = _
  rw [← hims, perm_mul_image]
  rw [← hlen] at himt
  simpa only [Set.image_image, Perm.inv_def, Equiv.symm_apply_apply] using himt

include hd hn hn' hlt hlt' hlen in
theorem aggnTransportCandidates_spec {r : RawPerm}
    (hr : r ∈ aggnTransportCandidates (dom, row, row')) :
    RawPerm.WF m r ∧ (decPerm m r) '' winSet m row = winSet m row' := by
  have hb := aggnTransportBase_spec hd hn hn' hlt hlt' hlen
  rcases List.mem_cons.mp hr with rfl | hr
  · exact hb
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
    obtain ⟨τ, hτ, rfl⟩ := (mem_topPartSwaps hd).mp hs
    refine ⟨wf_rawMul hb.1 (wf_encPerm m τ), ?_⟩
    rw [rawMul_of_wf hb.1 (wf_encPerm m τ), decPerm_encPerm, decPerm_encPerm,
      perm_mul_image, hτ.image, hb.2]

include hn hlt in
private theorem aggnPartSwap_exists (h2 : 2 ≤ row.length) :
    ∃ s : Perm (Fin m), PartSwap (winSet m row) s := by
  cases row with
  | nil => simp at h2
  | cons a rest =>
    cases rest with
    | nil => simp at h2
    | cons b rest =>
      have ha := hlt a (by simp)
      have hb := hlt b (by simp)
      refine ⟨swap ⟨a, ha⟩ ⟨b, hb⟩, ⟨a, ha⟩, ⟨b, hb⟩, ?_, ?_, rfl⟩
      · intro h
        exact (List.nodup_cons.mp hn).1 (List.mem_cons.mpr (Or.inl (congrArg Fin.val h)))
      · simp [winSet]

include hd hn hn' hlt hlt' hlen in
/-- At least one candidate is even, hence lies in every giant image. -/
theorem aggnTransportCandidates_even (h2 : 2 ≤ row.length) :
    ∃ r ∈ aggnTransportCandidates (dom, row, row'), decPerm m r ∈ alternatingGroup (Fin m) := by
  have hb := (aggnTransportBase_spec hd hn hn' hlt hlt' hlen).1
  let b := aggnTransportBase (dom, row, row')
  by_cases he : decPerm m b ∈ alternatingGroup (Fin m)
  · exact ⟨b, List.mem_cons_self, he⟩
  obtain ⟨τ, hτ⟩ := aggnPartSwap_exists hn hlt h2
  refine ⟨rawMul (b, encPerm m τ), List.mem_cons_of_mem _ ?_, ?_⟩
  · exact List.mem_map.mpr ⟨encPerm m τ, (mem_topPartSwaps hd).mpr ⟨τ, hτ, rfl⟩, rfl⟩
  · rw [rawMul_of_wf hb (wf_encPerm m τ), decPerm_encPerm, decPerm_encPerm,
      Perm.mem_alternatingGroup, map_mul, hτ.isSwap.sign_eq]
    have hs : Perm.sign (decPerm m b) = -1 :=
      (Int.units_eq_one_or _).resolve_left (by simpa only [Perm.mem_alternatingGroup] using he)
    dsimp only [b] at hs
    simp [hs]

end Top

section Lift
variable {n m : ℕ} {A : RawAction} {row row' : List ℕ}
  {ϕ : decGroup n A.1.2 →* Perm (Fin m)}
  (hA : RawAction.WF n m A ϕ) (hg : IsGiantRep ϕ)
  (hn : row.Nodup) (hn' : row'.Nodup)
  (hlt : ∀ u ∈ row, u < m) (hlt' : ∀ u ∈ row', u < m)
  (hlen : row.length = row'.length) (h2 : 2 ≤ row.length)

include hA in
private theorem aggnRawImageMem {r : RawPerm} (hr : RawPerm.WF m r) :
    rawMem (A.2, r) = true ↔ decPerm m r ∈ ϕ.range := by
  obtain ⟨hd, hm, hgs, his, hi⟩ := hA
  have h := rawMem_spec A.2.1 hm (A.2.2.map (decPerm m)) (decPerm m r)
  rw [map_encPerm_decPerm his, encPerm_decPerm hr] at h
  have hR : ϕ.range = genGroup (A.2.2.map (decPerm m)) := hi.range_eq_genGroup
  rw [hR]
  exact h

include hA hg hn hn' hlt hlt' hlen h2 in
/-- The guarded candidate search succeeds for the test sets of Section 13.1. -/
theorem aggnTransportTop_spec :
    ∃ r, aggnTransportTop (A, row, row') = some r ∧ RawPerm.WF m r ∧
      decPerm m r ∈ ϕ.range ∧ (decPerm m r) '' winSet m row = winSet m row' := by
  let L := (aggnTransportCandidates (A.2.1, row, row')).filter (fun r => rawMem (A.2, r))
  have hne : L ≠ [] := by
    obtain ⟨r, hr, he⟩ := aggnTransportCandidates_even hA.2.1 hn hn' hlt hlt' hlen h2
    have hw := (aggnTransportCandidates_spec hA.2.1 hn hn' hlt hlt' hlen hr).1
    have hmem : r ∈ L := List.mem_filter.mpr ⟨hr, (aggnRawImageMem hA hw).mpr (hg he)⟩
    intro hnil
    simp only [hnil, List.not_mem_nil] at hmem
  obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.mp (fun h => hne (List.head?_eq_none_iff.mp h))
  have hm := List.mem_of_mem_head? hr
  obtain ⟨hm, htest⟩ := List.mem_filter.mp hm
  obtain ⟨hw, himg⟩ := aggnTransportCandidates_spec hA.2.1 hn hn' hlt hlt' hlen hm
  exact ⟨r, hr, hw, (aggnRawImageMem hA hw).mp htest, himg⟩

include hA hg hn hn' hlt hlt' hlen h2 in
/-- Lifting a successful top candidate gives an ambient transporter. -/
theorem aggnTransportLift_spec :
    ∃ (σ : Perm (Fin n)) (hσ : σ ∈ decGroup n A.1.2),
      aggnTransportLift (A, row, row') = some (encPerm n σ) ∧
      testImage ϕ (winSet m row) ⟨σ, hσ⟩ = winSet m row' := by
  obtain ⟨r, hr, hw, hmem, himg⟩ := aggnTransportTop_spec hA hg hn hn' hlt hlt' hlen h2
  obtain ⟨hd, hm, hgs, his, hi⟩ := hA
  have hnone := actPreimage_eq_none_iff hd hm hi (decPerm m r)
  rw [map_encPerm_decPerm hgs, map_encPerm_decPerm his, encPerm_decPerm hw] at hnone
  have hne : actPreimage (A, r) ≠ none := fun h => (hnone.mp h) hmem
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hne
  have hsome := actPreimage_eq_some hd hm hi (decPerm m r) (r := q)
  rw [map_encPerm_decPerm hgs, map_encPerm_decPerm his, encPerm_decPerm hw] at hsome
  obtain ⟨σ, hσ, he, himage⟩ := hsome hq
  refine ⟨σ, hσ, ?_, ?_⟩
  · simp only [aggnTransportLift, hr, Option.bind_some, hq, he]
  · change (ϕ ⟨σ, hσ⟩) '' winSet m row = _
    have heq : (ϕ ⟨σ, hσ⟩ : Perm (Fin m)) = decPerm m r := himage
    exact (congrArg (fun t : Perm (Fin m) => t '' winSet m row) heq).trans himg

/-- The complete set of possible initial transporters. -/
def AggnTransportSet {G : Subgroup (Perm (Fin n))} (ϕ : G →* Perm (Fin m))
    (T T' : Set (Fin m)) : Set (Perm (Fin n)) :=
  {σ | ∃ hσ : σ ∈ G, testImage ϕ T ⟨σ, hσ⟩ = T'}

private theorem aggnInitialCoset_eq {G : Subgroup (Perm (Fin n))}
    (ϕ : G →* Perm (Fin m)) (T T' : Set (Fin m))
    {σ : Perm (Fin n)} (hσ : σ ∈ G) (hm : testImage ϕ T ⟨σ, hσ⟩ = T') :
    σ • (bigGT ϕ T : Set (Perm (Fin n))) =
      {r | ∃ hr : r ∈ G, testImage ϕ T ⟨r, hr⟩ = T'} := by
  ext r
  constructor
  · intro hr
    obtain ⟨hG, himg⟩ := initialCoset_testImage hσ hr
    exact ⟨hG, himg.trans hm⟩
  · rintro ⟨hr, himg⟩
    apply mem_perm_smul_set.mpr
    apply mem_stabIn.mpr
    refine ⟨G.mul_mem (G.inv_mem hσ) hr, ?_⟩
    have he : (⟨σ⁻¹ * r, G.mul_mem (G.inv_mem hσ) hr⟩ : G) = ⟨σ, hσ⟩⁻¹ * ⟨r, hr⟩ := rfl
    rw [he, map_mul, map_inv, perm_mul_image]
    change (fun u => (ϕ ⟨σ, hσ⟩).symm u) '' testImage ϕ T ⟨r, hr⟩ = _
    rw [himg, ← hm]
    simp only [testImage, Set.image_image, Equiv.symm_apply_apply, Set.image_id']

include hA hg hn hn' hlt hlt' hlen h2 in
/-- The machine returns the uniquely determined least transporter in the
ambient point order. Its choice does not depend on a lift or generator list. -/
theorem aggnTransport_spec :
    ∃ r, aggnTransport (A, row, row') = some r ∧ RawPerm.WF n r ∧
      AggnPrefixMin (AggnTransportSet ϕ (winSet m row) (winSet m row')) (decPerm n r) n := by
  obtain ⟨σ, hσ, hs, hm⟩ := aggnTransportLift_spec hA hg hn hn' hlt hlt' hlen h2
  have hc := aggnCanonCoset_spec hA.1 (topStab (A, row)) (encPerm n σ)
  refine ⟨_, by simp only [aggnTransport, hs, Option.map_some], hc.1, ?_⟩
  have hK : decCoset n (some (topStab (A, row), encPerm n σ)) =
      AggnTransportSet ϕ (winSet m row) (winSet m row') := by
    rw [decCoset_some, decPerm_encPerm, topStab_bigGT_of_wf (A, row) ϕ hA hg,
      aggnInitialCoset_eq ϕ _ _ hσ hm]
    rfl
  rw [hK] at hc
  exact hc.2

end Lift

/-- Fix the initial mathematical transporter using only the transporter set. -/
noncomputable def aggnCanonTransport {n m : ℕ} {G : Subgroup (Perm (Fin n))}
    (ϕ : G →* Perm (Fin m)) (T T' : Set (Fin m)) : Option (Perm (Fin n)) := by
  classical
  exact if (AggnTransportSet ϕ T T').Nonempty then
    some (aggnLeastPerm (AggnTransportSet ϕ T T')) else none

/-- This fixes only the allowed choice on line 01 of Proposition 13.1.11. -/
theorem aggnCanonTransport_spec {n m : ℕ} {G : Subgroup (Perm (Fin n))}
    (ϕ : G →* Perm (Fin m)) (T T' : Set (Fin m)) :
    StrongTransporterSpec ϕ T T' (aggnCanonTransport ϕ T T') := by
  classical
  unfold aggnCanonTransport
  split
  · rename_i h
    obtain ⟨σ, hσ, hm⟩ := h
    have he : σ • (bigGT ϕ T : Set (Perm (Fin n))) = AggnTransportSet ϕ T T' :=
      aggnInitialCoset_eq ϕ T T' hσ hm
    have hmem := (aggnLeastPerm_coset (bigGT ϕ T) σ).1
    rw [he] at hmem
    exact hmem
  · rename_i h
    rintro ⟨σ, hm⟩
    exact h ⟨σ, σ.2, hm⟩

/-- The executable and mathematical initial transporters agree exactly. -/
theorem aggnTransport_eq_canonical {n m : ℕ} {A : RawAction} {row row' : List ℕ}
    {ϕ : decGroup n A.1.2 →* Perm (Fin m)}
    (hA : RawAction.WF n m A ϕ) (hg : IsGiantRep ϕ)
    (hn : row.Nodup) (hn' : row'.Nodup)
    (hlt : ∀ u ∈ row, u < m) (hlt' : ∀ u ∈ row', u < m)
    (hlen : row.length = row'.length) (h2 : 2 ≤ row.length) :
    aggnTransport (A, row, row') =
      (aggnCanonTransport ϕ (winSet m row) (winSet m row')).map (encPerm n) := by
  classical
  obtain ⟨r, hr, hw, hm⟩ := aggnTransport_spec hA hg hn hn' hlt hlt' hlen h2
  have hne : (AggnTransportSet ϕ (winSet m row) (winSet m row')).Nonempty := ⟨_, hm.1⟩
  rw [aggnCanonTransport, if_pos hne, Option.map_some, aggnLeastPerm_eq hm, encPerm_decPerm hw, hr]

end Algo
