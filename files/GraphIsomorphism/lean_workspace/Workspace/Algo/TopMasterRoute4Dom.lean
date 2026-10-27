/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 15, lines 4c–4d with a dominant color class, on the hinted node carrier: route 4 of
the master recursion (`Algo.MasterRoute4Dom`).
-/
import Workspace.Algo.TopMasterRoute4Hint
import Workspace.Master.AlignHintedCall

/-!
# Route 4 with a dominant class on the hinted node carrier

At a good node of route `4` where line 6 of Procedure Align finds a dominant color class, the
hinted node carrier (`Algo.masterFinalOps`) runs the carrier `Algo.line4dDomOps` of lines 7–11
with the hint routine `Algo.line4dDomHint` of line 11 on its children. This file proves that it
walks the lift of the Master's round of Procedure Align (`Babai.Line4cdData`, built from the
machine's computation by the Section 13 track, `Algo.line4dDomOps_match_built`), with good
children that make the progress of Sec. 11.4:

* a call without a hint has at most `4|Δ|/5` points (Eq. (72));
* the hinted call of case 3 (the dominant orbit of `G*`) carries a hint with its meaning
  (`Algo.alignDomHintAt_good`), its window is at most the node's, and its Johnson parameter
  `m*` is at most half of the node's (Eq. (73)).

The steps:

* `Algo.masterAdmittedRound_checked_matchH`: `Algo.masterAdmittedRound_checked_match` for a
  carrier with hints, from a match with a condition at every step (`Algo.LoopMatchS`);
* `Algo.masterCheckedCall_liftedCoset`: the call the carrier makes for the dominant-orbit
  call has as its group the preimage of `G*` and as its window the image of the orbit;
* `Algo.line4dDomOpsH_matchG`: the carrier `line4dDomOps` with the hints of `H4`, at a node;
* `Algo.masterNodeH_route4Dom_treeOK`: the same through the layers of the node carrier, as a
  tree with `Algo.MasterNodeTreeOK`;
* `Algo.masterRoute4Dom_final`: the obligation `Algo.MasterRoute4Dom` of
  `Algo.siWorkspaceRoutine_of_openRoutes`, with `H4 = Algo.line4dDomHint`;
* `Algo.siWorkspaceRoutine_of_route5`: the wrapper with route 4 discharged.
-/
set_option synthInstance.maxSize 4096

namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Pointwise

/-! ## Admission with hints -/

section CheckedH

variable {ι ω : Type} (a b : ℕ) {R : Round ι ω RawCoset} {F : MasterOps ω}
    {H : (RawMasterSI × ℕ × ω) × RawMasterSI → Option RawMasterHint}
    {n : ℕ} {I : ι} {p : RawMasterSI} (hn : masterDegree p = n)
    (read : ι → RawWinSI) (decI : ι → SIInstance (Fin n) ℕ)
    (hread : ∀ j s J, R.child (I, j, s) = some J → decI J = decWinSI n (read J))
    (hw : F.width p = R.width I)
    (hc : ∀ j s, F.child (p, j, s) =
      (R.child (I, j, s)).map (fun J => masterCheckedCall (p.1.2.2.2.1, read J)))
    (hu : ∀ j s A, F.combine (p, j, s, A) = R.combine (I, j, s, A))
    (hf : ∀ s, F.finish (p, s) = R.finish (I, s)) (Cg : RawMasterSI → Prop)

/-- **The condition at a step of a checked round with hints**: the call the step proposes,
read on the node's domain with the hint `H` attaches, is admitted at the node and satisfies
the condition `Cg` on the children. -/
def MasterCheckedStepH (a b : ℕ) (H : (RawMasterSI × ℕ × ω) × RawMasterSI → Option RawMasterHint)
    (read : ι → RawWinSI) (Cg : RawMasterSI → Prop) (p : RawMasterSI) (j : ℕ) (s : ω) (J : ι) :
    Prop :=
  masterAdmitChild a b (p, some (masterLiftHinted H p j s (read J))) =
      some (masterLiftHinted H p j s (read J)) ∧ Cg (masterLiftHinted H p j s (read J))

include hn hread hw hc hu hf in
/-- **`Algo.masterAdmittedRound_checked_match` with hints.** A fold of `R` that walks `T`, with
the condition `Algo.MasterCheckedStepH` at every step, is a fold of the admitted carrier `F`
with the hints of `H` that walks `T`, every child of which satisfies `Cg`. -/
theorem masterAdmittedRound_checked_matchH :
    ∀ {w j : ℕ} {s : ω} {T : SIReduction (Fin n) ℕ (Set (Perm (Fin n)))},
      LoopMatchS R (MasterCheckedStepH a b H read Cg p) decI (decCoset n) I w j s T →
      (∀ J ∈ T.calls, MasterCallLetters (2 * n + 1) J) →
      LoopMatchG (masterAdmittedRound a b (F.withHint H)) Cg (fun J => decWinSI n J.1)
        (fun _ => decCoset n) p w j s T := by
  intro w j s T h
  induction h with
  | done w j s A hch ha =>
    intro _
    refine .done w j s A ?_ ?_
    · change masterGuardedChild a b _ (p, j, s) = none
      unfold masterGuardedChild
      split_ifs
      · rw [MasterOps.withHint_child, hc, hch]
        rfl
      · rfl
    · change decCoset n (F.finish (p, s)) = A
      rw [hf]
      exact ha
  | call w j s J k hch hC hnext ih =>
    intro hL
    have hLJ : MasterCallLetters (2 * n + 1) (decI J) := hL _ (by simp [SIReduction.calls])
    have hdJ := hread j s J hch
    have hj : j < R.width I := by
      by_contra hj
      have hnone := R.child_eq_none I j s (Nat.le_of_not_gt hj)
      rw [hch] at hnone
      contradiction
    have hchild : masterGuardedChild a b (F.withHint H) (p, j, s) =
        some (masterLiftHinted H p j s (read J)) := by
      unfold masterGuardedChild
      rw [if_pos (by rw [MasterOps.withHint_width, hw]; exact hj), MasterOps.withHint_child, hc,
        hch, Option.map_some, Option.map_some]
      exact hC.1
    have hDV : decWinSI n (masterLiftHinted H p j s (read J)).1 = decI J := by
      rw [masterLiftHinted, masterAttachHint_fst, masterCheckedCall_decode hn (read J)
        (hdJ ▸ hLJ), hdJ]
    rw [← hDV]
    refine .call w j s _ _ hchild hC.2 fun A hA => ?_
    have hcomb : (masterAdmittedRound a b (F.withHint H)).combine (p, j, s, A) =
        R.combine (I, j, s, A) := hu j s A
    rw [hcomb, hDV]
    refine ih A (hDV ▸ hA) fun K hK => hL K ?_
    simp only [SIReduction.calls, List.mem_cons]
    exact Or.inr hK

end CheckedH

/-! ## The hinted call of line 4d -/

section Transport

open MulAction

/-- **The hinted call, lifted to the node's domain and read back.** Let `K` be a call on the
window positions whose candidate set is a coset `σ H` of a group `H` and whose window is an
orbit `u^H`, and let the raw call `V` decode to its lift (`Algo.topwInstance`) in the node's
group `G`. Then the call `W' = masterCheckedCall (x, V)` the carrier makes has as its group the
full preimage of `H` in `G` (under the restriction to the window), and as its window the image
of `u^H` in the node's domain. These are the hypotheses `hKW` and `hwinW` of
`Algo.alignDomHintAt_good`. -/
theorem masterCheckedCall_liftedCoset {n : ℕ} {Δ : List ℕ} (hnd : Δ.Nodup)
    (hlt : ∀ u ∈ Δ, u < n) {G : Subgroup (Perm (Fin n))} (hinv : IsInvariant G (winSet n Δ))
    (xs : Fin n → ℕ) {H : Subgroup (Perm (Fin Δ.length))} {σ : Perm (Fin Δ.length)}
    {u : Fin Δ.length} {K : SIInstance (Fin Δ.length) ℕ}
    (hKK : K.K = σ • (H : Set (Perm (Fin Δ.length)))) (hKΔ : K.Δ = orbit H u)
    {x : RawStr} (hx : x.length = n) {V : RawWinSI}
    (hV : decWinSI n V = topwInstance Δ hnd hlt G hinv xs K)
    (hL : MasterCallLetters (2 * n + 1) (decWinSI n V)) :
    (∀ g, g ∈ decGroup n (masterCheckedCall (x, V)).1.2.1 ↔
      ∃ hg : g ∈ G, winRestrictHom n Δ hnd hlt G hinv ⟨g, hg⟩ ∈ H) ∧
    ∀ z : Fin n, z ∈ winSet n (masterCheckedCall (x, V)).1.1 ↔
      ∃ k ∈ orbit H u, ((winEquiv n Δ hnd hlt k : ↥(winSet n Δ)) : Fin n) = z := by
  have hD := masterCheckedCall_decode hx V hL
  rw [hV] at hD
  set W' := (masterCheckedCall (x, V)).1 with hW'
  have hΔ : winSet n W'.1 =
      (fun i : Fin Δ.length => ((winEquiv n Δ hnd hlt i : ↥(winSet n Δ)) : Fin n)) '' K.Δ :=
    congrArg SIInstance.Δ hD
  have hK : decCoset n (some (W'.2.1, W'.2.2.1)) =
      topwPreimageSet Δ hnd hlt G hinv K.K := congrArg SIInstance.K hD
  refine ⟨fun g => ?_, fun z => ?_⟩
  · set ρ := winRestrictHom n Δ hnd hlt G hinv
    set τ := decPerm n W'.2.2.1
    have hmemC : ∀ y, y ∈ decCoset n (some (W'.2.1, W'.2.2.1)) ↔
        ∃ hy : y ∈ G, σ⁻¹ * ρ ⟨y, hy⟩ ∈ H := by
      intro y
      rw [hK, topwPreimageSet, Set.mem_setOf_eq, hKK]
      simp only [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, SetLike.mem_coe]
      exact Iff.rfl
    have hτ : τ ∈ decCoset n (some (W'.2.1, W'.2.2.1)) :=
      ⟨1, one_mem _, by simp [τ]⟩
    obtain ⟨hτG, hτH⟩ := (hmemC τ).1 hτ
    have hρmul : ∀ (a b : Perm (Fin n)) (ha : a ∈ G) (hb : b ∈ G),
        ρ ⟨a * b, G.mul_mem ha hb⟩ = ρ ⟨a, ha⟩ * ρ ⟨b, hb⟩ := by
      intro a b ha hb
      rw [← map_mul]
      rfl
    constructor
    · intro hg
      have hτg : τ * g ∈ decCoset n (some (W'.2.1, W'.2.2.1)) := ⟨g, hg, rfl⟩
      obtain ⟨hG', hH'⟩ := (hmemC _).1 hτg
      have hgG : g ∈ G := by
        have := G.mul_mem (G.inv_mem hτG) hG'
        simpa using this
      refine ⟨hgG, ?_⟩
      have he : ρ ⟨τ * g, hG'⟩ = ρ ⟨τ, hτG⟩ * ρ ⟨g, hgG⟩ := hρmul τ g hτG hgG
      have := H.mul_mem (H.inv_mem hτH) hH'
      rw [he] at this
      simpa [mul_assoc] using this
    · rintro ⟨hgG, hgH⟩
      have hτg : τ * g ∈ decCoset n (some (W'.2.1, W'.2.2.1)) := by
        refine (hmemC _).2 ⟨G.mul_mem hτG hgG, ?_⟩
        rw [hρmul τ g hτG hgG, ← mul_assoc]
        exact H.mul_mem hτH hgH
      obtain ⟨g', hg', he⟩ := hτg
      rw [mul_left_cancel he]
      exact hg'
  · rw [hΔ, hKΔ]
    simp only [Set.mem_image]

end Transport


section Hinted

variable (c tt dd : ℕ)

variable {c tt dd}

set_option maxHeartbeats 1000000 in
/-- **Section 15, line 4d with a dominant color class, on the hinted carrier, at a node.** At a
good node `(W, h)` of route `4` where line 6 of Procedure Align finds a dominant class, there
is a round of Procedure Align of the Master (`Babai.Line4cdData`, built by the Section 13
track, `Algo.line4dDomOps_match_built`) whose lift the carrier `Algo.line4dDomOps`, with the
hints of `Algo.line4dDomHint`, walks; every child it proposes is admitted, good, and makes the
progress of Sec. 11.4:

* in case 1 of the repair, and in cases 2–3 at a call on at most `2|Δ|/3` points, the child
  has no hint and at most `4|Δ|/5` points (Eq. (72));
* at a call on more than `2|Δ|/3` points in case 3, the child is the dominant-orbit call and
  carries the hint of line 11 (`Algo.alignDomHintAt_good`): it is the dominant-orbit call
  (`Babai.Line4cdData.large_call_spec`, from the bound `2n/3` on the other color classes,
  `Babai.three_mul_ncard_omegaColorClass_le_of_ne_dom`), read on the node by
  `Algo.masterCheckedCall_liftedCoset`; Johnson parameter `m* ≤ m/2` (Eq. (73)). -/
theorem line4dDomOpsH_matchG {a b n : ℕ} (hb : Line4cBounds c tt dd)
    (hcap : masterCameronChildBound n ≤ masterInputCap a b n)
    {W : RawWinSI} {h : RawMasterHint} (hW : AggnCheckedWindowWF n W)
    (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1)) (hg : MasterHintGood (W, h))
    (hr : masterHintRoute (W, h) = 4)
    (hd : masterHasDom c tt dd ((W, some h) : RawMasterSI) = true) :
    ∃ (par : ℕ) (D : Line4cdData (Fin W.1.length) ℕ
        (decGroup W.1.length (masterHintTop ((W, h) : MasterHintInput)).1.1.2)
        (decStrN W.1.length (masterHintTop ((W, h) : MasterHintInput)).2.1)
        (decStrN W.1.length (masterHintTop ((W, h) : MasterHintInput)).2.2) par
        (line4cdCost (line4dQ c tt dd) c923 (Fintype.card (Fin W.1.length)))),
      LoopMatchG (masterAdmittedRound a b
          ((line4dDomOps c tt dd).withHint (line4dDomHint c tt dd)))
        (fun J => MasterNodeGood n J ∧ MasterStepProgress (W, some h) J)
        (fun J => decWinSI n J.1) (fun _ => decCoset n) (W, some h)
        ((line4dDomOps c tt dd).width (W, some h)) 0
        ((line4dDomOps c tt dd).init (W, some h))
        ((top4wTree W.1 hW.1 hW.2.1 (decGroup n W.2.1) hinv (decStrN n W.2.2.2.1)
          D.shape.red).bind (fun A => .done (decPerm n W.2.2.1 • A))) := by
  obtain ⟨m, ϕ, B', hB, hp, hG, hϕ, -, -, -, -, -, h64⟩ := id hg
  have hx := hW.2.2.2.2.2.1
  have hy := hW.2.2.2.2.2.2
  have hgs := hW.2.2.1
  have hnd := hW.1
  have hlt := hW.2.1
  have h64' : 64 ≤ W.1.length := h64
  have hΔn : W.1.length ≤ n := length_le_of_nodup_lt hnd hlt
  obtain ⟨D, Dd, hdom, hsm, hlg, htl, hGs, hDw⟩ := line4dDomOps_match_built (p := ((W, h) : MasterHintInput))
    hx hy hgs hnd hlt hinv hp hG hϕ h64 hr hb a b hd
  refine ⟨m, D, ?_⟩
  set hdr := line4dDomHdr c tt dd ((W, h) : MasterHintInput) with hhdr
  have hxl : (masterHintTop ((W, h) : MasterHintInput)).2.1.length = W.1.length :=
    length_rawRestrictStr _ _
  have hyl : (masterHintTop ((W, h) : MasterHintInput)).2.2.length = W.1.length :=
    length_rawRestrictStr _ _
  -- stretch 3 on the window walks the Master's round, in both cases
  have hin : LoopMatch line4dDomInnerRound (line4dInnerDecode W.1.length)
      (decCoset W.1.length) (hdr, none) (l57Calls hdr) 0 (l57Init hdr) D.shape.red := by
    cases hs : l57Small hdr
    · exact line4dDomInner_loopMatch_large (hlg hs).2.1 hs hxl
    · exact line4dDomInner_loopMatch_small (hsm hs).1 hs hxl
  have hgrp := masterLine4b_group (p := ((W, h) : MasterHintInput)) hgs hnd hlt hinv
  have hK' : ∀ J ∈ D.shape.red.calls, J.K ⊆
      ((winRestrictHom n W.1 hnd hlt (decGroup n W.2.1) hinv).range :
        Set (Perm (Fin W.1.length))) := by
    rw [← hgrp]
    exact D.calls_K
  have hR : D.shape.red.run ⊆
      ((winRestrictHom n W.1 hnd hlt (decGroup n W.2.1) hinv).range :
        Set (Perm (Fin W.1.length))) := by
    rw [D.run_red, ← hgrp]
    exact fun _ h => h.1
  have hlift := line4dDomRound_lift c tt dd (q := ((W, h) : MasterHintInput))
    (gens := W.2.1.map (decPerm n)) (map_encPerm_decPerm hgs).symm hx.1 hnd hlt hinv hin hK' hR
  -- the calls of the Master's round have the letters of the node's strings
  obtain ⟨hix, hiy⟩ := masterHintTop_letters hx hy hnd hlt (p := ((W, h) : MasterHintInput))
  have hlet0 : ∀ K ∈ D.shape.red.calls, MasterCallLetters (2 * n + 1) K := by
    cases hs : l57Small hdr
    · exact alignShape_letters_of_dom_large D.shape D.head_not_mem hdom (hlg hs).1 hix hiy
    · exact alignShape_letters_of_dom_small D.shape D.head_not_mem hdom (hsm hs).1.small hix hiy
  have hxx := (masterStrWF_iff hx.1).mp hx
  have hcos := top4wTree_calls_isCosetInstance hnd hlt hinv (decStrN n W.2.2.2.1) D.shape.red
    (by rw [← hgrp]; exact D.calls_coset)
  have hcallsT : (top4wTree W.1 hnd hlt (decGroup n W.2.1) hinv (decStrN n W.2.2.2.1)
      D.shape.red).calls =
      D.shape.red.calls.map (topwInstance W.1 hnd hlt (decGroup n W.2.1) hinv
        (decStrN n W.2.2.2.1)) := by
    simp only [top4wTree, SIReduction.calls_bind, SIReduction.calls_done, List.append_nil]
    exact calls_topwReduction hnd hlt hinv _ _ hK'
  set T := (top4wTree W.1 hnd hlt (decGroup n W.2.1) hinv (decStrN n W.2.2.2.1)
    D.shape.red).bind (fun A => .done (decPerm n W.2.2.1 • A)) with hT
  have hcallsT' : ∀ J ∈ T.calls, ∃ K ∈ D.shape.red.calls, J =
      topwInstance W.1 hnd hlt (decGroup n W.2.1) hinv (decStrN n W.2.2.2.1) K := by
    intro J hJ
    simp only [hT, SIReduction.calls_bind, SIReduction.calls_done, List.append_nil,
      hcallsT] at hJ
    obtain ⟨K, hKm, rfl⟩ := List.mem_map.mp hJ
    exact ⟨K, hKm, rfl⟩
  have hLT : ∀ J ∈ T.calls, MasterCallLetters (2 * n + 1) J := by
    intro J hJ
    obtain ⟨K, hKm, rfl⟩ := hcallsT' J hJ
    exact masterLetters_topwInstance W.1 hnd hlt _ hinv _ hxx K (hlet0 K hKm)
  have hcosT : ∀ J ∈ T.calls, IsCosetInstance (decGroup n W.2.1) J := by
    intro J hJ
    simp only [hT, SIReduction.calls_bind, SIReduction.calls_done, List.append_nil] at hJ
    exact hcos J hJ
  -- the facts of case 3 that `Algo.alignDomHintAt_good` asks
  obtain ⟨inst, hKc⟩ := exists_isCatAction_splitOutcomes (Γ := Fin m)
  letI := inst
  obtain ⟨hvl, idc, -, hm217, hmn, -⟩ :=
    masterLine4c_facts ((W, h) : MasterHintInput) hp hG hϕ h64 hr
  obtain ⟨-, -, -, -, -, -, hgoodV⟩ :=
    masterLine4c_versions ((W, h) : MasterHintInput) hp hG hϕ h64 hr hb hxl hyl hKc
  obtain ⟨X', hXdec, hXmem⟩ :=
    line4dFixed_spec ((W, h) : MasterHintInput) hp hG hϕ h64 hr hb hxl hyl hKc
  have hZ := hgoodV _ X' hXmem
  have hhd1 : alignRHasDom (alignRColorOf ((masterHintTop ((W, h) : MasterHintInput)).1,
      line4dFixed c tt dd ((W, h) : MasterHintInput))) = true := (Bool.and_eq_true_iff.1 hd).1
  have hnt : 2 ≤ alignRMs ((masterHintTop ((W, h) : MasterHintInput)).1,
      line4dFixed c tt dd ((W, h) : MasterHintInput)) :=
    of_decide_eq_true (Bool.and_eq_true_iff.1 hd).2
  have hS := LoopMatch.toS (C := MasterCheckedStepH a b (line4dDomHint c tt dd) line4dNodeRead
      (fun J => MasterNodeGood n J ∧ MasterStepProgress (W, some h) J) (W, some h))
    (fun K => K ∈ T.calls) ?_ hlift (fun K hK => hK)
  · exact masterAdmittedRound_checked_matchH a b (R := line4dDomRound c tt dd)
      (F := line4dDomOps c tt dd) (H := line4dDomHint c tt dd)
      (I := (((W, h) : MasterHintInput), none)) (p := (W, some h)) hx.1 line4dNodeRead
      (line4dDecode n) (fun _ _ _ _ => rfl) rfl (fun _ _ => rfl) (fun _ _ _ => rfl)
      (fun _ => rfl) _ hS hLT
  intro j s J _ hJT
  obtain ⟨K, hKm, hKeq⟩ := hcallsT' _ hJT
  have hdec : decWinSI n (line4dNodeRead J) = line4dDecode n J := rfl
  have hL : MasterCallLetters (2 * n + 1) (decWinSI n (line4dNodeRead J)) := hLT _ hJT
  have hC : ∃ G : Subgroup (Perm (Fin n)), IsCosetInstance G (decWinSI n (line4dNodeRead J)) :=
    ⟨_, hcosT _ hJT⟩
  have hwK : (decWinSI n (line4dNodeRead J)).windowSize = K.windowSize := by
    rw [hdec, hKeq, topwInstance_windowSize]
  have hwin : (decWinSI n (line4dNodeRead J)).windowSize ≤ W.1.length := by
    rw [hwK]
    exact (Set.ncard_le_card _).trans (by simp)
  refine masterLiftStepOK_of_hintStep hW hg hcap j s (line4dNodeRead J) ?_ hL hC hwin
  have hW' : (masterCheckedCall (W.2.2.2.1, line4dNodeRead J)).1.1.length = K.windowSize :=
    (masterCheckedCall_window hx.1 _).trans hwK
  have htest : line4dDomHintTest c tt dd ((((W, some h) : RawMasterSI), j, s),
      masterCheckedCall (W.2.2.2.1, line4dNodeRead J)) =
      (!l57Small hdr && decide (2 * W.1.length < 3 * K.windowSize)) := by
    rw [← hW']
    rfl
  unfold MasterHintStepOK line4dDomHint
  split_ifs with ht
  · -- the hinted call: case 3 and more than `2|Δ|/3` points
    rw [htest, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at ht
    obtain ⟨hs, hbigK⟩ := ht
    -- it is the dominant-orbit call (`Babai.Line4cdData.large_call_spec`), read on the node
    obtain ⟨-, u, hu, hKΔ, -, σ, hKK⟩ :=
      D.large_call_spec hdom htl hKm (by rw [Fintype.card_fin]; exact hbigK)
    rw [← hGs] at hKΔ hKK
    have hu' : u ∈ winSet W.1.length (alignRDomWindow
        (alignRColorOf ((masterHintTop ((W, h) : MasterHintInput)).1,
          line4dFixed c tt dd ((W, h) : MasterHintInput)),
        alignRDomColor (alignRColorOf ((masterHintTop ((W, h) : MasterHintInput)).1,
          line4dFixed c tt dd ((W, h) : MasterHintInput))))) := by
      rw [hDw]; exact hu
    obtain ⟨hKW, hwinW⟩ := masterCheckedCall_liftedCoset hnd hlt hinv (decStrN n W.2.2.2.1)
      hKK hKΔ hx.1 (hdec.trans hKeq) hL
    have hCW := aggnCheckedWindow_wf W.2.2.2.1 (line4dNodeRead J)
    rw [hx.1] at hCW
    have hlarge : alignRLarge ((masterHintTop ((W, h) : MasterHintInput)).1,
        line4dFixed c tt dd ((W, h) : MasterHintInput)) = true := by
      have hs' : alignRSmall ((masterHintTop ((W, h) : MasterHintInput)).1,
          line4dFixed c tt dd ((W, h) : MasterHintInput)) = false := by
        have h' := hs
        rw [l57Small_eq_of_two_le (h := hdr) hnt] at h'
        exact h'
      unfold alignRSmall at hs'
      unfold alignRLarge
      rw [hhd1] at hs' ⊢
      simpa using hs'
    have hLP := ((alignRLarge_iff (alignPairG1_wf hp.1) hp.1).1 hlarge).2
    have hbig : 2 * W.1.length < 3 * (masterCheckedCall (W.2.2.2.1, line4dNodeRead J)).1.1.length := by
      rw [hW']
      exact hbigK
    obtain ⟨hG', hlen, h2m, hlab⟩ := alignDomHintAt_good hnd hlt hinv hgrp hp hG hϕ hvl
      idc.tPointOf_eq hKc hXdec hZ hm217 hmn hhd1 hnt hLP hCW.1 hCW.2.1 hCW.2.2.1 hKW hu' hwinW
      hbig
    have hpm : h.1.1.length = m := hp.2.1
    refine ⟨hG', fun i hi => ?_, ?_⟩
    · have := hlab i hi
      have hmn' : m ≤ W.1.length := hmn
      omega
    · have h2 := le_of_eq_of_le (congrArg (fun x => 2 * x) hlen) h2m
      change 2 * _ ≤ h.1.1.length
      rw [hpm]
      exact h2
  · -- no hint: at most `4|Δ|/5` points
    change 5 * (decWinSI n (line4dNodeRead J)).windowSize ≤ 4 * W.1.length
    rw [hwK]
    rw [htest] at ht
    cases hs : l57Small hdr
    · rw [hs] at ht
      simp only [Bool.not_false, Bool.true_and, decide_eq_true_eq, not_lt] at ht
      omega
    · have h5 := line4cdData_five_mul_windowSize_of_noHint D
        (alignShape_hint_eq_none_of_dom_small D.shape hdom (hsm hs).1.small) K hKm
      exact h5

end Hinted

/-! ## Through the layers of the node carrier -/

section Layers

variable {cameron : RawGens × List ℕ → Option RawCameron} {e f u v c tt dd : ℕ}
    {c' b' t d dc dp E : ℕ}
    {H5 : (RawMasterSI × ℕ × AggnL57GState) × RawMasterSI → Option RawMasterHint}

set_option maxHeartbeats 1000000 in
/-- **Section 15, route `4` with a dominant class, in the hinted node carrier.** At a good node
of route `4` where line 6 of Procedure Align finds a dominant class, the hinted node carrier
with `GD = Algo.line4dDomOps` and `H4 = Algo.line4dDomHint` walks a tree with
`Algo.MasterNodeTreeOK` for the cost `Algo.masterRoute4Cost` (`Algo.line4dDomOpsH_matchG`,
through the selectors of the carrier: line 1 fails, routes 1–3 fail, route 4 holds, and line 6
finds a dominant class). -/
theorem masterNodeH_route4Dom_treeOK {a b n : ℕ} (hb : Line4cBounds c tt dd)
    (hcap : masterCameronChildBound n ≤ masterInputCap a b n)
    {W : RawWinSI} {h : RawMasterHint} (hg : MasterNodeGood n (W, some h))
    (hr : masterHintRoute (W, h) = 4)
    (hd : masterHasDom c tt dd ((W, some h) : RawMasterSI) = true) :
    ∃ T, MasterNodeTreeOK (masterAdmittedRound a b
      (masterNodeHOps masterLine1B masterLine1C₀ cameron e f u v c tt dd
        (line4dDomOps c tt dd) default c' b' t d dc dp E (line4dDomHint c tt dd) H5))
      n (masterRoute4Cost c tt dd) (W, some h) T := by
  obtain ⟨⟨-, hW, hinv⟩, hgood⟩ := hg
  have hgh := hgood h rfl
  obtain ⟨par, D, h1⟩ := line4dDomOpsH_matchG hb hcap hW hinv hgh hr hd (a := a) (b := b)
  have h2 := masterPairIte_matchG_pos (sel := masterHasDom c tt dd)
    (F := (line4dDomOps c tt dd).withHint (line4dDomHint c tt dd)) (G := line4dOps c tt dd)
    (dS := (default : ADState)) (dT := default) a b hd h1
  have h3 := masterPairIte_matchG_pos (sel := masterRouteAt 4)
    (F := masterLine4cdOps c tt dd ((line4dDomOps c tt dd).withHint (line4dDomHint c tt dd))
      default)
    (G := (masterL57Ops c' b' t d dc dp e f E).withHint H5)
    (dS := ((default : ADState), default)) (dT := default)
    a b (masterRouteAt_true (p := (W, h)) hr) h2
  have h4 := masterPairIte_matchG_neg (sel := masterRouteAt 3) (F := master4bOps e f u v)
    (dS := default) (dT := (((default : ADState), default), default))
    a b (masterRouteAt_false (p := (W, h)) (by omega)) h3
  have h5 := masterPairIte_matchG_neg (sel := masterRouteAt 2)
    (F := masterLeafOps primitiveWindowLeaf) (dS := masterCamFoldEmbed none)
    (dT := (default, ((default : ADState), default), default))
    a b (masterRouteAt_false (p := (W, h)) (by omega)) h4
  have h6 := masterPairIte_matchG_neg (sel := masterRouteAt 1)
    (F := masterDescPreparedOps 3) (dS := masterCamFoldEmbed none)
    (dT := (masterCamFoldEmbed none, default, ((default : ADState), default), default))
    a b (masterRouteAt_false (p := (W, h)) (by omega)) h5
  have hl1 : masterIsLine1 ((W, some h) : RawMasterSI) = false := by
    cases hq : masterIsLine1 ((W, some h) : RawMasterSI)
    · rfl
    · exact absurd ((masterIsLine1_iff _).mp hq) (by simp)
  have h7 := masterPairIte_matchG_neg (sel := masterIsLine1)
    (F := masterLine1Ops masterLine1B masterLine1C₀ cameron)
    (dS := masterCamFoldEmbed none)
    (dT := (masterCamFoldEmbed none, masterCamFoldEmbed none, default,
      ((default : ADState), default), default))
    a b hl1 h6
  refine ⟨_, masterRoute4_treeOK_of_matchG hW hinv D ?_ h7⟩
  rw [Fintype.card_fin]
  rfl

end Layers

/-! ## The obligation of route 4 of `Algo.siWorkspaceRoutine_of_openRoutes` -/

section Final

/-- **The obligation `h4` of `Algo.siWorkspaceRoutine_of_openRoutes`, with
`H4 = Algo.line4dDomHint`**, for any call bound above `Algo.masterRoute4Cost`. -/
theorem masterRoute4Dom_final {c c' b' t d dc dp : ℕ}
    {H5 : (RawMasterSI × ℕ × AggnL57GState) × RawMasterSI → Option RawMasterHint}
    {q : ℕ → ℕ}
    (hq : ∀ k, masterRoute4Cost c (masterLine4TT c) (masterLine4DD c) k ≤ q k) (n : ℕ) :
    MasterRoute4Dom (masterAdmittedRound masterCapA masterCapB
      (masterFinalOps c c' b' t d dc dp
        (line4dDomHint c (masterLine4TT c) (masterLine4DD c)) H5))
      n q c (masterLine4TT c) (masterLine4DD c) := by
  intro W h hg _ hr hd
  obtain ⟨T, hT⟩ := masterNodeH_route4Dom_treeOK (cameron := masterCameron) (e := masterTopE)
    (f := masterTopF) (u := masterTopU) (v := masterTopV) (c' := c') (b' := b') (t := t)
    (d := d) (dc := dc) (dp := dp) (E := masterL57E c' b' t d dc dp) (H5 := H5)
    (masterLine4_spec c) (masterCap_spec n) hg hr hd
  exact ⟨T, hT.mono_q hq⟩

/-- A supply of route 5 for a call bound is a supply for any larger bound. -/
theorem MasterL57SupplyH.mono_q {c' b' t d dc dp e f n : ℕ} {q q' : ℕ → ℕ}
    {H5 : (RawMasterSI × ℕ × AggnL57GState) × RawMasterSI → Option RawMasterHint}
    (hS : MasterL57SupplyH c' b' t d dc dp e f n q H5) (hq : ∀ k, q k ≤ q' k) :
    MasterL57SupplyH c' b' t d dc dp e f n q' H5 := by
  intro W h hg hr
  obtain ⟨T₀, hm, hK, hcos, hrun, hlet, hlen⟩ := hS W h hg hr
  exact ⟨T₀, hm, hK, hcos, hrun, hlet, hlen.trans (hq _)⟩

set_option synthInstance.maxSize 4096 in
/-- **Theorem 1.1.1 on the RAM, from the supply of route 5.** `Algo.siWorkspaceRoutine_of_openRoutes` with `H4 = Algo.line4dDomHint`, its route-4
obligation discharged by `Algo.masterRoute4Dom_final`; what is left is the supply of lines 5–7
(`Algo.MasterL57SupplyH`). -/
theorem siWorkspaceRoutine_of_route5 {c c' b' t d dc dp : ℕ}
    {H5 : (RawMasterSI × ℕ × AggnL57GState) × RawMasterSI → Option RawMasterHint}
    (hH5 : QuasiFun H5) {q5 : ℕ → ℕ} (hq5 : Monotone q5) (hq : QuasiPolyBound q5)
    (h5 : ∀ n, MasterL57SupplyH c' b' t d dc dp masterTopE masterTopF n q5 H5) :
    SIWorkspaceRoutine :=
  siWorkspaceRoutine_of_openRoutes (quasiFun_line4dDomHint _ _ _) hH5
    (q45 := fun k => masterRoute4Cost c (masterLine4TT c) (masterLine4DD c) k + q5 k)
    ((masterRoute4Cost_mono _ _ _).add hq5) ((quasiPolyBound_masterRoute4Cost _ _ _).add hq)
    (fun n => masterRoute4Dom_final (fun _ => Nat.le_add_right _ _) n)
    (fun n => (h5 n).mono_q fun _ => Nat.le_add_left _ _)

end Final

end Algo
