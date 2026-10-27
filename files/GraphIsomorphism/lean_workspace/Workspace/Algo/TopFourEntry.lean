import Workspace.Algo.TopFourAlignmentRAM

/-! # Preparing the supplied alignment
The target is acted on by the inverse aligning permutation, as in
Corollary 12.0.10. The raw permutation is normalized before it is stored.
The class-size guard compares the two supplied repetition-free lists.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Pointwise

 def top4aTarget (p : List ℕ × RawPerm × RawStr) : RawStr :=
  fixStr (p.1, rawStrAct (rawInv (normPerm (p.1, p.2.1)), fixStr (p.1, p.2.2)))

 theorem top4aTarget_length (p : List ℕ × RawPerm × RawStr) : (top4aTarget p).length = p.1.length :=
  length_fixStr _

 theorem top4aTarget_spec {n : ℕ} {dom : List ℕ} (hd : dom.length = n) (α : RawPerm) (y : RawStr) :
    decStrN n (top4aTarget (dom, α, y)) = strAct (decStrN n y) (decPerm n α)⁻¹ := by
  have hf : fixStr (dom, y) = encStrN (decStrN n y) := by
    rw [← decStrN_fixStr hd y]
    exact (encStrN_decStrN ((length_fixStr _).trans hd)).symm
  rw [top4aTarget, decStrN_fixStr hd, normPerm_eq_enc hd, rawInv_encPerm, hf,
    rawStrAct_encStrN, decStrN_encStrN]

 theorem polyFun_top4aTarget : PolyFun top4aTarget := by
  have hd : PolyFun (fun p : List ℕ × RawPerm × RawStr => p.1) := polyFun_fst
  have hα := ((hd.pair (polyFun_snd.comp polyFun_fst)).comp polyFun_normPerm).comp polyFun_rawInv
  have hy := (hd.pair (polyFun_snd.comp polyFun_snd)).comp polyFun_fixStr
  exact (hd.pair ((hα.pair hy).comp polyFun_rawStrAct)).comp polyFun_fixStr

 theorem top4aTarget_restrict {n : ℕ} {dom Δ : List ℕ} (hd : dom.length = n)
    (hnd : Δ.Nodup) (hlt : ∀ u ∈ Δ, u < n) (α : RawPerm) (y : RawStr) :
    decStrN Δ.length (rawRestrictStr (top4aTarget (dom, α, y), Δ)) =
      fun i => strAct (decStrN n y) (decPerm n α)⁻¹ (winEquiv n Δ hnd hlt i) := by
  funext i
  change (rawRestrictStr (top4aTarget (dom, α, y), Δ)).getD i.val 0 = _
  rw [List.getD_eq_getElem _ _ (by simpa only [length_rawRestrictStr] using i.isLt)]
  simp only [rawRestrictStr, List.getElem_map]
  have he := congrFun (top4aTarget_spec hd α y) (winEquiv n Δ hnd hlt i)
  simpa only [decStrN, winEquiv_coe Δ hnd hlt i.isLt] using he

abbrev Top4aEntry := Top4Context × RawPerm × List ℕ × List ℕ

def top4aEnter (p : Top4aEntry) : Top4aNode :=
  ((p.1, none), normPerm (top4X p.1, p.2.1), decide (p.2.2.1.length = p.2.2.2.length))

theorem polyFun_top4aEnter : PolyFun top4aEnter := by
  have hC : PolyFun (fun p : Top4aEntry => p.1) := polyFun_fst
  have hα := ((hC.comp polyFun_top4X).pair (polyFun_snd.comp polyFun_fst)).comp polyFun_normPerm
  have hcx : PolyFun (fun p : Top4aEntry => p.2.2.1.length) := ((polyFun_snd.comp polyFun_snd).comp polyFun_fst).comp polyFun_length
  have hcy : PolyFun (fun p : Top4aEntry => p.2.2.2.length) := ((polyFun_snd.comp polyFun_snd).comp polyFun_snd).comp polyFun_length
  exact (hC.pair (polyFun_const (none : Option RawWinSI))).pair (hα.pair (hcx.natEq hcy))

theorem top4aEnter_wf {c d e f : ℕ} (p : Top4aEntry)
    (hC : Enc.size p.1 ≤ topcsContextCap c d (top4X p.1).length) :
    Top4aWF c d e f (top4aEnter p) :=
  ⟨⟨hC, by simp [top4aEnter]⟩, size_perm_le' le_rfl (wf_normPerm rfl _)⟩

theorem top4aEnter_guard {m : ℕ} (C : Top4Context) (α : RawPerm) (Cx Cy : List ℕ)
    (hxnd : Cx.Nodup) (hxlt : ∀ u ∈ Cx, u < m) (hynd : Cy.Nodup) (hylt : ∀ u ∈ Cy, u < m) :
    (top4aEnter (C, α, Cx, Cy)).2.2 = true ↔ (winSet m Cx).ncard = (winSet m Cy).ncard := by
  simp only [top4aEnter, decide_eq_true_eq, ncard_winSet Cx hxnd hxlt, ncard_winSet Cy hynd hylt]

 theorem top4aEnter_loopMatch {n c d e f : ℕ} {C : Top4Context} {α : RawPerm} {Cx Cy : List ℕ}
    (hx : (top4X C).length = n) (solve : RawWinSI → RawCoset)
    {T : SIReduction (Fin n) ℕ (Set (Perm (Fin n)))}
    (h : LoopMatch (top4Round c d e f solve) (top4Decode n) (decCoset n) (C, none)
      (top4Width C) 0 (top4Init (C, none)) T) :
    LoopMatch (top4aRound c d e f solve) (top4aDecode n) (decCoset n) (top4aEnter (C, α, Cx, Cy))
      ((top4aRound c d e f solve).width (top4aEnter (C, α, Cx, Cy))) 0
      (top4aInit (top4aEnter (C, α, Cx, Cy)))
      (if Cx.length = Cy.length then T.bind (fun A => .done (decPerm n α • A)) else .done ∅) := by
  by_cases hc : Cx.length = Cy.length
  · simp only [if_pos hc, top4aEnter, hc, decide_true]
    have hh := top4aLoopMatch (α := normPerm (top4X C, α)) hx solve h
    rw [decPerm_normPerm hx] at hh
    exact hh
  · simp only [if_neg hc, top4aEnter, hc, decide_false]
    exact top4aLoopMismatch C _ solve _ _ _

end Algo
