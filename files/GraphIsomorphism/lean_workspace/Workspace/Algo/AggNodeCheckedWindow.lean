import Workspace.Algo.AggNodeCertBounds

/-! # A bounded window boundary for the certificate phase

The Recompute cache is not trusted by the machine interface. We read its
window on the parent domain, shorten its generators, and cap its strings.
On the calls of Sec. 13.1, line 04e, this only changes the raw encoding:
the decoded instance is unchanged. The alphabet bound is the one supplied
by the existing input normalization, with one spare label for malformed data.
-/
namespace Algo
open RAM RAM.Targets
open Babai Equiv

/-- Read a cached string on the parent domain and cap its letters. -/
def aggnCheckedStr (p : RawStr × RawStr) : RawStr :=
  (rawOne p.1).map fun i => min (rawGet (p.2, i)) (2 * p.1.length)

/-- Read a cached window as a subset of the parent domain. -/
def aggnCheckedWin (p : RawStr × List ℕ) : List ℕ :=
  (rawOne p.1).filter fun i => i ∈ p.2

/-- The parent, rather than the cached string, determines the domain. -/
def aggnCheckedWindow (p : RawStr × RawWinSI) : RawWinSI :=
  (aggnCheckedWin (p.1, p.2.1), tidyGens (p.1, p.2.2.1),
    normPerm (p.1, p.2.2.2.1), aggnCheckedStr (p.1, p.2.2.2.2.1),
    aggnCheckedStr (p.1, p.2.2.2.2.2))

/-- The size conditions required of a window child, independent of its cache. -/
def AggnCheckedWindowWF (n : ℕ) (W : RawWinSI) : Prop :=
  W.1.Nodup ∧ (∀ i ∈ W.1, i < n) ∧
    RawGens.WF n W.2.1 ∧ W.2.1.length ≤ n * n ∧
    RawPerm.WF n W.2.2.1 ∧
    RawStr.WF n (2 * n + 1) W.2.2.2.1 ∧ RawStr.WF n (2 * n + 1) W.2.2.2.2

theorem aggnCheckedStr_wf (dom xs : RawStr) :
    RawStr.WF dom.length (2 * dom.length + 1) (aggnCheckedStr (dom, xs)) := by
  constructor
  · simp [aggnCheckedStr, rawOne]
  · intro a ha
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
    exact Nat.lt_succ_of_le (min_le_right _ _)

theorem aggnCheckedWindow_wf (dom : RawStr) (W : RawWinSI) :
    AggnCheckedWindowWF dom.length (aggnCheckedWindow (dom, W)) := by
  refine ⟨?_, ?_, wf_tidyGens rfl _, length_tidyGens rfl _, wf_normPerm rfl _,
    aggnCheckedStr_wf _ _, aggnCheckedStr_wf _ _⟩
  · exact (wf_rawOne dom).nodup.filter _
  · intro i hi
    exact (wf_rawOne dom).lt (List.mem_of_mem_filter hi)

theorem aggnCheckedWin_decode {dom : RawStr} {n : ℕ} (hd : dom.length = n) (W : List ℕ) :
    winSet n (aggnCheckedWin (dom, W)) = winSet n W := by
  ext i
  simp only [winSet, Set.mem_setOf_eq, aggnCheckedWin, List.mem_filter, decide_eq_true_eq]
  apply and_iff_right
  simp [rawOne, hd]

theorem aggnCheckedStr_decode {dom : RawStr} {n : ℕ} (hd : dom.length = n) (xs : RawStr)
    (hx : ∀ i : Fin n, decStrN n xs i ≤ 2 * n) :
    decStrN n (aggnCheckedStr (dom, xs)) = decStrN n xs := by
  funext i
  have hi : (i : ℕ) < dom.length := hd ▸ i.isLt
  simp only [aggnCheckedStr, rawOne_eq, encPerm, List.map_ofFn]
  change (List.ofFn (fun j : Fin dom.length => min (rawGet (xs, j.val))
    (2 * dom.length))).getD i.val 0 = xs.getD i.val 0
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]
  exact Nat.min_eq_left (by simpa only [rawGet, decStrN, hd] using hx i)

/-- On bounded decoded strings, normalization preserves the entire instance,
including its coset and its window. No cache well-formedness is assumed. -/
theorem aggnCheckedWindow_decode {dom : RawStr} {n : ℕ} (hd : dom.length = n)
    (W : RawWinSI)
    (hx : ∀ i : Fin n, (decWinSI n W).x i ≤ 2 * n)
    (hy : ∀ i : Fin n, (decWinSI n W).y i ≤ 2 * n) :
    decWinSI n (aggnCheckedWindow (dom, W)) = decWinSI n W := by
  unfold decWinSI aggnCheckedWindow
  simp only [decCoset_some, decGroup_tidyGens hd, decPerm_normPerm hd,
    aggnCheckedWin_decode hd, aggnCheckedStr_decode hd W.2.2.2.1 hx,
    aggnCheckedStr_decode hd W.2.2.2.2 hy]

/-- A fixed polynomial in the parent degree bounds every normalized child. -/
def aggnCheckedWindowBound (n : ℕ) : ℕ :=
  32 * (gensBound n + strBound (2 * n + 1) + 1)

theorem aggnCheckedWindow_size {n : ℕ} {W : RawWinSI} (h : AggnCheckedWindowWF n W) :
    Enc.size W ≤ aggnCheckedWindowBound n := by
  have hwin : Enc.size W.1 ≤ strBound n :=
    size_natList_le (length_le_of_nodup_lt h.1 h.2.1) h.2.1
  have hrep : Enc.size W.2.2.1 ≤ strBound n :=
    size_natList_le (by rw [h.2.2.2.2.1.length]) (fun a ha => h.2.2.2.2.1.lt ha)
  have hgens : Enc.size W.2.1 ≤ gensBound n := by
    have hs := size_list_le_of_entries W.2.1 (strBound n) (fun g hg =>
      size_natList_le (by rw [(h.2.2.1 g hg).length]) (fun a ha => (h.2.2.1 g hg).lt ha))
    have hl := Nat.mul_le_mul_right (2 * strBound n + 1) h.2.2.2.1
    dsimp [gensBound]
    omega
  have hx : Enc.size W.2.2.2.1 ≤ strBound (2 * n + 1) :=
    size_natList_le (by rw [h.2.2.2.2.2.1.1]; omega) h.2.2.2.2.2.1.2
  have hy : Enc.size W.2.2.2.2 ≤ strBound (2 * n + 1) :=
    size_natList_le (by rw [h.2.2.2.2.2.2.1]; omega) h.2.2.2.2.2.2.2
  have h1 : Enc.size W ≤ 2 * Enc.size W.1 + 2 * Enc.size W.2 := Combine.size_pair_le _ _
  have h2 : Enc.size W.2 ≤ 2 * Enc.size W.2.1 + 2 * Enc.size W.2.2 := Combine.size_pair_le _ _
  have h3 : Enc.size W.2.2 ≤ 2 * Enc.size W.2.2.1 + 2 * Enc.size W.2.2.2 := Combine.size_pair_le _ _
  have h4 : Enc.size W.2.2.2 ≤ 2 * Enc.size W.2.2.2.1 + 2 * Enc.size W.2.2.2.2 := Combine.size_pair_le _ _
  have hsg := strBound_le_gensBound n
  dsimp [aggnCheckedWindowBound]
  omega

theorem aggnPolyBound_checkedWindow : PolyBound aggnCheckedWindowBound :=
  (polyBound_const 32).mul ((polyBound_gensBound.add
    (polyBound_strBound.comp (((polyBound_const 2).mul polyBound_id).add
      (polyBound_const 1)))).add (polyBound_const 1))

theorem aggnMono_checkedWindowBound : Monotone aggnCheckedWindowBound := by
  intro a b hab
  have hg := mono_gensBound hab
  have hs := mono_strBound (show 2 * a + 1 ≤ 2 * b + 1 by omega)
  dsimp [aggnCheckedWindowBound]
  omega

theorem aggnPolyFun_checkedStr : PolyFun aggnCheckedStr := by
  have hf : PolyFun (fun z : (RawStr × ℕ) × ℕ => min (rawGet (z.1.1, z.2)) z.1.2) :=
    ((((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp polyFun_rawGet).pair
      (polyFun_fst.comp polyFun_snd)).comp polyFun_min
  have hp : PolyFun (fun p : RawStr × RawStr =>
      ((p.2, 2 * p.1.length), rawOne p.1)) :=
    (polyFun_snd.pair (((polyFun_const 2).pair
      (polyFun_fst.comp polyFun_length)).comp polyFun_mul)).pair
        (polyFun_fst.comp polyFun_rawOne)
  exact (hp.comp (PolyFun.mapParam hf)).of_eq (fun _ => rfl)

theorem aggnPolyFun_checkedWin : PolyFun aggnCheckedWin := by
  have hp : PolyFun (fun p : RawStr × List ℕ => (p.2, rawOne p.1)) :=
    polyFun_snd.pair (polyFun_fst.comp polyFun_rawOne)
  have hf : PolyFun (fun z : List ℕ × ℕ => decide (z.2 ∈ z.1)) :=
    (polyFun_snd.pair polyFun_fst).comp polyFun_natListMem
  exact (hp.comp (PolyFun.filterParam hf)).of_eq (fun _ => rfl)

theorem aggnPolyFun_checkedWindow : PolyFun aggnCheckedWindow := by
  have hw : PolyFun (fun p : RawStr × RawWinSI => p.2.1) :=
    polyFun_snd.comp polyFun_fst
  have hg : PolyFun (fun p : RawStr × RawWinSI => p.2.2.1) :=
    (polyFun_snd.comp polyFun_snd).comp polyFun_fst
  have hr : PolyFun (fun p : RawStr × RawWinSI => p.2.2.2.1) :=
    ((polyFun_snd.comp polyFun_snd).comp polyFun_snd).comp polyFun_fst
  have hx : PolyFun (fun p : RawStr × RawWinSI => p.2.2.2.2.1) :=
    (((polyFun_snd.comp polyFun_snd).comp polyFun_snd).comp polyFun_snd).comp polyFun_fst
  have hy : PolyFun (fun p : RawStr × RawWinSI => p.2.2.2.2.2) :=
    (((polyFun_snd.comp polyFun_snd).comp polyFun_snd).comp polyFun_snd).comp polyFun_snd
  exact (((polyFun_fst.pair hw).comp aggnPolyFun_checkedWin).pair
    (((polyFun_fst.pair hg).comp polyFun_tidyGens).pair
      (((polyFun_fst.pair hr).comp polyFun_normPerm).pair
        (((polyFun_fst.pair hx).comp aggnPolyFun_checkedStr).pair
          ((polyFun_fst.pair hy).comp aggnPolyFun_checkedStr))))).of_eq (fun _ => rfl)

end Algo
