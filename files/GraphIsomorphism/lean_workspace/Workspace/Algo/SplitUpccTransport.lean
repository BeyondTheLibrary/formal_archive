import Workspace.Algo.SplitUpccSpec

/-!
# Shifted canonicity for Lemma 9.3.1

The individualized vertex moves with its name. The order of each part list
is transported from the input. Thus the matrix positions stay fixed.
Block names here are original color labels, so they need no normalization.
-/

namespace Algo

open Babai RAM

theorem upccPairs_permList (π : RawPerm) (l : List ℕ) :
    upccPairs (permList π l) =
      (upccPairs l).map (fun q => (rawApply (π,q.1),rawApply (π,q.2))) := by
  simp [upccPairs,permList,List.flatMap_map,List.map_flatMap,List.map_map,Function.comp_def]

theorem upccWitnessColors_relabel {n : ℕ} {p : RawConfig} {π : RawPerm}
    (h : RawWL.WF n 2 p) (hπ : RawPerm.WF n π) (x : Fin n) {u v : ℕ}
    (hu : u < n) (hv : v < n) :
    upccWitnessColors ((relabelWL (π,p),rawApply (π,x)),
      (rawApply (π,u),rawApply (π,v))) = upccWitnessColors ((p,x),(u,v)) := by
  simp only [upccWitnessColors,binColor_relabel h hπ x.isLt hv,
    binColor_relabel h hπ hu hv]

theorem upccMidWitness_relabel {n : ℕ} {p : RawConfig} {π : RawPerm}
    (h : RawWL.WF n 2 p) (hπ : RawPerm.WF n π) (x : Fin n) (k : ℕ) {u v : ℕ}
    (hu : u < n) (hv : v < n) :
    upccMidWitness (((relabelWL (π,p),rawApply (π,x)),k),
      (rawApply (π,u),rawApply (π,v))) = upccMidWitness (((p,x),k),(u,v)) := by
  simp only [upccMidWitness,upccWitnessColors_relabel h hπ x hu hv,
    binColor_relabel h hπ x.isLt x.isLt,binColor_relabel h hπ x.isLt hu]

theorem upccMidCandidates_relabel {n : ℕ} {p : RawConfig} {π : RawPerm}
    (h : RawWL.WF n 2 p) (hπ : RawPerm.WF n π) (x : Fin n) (k : ℕ) :
    upccMidCandidates ((relabelWL (π,p),rawApply (π,x)),k) =
      upccMidCandidates ((p,x),k) := by
  unfold upccMidCandidates
  rw [relabelWL_fst,upccPairs_permList,List.filter_map,List.map_map]
  dsimp only [Function.comp_def]
  have hf : (upccPairs p.1).filter (fun q =>
      upccMidWitness (((relabelWL (π,p),rawApply (π,x)),k),
        (rawApply (π,q.1),rawApply (π,q.2)))) =
      (upccPairs p.1).filter (fun q => upccMidWitness (((p,x),k),q)) := by
    apply List.filter_congr
    intro q hq
    obtain ⟨hu,hv⟩ := (mem_upccPairs _ _).1 hq
    exact upccMidWitness_relabel h hπ x k ((h.domMem q.1).1 hu) ((h.domMem q.2).1 hv)
  rw [hf]
  apply List.map_congr_left
  intro q hq
  obtain ⟨hu,hv⟩ := (mem_upccPairs _ _).1 (List.mem_of_mem_filter hq)
  exact upccWitnessColors_relabel h hπ x ((h.domMem q.1).1 hu) ((h.domMem q.2).1 hv)

theorem upccMidIJRaw_relabel {n : ℕ} {p : RawConfig} {π : RawPerm}
    (h : RawWL.WF n 2 p) (hπ : RawPerm.WF n π) (x : Fin n) (k : ℕ) :
    upccMidIJRaw ((relabelWL (π,p),rawApply (π,x)),k) = upccMidIJRaw ((p,x),k) := by
  simp only [upccMidIJRaw,upccMidCandidates_relabel h hπ]

/-- Move the two lists of ambient names, keeping the matrix in the same positions. -/
def upccRelabelBip (π : RawPerm) (g : RawUpccBip) : RawUpccBip :=
  (permList π g.1,permList π g.2.1,g.2.2)

theorem upccBipRows_relabel {n : ℕ} {z : RawBipConstituent} {π : RawPerm}
    (h : RawWL.WF n 2 z.1.1) (hπ : RawPerm.WF n π)
    (hl : ∀ u ∈ z.2.1, u < n) (hr : ∀ v ∈ z.2.2, v < n) :
    upccBipRows (splitRelabelBipRaw (π,z)) = upccBipRows z := by
  simp only [upccBipRows,upccBipRow,splitRelabelBipRaw,permList,List.map_map]
  apply List.map_congr_left
  intro u hu
  apply List.map_congr_left
  intro v hv
  dsimp only [Function.comp_def]
  simp only [binColor_relabel h hπ (hl u hu) (hr v hv)]

theorem upccBipRaw_relabel {n : ℕ} {p : RawConfig} {π : RawPerm}
    (h : RawWL.WF n 2 p) (hπ : RawPerm.WF n π) (x : Fin n) (k i j : ℕ) :
    upccBipRaw ((relabelWL (π,p),rawApply (π,x)),(k,i,j)) =
      upccRelabelBip π (upccBipRaw ((p,x),(k,i,j))) := by
  simp only [upccBipRaw,upccCellRaw_relabel h hπ,upccRelabelBip]
  congr 2
  apply upccBipRows_relabel (z := ((p,j),
    (upccCellRaw ((p,x),k),upccCellRaw ((p,x),i)))) h hπ
  · intro u hu
    exact (h.domMem u).1 (List.mem_of_mem_filter hu)
  · intro v hv
    exact (h.domMem v).1 (List.mem_of_mem_filter hv)

/-- Relocate color labels by the inverse permutation. Their values stay fixed. -/
def upccRelabelColors (π : RawPerm) (lab : RawLab) : RawLab :=
  (List.range lab.length).map (fun v => labAt lab (invAt π v))

theorem upccCellsRaw_relabel {n : ℕ} {p : RawConfig} {π : RawPerm}
    (h : RawWL.WF n 2 p) (hπ : RawPerm.WF n π) (x : Fin n) :
    upccCellsRaw (relabelWL (π,p),rawApply (π,x)) =
      upccRelabelColors π (upccCellsRaw (p,x)) := by
  unfold upccCellsRaw upccRelabelColors
  simp only [relabelWL_fst,permList,List.length_map,List.length_range]
  apply List.map_congr_left
  intro v hv
  have hv' : v < n := by simpa [card_eq_length_dom h] using List.mem_range.1 hv
  have hi := invAt_lt hπ hv'
  have hc := binColor_relabel h hπ x.isLt hi
  rw [rawApply_invAt hπ hv'] at hc
  simpa [labAt,card_eq_length_dom h,hi] using hc

namespace Upcc

/-- Fix the rational threshold and transport the binary table. -/
def relabelInput (π : RawPerm) (r : RawUpcc) : RawUpcc := (relabelWL (π,r.1),r.2)

/-- Relabel the two ambient labellings and the vertex lists of a graph outcome. -/
def relabelOutcome (π : RawPerm) (q : RawUpccOutcome) : RawUpccOutcome :=
  ((upccRelabelColors π q.1.1,upccRelabelColors π q.1.2),
    q.2.map (fun g => (g.1,upccRelabelBip π g.2)))

/-- Lemma 9.3.1: transport the input and the individualized vertex together.
This is an equality of the whole raw outcome, including list order. -/
theorem versionF_relabel {n : ℕ} {r : RawUpcc} {π : RawPerm}
    (h : RawWL.WF n 2 r.1) (hπ : RawPerm.WF n π) (x : Fin n) :
    versionF (relabelInput π r,rawApply (π,x)) = relabelOutcome π (versionF (r,x)) := by
  rcases r with ⟨p,a,b⟩
  have hbranch : ∀ k,
      upccBipBranch (((relabelWL (π,p),(a,b)),rawApply (π,x)),k) =
      ((upccBipBranch (((p,(a,b)),x),k)).1,
        upccRelabelBip π (upccBipBranch (((p,(a,b)),x),k)).2) := by
    intro k
    simp only [upccBipBranch,upccCellRaw_relabel h hπ,upccMidIJRaw_relabel h hπ,
      relabelWL_fst,permList,List.length_map,upccBipRaw_relabel h hπ]
  simp only [versionF,relabelInput,relabelOutcome,upccBigColor_relabel h hπ,
    upccCellsRaw_relabel h hπ]
  cases hk : upccBigColor ((p,(a,b)),x) with
  | none => rfl
  | some k => simp only [Option.elim_some,Option.map_some,hbranch]

end Upcc

end Algo
