import Workspace.Algo.AggNodeOrbitalSpec

/-! # The computed family in Section 13.2 Case 2b

Each increasing name of a set of `d-1` points supplies a pointwise
stabilizer. Its non-diagonal orbitals are returned with the remaining
vertex set. All loops have unconditional polynomial RAM bounds.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv MulAction
open scoped Classical

abbrev AggnRawConstituent := List ℕ × RawRel

def aggnPointStab (p : (List ℕ × RawGens) × List ℕ) : RawGens :=
  tidyGens (p.1.1,rawPointStab p)

def aggnSetDiff (p : List ℕ × List ℕ) : List ℕ :=
  p.1.filter fun u => decide (u ∉ p.2)

def aggnCase2bAt (p : (List ℕ × RawGens) × (List ℕ × List ℕ)) : List AggnRawConstituent :=
  let W := aggnSetDiff p.2
  (aggnOrbitals ((p.1.1,aggnPointStab (p.1,p.2.2)),W)).map (fun R => (W,R))

def aggnCase2bFamily (p : List ℕ × RawGens) : List AggnRawConstituent :=
  let C := aggnLargeOrbitPoints p
  (aggnSmallSets (p.1,C,aggnMajorityDegree p - 1)).flatMap
    (fun S => aggnCase2bAt (p,(C,S)))

def aggnDecodeConstituent (m : ℕ) (q : AggnRawConstituent) : Set (Fin m) × Set (Fin m × Fin m) :=
  (winSet m q.1,aggnDecodePairRel m q.2)

theorem aggnPolyFun_pointStab : PolyFun aggnPointStab :=
  ((polyFun_fst.comp polyFun_fst).pair polyFun_rawPointStab).comp polyFun_tidyGens

theorem aggnPolyFun_setDiff : PolyFun aggnSetDiff := by
  have hf : PolyFun (fun z : List ℕ × ℕ => decide (z.2 ∉ z.1)) := by
    have hm := (polyFun_snd.pair polyFun_fst).comp polyFun_natListMem
    exact (PolyFun.ite hm (polyFun_const false) (polyFun_const true)).of_eq (fun z => by
      by_cases h : z.2 ∈ z.1 <;> simp [h])
  exact (polyFun_snd.pair polyFun_fst).comp (PolyFun.filterParam hf)

theorem aggnPolyFun_case2bAt : PolyFun aggnCase2bAt := by
  have hd : PolyFun (fun p : (List ℕ × RawGens) × (List ℕ × List ℕ) => p.1.1) :=
    polyFun_fst.comp polyFun_fst
  have hw : PolyFun (fun p : (List ℕ × RawGens) × (List ℕ × List ℕ) => aggnSetDiff p.2) :=
    polyFun_snd.comp aggnPolyFun_setDiff
  have hs : PolyFun (fun p : (List ℕ × RawGens) × (List ℕ × List ℕ) =>
      aggnPointStab (p.1,p.2.2)) :=
    (polyFun_fst.pair (polyFun_snd.comp polyFun_snd)).comp aggnPolyFun_pointStab
  have ho := ((hd.pair hs).pair hw).comp aggnPolyFun_orbitals
  exact (hw.pair ho).comp (polyFun_fst.pair polyFun_snd).mapParam

theorem aggnPolyFun_case2bFamily : PolyFun aggnCase2bFamily := by
  have hc := aggnPolyFun_largeOrbitPoints
  have hs := (polyFun_fst.pair (hc.pair
    ((aggnPolyFun_majorityDegree.pair (polyFun_const 1)).comp polyFun_sub))).comp aggnPolyFun_smallSets
  have hf : PolyFun (fun z : ((List ℕ × RawGens) × List ℕ) × List ℕ =>
      aggnCase2bAt (z.1.1,z.1.2,z.2)) :=
    ((polyFun_fst.comp polyFun_fst).pair
      ((polyFun_fst.comp polyFun_snd).pair polyFun_snd)).comp aggnPolyFun_case2bAt
  exact ((polyFun_id.pair hc).pair hs).comp hf.flatMapParam

theorem aggnPointStab_spec {m : ℕ} {dom S : List ℕ} {gs : RawGens}
    (hd : dom.length = m) (hw : RawGens.WF m gs) (hs : S.Nodup) (hlt : ∀ u ∈ S,u < m) :
    decGroup m (aggnPointStab ((dom,gs),S)) = pointwiseStabilizer (decGroup m gs) (winSet m S) := by
  rw [aggnPointStab,decGroup_tidyGens hd]
  have h := decGroup_rawPointStab dom hd (gs.map (decPerm m)) S hs hlt
  simpa only [map_encPerm_decPerm hw] using h

theorem aggnSetDiff_spec {m : ℕ} (C S : List ℕ) :
    winSet m (aggnSetDiff (C,S)) = winSet m C \ winSet m S := by
  ext u
  simp [aggnSetDiff,winSet]

theorem aggnCase2bAt_length (p : (List ℕ × RawGens) × (List ℕ × List ℕ)) :
    (aggnCase2bAt p).length ≤ (aggnSetDiff p.2).length - 1 := by
  rw [aggnCase2bAt,List.length_map]
  exact aggnOrbitals_length _

end Algo
