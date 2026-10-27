import Workspace.Algo.AggNodePairOrbit
import Workspace.Algo.AggNodeSmallSets
import Workspace.Master.Case2bDefect
import Workspace.Algo.Functors

/-! # The non-diagonal orbitals after individualization

For a transitive action, every non-diagonal orbital meets the row through
one chosen point. Scanning this row lists each orbital once and uses at
most one fewer choices than vertices, as in Section 13.2 Case 2b.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv MulAction
open scoped Classical

/-- The encoded pairs through the first vertex, with the diagonal omitted. -/
def aggnPairRow (p : List ℕ × List ℕ) : List ℕ :=
  (p.2.filter fun b => decide (b ≠ p.2.headD 0)).map
    (fun b => aggnPairName (p.1.length,(p.2.headD 0,b)))

/-- Read an orbit of numbered pairs as a binary relation on the original names. -/
def aggnPairRel (p : List ℕ × List ℕ) : RawRel :=
  (tuplesOf (List.range p.1.length) 2).filter fun row =>
    decide (aggnPairName (p.1.length,(row.getD 0 0,row.getD 1 0)) ∈ p.2)

def aggnOrbitals (p : (List ℕ × RawGens) × List ℕ) : List RawRel :=
  (winOrbits (aggnPairGens p.1,aggnPairRow (p.1.1,p.2))).map
    (fun orb => aggnPairRel (p.1.1,orb))

def aggnDecodePairRel (m : ℕ) (R : RawRel) : Set (Fin m × Fin m) :=
  {uv | [uv.1.val,uv.2.val] ∈ R}

theorem aggnPolyFun_pairRow : PolyFun aggnPairRow := by
  have hh : PolyFun (fun p : List ℕ => p.headD 0) :=
    ((polyFun_headOption.pair (polyFun_const 0)).comp polyFun_optionGetD).of_eq (fun p => by cases p <;> rfl)
  have hf : PolyFun (fun z : List ℕ × ℕ => decide (z.2 ≠ z.1.headD 0)) := by
    have he := polyFun_snd.natEq (polyFun_fst.comp hh)
    exact (PolyFun.ite he (polyFun_const false) (polyFun_const true)).of_eq (fun z => by
      by_cases h : z.2 = z.1.headD 0 <;> simp [h])
  have hs : PolyFun (fun p : List ℕ × List ℕ =>
      p.2.filter (fun b => decide (b ≠ p.2.headD 0))) :=
    ((polyFun_snd.pair polyFun_snd).comp (PolyFun.filterParam hf))
  have hm : PolyFun (fun z : (List ℕ × List ℕ) × ℕ =>
      aggnPairName (z.1.1.length,(z.1.2.headD 0,z.2))) :=
    (((polyFun_fst.comp polyFun_fst).comp polyFun_length).pair
      (((polyFun_fst.comp polyFun_snd).comp hh).pair polyFun_snd)).comp aggnPolyFun_pairName
  exact (polyFun_id.pair hs).comp hm.mapParam

theorem aggnPolyFun_pairRel : PolyFun aggnPairRel := by
  have hget (i : ℕ) : PolyFun (fun z : (List ℕ × List ℕ) × List ℕ => z.2.getD i 0) :=
    (polyFun_snd.pair (polyFun_const i)).comp polyFun_rawGet
  have hn : PolyFun (fun z : (List ℕ × List ℕ) × List ℕ =>
      aggnPairName (z.1.1.length,(z.2.getD 0 0,z.2.getD 1 0))) :=
    (((polyFun_fst.comp polyFun_fst).comp polyFun_length).pair
      ((hget 0).pair (hget 1))).comp aggnPolyFun_pairName
  have hf := (hn.pair (polyFun_fst.comp polyFun_snd)).comp polyFun_natListMem
  exact (polyFun_id.pair ((polyFun_fst.comp polyFun_rangeLength).comp
    ((polyFun_tuplesOf 2).comp polyFun_snd))).comp (PolyFun.filterParam hf)

theorem aggnPolyFun_orbitals : PolyFun aggnOrbitals := by
  have hd : PolyFun (fun p : (List ℕ × RawGens) × List ℕ => p.1.1) :=
    polyFun_fst.comp polyFun_fst
  have ho := ((polyFun_fst.comp aggnPolyFun_pairGens).pair
    ((hd.pair polyFun_snd).comp aggnPolyFun_pairRow)).comp polyFun_winOrbits
  exact (hd.pair ho).comp aggnPolyFun_pairRel.mapParam

theorem aggnPairRel_mem {m : ℕ} {dom orb : List ℕ} (hd : dom.length = m) (u v : Fin m) :
    (u,v) ∈ aggnDecodePairRel m (aggnPairRel (dom,orb)) ↔
      aggnPairName (m,(u.val,v.val)) ∈ orb := by
  change [u.val,v.val] ∈ aggnPairRel (dom,orb) ↔ _
  simp only [aggnPairRel,List.mem_filter,mem_tuplesOf,hd]
  simp [u.isLt,v.isLt]

theorem aggnPairRel_orbit {m : ℕ} {dom : List ℕ} {gs : RawGens}
    (hd : dom.length = m) (hw : RawGens.WF m gs) (a b : Fin m) :
    aggnDecodePairRel m (aggnPairRel (dom,aggnPairOrbit ((dom,gs),(a.val,b.val)))) =
      {uv | ∃ g ∈ decGroup m gs,g a = uv.1 ∧ g b = uv.2} := by
  ext uv
  exact (aggnPairRel_mem hd uv.1 uv.2).trans (aggnPairOrbit_mem hd hw a b uv.1 uv.2)

end Algo
