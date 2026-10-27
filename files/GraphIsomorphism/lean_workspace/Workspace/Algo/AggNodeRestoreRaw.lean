import Workspace.Algo.ExtendPartitionSpec

/-! # Restore aggregate outcomes to the original giant domain

A partition gains the one complement block used by the paper's extension.
A Johnson outcome retains its subset rows and restores its original vertex
names through the stored local dictionary. Both operations are polynomial
on every raw input, and malformed output tags remain malformed.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv

/-- Restore a Johnson carrier's old vertex names, retaining every subset row. -/
def aggnRestoreJohnson (p : List ℕ × RawJohnson) : RawJohnson :=
  (rawRestrictStr (p.1,p.2.1),p.2.2)

/-- Degree witness, local old-name dictionary, and the returned raw outcome. -/
abbrev AggnRestoreOutcomeInput := (List ℕ × List ℕ) × RawAlignOutcome

def aggnRestoreOutcome (p : AggnRestoreOutcomeInput) : RawAlignOutcome :=
  (p.2.1.map (fun P => rawExtendPartition ((List.range p.1.1.length,p.1.2),P)),
    p.2.2.map (fun J => aggnRestoreJohnson (p.1.2,J)))

def aggnRestoreFamily (p : (List ℕ × List ℕ) × List RawAlignOutcome) : List RawAlignOutcome :=
  p.2.map fun o => aggnRestoreOutcome (p.1,o)

theorem aggnPolyFun_restoreJohnson : PolyFun aggnRestoreJohnson :=
  ((polyFun_fst.pair (polyFun_snd.comp polyFun_fst)).comp polyFun_rawRestrictStr).pair
    (polyFun_snd.comp polyFun_snd)

theorem aggnPolyFun_restoreOutcome : PolyFun aggnRestoreOutcome := by
  have hp : PolyFun (fun p : RawColPart × (List ℕ × List ℕ) =>
      some (rawExtendPartition ((List.range p.2.1.length,p.2.2),p.1))) :=
    (((((polyFun_snd.comp polyFun_fst).comp polyFun_rangeLength).pair
      (polyFun_snd.comp polyFun_snd)).pair polyFun_fst).comp polyFun_rawExtendPartition).comp polyFun_some
  have hj : PolyFun (fun p : RawJohnson × (List ℕ × List ℕ) =>
      some (aggnRestoreJohnson (p.2.2,p.1))) :=
    (((polyFun_snd.comp polyFun_snd).pair polyFun_fst).comp aggnPolyFun_restoreJohnson).comp polyFun_some
  have hP : PolyFun (fun p : AggnRestoreOutcomeInput =>
      p.2.1.elim none (fun P => some (rawExtendPartition ((List.range p.1.1.length,p.1.2),P)))) := (((polyFun_snd.comp polyFun_fst).pair polyFun_fst).comp
    (PolyFun.optionElim (polyFun_const none) hp))
  have hJ : PolyFun (fun p : AggnRestoreOutcomeInput =>
      p.2.2.elim none (fun J => some (aggnRestoreJohnson (p.1.2,J)))) := (((polyFun_snd.comp polyFun_snd).pair polyFun_fst).comp
    (PolyFun.optionElim (polyFun_const none) hj))
  exact (hP.pair hJ).of_eq (fun p => by
    rcases p with ⟨d,P,J⟩
    cases P <;> cases J <;> rfl)

theorem aggnPolyFun_restoreFamily : PolyFun aggnRestoreFamily :=
  PolyFun.mapParam aggnPolyFun_restoreOutcome

theorem aggnRestoreOutcome_partition (dom D : List ℕ) (P : RawColPart) :
    aggnRestoreOutcome ((dom,D),rawAlignPartition P) =
      rawAlignPartition (rawExtendPartition ((List.range dom.length,D),P)) := rfl

theorem aggnRestoreOutcome_johnson (dom D : List ℕ) (J : RawJohnson) :
    aggnRestoreOutcome ((dom,D),rawAlignJohnson J) = rawAlignJohnson (aggnRestoreJohnson (D,J)) := rfl

/-- Every extended partition has a full-domain label array. -/
theorem aggnRestoreOutcome_partition_wf (dom D : List ℕ) (P : RawColPart) :
    (rawExtendPartition ((List.range dom.length,D),P)).WF dom.length := by
  simpa only [List.length_range] using rawExtendPartition_wf ((List.range dom.length,D),P)

end Algo
