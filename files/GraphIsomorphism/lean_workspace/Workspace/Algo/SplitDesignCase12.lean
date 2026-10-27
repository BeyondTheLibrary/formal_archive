import Workspace.Algo.SplitDesignGraphSpec
import Workspace.Algo.SplitDesignDomColor
import Workspace.Algo.AlignOutcomeRaw

/-! # Section 9.7: the first two cases as one executable branch

The local names stay with a partition or Johnson output. A graph output
carries its selected block list and hint into the next turn. Case 3 is the
only branch left to the Design Lemma continuation.
-/
namespace Algo
open Babai RAM

abbrev RawDesignCaseOut := (List ℕ × RawAlignOutcome) × Option RawDesignGraph

def designPartExit (z : RawUpccCase × RawColPart) : RawDesignCaseOut :=
  ((z.1.2.1,rawAlignPartition z.2),none)

def designJohnsonExit (z : RawUpccCase × RawJohnson) : RawDesignCaseOut :=
  ((z.1.2.1,rawAlignJohnson z.2),none)

def designGraphExit (z : RawDesignGraph) : RawDesignCaseOut := (([],(none,none)),some z)

def designOtherNames (r : RawUpccCase) : List ℕ :=
  r.2.2.filter (fun b => !decide (b ∈ designBigNames r))

def designTieGraph (r : RawUpccCase) : RawDesignGraph := ((r,r.2.2),designTwinHint r)

def designOtherGraph (r : RawUpccCase) : RawDesignGraph := ((r,designOtherNames r),([],[]))

def designDominantExit (z : RawDesignLocal) : RawDesignCaseOut :=
  if designHasDomTwins z then designPartExit (z.1,designDomPartition z)
  else if designDomBoundary z then designPartExit (z.1,designPairPartition z)
  else designJohnsonExit (z.1,designDomJohnson z)

def designCase2Exit (z : RawDesignLocal) : RawDesignCaseOut :=
  if designTie z.1 then designGraphExit (designTieGraph z.1)
  else if designSelectC z.1 then
    if designSmall z then designPartExit (z.1,designSmallPartition z.1)
    else designDominantExit z
  else designGraphExit (designOtherGraph z.1)

def designCase12 (z : RawDesignLocal) : Option RawDesignCaseOut :=
  if designCase1 z.1 then some (designJohnsonExit (z.1,designJohnson z.1))
  else if designCase2 z.1 then some (designCase2Exit z) else none

theorem polyFun_designPartExit : PolyFun designPartExit :=
  ((((polyFun_fst.comp polyFun_snd).comp polyFun_fst).pair
    (polyFun_snd.comp polyFun_rawAlignPartition)).pair (polyFun_const none))

theorem polyFun_designJohnsonExit : PolyFun designJohnsonExit :=
  ((((polyFun_fst.comp polyFun_snd).comp polyFun_fst).pair
    (polyFun_snd.comp polyFun_rawAlignJohnson)).pair (polyFun_const none))

theorem polyFun_designGraphExit : PolyFun designGraphExit :=
  (polyFun_const ([],(none,none))).pair polyFun_some

theorem polyFun_designOtherNames : PolyFun designOtherNames := by
  have ht : PolyFun (fun z : List ℕ × ℕ => !decide (z.2 ∈ z.1)) :=
    polyFun_rawJNot ((polyFun_snd.pair polyFun_fst).comp polyFun_natListMem)
  exact (polyFun_designBigNames.pair (polyFun_snd.comp polyFun_snd)).comp (PolyFun.filterParam ht)

theorem polyFun_designTieGraph : PolyFun designTieGraph :=
  (polyFun_id.pair (polyFun_snd.comp polyFun_snd)).pair polyFun_designTwinHint

theorem polyFun_designOtherGraph : PolyFun designOtherGraph :=
  (polyFun_id.pair polyFun_designOtherNames).pair (polyFun_const ([],[]))

theorem polyFun_designDominantExit : PolyFun designDominantExit :=
  PolyFun.ite polyFun_designHasDomTwins
    ((polyFun_fst.pair polyFun_designDomPartition).comp polyFun_designPartExit)
    (PolyFun.ite polyFun_designDomBoundary
      ((polyFun_fst.pair polyFun_designPairPartition).comp polyFun_designPartExit)
      ((polyFun_fst.pair polyFun_designDomJohnson).comp polyFun_designJohnsonExit))

theorem polyFun_designCase2Exit : PolyFun designCase2Exit :=
  PolyFun.ite (polyFun_fst.comp polyFun_designTie)
    ((polyFun_fst.comp polyFun_designTieGraph).comp polyFun_designGraphExit)
    (PolyFun.ite (polyFun_fst.comp polyFun_designSelectC)
      (PolyFun.ite polyFun_designSmall
        ((polyFun_fst.pair (polyFun_fst.comp polyFun_designSmallPartition)).comp polyFun_designPartExit)
        polyFun_designDominantExit)
      ((polyFun_fst.comp polyFun_designOtherGraph).comp polyFun_designGraphExit))

theorem polyFun_designCase12 : PolyFun designCase12 :=
  PolyFun.ite (polyFun_fst.comp polyFun_designCase1)
    (((polyFun_fst.pair (polyFun_fst.comp polyFun_designJohnson)).comp
      polyFun_designJohnsonExit).comp polyFun_some)
    (PolyFun.ite (polyFun_fst.comp polyFun_designCase2)
      (polyFun_designCase2Exit.comp polyFun_some) (polyFun_const none))

/-- The Design Lemma continuation is entered exactly after the first two tests fail. -/
theorem designCase12_none (z : RawDesignLocal) :
    designCase12 z = none ↔ designCase1 z.1 = false ∧ designCase2 z.1 = false := by
  cases h1 : designCase1 z.1 <;> cases h2 : designCase2 z.1 <;> simp [designCase12,h1,h2]

end Algo
