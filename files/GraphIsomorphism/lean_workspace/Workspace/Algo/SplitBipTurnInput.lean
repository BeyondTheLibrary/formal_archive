import Workspace.Algo.SplitBipGraphEarlyRaw
import Workspace.Algo.SplitBipGraphStep9Dictionary

/-! One recursive turn retains the original point-name bound and block
dictionary. Step 9 gets a new compact vertex table and its computed
dictionary. The parent first part stays available for extending answers. -/
namespace Algo
open RAM Babai

abbrev RawSbipTurnInput := List ℕ × (RawSbipStored × (ℕ × ℕ))
abbrev RawSbipTurnCase := ((List ℕ × List (List ℕ)) × List ℕ) × (RawUpccCase × (ℕ × ℕ))

def sbipTurnGraphInput (z : RawSbipTurnInput) : RawSbipGraph × (ℕ × ℕ) :=
  (z.2.1.1,z.2.2)

def sbipTurnCase (z : RawSbipTurnInput) : RawSbipTurnCase :=
  (((z.1,sbipGraphStep9Dictionary z.2),z.2.1.1.1.1),
    (sbipGraphStep9Input (sbipTurnGraphInput z),
      (sbipStep5 (sbipGraphPrepared (sbipTurnGraphInput z))).1.2))

theorem polyFun_sbipTurnGraphInput : PolyFun sbipTurnGraphInput :=
  ((polyFun_snd.comp polyFun_fst).comp polyFun_fst).pair (polyFun_snd.comp polyFun_snd)

theorem polyFun_sbipTurnCase : PolyFun sbipTurnCase :=
  ((polyFun_fst.pair (polyFun_snd.comp polyFun_sbipGraphStep9Dictionary)).pair
    ((((polyFun_snd.comp polyFun_fst).comp polyFun_fst).comp polyFun_fst).comp polyFun_fst)).pair
    ((polyFun_sbipTurnGraphInput.comp polyFun_sbipGraphStep9Input).pair
      ((((polyFun_sbipTurnGraphInput.comp polyFun_sbipGraphPrepared).comp sbipPoly_step5).comp
        polyFun_fst).comp polyFun_snd))

end Algo
