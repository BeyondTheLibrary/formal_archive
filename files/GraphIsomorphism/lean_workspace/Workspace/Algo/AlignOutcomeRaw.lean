import Workspace.Algo.AlignJohnson
import Workspace.SplitOrJohnson.Defs

/-! # The raw outcome shared by Split-or-Johnson and Align
The two tags retain the computed partition labels or Johnson subset rows.
The semantic decoder rejects malformed tags and invalid Johnson data.
-/
namespace Algo
open RAM Babai
open scoped Classical

abbrev RawAlignOutcome := Option RawColPart × Option RawJohnson

def rawAlignPartition (P : RawColPart) : RawAlignOutcome := (some P, none)
def rawAlignJohnson (J : RawJohnson) : RawAlignOutcome := (none, some J)

def decAlignPartition (m : ℕ) (P : RawColPart) : Pt (SplitOutcomes (Fin m)) :=
  ⟨Set.univ, Sum.inl
    { color := fun u => (decColPartition m P).color u.val
      part := Setoid.comap Subtype.val (decColPartition m P).part
      part_le_color := fun h => (decColPartition m P).part_le_color h }⟩

noncomputable def decAlignJohnson {m ms ts : ℕ} (J : RawJohnson) (h : J.WF m ms ts) :
    Pt (SplitOutcomes (Fin m)) :=
  ⟨RawJohnson.carrier m J, Sum.inr ⟨
    fun u v => rawJDiff (J, (u.val.val, v.val.val)),
    ⟨ms, ts, Equiv.ofBijective _ h.toBinom_bijective, h.two_le, h.params,
      fun u v => rawJDiff_eq_card (h.rowNodup (h.rawJRow_mem u.2))
        (h.rowLt _ (h.rawJRow_mem u.2))⟩⟩⟩

noncomputable def decAlignOutcome (m : ℕ) (r : RawAlignOutcome) : Option (Pt (SplitOutcomes (Fin m))) :=
  match r with
  | (some P, none) => some (decAlignPartition m P)
  | (none, some J) => if h : J.WF m (rawJDeg J) J.2.1 then some (decAlignJohnson J h) else none
  | _ => none

theorem decAlignOutcome_partition (m : ℕ) (P : RawColPart) :
    decAlignOutcome m (rawAlignPartition P) = some (decAlignPartition m P) := rfl

theorem decAlignOutcome_johnson {m ms ts : ℕ} (J : RawJohnson) (h : J.WF m ms ts) :
    decAlignOutcome m (rawAlignJohnson J) = some (decAlignJohnson J h) := by
  have hh : J.WF m (rawJDeg J) J.2.1 := by rw [h.rawJDeg_eq, h.hdr]; exact h
  simp only [decAlignOutcome, rawAlignJohnson, dif_pos hh]
  congr 1

theorem polyFun_rawAlignPartition : PolyFun rawAlignPartition :=
  polyFun_some.pair (polyFun_const none)
theorem polyFun_rawAlignJohnson : PolyFun rawAlignJohnson :=
  (polyFun_const none).pair polyFun_some

end Algo
