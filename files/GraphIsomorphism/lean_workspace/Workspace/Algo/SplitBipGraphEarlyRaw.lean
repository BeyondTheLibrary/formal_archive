import Workspace.Algo.SplitBipGraphComponentValidity
import Workspace.Algo.SplitBipStep1

/-! The early partition exits read the common graph in its stored first-
part order. Step 2 gathers the full point-color array at those names before
calling the existing numbering routine.
-/
namespace Algo
open Babai RAM

def sbipGraphFirstColors (r : RawSbipGraph) : RawLab :=
  r.1.1.map (fun a => labAt r.2.1 a)

def sbipGraphEarly2Input (r : RawSbipGraph) : RawUpccBip × RawLab :=
  (r.1,sbipGraphFirstColors r)

def sbipGraphEarly1 (c : ℕ) (z : RawSbipGraph × (ℕ × ℕ)) : List RawColPart :=
  sbipStep1Versions c (z.1.1.1,z.2)

def sbipGraphEarly2 (c : ℕ) (r : RawSbipGraph) : List RawColPart :=
  sbipStep2Versions c (sbipGraphEarly2Input r)

def sbipGraphEarly4 (z : RawSbipGraph × (ℕ × ℕ)) : RawColPart :=
  sbipStep4 (sbipGraphClasses z)

def sbipGraphSmall1 (c : ℕ) (r : RawSbipGraph) : Bool := decide (r.1.1.length ≤ c)

def sbipGraphSmall2 (c : ℕ) (r : RawSbipGraph) : Bool :=
  decide (r.1.2.1.length ≤ c * Nat.log 2 r.1.1.length)

theorem polyFun_sbipGraphSmall1 (c : ℕ) : PolyFun (sbipGraphSmall1 c) :=
  ((polyFun_fst.comp polyFun_fst).comp polyFun_length).le (polyFun_const c)

theorem polyFun_sbipGraphSmall2 (c : ℕ) : PolyFun (sbipGraphSmall2 c) :=
  (((polyFun_fst.comp polyFun_snd).comp polyFun_fst).comp polyFun_length).le
    ((polyFun_const c).mul (((polyFun_fst.comp polyFun_fst).comp polyFun_length).comp polyFun_log2))

theorem polyFun_sbipGraphFirstColors : PolyFun sbipGraphFirstColors :=
  ((polyFun_snd.comp polyFun_fst).pair (polyFun_fst.comp polyFun_fst)).comp
    (PolyFun.mapParam polyFun_labAt)

theorem polyFun_sbipGraphEarly2Input : PolyFun sbipGraphEarly2Input :=
  polyFun_fst.pair polyFun_sbipGraphFirstColors

theorem quasiFun_sbipGraphEarly1 (c : ℕ) : QuasiFun (sbipGraphEarly1 c) :=
  (((polyFun_fst.comp polyFun_fst).comp polyFun_fst).pair polyFun_snd).comp_quasiFun
    (quasiFun_sbipStep1Versions c)

theorem quasiFun_sbipGraphEarly2 (c : ℕ) : QuasiFun (sbipGraphEarly2 c) :=
  polyFun_sbipGraphEarly2Input.comp_quasiFun (quasiFun_sbipStep2Versions c)

theorem polyFun_sbipGraphEarly4 : PolyFun sbipGraphEarly4 :=
  polyFun_sbipGraphClasses.comp sbipPoly_step4

@[simp] theorem sbipGraphEarly4_eq (z : RawSbipGraph × (ℕ × ℕ)) :
    sbipGraphEarly4 z = (sbipGraphSteps35 z).1.2 := rfl

theorem sbipGraphFirstColors_get (r : RawSbipGraph) (i : Fin r.1.1.length) :
    labAt (sbipGraphFirstColors r) i = labAt r.2.1 r.1.1[i.val] := by
  simp [sbipGraphFirstColors,labAt,i.isLt]

theorem sbipGraphEarly1_wf {c : ℕ} {z : RawSbipGraph × (ℕ × ℕ)}
    {q : RawColPart} (hq : q ∈ sbipGraphEarly1 c z) : RawColPart.WF z.1.1.1.length q := by
  obtain ⟨row,_,rfl⟩ := List.mem_map.1 hq
  exact sbipStep1_lengths _

theorem sbipGraphEarly2_wf {c : ℕ} {r : RawSbipGraph}
    {q : RawColPart} (hq : q ∈ sbipGraphEarly2 c r) : RawColPart.WF r.1.1.length q := by
  obtain ⟨row,_,rfl⟩ := List.mem_map.1 hq
  exact sbipStep2_lengths _

theorem sbipGraphEarly4_wf (z : RawSbipGraph × (ℕ × ℕ)) :
    RawColPart.WF z.1.1.1.length (sbipGraphEarly4 z) := sbipStep4_lengths _

end Algo
