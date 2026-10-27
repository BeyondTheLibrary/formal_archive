import Workspace.Algo.AggregateImage

/-! # Connecting the final local state to the aggregate store

This file gives the boundary between the loop fold and the certificate table. The
fullness equivalence is a mathematical hypothesis, because its proof uses the cited
local-certificate theory. No running-time assumption about a solver is needed.
-/
namespace Algo
open RAM RAM.Targets
open Equiv (Perm)

/-- Store the output of one completed loop. The fullness equivalence is the
first conclusion of Theorem 13.1.3. Keeping it explicit separates the raw read-off
from the cited group theory used to prove fullness. -/
theorem aggPack_outStage {n m : ℕ} {G : Subgroup (Perm (Fin n))}
    {ϕ : G →* Perm (Fin m)} {xs row : List ℕ} {hc : LCCtxWF n m xs row} {st : RawLCSt}
    (h : StateFor hc (Babai.outStage ϕ (decStrN n xs) (winSet m row)) st)
    (hfull : Babai.isFullOut ϕ (decStrN n xs) (winSet m row) ↔
      Babai.IsFull ϕ (decStrN n xs) (winSet m row)) :
    AggCertFor ϕ (decStrN n xs) row.length (aggPack (xs, row, lcOutOf ((xs, row), st))) := by
  refine ⟨aggPack_wf _ hc.lenStr hc.nodup hc.ltM rfl, (lcwOut_full h).trans hfull, ?_, ?_⟩
  · change decGroup n (tidyGens (xs, (lcOutOf ((xs, row), st)).2.2.1)) = _
    rw [decGroup_tidyGens hc.lenStr]
    exact lcwOut_certK h
  · change decGroup row.length (tidyGens (row, (lcOutOf ((xs, row), st)).2.2.2)) = _
    rw [decGroup_tidyGens rfl]
    exact lcwOut_certM h

/-- `PolyFun` gives a polynomial size bound on the read-off, even on malformed states. -/
theorem lcwSize_out : SizeBound lcOutOf := lcwPolyFun_out.size

theorem aggSize_add : SizeBound aggAdd := aggPolyFun_add.size

theorem aggSize_nonfull : SizeBound aggNonfull := aggPolyFun_nonfull.size

/-- The aggregate functions are quasipolynomial routines on the supplied table. -/
theorem aggQuasiPolyFun_F : QuasiPolyFun rawF := aggPolyFun_F.quasiPolyFun

theorem aggQuasiPolyFun_FGamma : QuasiPolyFun aggFGamma := aggPolyFun_FGamma.quasiPolyFun

theorem aggQuasiPolyFun_fixedGamma : QuasiPolyFun aggFixedGamma :=
  aggPolyFun_fixedGamma.quasiPolyFun

/-- Return from a large table to a small group. The domain witness is still bounded by
the original input, so the answer has a polynomial size bound there. -/
theorem aggQuasiPolyFun_F_of {α : Type*} [Enc α] {f : α → List ℕ × RawAggStore}
    (hf : QuasiFun f) (hd : ∀ a, (f a).1.length ≤ Enc.size a) :
    QuasiPolyFun (fun a => rawF (f a)) := by
  apply (hf.comp_poly aggPolyFun_F).quasiPolyFun
  obtain ⟨c, d, h⟩ := polyBound_gensBound
  exact ⟨c, d, fun a => (aggSize_F (f a)).trans
    ((mono_gensBound (hd a)).trans (h _))⟩

theorem aggQuasiPolyFun_FGamma_of {α : Type*} [Enc α] {f : α → RawAction × RawAggStore}
    (hf : QuasiFun f) (hd : ∀ a, (f a).1.2.1.length ≤ Enc.size a) :
    QuasiPolyFun (fun a => aggFGamma (f a)) := by
  apply (hf.comp_poly aggPolyFun_FGamma).quasiPolyFun
  obtain ⟨c, d, h⟩ := polyBound_gensBound
  exact ⟨c, d, fun a => (aggSize_FGamma (f a)).trans
    ((mono_gensBound (hd a)).trans (h _))⟩

theorem aggQuasiPolyFun_fixedGamma_of {α : Type*} [Enc α]
    {f : α → RawAction × RawAggStore} (hf : QuasiFun f)
    (hd : ∀ a, (f a).1.2.1.length ≤ Enc.size a) :
    QuasiPolyFun (fun a => aggFixedGamma (f a)) := by
  apply (hf.comp_poly aggPolyFun_fixedGamma).quasiPolyFun
  obtain ⟨c, d, h⟩ := polyBound_strBound
  exact ⟨c, d, fun a => (aggSize_fixedGamma (f a)).trans
    ((mono_strBound (hd a)).trans (h _))⟩

end Algo
