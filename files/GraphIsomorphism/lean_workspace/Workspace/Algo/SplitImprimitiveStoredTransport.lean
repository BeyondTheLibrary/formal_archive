import Workspace.Algo.SplitImprimitiveFamilyTransport
import Workspace.Algo.SplitImprimitiveStoredFamily
import Workspace.Algo.SplitBipTurnInvariant

/-! Transport the actual stored graphs selected by ImprimitiveCase.
The two dictionaries and their compact orders are independent; each is
read through its member-row invariant. Thus the graph isomorphism keeps
all point colors, block colors, edges, and hints after restoration.
-/
namespace Algo
open Babai RAM
open scoped Classical
section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s t : Set Ω}
    {X : BlkImprimitiveObj s} {Y : BlkImprimitiveObj t} {φ : ↥s ≃ ↥t}
    (hφ : φ ∈ (BlkImprimitiveCases Ω).Iso X Y)
    {r r' : RawUpccCase}
    {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {name₁' : ↥Y.Pt₁ → ℕ} {name₂' : ↥Y.blocks → ℕ}
    (hn : ImpNames X name₁ name₂ r) (hn' : ImpNames Y name₁' name₂' r')
    (hl : r.2.1.Nodup) (hr : r.2.2.Nodup)
    (hl' : r'.2.1.Nodup) (hr' : r'.2.2.Nodup)
    (e₂ : ↥X.blocks ≃ Fin r.2.2.length) (he₂ : ∀ B,r.2.2[(e₂ B).val] = name₂ B)
    (e₂' : ↥Y.blocks ≃ Fin r'.2.2.length) (he₂' : ∀ B,r'.2.2[(e₂' B).val] = name₂' B)
    (point : ↥s → ℕ) (point' : ↥t → ℕ) (dom dom' : List ℕ) (d d' : List (List ℕ))
    (hd : ImpStoredNames X name₁ name₂ point d)
    (hd' : ImpStoredNames Y name₁' name₂' point' d')
    (hp : Function.Injective point) (hp' : Function.Injective point')
    (hlt : ∀ x,point x < dom.length) (hlt' : ∀ x,point' x < dom'.length)
include hφ hn hn' hl hr hl' hr' he₂ he₂' hd hd' hp hp' hlt hlt'

theorem impStoredGraphs_transport (hsplit : ¬ ImprimitiveSplits X)
    (g : RawSbipStored) (hg : g ∈ impStoredGraphs ((dom,d),r)) :
    ∃ g' ∈ impStoredGraphs ((dom',d'),r'),
      ∃ (G : VColBipBlk ↥s ℕ) (G' : VColBipBlk ↥t ℕ),
        SbipStoredRep G point g ∧ SbipStoredRep G' point' g' ∧ G.IsIsoTo G' φ := by
  obtain ⟨q,hq,rfl⟩ := (impStoredGraphs_mem _ _).1 hg
  obtain ⟨q',hq',G,G',hrep,hrep',hiso,_⟩ :=
    impStep2Graphs_transport hφ hn hn' hl hr hl' hr' e₂ he₂ e₂' he₂' hsplit q hq
  exact ⟨impStoredGraph ((dom',d'),q'),(impStoredGraphs_mem _ _).2 ⟨q',hq',rfl⟩,
    G,G',impStoredGraph_complete hrep hn hl point dom d hd hq hp hlt,
    impStoredGraph_complete hrep' hn' hl' point' dom' d' hd' hq' hp' hlt',hiso⟩

end
end Algo
