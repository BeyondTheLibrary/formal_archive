import Workspace.Algo.SplitBipSingleton
import Workspace.Algo.SplitBipRunSpec

/-! The paper's vertex-colored bipartite input enters the recursive RAM
routine through singleton blocks. The bounds are fixed before the input
degree, and the original first-part names are used to read the answers. -/
namespace Algo
open Babai RAM
open scoped Classical

abbrev RawBipInput := RawSbipSingleton × (ℕ × ℕ)

def bipInputNode (r : RawBipInput) : RawSbipNode :=
  ((r.1.1,sbipSingletonStored r.1,r.2),1)

def bipInputRun (c t d : ℕ) (r : RawBipInput) : Option RawSbipAnswers :=
  sbipRun c t d (bipInputNode r)

theorem polyFun_bipInputNode : PolyFun bipInputNode :=
  (((polyFun_fst.comp polyFun_fst).pair
    ((polyFun_fst.comp polyFun_sbipSingletonStored).pair polyFun_snd)).pair
      (polyFun_const 1))

theorem quasiFun_bipInputRun (c t d : ℕ) : QuasiFun (bipInputRun c t d) :=
  polyFun_bipInputNode.comp_quasiFun (quasiFun_sbipRun c t d)

structure BipInputRep (m : ℕ) (r : RawBipInput) (X : Pt (BipInputs (Fin m))) : Prop where
  ground : r.1.1.length = m
  graph : UpccBipRep (Equiv.Set.univ (Fin m)) r.1.2.1 r.1.2.2
    (Set.subset_univ X.car) X.obj.1.1
  alpha : sbipAlphaValue r.2 = BipInputs.alpha X
  denominator : 0 < r.2.2

theorem BipInputRep.node {m : ℕ} {r : RawBipInput} {X : Pt (BipInputs (Fin m))}
    (h : BipInputRep m r X) : SbipNodeRep m (bipInputNode r) (bipToBlkObj X) := by
  refine ⟨h.ground,?_,h.alpha,h.denominator,?_⟩
  · exact sbipSingletonStored_complete (Equiv.Set.univ (Fin m))
      (Set.subset_univ X.car) X.obj.1.1 _ _ h.graph r.1.1 (h.ground ▸ le_rfl)
  · simp [bipInputNode,sbipNodeBit]

/-- The actual ordinary bipartite RAM routine returns a nonempty family
whose every member satisfies Theorem 9.2.2. Canonical transport of the
whole family is a separate obligation. -/
theorem exists_bipInputRun_valid (c : ℕ) :
    ∃ t d,QuasiFun (bipInputRun c t d) ∧
      ∀ m r (X : Pt (BipInputs (Fin m))),BipInputRep m r X →
      ∃ A,bipInputRun c t d r = some A ∧ (∃ o,o ∈ A) ∧
        ∀ o ∈ A,∃ Z,sbipDecodeNamed m r.1.2.2.1 o = some Z ∧
          IsSplitOutcome (BipInputs.alpha X) (BipInputs.V₁ X) Z := by
  obtain ⟨t,d,hr,he⟩ := exists_sbipRun_valid c
  refine ⟨t,d,quasiFun_bipInputRun c t d,?_⟩
  intro m r X h
  obtain ⟨A,hA,hne,hgood⟩ := he m (bipInputNode r) ⟨bipToBlkObj X,h.node⟩
  exact ⟨A,hA,hne,fun o ho => hgood (bipToBlkObj X) h.node o ho⟩

end Algo
