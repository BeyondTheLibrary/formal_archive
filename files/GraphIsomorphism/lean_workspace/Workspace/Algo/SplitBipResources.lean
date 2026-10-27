import Workspace.Algo.SplitBipOrbit
import Workspace.Algo.SplitBipTurnChildren

/-! The fixed original degree, witness size, and threshold potential
survive every actual child. They give one storage bound for the whole
uncapped evaluator, measured in its initial input encoding. -/
namespace Algo
open RAM Babai

structure SbipResources (m n : ℕ) (I : RawSbipNode) : Prop where
  valid : SbipNodeValid m I
  degree : m ≤ n
  witness : Enc.size I.1.1 ≤ n
  alpha : sbipNodeAlphaPotential m I ≤ sbipAlphaEnvelope n

theorem SbipNodeRep.resources {m : ℕ} {I : RawSbipNode}
    {X : Pt (BipBlockInputs (Fin m))} (h : SbipNodeRep m I X) :
    SbipResources m (Enc.size I) I :=
  ⟨⟨X,h⟩,h.initial_resources.1,h.initial_resources.2.1,h.initial_resources.2.2⟩

theorem SbipResources.child {m n c j : ℕ} {I J : RawSbipNode}
    (h : SbipResources m n I) (hc : sbipNodeChild c (I,j) = some J) :
    SbipResources m n J := by
  obtain ⟨X,hX⟩ := h.valid
  refine ⟨sbipNodeChild_valid h.valid hc,h.degree,?_,
    (hX.child_alpha_potential hc).trans h.alpha⟩
  obtain ⟨g,_,rfl,_⟩ := sbipNodeChild_some hc
  exact h.witness

theorem exists_sbipNode_envelope :
    ∃ K : ℕ → ℕ,QuasiPolyBound K ∧ Monotone K ∧ (∀ n,n ≤ K n) ∧
      ∀ m n c j I J,SbipResources m n I → sbipNodeChild c (I,j) = some J → Enc.size J ≤ K n := by
  obtain ⟨K,hK,hmK,hk⟩ := exists_sbipNodeChild_bound
  refine ⟨fun n => K n+n,hK.add polyBound_id.quasiPoly,?_,?_,?_⟩
  · intro a b hab
    exact Nat.add_le_add (hmK hab) hab
  · intro n; exact Nat.le_add_left _ _
  · intro m n c j I J h hc
    obtain ⟨X,hX⟩ := h.valid
    obtain ⟨g,hg,rfl,_⟩ := sbipNodeChild_some hc
    exact (hk c n m I X hX h.degree h.witness h.alpha g
      (List.mem_of_getElem? hg)).trans (Nat.le_add_right _ _)

theorem exists_sbipOrbit_envelope (c : ℕ) (q : ℕ → ℕ) (hq : QuasiPolyBound q) :
    ∃ B : ℕ → ℕ,QuasiPolyBound B ∧
      ∀ m I,SbipNodeValid m I → ∀ t,t ≤ q (Enc.size I) →
        Enc.size ((sbipRound c).stepDFS^[t] ((sbipRound c).startState I)) ≤ B (Enc.size I) := by
  obtain ⟨K,hK,hmK,hKid,hchild⟩ := exists_sbipNode_envelope
  obtain ⟨S,hS,hmS,hs⟩ := (quasiFun_sbipNodeInit c).size.exists_quasiPolyBound
  let L := fun n => S (K n)+n+1
  have hL : QuasiPolyBound L := ((hS.comp hK).add polyBound_id.quasiPoly).add
    (polyBound_const 1).quasiPoly
  refine ⟨fun n => sbipOrbitBound (K n) (L n) (q n),quasiPolyBound_sbipOrbitBound hK hL hq,?_⟩
  intro m I hI t ht
  let N := Enc.size I
  let P : RawSbipNode → Prop := fun J => SbipResources m N J ∧ Enc.size J ≤ K N
  have hp : ∀ J j J',P J → sbipNodeChild c (J,j) = some J' → P J' := by
    intro J j J' hJ hc
    exact ⟨hJ.1.child hc,hchild m N c j J J' hJ.1 hc⟩
  have hroot : P I := by
    obtain ⟨X,hX⟩ := hI
    exact ⟨hX.resources,hKid N⟩
  apply sbipOrbit_size_le c P (K N) (L N) (q N) hp (fun _ h => h.2) _ _ hroot ht
  · intro J hJ
    obtain ⟨X,hX⟩ := hJ.1.valid
    have hl := hX.first_length_le.trans hJ.1.degree
    exact hl.trans (by dsimp [L]; omega)
  · intro J hJ
    exact ((hs J).trans (hmS _ _ hJ.2)).trans (by dsimp [L]; omega)

end Algo
