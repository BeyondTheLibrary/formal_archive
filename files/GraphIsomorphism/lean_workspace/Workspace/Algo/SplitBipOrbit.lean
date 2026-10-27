import Workspace.Algo.FamilyOrbit
import Workspace.Algo.SplitBipAnswerSize
import Workspace.Algo.SplitBipStoredBounds
import Workspace.Algo.SplitBipNodeRAM

/-! A complete uncapped run stores only the local families it has already
initialized. Partition labels gain at most one bit per fold. Combining
these facts gives a bound for every intermediate machine state. -/
namespace Algo
open RAM Babai

def sbipOrbitBound (K L T : ℕ) : ℕ :=
  Round.familyStateBound K T ((T+1)*L) (sbipOutcomeBound L (L+T)) (T+1)

theorem quasiPolyBound_sbipOrbitBound {K L T : ℕ → ℕ}
    (hK : QuasiPolyBound K) (hL : QuasiPolyBound L) (hT : QuasiPolyBound T) :
    QuasiPolyBound (fun n => sbipOrbitBound (K n) (L n) (T n)) := by
  have hc (c : ℕ) := (polyBound_const c).quasiPoly
  have hB : QuasiPolyBound (fun n => sbipOutcomeBound (L n) (L n+T n)) :=
    (((hc 8).mul ((hc 1).add (hL.mul
      (((hc 2).mul ((hL.add hT).add (hc 2))).add (hc 1))))).add
        ((hc 2).mul hL)).add (hc 8)
  exact Round.quasiPolyBound_familyStateBound hK hT
    ((hT.add (hc 1)).mul hL) hB (hT.add (hc 1))

theorem sbipOrbit_size_le (c : ℕ) (P : RawSbipNode → Prop) (K L T : ℕ)
    (hpres : ∀ I j J,P I → sbipNodeChild c (I,j) = some J → P J)
    (hnode : ∀ I,P I → Enc.size I ≤ K)
    (hleft : ∀ I,P I → I.1.2.1.1.1.1.length ≤ L)
    (hinit : ∀ I,P I → Enc.size (sbipNodeInit c I) ≤ L)
    {I : RawSbipNode} (hI : P I) {t : ℕ} (ht : t ≤ T) :
    Enc.size ((sbipRound c).stepDFS^[t] ((sbipRound c).startState I)) ≤ sbipOrbitBound K L T := by
  let R := sbipRound c
  have hp : ∀ I j s J,P I → R.child (I,j,s) = some J → P J :=
    fun I j s J hI hc => hpres I j J hI hc
  have hn := R.familyNodes_iterate P hp hI t
  have hmass := R.familyMass_iterate_le P L
    (fun I hI => (length_le_size _).trans (hinit I hI))
    (fun _ _ _ => le_rfl)
    (fun I j s A hI => by simp [R,sbipRound,sbipNodeCombine]) hp hI t
  let G : ℕ → RawAlignOutcome → Prop := fun t o => SbipOutcomeSize L (L+t) o
  have hmono : ∀ t o,G t o → G (t+1) o :=
    fun t o ho => ho.mono le_rfl (by omega)
  have hi : ∀ I,P I → ∀ t o,o ∈ R.init I → G t o := by
    intro I hI t o ho
    exact (sbipOutcomeSize_of_size ((size_mem_le ho).trans (hinit I hI))).mono le_rfl (by omega)
  have hc : ∀ I j s A,P I → ∀ t,(∀ o ∈ s,G t o) → (∀ o ∈ A,G t o) →
      ∀ o ∈ R.combine (I,j,s,A),G (t+1) o := by
    intro I j s A hI t hs hA o ho
    change o ∈ s ++ A.map _ at ho
    rcases List.mem_append.1 ho with ho | ho
    · exact hmono t o (hs o ho)
    · obtain ⟨a,ha,rfl⟩ := List.mem_map.1 ho
      exact sbipNodeLift_size_shape _ _ (hleft I hI) (hA a ha)
  have hg := R.familyGood_iterate P G hmono hi (fun _ _ _ _ hs => hs) hc hp hI t
  have hidx := R.family_indices_iterate I t
  apply Round.size_familyState_le
  · exact fun fr hf => hnode fr.1 (hn fr hf)
  · exact fun fr hf => (hidx.2 fr hf).trans ht
  · constructor
    · intro fr hf o ho
      exact ((hg.1 fr hf o ho).mono le_rfl (Nat.add_le_add_left ht L)).size_le
    · intro A hA o ho
      exact ((hg.2 A hA o ho).mono le_rfl (Nat.add_le_add_left ht L)).size_le
  · exact hmass.trans (Nat.mul_le_mul_right L (Nat.add_le_add_right ht 1))
  · exact hidx.1.trans (Nat.add_le_add_right ht 1)

end Algo
