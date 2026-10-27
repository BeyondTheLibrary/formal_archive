import Workspace.Algo.TopMasterFourEntry
import Workspace.Algo.TopMasterRound

/-! # Alphabet bounds of the supplied top-action calls
Coset-form calls retain the source and target letters. Aligning a target
permutes its positions, and a window lift fills its complement with the
reference source. None of these steps introduces a new letter.
-/
namespace Algo
open Babai Equiv MulAction
open scoped Classical

 def MasterCallLetters {Ω : Type*} (k : ℕ) (J : SIInstance Ω ℕ) : Prop :=
  (∀ u, J.x u < k) ∧ ∀ u, J.y u < k

 theorem masterLetters_cosetChain {Ω : Type*} (k : ℕ) (x y : Ω → ℕ)
    (hx : ∀ u, x u < k) (hy : ∀ u, y u < k) :
    ∀ (L : List (Set Ω)) (C : Set (Perm Ω)) J,
      J ∈ (Babai.cosetChain x y L C).calls → MasterCallLetters k J := by
  intro L
  induction L with
  | nil => intro C J hJ; simp [Babai.cosetChain] at hJ
  | cons D L ih =>
    intro C J hJ
    simp only [Babai.cosetChain] at hJ
    split at hJ
    · simp at hJ
    · simp only [SIReduction.calls_call, List.mem_cons] at hJ
      rcases hJ with rfl | hJ
      · exact ⟨hx, hy⟩
      · exact ih _ _ hJ

 theorem masterLetters_giantA {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {G : Subgroup (Perm Ω)} {m k : ℕ} (ψ : G →* alternatingGroup (Fin m))
    (S : List (alternatingGroup (Fin m))) (E : OrbitEnum (kerSubgroup ψ)) (x y : Ω → ℕ)
    (hx : ∀ u, x u < k) (hy : ∀ u, y u < k) :
    ∀ J ∈ (cosetGiantAWith ψ S E x y).calls, MasterCallLetters k J := by
  refine SIReduction.mem_calls_expand_of_calls
    (f := fun J : SIInstance Ω ℕ => Babai.cosetChain J.x J.y E.windows J.K)
    (P := fun J => J.Δ = Set.univ ∧ MasterCallLetters k J)
    (fun J hJ => E.run_chain J hJ.1) ?_ _ ?_
  · intro J hJ
    exact masterLetters_cosetChain k J.x J.y hJ.2.1 hJ.2.2 E.windows J.K
  · intro J hJ
    rw [calls_cosetTopAction1, List.mem_map] at hJ
    obtain ⟨σ, _, rfl⟩ := hJ
    exact ⟨rfl, hx, hy⟩

 theorem masterLetters_top3 {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {G : Subgroup (Perm Ω)} {m k : ℕ} (ϕ : G →* Perm (Fin m))
    (S : List (alternatingGroup (Fin m))) (O : TopActionOdd ϕ)
    (E : OrbitEnum (kerSubgroup ϕ)) (x y : Ω → ℕ)
    (hx : ∀ u, x u < k) (hy : ∀ u, y u < k) :
    ∀ J ∈ (cosetTopAction3With ϕ S O E x y).calls, MasterCallLetters k J := by
  rw [cosetTopAction3With, SIReduction.calls_bind]
  intro J hJ
  rcases List.mem_append.mp hJ with hJ | hJ
  · exact masterLetters_giantA (altHom ϕ) S (E.alt ϕ) x x hx hx J hJ
  · split at hJ
    · simp at hJ
    · rw [SIReduction.calls_bind] at hJ
      rcases List.mem_append.mp hJ with hJ | hJ
      · exact masterLetters_cosetChain k x y hx hy _ _ J hJ
      · split at hJ
        · simp at hJ
        · simp only [SIReduction.calls_bind, SIReduction.calls_done, List.append_nil] at hJ
          exact masterLetters_cosetChain k x y hx hy _ _ J hJ

 theorem masterLetters_window {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {k : ℕ} (G : Subgroup (Perm Ω)) (D : Set Ω) (hinv : IsInvariant G D)
    (x : Ω → ℕ) (hx : ∀ u, x u < k) (J : SIInstance D ℕ) (hJ : MasterCallLetters k J) :
    MasterCallLetters k (windowInstance G D hinv x J) := by
  constructor
  · intro u
    change extendStr D x J.x u < k
    unfold extendStr
    split_ifs
    · exact hJ.1 _
    · exact hx u
  · intro u
    change extendStr D x J.y u < k
    unfold extendStr
    split_ifs
    · exact hJ.2 _
    · exact hx u

 theorem masterLetters_windowTop3 {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {m k : ℕ} (G : Subgroup (Perm Ω)) (D : Set Ω) (hinv : IsInvariant G D)
    (ϕ : restrictTo G D hinv →* Perm (Fin m))
    (S : List (alternatingGroup (Fin m))) (O : TopActionOdd ϕ)
    (E : OrbitEnum (kerSubgroup ϕ)) (x y : Ω → ℕ)
    (hx : ∀ u, x u < k) (hy : ∀ u, y u < k) :
    ∀ J ∈ (cosetWindowTopAction3With G D hinv ϕ S O E x y).calls, MasterCallLetters k J := by
  rw [cosetWindowTopAction3With, SIReduction.calls_bind, SIReduction.calls_done,
    List.append_nil, SIReduction.calls_window hinv x _ (calls_cosetTopAction3With_K ϕ S O E _ _)]
  intro J hJ
  obtain ⟨K, hK, rfl⟩ := List.mem_map.mp hJ
  exact masterLetters_window G D hinv x hx K
    (masterLetters_top3 ϕ S O E (restrictStr D x) (restrictStr D y)
      (fun u => hx u.val) (fun u => hy u.val) K hK)

 theorem masterLetters_top4Body {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {G : Subgroup (Perm Ω)} {m k : ℕ} (hG : IsTransitive G) (ϕ : G →* Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength G)) (C : Set (Fin m))
    (hC : m < 2 * C.ncard) (E : TopAction4Data hG ϕ hϕ hk C hC) (x y : Ω → ℕ)
    (hx : ∀ u, x u < k) (hy : ∀ u, y u < k) :
    ∀ J ∈ (cosetTopAction4BodyWith hG ϕ hϕ hk C hC E x y).calls, MasterCallLetters k J := by
  rw [cosetTopAction4BodyWith, SIReduction.calls_bind]
  intro J hJ
  rcases List.mem_append.mp hJ with hJ | hJ
  · exact masterLetters_windowTop3 _ _ _ _ E.generators E.odd E.orbits x y hx hy J hJ
  · split at hJ
    · simp at hJ
    · exact masterLetters_cosetChain k x y hx hy _ _ J hJ

 theorem masterLetters_top4 {Ω κ : Type*} [Fintype Ω] [DecidableEq Ω]
    {G : Subgroup (Perm Ω)} {m k : ℕ} (hG : IsTransitive G) (ϕ : G →* Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength G))
    (col : (Ω → ℕ) → Fin m → κ) (c : κ) (x y : Ω → ℕ)
    (hC : m < 2 * (colorClass col x c).ncard)
    (E : TopAction4Data hG ϕ hϕ hk (colorClass col x c) hC) (τ : G)
    (hx : ∀ u, x u < k) (hy : ∀ u, y u < k) :
    ∀ J ∈ (cosetTopAction4With hG ϕ hϕ hk col c x y hC E τ).calls, MasterCallLetters k J := by
  unfold cosetTopAction4With
  split
  · simp only [SIReduction.calls_bind, SIReduction.calls_done, List.append_nil]
    exact masterLetters_top4Body hG ϕ hϕ hk _ hC E x _ hx (fun u => hy _)
  · intro J hJ; simp at hJ

 theorem masterLetters_topwInstance {n k : ℕ} (Δ : List ℕ) (hnd : Δ.Nodup)
    (hlt : ∀ u ∈ Δ, u < n) (G : Subgroup (Perm (Fin n)))
    (hinv : IsInvariant G (winSet n Δ)) (x : Fin n → ℕ) (hx : ∀ u, x u < k)
    (J : SIInstance (Fin Δ.length) ℕ) (hJ : MasterCallLetters k J) :
    MasterCallLetters k (topwInstance Δ hnd hlt G hinv x J) := by
  constructor
  · intro u
    dsimp only [topwInstance]
    unfold extendStr
    split_ifs
    · exact hJ.1 _
    · exact hx u
  · intro u
    dsimp only [topwInstance]
    unfold extendStr
    split_ifs
    · exact hJ.2 _
    · exact hx u

 theorem master4Tree_letters {n m k : ℕ} {p : MasterHintInput}
    (hx : RawStr.WF n k p.1.2.2.2.1) (hy : RawStr.WF n k p.1.2.2.2.2)
    (hgs : RawGens.WF n p.1.2.1) (hnd : p.1.1.Nodup) (hlt : ∀ u ∈ p.1.1, u < n)
    (hinv : IsInvariant (decGroup n p.1.2.1) (winSet n p.1.1))
    {ϕ : decGroup p.1.1.length (masterHintTop p).1.1.2 →* Perm (Fin m)}
    (hp : RawAction.WF p.1.1.length m (masterHintTop p).1 ϕ)
    (hG : IsTransitive (decGroup p.1.1.length (masterHintTop p).1.1.2))
    (hϕ : IsGiantRep ϕ) (hn : 64 ≤ p.1.1.length) (hr : masterHintRoute p = 3) :
    ∀ J ∈ (master4Tree hnd hlt hinv hp hG hϕ hn hr).calls, MasterCallLetters k J := by
  have hxx := (masterStrWF_iff hx.1).mp hx
  have hyy := (masterStrWF_iff hy.1).mp hy
  have hix : ∀ u, decStrN p.1.1.length (masterHintTop p).2.1 u < k := by
    rw [show (masterHintTop p).2.1 = rawRestrictStr (p.1.2.2.2.1, p.1.1) from rfl,
      topwRestrictStr_decode hnd hlt]
    exact fun u => hxx _
  have hiy : ∀ u, decStrN p.1.1.length (masterHintTop p).2.2 u < k := by
    rw [show (masterHintTop p).2.2 = rawRestrictStr
      (top4aTarget (p.1.2.2.2.1, p.1.2.2.1, p.1.2.2.2.2), p.1.1) from rfl,
      top4aTarget_restrict hx.1 hnd hlt]
    exact fun u => hyy _
  let hm := masterHintRoute_huge hp.2.1 hn (by omega : masterHintRoute p ≠ 1)
  let ht := ((masterHintRoute_line4b p).mp hr).2.1
  let hs := ((masterHintRoute_line4b p).mp hr).2.2.2
  let T := top4PrimitiveTree hp hG hϕ hm ht (masterHintTop p).2.1 (masterHintTop p).2.2 hs
  have hT : ∀ J ∈ T.calls, MasterCallLetters k J := by
    exact masterLetters_top4 _ _ _ _ _ _ _ _ _ _ _ hix hiy
  have hK : ∀ J ∈ T.calls, J.K ⊆
      ((winRestrictHom n p.1.1 hnd hlt (decGroup n p.1.2.1) hinv).range : Set (Perm (Fin p.1.1.length))) := by
    rw [← masterLine4b_group hgs hnd hlt hinv]
    exact masterLine4b_inner_calls (n := n) hp hG hϕ hn hr
  simp only [master4Tree, masterLine4bTree, top4wTree, SIReduction.calls_bind,
    SIReduction.calls_done, List.append_nil]
  change ∀ J ∈ (topwReduction p.1.1 hnd hlt (decGroup n p.1.2.1) hinv
    (decStrN n p.1.2.2.2.1) T).calls, MasterCallLetters k J
  rw [calls_topwReduction hnd hlt hinv _ T hK]
  intro J hJ
  obtain ⟨K, hK, rfl⟩ := List.mem_map.mp hJ
  exact masterLetters_topwInstance p.1.1 hnd hlt _ hinv _ hxx K (hT K hK)
end Algo
