import Workspace.Algo.AggNodeCheckedWindow
import Workspace.Algo.RoundQ

/-! # A certificate carrier with a bounded child boundary

The raw phase keeps its state and its call order. Its children pass through
`aggnCheckedWindow`, so arbitrary cached data cannot enlarge the child domain.
The well-formedness predicate also bounds the stored parent context. These
are the instance-size obligations of `CostQ`; no fold-state bound is claimed.
-/
namespace Algo
open RAM RAM.Targets

/-- Normalize the optional window against the retained parent context. -/
def aggnCheckedNode (I : AggnPhaseNode) : AggnPhaseNode :=
  (I.1, I.2.map fun W => aggnCheckedWindow (I.1.2.1, W))

/-- A size condition on the input context, and structural bounds on every leaf. -/
def AggnCheckedWF (n : ℕ) (I : AggnPhaseNode) : Prop :=
  I.1.2.1.length = n ∧ Enc.size I.1 ≤ 2 * aggnCheckedWindowBound n ∧
    ∀ W, I.2 = some W → AggnCheckedWindowWF n W

/-- The checked boundary preserves whether the phase makes a call. -/
def aggnCheckedChild (c : ℕ) (z : AggnPhaseNode × ℕ × AggnPhaseState) :
    Option AggnPhaseNode := (aggnPhaseChild c z).map aggnCheckedNode

theorem aggnCheckedChild_some {c : ℕ} {z : AggnPhaseNode × ℕ × AggnPhaseState}
    {J : AggnPhaseNode} (h : aggnCheckedChild c z = some J) :
    z.1.2 = none ∧ ∃ W, aggnPhaseChild c z = some (z.1.1, some W) ∧
      J = (z.1.1, some (aggnCheckedWindow (z.1.1.2.1, W))) := by
  obtain ⟨J', hJ', rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨ho, W, rfl⟩ := aggnPhaseChild_some hJ'
  exact ⟨ho, W, hJ', rfl⟩

/-- The certificate phase with a total bounded child routine. -/
def aggnCheckedRound (c n : ℕ) : Round AggnPhaseNode AggnPhaseState RawCoset where
  WF := AggnCheckedWF n
  ground := (aggnPhaseRound c n).ground
  measure := (aggnPhaseRound c n).measure
  width := (aggnPhaseRound c n).width
  child := aggnCheckedChild c
  init := (aggnPhaseRound c n).init
  combine := (aggnPhaseRound c n).combine
  finish := (aggnPhaseRound c n).finish
  bot := (aggnPhaseRound c n).bot
  child_eq_none := by
    intro I j s hj
    unfold aggnCheckedChild
    change ((aggnPhaseRound c n).child (I, j, s)).map aggnCheckedNode = none
    rw [(aggnPhaseRound c n).child_eq_none I j s hj]
    rfl
  child_wf := by
    intro I j s J hI hJ
    obtain ⟨_, W, _, rfl⟩ := aggnCheckedChild_some hJ
    refine ⟨hI.1, hI.2.1, ?_⟩
    intro W' hW'
    cases Option.some.inj hW'
    simpa only [hI.1] using aggnCheckedWindow_wf I.1.2.1 W
  child_measure := by
    intro I j s J _ hJ
    obtain ⟨ho, W, _, rfl⟩ := aggnCheckedChild_some hJ
    change 0 < I.2.elim 1 (fun _ => 0)
    rw [ho]
    exact Nat.zero_lt_one
  child_ground := by
    intro I j s J _ hJ
    obtain ⟨_, W, _, rfl⟩ := aggnCheckedChild_some hJ
    exact le_rfl

/-- The retained context and the normalized leaf are both polynomially small. -/
def aggnCheckedBound (n : ℕ) : ℕ := 6 * aggnCheckedWindowBound n + 4

theorem aggnPolyBound_checked : PolyBound aggnCheckedBound :=
  ((polyBound_const 6).mul aggnPolyBound_checkedWindow).add (polyBound_const 4)

theorem aggnMono_checkedBound : Monotone aggnCheckedBound := by
  intro a b hab
  have h := aggnMono_checkedWindowBound hab
  dsimp [aggnCheckedBound]
  omega

theorem aggnCheckedRound_size (c n : ℕ) (I : AggnPhaseNode)
    (hI : (aggnCheckedRound c n).WF I) :
    Enc.size I ≤ aggnCheckedBound ((aggnCheckedRound c n).ground I) := by
  have hctx := hI.2.1
  have hp : Enc.size I ≤ 2 * Enc.size I.1 + 2 * Enc.size I.2 := Combine.size_pair_le _ _
  have ho : Enc.size I.2 ≤ aggnCheckedWindowBound n + 2 := by
    cases h : I.2 with
    | none => rw [Round.size_none_eq]; omega
    | some W =>
      have hs := aggnCheckedWindow_size (hI.2.2 W h)
      rw [size_some_eq]
      omega
  change Enc.size I ≤ aggnCheckedBound I.1.2.1.length
  rw [hI.1]
  dsimp [aggnCheckedBound]
  omega

/-- There is no hypothesis on the state, its size, or its reachability. -/
theorem aggnCheckedChild_size (c n : ℕ) (I : AggnPhaseNode)
    (hI : (aggnCheckedRound c n).WF I) (j : ℕ) (s : AggnPhaseState)
    {J : AggnPhaseNode} (hJ : aggnCheckedChild c (I, j, s) = some J) :
    Enc.size J ≤ aggnCheckedBound n := by
  have hw := (aggnCheckedRound c n).child_wf I j s J hI hJ
  simpa only [show (aggnCheckedRound c n).ground J = n from hw.1] using
    aggnCheckedRound_size c n J hw

/-- Normalized root contexts enter the checked carrier without a leaf condition. -/
theorem aggnCheckedWF_root {n : ℕ} {C : AggnPhaseCtx}
    (hlen : C.2.1.length = n) (hsize : Enc.size C ≤ 2 * aggnCheckedWindowBound n) :
    AggnCheckedWF n (C, none) :=
  ⟨hlen, hsize, fun _ h => by cases h⟩

/-- Short generator lists on a smaller domain fit the parent degree bound. -/
private theorem aggnSize_gens {d n : ℕ} {gs : RawGens}
    (hd : d ≤ n) (hw : RawGens.WF d gs) (hl : gs.length ≤ n * n) :
    Enc.size gs ≤ gensBound n := by
  have hs := size_list_le_of_entries gs (strBound n) (fun g hg =>
    size_natList_le (by rw [(hw g hg).length]; exact hd)
      (fun a ha => ((hw g hg).lt ha).trans_le hd))
  have ht := Nat.mul_le_mul_right (2 * strBound n + 1) hl
  dsimp [gensBound]
  omega

/-- A normal input representation satisfies the concrete context-size condition:
shortened generators and bounded names suffice. The action hypotheses also
bound the number and degrees of its stored image generators. -/
theorem aggnCheckedWF_of_context {c n m : ℕ} {C : AggnPhaseCtx}
    {ϕ : decGroup n C.1.1.2 →* Equiv.Perm (Fin m)}
    (hC : AggnPhaseCtxWF c n m C ϕ) (hshort : C.1.1.2.length ≤ n * n)
    (hletters : ∀ xs ∈ [C.1.1.1, C.1.2.1, C.2.1, C.2.2.1, C.2.2.2],
      ∀ a ∈ xs, a < 2 * n + 1) :
    AggnCheckedWF n (C, none) := by
  apply aggnCheckedWF_root hC.source
  have hlen : ∀ xs ∈ [C.1.1.1, C.1.2.1, C.2.1, C.2.2.1, C.2.2.2], xs.length ≤ n := by
    intro xs hxs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hxs
    rcases hxs with rfl | rfl | rfl | rfl | rfl
    · exact hC.action.1.le
    · exact hC.action.2.1.le.trans hC.degree
    · exact hC.source.le
    · exact hC.target.le
    · exact hC.arity
  have hs : ∀ xs ∈ [C.1.1.1, C.1.2.1, C.2.1, C.2.2.1, C.2.2.2],
      Enc.size xs ≤ strBound (2 * n + 1) := by
    intro xs hxs
    exact size_natList_le ((hlen xs hxs).trans (by omega)) (hletters xs hxs)
  have hdom := hs C.1.1.1 (by simp)
  have htop := hs C.1.2.1 (by simp)
  have hx := hs C.2.1 (by simp)
  have hy := hs C.2.2.1 (by simp)
  have ht := hs C.2.2.2 (by simp)
  have hgs := aggnSize_gens (le_refl n) hC.action.2.2.1 hshort
  have himglen : C.1.2.2.length = C.1.1.2.length := by
    simpa only [List.length_map] using hC.action.2.2.2.2.1.symm
  have himgs := aggnSize_gens hC.degree hC.action.2.2.2.1 (by rwa [himglen])
  have h0 : Enc.size C ≤ 2 * Enc.size C.1 + 2 * Enc.size C.2 := Combine.size_pair_le _ _
  have h1 : Enc.size C.1 ≤ 2 * Enc.size C.1.1 + 2 * Enc.size C.1.2 := Combine.size_pair_le _ _
  have h2 : Enc.size C.1.1 ≤ 2 * Enc.size C.1.1.1 + 2 * Enc.size C.1.1.2 := Combine.size_pair_le _ _
  have h3 : Enc.size C.1.2 ≤ 2 * Enc.size C.1.2.1 + 2 * Enc.size C.1.2.2 := Combine.size_pair_le _ _
  have h4 : Enc.size C.2 ≤ 2 * Enc.size C.2.1 + 2 * Enc.size C.2.2 := Combine.size_pair_le _ _
  have h5 : Enc.size C.2.2 ≤ 2 * Enc.size C.2.2.1 + 2 * Enc.size C.2.2.2 := Combine.size_pair_le _ _
  dsimp [aggnCheckedWindowBound]
  omega

/-- The extra work at the child boundary is polynomial on all inputs. -/
theorem aggnPolyFun_checkedNode : PolyFun aggnCheckedNode := by
  have hd : PolyFun (fun I : AggnPhaseNode => I.1.2.1) :=
    ((polyFun_fst.comp polyFun_snd).comp polyFun_fst)
  have hb : PolyFun (fun z : RawWinSI × AggnPhaseNode =>
      some (aggnCheckedWindow (z.2.1.2.1, z.1))) :=
    (((polyFun_snd.comp hd).pair polyFun_fst).comp aggnPolyFun_checkedWindow).comp polyFun_some
  have ho : PolyFun (fun I : AggnPhaseNode =>
      I.2.elim none (fun W => some (aggnCheckedWindow (I.1.2.1, W)))) :=
    (polyFun_snd.pair polyFun_id).comp (PolyFun.optionElim (polyFun_const none) hb)
  exact (polyFun_fst.pair ho).of_eq (fun I => by unfold aggnCheckedNode; cases I.2 <;> rfl)

end Algo
