import Workspace.Algo.TopMasterDescentRaw
import Workspace.Algo.AggCanonRecompute
import Workspace.Algo.TopMasterCheckedMatch

/-! # The ordered kernel-coset and orbit lists for master descent
The representative scan runs over the indices of two guarded tuple tables.
The first has the image domain as arity and domain. On the small-image
route of line 2 it contains every image-group element. The second has
arity `log₂ n + 2` over the ground set, so it has `n^{log₂ n + 2}` entries.
This covers the image of the block action at line 1, step 5, where the
number of blocks can be large but the image order is at most
`m^{2 + log₂ m}`. The scan takes the first `|Ḡ|` indices, in
stabilizer-chain order. Each representative is followed by the same
ordered kernel-orbit chain.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Classical Pointwise

 /-- The arity `min n (log₂ n + 2)` of the second index table, as a list. -/
 def masterDescArity (xs : RawStr) : List ℕ := (rawOne xs).take (Nat.log 2 xs.length + 2)

 /-- The index keys of both tables: first the image-domain table, then the
 ground table. -/
 def masterDescKeys (c : ℕ) (p : MasterDescInput) : List (List ℕ × ℕ) :=
  (aggTable c (p.2.1, p.1.2.2.2.1, p.2.1)).2 ++
    (aggTable 2 (masterDescArity p.1.2.2.2.1, p.1.2.2.2.1, rawOne p.1.2.2.2.1)).2

 def masterDescFuel (c : ℕ) (p : MasterDescInput) : List ℕ :=
  (List.range (masterDescKeys c p).length).take (masterDescWidth p)

 def masterDescReps (c : ℕ) (p : MasterDescInput) : RawGens :=
  (masterDescFuel c p).map (fun j => masterDescRep (p, j))

 def masterDescLists (c : ℕ) (p : MasterDescInput) : AggnRecomputeInput :=
  (p.1, topKernel (masterDescAction p), masterDescReps c p,
    winOrbits (topKernel (masterDescAction p), p.1.1))

 theorem polyFun_masterDescArity : PolyFun masterDescArity :=
  (polyFun_rawOne.pair ((polyFun_length.comp polyFun_log2).add (polyFun_const 2))).comp
    polyFun_take

 theorem quasiFun_masterDescKeys (c : ℕ) : QuasiFun (masterDescKeys c) := by
  have ht : PolyFun (fun p : MasterDescInput => p.2.1) := polyFun_snd.comp polyFun_fst
  have hx : PolyFun (fun p : MasterDescInput => p.1.2.2.2.1) :=
    (((polyFun_fst.comp polyFun_snd).comp polyFun_snd).comp polyFun_snd).comp polyFun_fst
  have h1 := ((ht.pair (hx.pair ht)).comp_quasiFun (aggQuasiFun_table c)).comp_poly polyFun_snd
  have h2 := (((hx.comp polyFun_masterDescArity).pair (hx.pair (hx.comp polyFun_rawOne))).comp_quasiFun
    (aggQuasiFun_table 2)).comp_poly polyFun_snd
  exact (h1.pair h2).comp_poly polyFun_append

 theorem quasiFun_masterDescFuel (c : ℕ) : QuasiFun (masterDescFuel c) := by
  have h := (quasiFun_masterDescKeys c).comp_poly polyFun_rangeLength
  exact (h.pair polyFun_masterDescWidth.quasiFun).comp_poly polyFun_take

 theorem quasiFun_masterDescReps (c : ℕ) : QuasiFun (masterDescReps c) :=
  (polyFun_id.quasiFun.pair (quasiFun_masterDescFuel c)).comp_poly
    (PolyFun.mapParam polyFun_masterDescRep)

 theorem quasiFun_masterDescLists (c : ℕ) : QuasiFun (masterDescLists c) := by
  have hk := polyFun_masterDescAction.comp polyFun_topKernel
  exact polyFun_fst.quasiFun.pair (hk.quasiFun.pair
    ((quasiFun_masterDescReps c).pair
      ((hk.pair (polyFun_fst.comp polyFun_fst)).comp polyFun_winOrbits).quasiFun))

 /-- The scan runs over exactly the first `|Ḡ|` indices when there are enough keys. -/
 theorem masterDescFuel_eq_of_le {c : ℕ} {p : MasterDescInput}
    (hk : masterDescWidth p ≤ (masterDescKeys c p).length) :
    masterDescFuel c p = List.range (masterDescWidth p) := by
  rw [masterDescFuel, List.take_range, Nat.min_eq_left hk]

 theorem masterDescFuel_eq {c : ℕ} {p : MasterDescInput}
    (hg : p.2.1.length ≤ guardBound c p.1.2.2.2.1.length)
    (hi : masterDescWidth p ≤ Nat.factorial p.2.1.length) :
    masterDescFuel c p = List.range (masterDescWidth p) := by
  apply masterDescFuel_eq_of_le
  rw [masterDescKeys, List.length_append, aggTable_of_guard hg, tupleTable, List.length_map,
    length_tuplesOf]
  exact (hi.trans (Nat.factorial_le_pow _)).trans (Nat.le_add_right _ _)

 theorem length_masterDescArity (xs : RawStr) :
    (masterDescArity xs).length = min (Nat.log 2 xs.length + 2) xs.length := by
  rw [masterDescArity, List.length_take, rawOne, List.length_range]

 theorem masterDescArity_guard (xs : RawStr) :
    (masterDescArity xs).length ≤ guardBound 2 xs.length := by
  rw [length_masterDescArity, guardBound]
  rcases Nat.eq_zero_or_pos (Nat.log 2 xs.length) with h | h
  · have h2 : xs.length < 2 := by
      rcases Nat.log_eq_zero_iff.mp h with h' | h'
      · exact h'
      · omega
    rw [h]
    exact (Nat.min_le_right _ _).trans (by omega)
  · refine (Nat.min_le_left _ _).trans ?_
    nlinarith

 theorem add_two_le_two_pow : ∀ L : ℕ, 2 ≤ L → L + 2 ≤ 2 ^ L
  | 0, h => absurd h (by omega)
  | 1, h => absurd h (by omega)
  | 2, _ => by norm_num
  | L + 3, _ => by
    have := add_two_le_two_pow (L + 2) (by omega)
    rw [pow_succ]
    omega

 /-- **The ground table covers large images.** When `n ≥ 4`, the second table
 has `n^{log₂ n + 2}` keys, so the scan covers every image of order at most
 that. -/
 theorem masterDescFuel_eq_of_ground {c : ℕ} {p : MasterDescInput}
    (hn : 4 ≤ p.1.2.2.2.1.length)
    (hi : masterDescWidth p ≤ p.1.2.2.2.1.length ^ (Nat.log 2 p.1.2.2.2.1.length + 2)) :
    masterDescFuel c p = List.range (masterDescWidth p) := by
  apply masterDescFuel_eq_of_le
  rw [masterDescKeys, List.length_append,
    aggTable_of_guard (c := 2) (masterDescArity_guard _), tupleTable, List.length_map,
    length_tuplesOf, length_masterDescArity, rawOne, List.length_range]
  have hlog : Nat.log 2 p.1.2.2.2.1.length + 2 ≤ p.1.2.2.2.1.length := by
    have h4 : 2 ≤ Nat.log 2 p.1.2.2.2.1.length :=
      Nat.le_log_of_pow_le (by norm_num) (by simpa using hn)
    exact (add_two_le_two_pow _ h4).trans (Nat.pow_log_le_self 2 (by omega))
  rw [Nat.min_eq_left hlog]
  exact hi.trans (Nat.le_add_left _ _)

section Spec
variable {n m c : ℕ} {p : MasterDescInput}
    {ϕ : decGroup n p.1.2.1 →* Perm (Fin m)}
    (hp : RawAction.WF n m (masterDescAction p) ϕ)
    (hg : masterDescFuel c p = List.range (masterDescWidth p))

include hp in
 theorem masterDescWidth_le_factorial : masterDescWidth p ≤ Nat.factorial p.2.1.length := by
  rw [masterDescWidth_spec hp, show p.2.1.length = m from hp.2.1]
  have h := Subgroup.card_le_card_group ϕ.range
  simpa only [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] using h

include hp hg in
 theorem masterDescLists_reps : aggnrReps n (masterDescLists c p) = masterDescPerms n p := by
  simp only [aggnrReps, masterDescLists, masterDescReps,
    hg, masterDescPerms, List.map_map]
  rfl

include hp hg in
 theorem masterDescLists_count : aggnrCount (masterDescLists c p) = masterDescWidth p := by
  simp only [aggnrCount, masterDescLists, masterDescReps, List.length_map,
    hg, List.length_range]

include hp hg in
 theorem masterDescLists_cover : (decWinSI n p.1).K =
    ⋃ σ ∈ aggnrReps n (masterDescLists c p),
      σ • (decGroup n (masterDescLists c p).2.1 : Set (Perm (Fin n))) := by
  rw [masterDescLists_reps hp hg]
  exact masterDesc_cover hp

end Spec

 noncomputable def masterDescStrongTree (n c : ℕ) (p : MasterDescInput) :
    SIReduction (Fin n) ℕ (Set (Perm (Fin n))) :=
  let P := masterDescLists c p
  strongDescent (decGroup n P.2.1) (decStrN n p.1.2.2.2.1) (decStrN n p.1.2.2.2.2)
    (aggnrReps n P) ((aggnrWindows P).map (winSet n))

 theorem masterDescStrongTree_letters {n c k : ℕ} {p : MasterDescInput}
    (hx : ∀ u, decStrN n p.1.2.2.2.1 u < k)
    (hy : ∀ u, decStrN n p.1.2.2.2.2 u < k) :
    ∀ J ∈ (masterDescStrongTree n c p).calls, MasterCallLetters k J := by
  intro J hJ
  rw [masterDescStrongTree, calls_strongDescent, List.mem_flatMap] at hJ
  obtain ⟨σ, _, hJ⟩ := hJ
  exact masterLetters_cosetChain k _ _ hx hy _ _ J hJ

 theorem masterDescStrongTree_calls_le {n m c : ℕ} {p : MasterDescInput}
    {ϕ : decGroup n p.1.2.1 →* Perm (Fin m)}
    (hp : RawAction.WF n m (masterDescAction p) ϕ)
    (hg : masterDescFuel c p = List.range (masterDescWidth p)) :
    (masterDescStrongTree n c p).calls.length ≤ masterDescWidth p * p.1.1.length := by
  refine (length_calls_strongDescent _ _ _ _ _).trans ?_
  rw [aggnrReps_length, masterDescLists_count hp hg, List.length_map]
  exact Nat.mul_le_mul_left _ (length_winOrbits_le _ _)

end Algo
