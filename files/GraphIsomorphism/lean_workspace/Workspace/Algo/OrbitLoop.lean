/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

§1.1, Corollary 1.1.3: the reduction to the orbits, on raw data.
-/
import Workspace.Algo.OrbitSolver

/-!
# Corollary 1.1.3: String Isomorphism one orbit at a time

The paper derives Corollary 1.1.3 from Theorem 1.1.1 as "an immediate consequence" without
spelling out the reduction. The reduction it implies is Luks's Chain Rule over the orbits,
Eq. (63) of §11.1 iterated over the orbit partition, Eq. (64), with each window instance
solved by restricting it to its orbit (Observation 11.1.11 and Eq. (59), §11.1):

* let `Δ₁, …, Δ_k` be the orbits of `G`, and `C₀ = G`;
* for `j = 1, …, k`: `C_j = Iso^{Δ_j}_{C_{j-1}}(x, y)`.  When `C_{j-1} = ρ H` is a coset of a
  subgroup `H ≤ G`, the orbit `Δ_j` is `H`-invariant, and
  `Iso^{Δ_j}_{ρH}(x,y) = ρ · Iso^{Δ_j}_H(x, y^{ρ⁻¹})` (Eq. (59)); the set `Iso^{Δ_j}_H(x, y')`
  is the preimage, under the restriction `H → H^{Δ_j}`, of the set of isomorphisms of the
  restricted strings under `H^{Δ_j}` (Obs. 11.1.11). That is a String Isomorphism instance on
  `|Δ_j| ≤ n₀(G)` points, which the routine of Theorem 1.1.1 solves;
* `C_k = Iso^{Δ₁ ∪ … ∪ Δ_k}_G(x,y) = Iso_G(x,y)`.

So the routine of Theorem 1.1.1 is called at most `n` times, each time on an instance of
size polynomial in `n₀(G)`, and everything else is polynomial in the input size. That is
the time bound of Corollary 1.1.3.

This file defines the loop on raw data and proves what it computes. The running time is in
`Workspace/Algo/OrbitTime.lean`.

## Main definitions

* `Algo.orbLeaf`: one window instance, solved by restriction to its window and a call of a
  solver on the normalized restricted instance, then lifted back;
* `Algo.OrbState`, `Algo.orbStep`: the state of the loop and one step;
* `Algo.orbSetUp`: the orbits of `G` and the initial coset `G`.

## Main results

* `Algo.orbLeaf_spec`: Obs. 11.1.11 with Eq. (59) on raw data;
* `Algo.orbStep_iterate_spec`: after `j` steps the state holds `Iso^{Δ₁∪…∪Δ_j}_G(x,y)`;
* `Algo.orbFinal_spec`: after all the orbits the state holds `Iso_G(x,y)`.
-/

namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Pointwise

/-! ## One window instance, solved on its window -/

/-- **One window instance solved by restriction** (Obs. 11.1.11 with Eq. (59)): restrict the
group and the shifted strings to the window, normalize, call `sol`, lift the answer back to the
group and shift it by the representative. -/
def orbLeaf (sol : RawSI → RawCoset) (p : RawWinSI) : RawCoset :=
  top3Shift (p.2.2.2.1, p.2.2.1,
    topwCosetPreimage ((p.2.2.2.1, p.2.1), p.1, sol (rawNormSI (primitiveWindowInput p))))

/-- What a solver has to do: on every normalized instance, describe the set of isomorphisms. -/
def SolverSpec (sol : RawSI → RawCoset) : Prop :=
  ∀ (m : ℕ) (r : RawSI), NormSIWF m r →
    decCoset m (sol r) =
      strIso (decGroup m r.1 : Set (Perm (Fin m))) (decStrN m r.2.1) (decStrN m r.2.2)

/-- The normalized restricted instance is normalized for the window size. -/
theorem normSIWF_window (p : RawWinSI) :
    NormSIWF p.1.length (rawNormSI (primitiveWindowInput p)) :=
  rawNormSI_wf _ (length_rawRestrictStr _ _) (length_rawRestrictStr _ _)

/-- **Observation 11.1.11 with Eq. (59), on raw data.**  If the solver is correct, the window
instance is answered correctly. -/
theorem orbLeaf_spec {sol : RawSI → RawCoset} (hsol : SolverSpec sol) {n : ℕ} {p : RawWinSI}
    (hx : p.2.2.2.1.length = n) (hgs : RawGens.WF n p.2.1)
    (hnd : p.1.Nodup) (hlt : ∀ u ∈ p.1, u < n)
    (hinv : IsInvariant (decGroup n p.2.1) (winSet n p.1)) :
    decCoset n (orbLeaf sol p) = (decWinSI n p).answer := by
  have hgroup := decGroup_rawRestrictGens_of_raw (dom := p.2.2.2.1) hgs hnd hlt hinv
  have hI1 : (primitiveWindowInput p).2.1.length = p.1.length := length_rawRestrictStr _ _
  have hI2 : (primitiveWindowInput p).2.2.length = p.1.length := length_rawRestrictStr _ _
  have hs := hsol p.1.length (rawNormSI (primitiveWindowInput p)) (normSIWF_window p)
  have hi : decCoset p.1.length (sol (rawNormSI (primitiveWindowInput p))) =
      strIso (decGroup p.1.length (rawRestrictGens ((p.2.2.2.1, p.2.1), p.1)) :
          Set (Perm (Fin p.1.length)))
        (decStrN p.1.length (rawRestrictStr (p.2.2.2.1, p.1)))
        (decStrN p.1.length
          (rawRestrictStr (top4aTarget (p.2.2.2.1, p.2.2.1, p.2.2.2.2), p.1))) := by
    rw [hs, decGroup_rawNormSI _ hI1]
    exact strIso_rawRenameStr _ ((primitiveWindowInput p).2.1 ++ (primitiveWindowInput p).2.2)
      (primitiveWindowInput p).2.1 (primitiveWindowInput p).2.2 hI1 hI2
      (fun _ h => List.mem_append_left _ h) (fun _ h => List.mem_append_right _ h)
  rw [hgroup, topwRestrictStr_decode hnd hlt, top4aTarget_restrict hx hnd hlt] at hi
  have hsub : decCoset p.1.length (sol (rawNormSI (primitiveWindowInput p))) ⊆
      ((winRestrictHom n p.1 hnd hlt (decGroup n p.2.1) hinv).range :
        Set (Perm (Fin p.1.length))) := by
    rw [hi]
    exact fun _ h => h.1
  have hpre := topwCosetPreimage_spec (gens := p.2.1.map (decPerm n)) hx hnd hlt hinv
    (sol (rawNormSI (primitiveWindowInput p))) hsub
  simp only [map_encPerm_decPerm hgs] at hpre
  change decCoset n _ = topwPreimageSet p.1 hnd hlt (decGroup n p.2.1) hinv
    (decCoset p.1.length (sol (rawNormSI (primitiveWindowInput p)))) at hpre
  rw [orbLeaf, decCoset_top3Shift hx, hpre, hi]
  rw [topwPreimage_strIso hnd hlt hinv]
  change _ = wIso (winSet n p.1) (decCoset n (some (p.2.1, p.2.2.1))) _ _
  rw [decCoset_some, wIso_smul]
  rfl

/-! ## The loop -/

/-- The state of the loop: the orbits still to be processed, the two strings, and the coset
reached so far (`none` once it is empty). -/
abbrev OrbState := List (List ℕ) × RawStr × RawStr × RawCoset

/-- The window instance of the next orbit. When the coset is already empty, the group and the
representative are placeholders; the step ignores the answer then. -/
def orbWin (st : OrbState) : RawWinSI :=
  (st.1.headD [], (st.2.2.2.getD ([], [])).1, (st.2.2.2.getD ([], [])).2, st.2.1, st.2.2.1)

/-- The instance the solver is called on in one step. -/
def orbPre (st : OrbState) : RawSI := rawNormSI (primitiveWindowInput (orbWin st))

/-- The rest of one step, given the answer `q.2` of the solver: lift and shift, and drop the
orbit. -/
def orbPost (q : OrbState × RawCoset) : OrbState :=
  (q.1.1.tail, q.1.2.1, q.1.2.2.1,
    q.1.2.2.2.bind fun c =>
      top3Shift (q.1.2.1, c.2, topwCosetPreimage ((q.1.2.1, c.1), q.1.1.headD [], q.2)))

/-- **One step of the loop**: Eq. (63) for the next orbit. -/
def orbStep (sol : RawSI → RawCoset) (st : OrbState) : OrbState :=
  orbPost (st, sol (orbPre st))

theorem orbStep_eq (sol : RawSI → RawCoset) (Os : List (List ℕ)) (x y : RawStr) (c : RawCoset) :
    orbStep sol (Os, x, y, c) =
      (Os.tail, x, y, c.bind fun q => orbLeaf sol (Os.headD [], q.1, q.2, x, y)) := by
  cases c with
  | none => simp only [orbStep, orbPost, Option.bind_none]
  | some q =>
    simp only [orbStep, orbPost, orbPre, orbWin, orbLeaf, Option.bind_some, Option.getD_some]

/-- The set-up: the generators made short and well formed, the orbits of the group, and the
initial coset `G = 1 · G`. -/
def orbSetUp (r : RawSI) : ℕ × OrbState :=
  ((rawOrbits (tidyGens (r.2.1, r.1), r.2.1)).length,
    (rawOrbits (tidyGens (r.2.1, r.1), r.2.1), r.2.1, r.2.2,
      some (tidyGens (r.2.1, r.1), rawOne r.2.1)))

/-! ## What the loop computes -/

/-- The window `Iso^Δ` of the window `Iso^D` is the window `Iso^{D ∪ Δ}`: Eq. (63). -/
theorem wIso_wIso {Ω A : Type*} (D Δ : Set Ω) (K : Set (Perm Ω)) (x y : Ω → A) :
    wIso Δ (wIso D K x y) x y = wIso (D ∪ Δ) K x y := by
  ext τ
  simp only [mem_wIso, Set.mem_union]
  constructor
  · rintro ⟨⟨hK, h1⟩, h2⟩
    exact ⟨hK, fun u hu => hu.elim (h1 u) (h2 u)⟩
  · rintro ⟨hK, h⟩
    exact ⟨⟨hK, fun u hu => h u (Or.inl hu)⟩, fun u hu => h u (Or.inr hu)⟩

/-- The invariant of the loop after `j` orbits: the coset is `Iso^{D}_G(x,y)` for the union
`D` of the first `j` orbits, and when it is nonempty its generators and representative are
well formed and its group lies in `G`. -/
def OrbInv (n : ℕ) (G : Subgroup (Perm (Fin n))) (x y : RawStr) (Os : List (List ℕ)) (j : ℕ)
    (c : RawCoset) : Prop :=
  decCoset n c = wIso (⋃ u ∈ Os.take j, winSet n u) (G : Set (Perm (Fin n)))
      (decStrN n x) (decStrN n y) ∧
    ∀ g ρ, c = some (g, ρ) →
      RawGens.WF n g ∧ g.length ≤ n * n ∧ RawPerm.WF n ρ ∧ decGroup n g ≤ G

/-- The facts about the orbits the loop needs. -/
structure OrbitsOK (n : ℕ) (G : Subgroup (Perm (Fin n))) (Os : List (List ℕ)) : Prop where
  nodup : ∀ u ∈ Os, u.Nodup
  lt : ∀ u ∈ Os, ∀ k ∈ u, k < n
  inv : ∀ u ∈ Os, IsInvariant G (winSet n u)
  cover : (⋃ u ∈ Os, winSet n u) = Set.univ

theorem orbitsOK_rawOrbits {n : ℕ} {gs : RawGens} (hgs : RawGens.WF n gs) {w : List ℕ}
    (hw : w.length = n) : OrbitsOK n (decGroup n gs) (rawOrbits (gs, w)) := by
  refine ⟨fun u hu => ?_, fun u hu => ?_, fun u hu => ?_, ?_⟩
  · obtain ⟨j, -, rfl⟩ := rawOrbits_mem hgs hw hu
    exact nodup_rawOrbit gs j
  · obtain ⟨j, hj, rfl⟩ := rawOrbits_mem hgs hw hu
    intro k hk
    exact ((mem_rawOrbit_iff hgs hj k).1 hk).1
  · obtain ⟨j, hj, rfl⟩ := rawOrbits_mem hgs hw hu
    exact isInvariant_rawOrbit hgs hj
  · ext u
    simp only [Set.mem_iUnion, exists_prop, Set.mem_univ, iff_true]
    obtain ⟨v, hv, huv⟩ := List.mem_flatten.1 (rawOrbits_cover hgs hw u.isLt)
    exact ⟨v, hv, huv⟩

/-- **One step keeps the invariant.** -/
theorem orbInv_step {sol : RawSI → RawCoset} (hsol : SolverSpec sol) {n : ℕ}
    {G : Subgroup (Perm (Fin n))} {x y : RawStr} (hx : x.length = n) {Os : List (List ℕ)}
    (hOs : OrbitsOK n G Os) {j : ℕ} (hj : j < Os.length) {c : RawCoset}
    (hc : OrbInv n G x y Os j c) :
    OrbInv n G x y Os (j + 1)
      (c.bind fun q => orbLeaf sol ((Os.drop j).headD [], q.1, q.2, x, y)) := by
  have hdrop : (Os.drop j).headD [] = Os[j] := by
    rw [List.drop_eq_getElem_cons hj]; rfl
  have htake : (⋃ u ∈ Os.take (j + 1), winSet n u)
      = (⋃ u ∈ Os.take j, winSet n u) ∪ winSet n Os[j] := by
    rw [List.take_succ_eq_append_getElem hj]
    ext v
    simp only [Set.mem_iUnion, Set.mem_union, List.mem_append, List.mem_singleton, exists_prop]
    constructor
    · rintro ⟨u, hu | rfl, hv⟩
      · exact Or.inl ⟨u, hu, hv⟩
      · exact Or.inr hv
    · rintro (⟨u, hu, hv⟩ | hv)
      · exact ⟨u, Or.inl hu, hv⟩
      · exact ⟨Os[j], Or.inr rfl, hv⟩
  have hmem : Os[j] ∈ Os := List.getElem_mem hj
  rw [hdrop]
  cases c with
  | none =>
    refine ⟨?_, fun g ρ h => absurd h (by simp)⟩
    rw [Option.bind_none, htake, ← wIso_wIso, ← hc.1]
    ext τ
    simp [decCoset, mem_wIso]
  | some q =>
    obtain ⟨g, ρ⟩ := q
    obtain ⟨hg, hgl, hρ, hgG⟩ := hc.2 g ρ rfl
    have hinv : IsInvariant (decGroup n g) (winSet n Os[j]) :=
      isInvariant_of_le (hOs.inv _ hmem) hgG
    have hleaf := orbLeaf_spec hsol (p := (Os[j], g, ρ, x, y)) hx hg (hOs.nodup _ hmem)
      (hOs.lt _ hmem) hinv
    have hval : decCoset n (orbLeaf sol (Os[j], g, ρ, x, y)) =
        wIso (⋃ u ∈ Os.take (j + 1), winSet n u) (G : Set (Perm (Fin n)))
          (decStrN n x) (decStrN n y) := by
      rw [hleaf, htake, ← wIso_wIso, ← hc.1]
      rfl
    refine ⟨hval, fun g' ρ' h' => ?_⟩
    change orbLeaf sol (Os[j], g, ρ, x, y) = some (g', ρ') at h'
    obtain ⟨h1, h2, h3⟩ := top3Shift_wf hx _ _ h'
    refine ⟨h1, h2, h3, ?_⟩
    have hsub : decCoset n (some (g', ρ')) ⊆ (G : Set (Perm (Fin n))) := by
      rw [← h', hval]
      exact fun _ h => h.1
    refine decGroup_le_of_subset (σ₀ := 1) (τ := decPerm n ρ') ?_
    rintro τ ⟨u, hu, rfl⟩
    exact ⟨decPerm n ρ' * u, hsub ⟨u, hu, rfl⟩, by rw [one_mul]⟩

/-- **The loop computes Eq. (63) iterated.**  After `j ≤ |Os|` steps from the coset `G`, the
state holds the window isomorphisms for the union of the first `j` orbits. -/
theorem orbStep_iterate_spec {sol : RawSI → RawCoset} (hsol : SolverSpec sol) {n : ℕ}
    {G : Subgroup (Perm (Fin n))} {x y : RawStr} (hx : x.length = n) {Os : List (List ℕ)}
    (hOs : OrbitsOK n G Os) {c₀ : RawCoset} (h₀ : OrbInv n G x y Os 0 c₀) :
    ∀ j ≤ Os.length, ∃ c, (orbStep sol)^[j] (Os, x, y, c₀) = (Os.drop j, x, y, c) ∧
      OrbInv n G x y Os j c := by
  intro j
  induction j with
  | zero => exact fun _ => ⟨c₀, rfl, h₀⟩
  | succ j ih =>
    intro hj
    obtain ⟨c, hst, hc⟩ := ih (by omega)
    refine ⟨_, ?_, orbInv_step hsol hx hOs (by omega) hc⟩
    rw [Function.iterate_succ_apply', hst, orbStep_eq, List.tail_drop]

/-- The initial coset satisfies the invariant: no orbit processed, the coset is `G`. -/
theorem orbInv_zero {n : ℕ} {gs : RawGens} (hgs : RawGens.WF n gs) (hgl : gs.length ≤ n * n)
    {x y : RawStr} (hx : x.length = n) (Os : List (List ℕ)) :
    OrbInv n (decGroup n gs) x y Os 0 (some (gs, rawOne x)) := by
  have hone : RawPerm.WF n (rawOne x) := by
    rw [rawOne, hx, ← encPerm_one]; exact wf_encPerm n 1
  have hdec1 : decPerm n (rawOne x) = 1 := by
    rw [rawOne, hx, ← encPerm_one, decPerm_encPerm]
  refine ⟨?_, fun g ρ h => ?_⟩
  · simp only [List.take_zero, List.not_mem_nil, Set.iUnion_of_empty, Set.iUnion_empty]
    ext τ
    simp only [decCoset, hdec1, one_mul, mem_wIso, Set.mem_empty_iff_false, IsEmpty.forall_iff,
      implies_true, and_true, Set.mem_setOf_eq, SetLike.mem_coe]
    constructor
    · rintro ⟨g, hg, rfl⟩; exact hg
    · intro h; exact ⟨τ, h, rfl⟩
  · cases h
    exact ⟨hgs, hgl, hone, le_rfl⟩

/-- **The answer of the loop.**  On the raw form of a typed instance, the set-up followed by
all the steps ends with a well-formed raw coset describing `Iso_G(x,y)`. -/
theorem orbFinal_spec {sol : RawSI → RawCoset} (hsol : SolverSpec sol) {n s : ℕ}
    (a : SIInput n s) :
    RawCoset.WF n ((orbStep sol)^[(orbSetUp (rawOfSI a)).1] (orbSetUp (rawOfSI a)).2).2.2.2 ∧
      decCoset n ((orbStep sol)^[(orbSetUp (rawOfSI a)).1] (orbSetUp (rawOfSI a)).2).2.2.2 =
        IsoSet a.1 a.2.1 a.2.2 := by
  set r := rawOfSI a with hr
  have hx : r.2.1.length = n := length_encStr _
  set g₀ := tidyGens (r.2.1, r.1) with hg₀
  have hg₀wf : RawGens.WF n g₀ := wf_tidyGens hx _
  have hg₀l : g₀.length ≤ n * n := length_tidyGens hx _
  have hG : decGroup n g₀ = genGroup a.1 := by
    rw [hg₀, decGroup_tidyGens hx]
    exact decGroup_map_encPerm n a.1
  set Os := rawOrbits (g₀, r.2.1) with hOsdef
  have hOs : OrbitsOK n (decGroup n g₀) Os := orbitsOK_rawOrbits hg₀wf hx
  obtain ⟨c, hst, hc⟩ := orbStep_iterate_spec hsol hx hOs (orbInv_zero hg₀wf hg₀l hx Os)
    Os.length le_rfl
  change RawCoset.WF n ((orbStep sol)^[Os.length] (Os, r.2.1, r.2.2, some (g₀, rawOne r.2.1))).2.2.2
    ∧ decCoset n ((orbStep sol)^[Os.length] (Os, r.2.1, r.2.2, some (g₀, rawOne r.2.1))).2.2.2
      = IsoSet a.1 a.2.1 a.2.2
  rw [hst]
  dsimp only
  refine ⟨?_, ?_⟩
  · cases c with
    | none => trivial
    | some q =>
      obtain ⟨g, ρ⟩ := q
      obtain ⟨h1, -, h3, -⟩ := hc.2 g ρ rfl
      exact ⟨h1, h3⟩
  · rw [hc.1, List.take_length, hOs.cover, wIso_univ, hG, strIso_eq_sep]
    ext τ
    simp only [IsoSet, Set.mem_setOf_eq, SetLike.mem_coe, hr, rawOfSI, decStrN_encStr,
      Fin.val_inj]

end Algo
