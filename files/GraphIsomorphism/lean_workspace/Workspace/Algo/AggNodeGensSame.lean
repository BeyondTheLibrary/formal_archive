/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the routines Section 13.2 runs on the group `F(z)^Γ` read off the
certificate stores depend on that group only, not on the generators that encode it.
-/
import Workspace.Algo.AggNodeLine57GiantMatch
import Workspace.Algo.TopPrimitiveWindow

/-!
# The routines on `F(z)^Γ` depend only on the group

After the two phases of Procedure AggregateCertificates (Sec. 13.2), the round of Sec. 15,
lines 5–7, reads the group `F(z)^Γ` off the certificate stores as a list of generators.  The
stores hold the answers of the calls of the certificate phase, and a call may answer with any
list of generators of its group.  So two runs of the phases that receive the same answers,
encoded differently, store different generators of the same group.

The Master's round (`Babai.Line57Shape.red`) is one tree for all these runs, so everything the
round computes after the phases must be a function of the groups alone (the rule "Enumeration
orders" of `PLAN.md`).  This file proves it for the routines on the group:

* `Algo.RawGensSame m gs gs'`: two well-formed generator lists of the same subgroup of
  `S(Fin m)`;
* the orbits, the fixed-point test, the least points of orbits, the large orbit, the tests of
  cases (1), (2), (2a), the degree of transitivity, and the family of outcome (2b) (the
  orbitals of the pointwise stabilizers) all take the same value on both lists.

The orbits listed by `Algo.winOrbits` are the same sets in the same order
(`Algo.RawGensSame.winOrbits_forall₂`): the loop walks the given points in their order and
starts a new orbit at a point not yet covered, which is a question about sets.
-/
set_option synthInstance.maxSize 2048
namespace Algo
open RAM RAM.Targets Babai Equiv MulAction

/-- Two well-formed generator lists of the same subgroup of `S(Fin m)`. -/
def RawGensSame (m : ℕ) (gs gs' : RawGens) : Prop :=
  RawGens.WF m gs ∧ RawGens.WF m gs' ∧ decGroup m gs = decGroup m gs'

/-- Two lists with the same members. -/
def SameMem (a b : List ℕ) : Prop := ∀ k, k ∈ a ↔ k ∈ b

theorem sameMem_refl (a : List ℕ) : SameMem a a := fun _ => Iff.rfl

/-- The least element of a list depends only on its members. -/
theorem upccCaseLeast_sameMem {a b : List ℕ} (ha : a ≠ []) (h : SameMem a b) :
    upccCaseLeast a = upccCaseLeast b := by
  have hb : b ≠ [] := by
    obtain ⟨k, hk⟩ := List.exists_mem_of_ne_nil a ha
    exact List.ne_nil_of_mem ((h k).1 hk)
  obtain ⟨ma, la⟩ := upccCaseLeast_spec a ha
  obtain ⟨mb, lb⟩ := upccCaseLeast_spec b hb
  exact le_antisymm (la _ ((h _).2 mb)) (lb _ ((h _).1 ma))

/-- Lists related member by member by `SameMem` have the same image under a function of
the members. -/
theorem map_eq_of_forall₂_sameMem {β : Type*} {f : List ℕ → β}
    (hf : ∀ a b, SameMem a b → f a = f b) :
    ∀ {l l' : List (List ℕ)}, List.Forall₂ SameMem l l' → l.map f = l'.map f
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h t => by
    simp only [List.map_cons, hf _ _ h, map_eq_of_forall₂_sameMem hf t]

theorem mem_flatten_of_forall₂_sameMem :
    ∀ {l l' : List (List ℕ)}, List.Forall₂ SameMem l l' → ∀ k, k ∈ l.flatten ↔ k ∈ l'.flatten
  | [], [], .nil, _ => Iff.rfl
  | _ :: _, _ :: _, .cons h t, k => by
    simp only [List.flatten_cons, List.mem_append, h k, mem_flatten_of_forall₂_sameMem t k]

namespace RawGensSame

variable {m : ℕ} {gs gs' : RawGens} (h : RawGensSame m gs gs')
include h

theorem symm : RawGensSame m gs' gs := ⟨h.2.1, h.1, h.2.2.symm⟩

theorem mem_rawOrbit {i : ℕ} (hi : i < m) : SameMem (rawOrbit (gs, i)) (rawOrbit (gs', i)) := by
  intro k
  rw [mem_rawOrbit_iff h.1 hi, mem_rawOrbit_iff h.2.1 hi, h.2.2]

theorem rawOrbit_length {i : ℕ} (hi : i < m) :
    (rawOrbit (gs, i)).length = (rawOrbit (gs', i)).length :=
  ((List.perm_ext_iff_of_nodup (nodup_rawOrbit _ _) (nodup_rawOrbit _ _)).2
    (h.mem_rawOrbit hi)).length_eq

theorem aggFixTest {i : ℕ} (hi : i < m) : aggFixTest (gs, i) = aggFixTest (gs', i) := by
  have h1 := aggFixTest_spec h.1 ⟨i, hi⟩
  have h2 := aggFixTest_spec h.2.1 ⟨i, hi⟩
  rw [h.2.2] at h1
  exact Bool.eq_iff_iff.2 (h1.trans h2.symm)

theorem aggnOrbitLabel {i : ℕ} (hi : i < m) : aggnOrbitLabel (gs, i) = aggnOrbitLabel (gs', i) :=
  upccCaseLeast_sameMem (List.ne_nil_of_mem (mem_rawOrbit_self gs i)) (h.mem_rawOrbit hi)

theorem aggnLargeOrbitPoints {dom : List ℕ} (hd : dom.length = m) :
    aggnLargeOrbitPoints (dom, gs) = aggnLargeOrbitPoints (dom, gs') := by
  unfold Algo.aggnLargeOrbitPoints
  refine List.filter_congr fun u hu => ?_
  have hu' : u < m := hd ▸ List.mem_range.1 hu
  simp only [h.rawOrbit_length hu']

theorem aggFixed {dom : List ℕ} (hd : dom.length = m) :
    Algo.aggFixed (dom, gs) = Algo.aggFixed (dom, gs') := by
  unfold Algo.aggFixed
  refine List.filter_congr fun u hu => ?_
  exact h.aggFixTest (hd ▸ List.mem_range.1 hu)

theorem aggnCase1 {dom : List ℕ} (hd : dom.length = m) :
    Algo.aggnCase1 (dom, gs) = Algo.aggnCase1 (dom, gs') := by
  unfold Algo.aggnCase1
  rw [h.aggFixed hd, h.aggnLargeOrbitPoints hd]

theorem aggnCase2 {dom : List ℕ} (hd : dom.length = m) :
    Algo.aggnCase2 (dom, gs) = Algo.aggnCase2 (dom, gs') := by
  unfold Algo.aggnCase2
  rw [h.aggnLargeOrbitPoints hd]

theorem aggnOrbitPartition {dom : List ℕ} (hd : dom.length = m) :
    Algo.aggnOrbitPartition (dom, gs) = Algo.aggnOrbitPartition (dom, gs') := by
  unfold Algo.aggnOrbitPartition
  have hc : ∀ u ∈ List.range dom.length, aggnOrbitColor (gs, u) = aggnOrbitColor (gs', u) := by
    intro u hu
    unfold aggnOrbitColor
    rw [h.aggFixTest (hd ▸ List.mem_range.1 hu)]
  have hb : ∀ u ∈ List.range dom.length, aggnOrbitBlock (gs, u) = aggnOrbitBlock (gs', u) := by
    intro u hu
    unfold aggnOrbitBlock
    rw [h.aggFixTest (hd ▸ List.mem_range.1 hu), h.aggnOrbitLabel (hd ▸ List.mem_range.1 hu)]
  rw [List.map_congr_left hc, List.map_congr_left hb]

theorem tidyGens {x : RawStr} (hx : x.length = m) :
    RawGensSame m (Algo.tidyGens (x, gs)) (Algo.tidyGens (x, gs')) :=
  ⟨wf_tidyGens hx _, wf_tidyGens hx _, by rw [decGroup_tidyGens hx, decGroup_tidyGens hx, h.2.2]⟩

omit h in
theorem range_winRestrictHom_congr {Δ : List ℕ} (hnd : Δ.Nodup) (hlt : ∀ u ∈ Δ, u < m)
    {G G' : Subgroup (Perm (Fin m))} (hG : G = G') (hinv : IsInvariant G (winSet m Δ))
    (hinv' : IsInvariant G' (winSet m Δ)) :
    (winRestrictHom m Δ hnd hlt G hinv).range = (winRestrictHom m Δ hnd hlt G' hinv').range := by
  subst hG
  rfl

theorem rawRestrictGens {dom Δ : List ℕ} (hnd : Δ.Nodup) (hlt : ∀ u ∈ Δ, u < m)
    (hinv : IsInvariant (decGroup m gs) (winSet m Δ)) :
    RawGensSame Δ.length (Algo.rawRestrictGens ((dom, gs), Δ))
      (Algo.rawRestrictGens ((dom, gs'), Δ)) := by
  have hinv' : IsInvariant (decGroup m gs') (winSet m Δ) := h.2.2 ▸ hinv
  refine ⟨rawRestrictGens_wf_of_raw (dom := dom) h.1 hnd hlt hinv,
    rawRestrictGens_wf_of_raw (dom := dom) h.2.1 hnd hlt hinv', ?_⟩
  rw [decGroup_rawRestrictGens_of_raw (dom := dom) h.1 hnd hlt hinv,
    decGroup_rawRestrictGens_of_raw (dom := dom) h.2.1 hnd hlt hinv']
  exact range_winRestrictHom_congr hnd hlt h.2.2 hinv hinv'

omit h in
theorem rawIsGiantSub_congr {k : ℕ} {dom : List ℕ} (hd : dom.length = k) {g1 g2 : RawGens}
    (h12 : RawGensSame k g1 g2) : rawIsGiantSub (dom, g1) = rawIsGiantSub (dom, g2) := by
  rw [← map_encPerm_decPerm h12.1, ← map_encPerm_decPerm h12.2.1]
  refine Bool.eq_iff_iff.2 ?_
  rw [rawIsGiantSub_eq_true_iff hd, rawIsGiantSub_eq_true_iff hd]
  change _ ≤ decGroup k g1 ↔ _ ≤ decGroup k g2
  rw [h12.2.2]

theorem aggnMajorityRestricted {dom : List ℕ} (hd : dom.length = m) :
    RawGensSame (Algo.aggnLargeOrbitPoints (dom, gs)).length
      (Algo.aggnMajorityRestricted (dom, gs)) (Algo.aggnMajorityRestricted (dom, gs')) := by
  unfold Algo.aggnMajorityRestricted
  rw [← h.aggnLargeOrbitPoints hd]
  exact (h.rawRestrictGens (dom := dom) (aggnLargeOrbitPoints_nodup _)
    (aggnLargeOrbitPoints_lt hd) (aggnLargeOrbitPoints_invariant hd h.1)).tidyGens rfl

theorem aggnCase2a {dom : List ℕ} (hd : dom.length = m) :
    Algo.aggnCase2a (dom, gs) = Algo.aggnCase2a (dom, gs') := by
  unfold Algo.aggnCase2a
  have := rawIsGiantSub_congr (dom := Algo.aggnLargeOrbitPoints (dom, gs)) rfl
    (h.aggnMajorityRestricted hd)
  rw [this, h.aggnLargeOrbitPoints hd]

theorem aggnMajorityDegree {dom : List ℕ} (hd : dom.length = m) :
    Algo.aggnMajorityDegree (dom, gs) = Algo.aggnMajorityDegree (dom, gs') := by
  rw [aggnMajorityDegree_spec hd h.1, aggnMajorityDegree_spec hd h.2.1, h.2.2,
    h.aggnLargeOrbitPoints hd]

theorem aggnPointStab {dom S : List ℕ} (hd : dom.length = m) (hnd : S.Nodup)
    (hlt : ∀ u ∈ S, u < m) :
    RawGensSame m (Algo.aggnPointStab ((dom, gs), S)) (Algo.aggnPointStab ((dom, gs'), S)) := by
  unfold Algo.aggnPointStab
  refine ⟨wf_tidyGens hd _, wf_tidyGens hd _, ?_⟩
  rw [decGroup_tidyGens hd, decGroup_tidyGens hd, ← map_encPerm_decPerm h.1,
    ← map_encPerm_decPerm h.2.1, decGroup_rawPointStab dom hd _ S hnd hlt,
    decGroup_rawPointStab dom hd _ S hnd hlt]
  change pointwiseStabilizer (decGroup m gs) _ = pointwiseStabilizer (decGroup m gs') _
  rw [h.2.2]

theorem aggnPairGens {dom : List ℕ} (hd : dom.length = m) :
    RawGensSame (m * m) (Algo.aggnPairGens (dom, gs)) (Algo.aggnPairGens (dom, gs')) :=
  ⟨aggnPairGens_wf hd h.1, aggnPairGens_wf hd h.2.1, by
    rw [aggnPairGens_spec hd h.1, aggnPairGens_spec hd h.2.1, h.2.2]⟩

/-- **The orbits listed by the loop are the same sets, in the same order.** -/
theorem winOrbits_forall₂ :
    ∀ (Δ : List ℕ), (∀ u ∈ Δ, u < m) → ∀ acc acc' : List (List ℕ),
      List.Forall₂ SameMem acc acc' →
      List.Forall₂ SameMem (List.foldl (fun a j => rawOrbitsStep (gs, (a, j))) acc Δ)
        (List.foldl (fun a j => rawOrbitsStep (gs', (a, j))) acc' Δ)
  | [], _, _, _, hacc => hacc
  | j :: Δ, hlt, acc, acc', hacc => by
    simp only [List.foldl_cons]
    refine winOrbits_forall₂ Δ (fun u hu => hlt u (List.mem_cons_of_mem _ hu)) _ _ ?_
    unfold rawOrbitsStep
    dsimp only
    by_cases hj : j ∈ acc.flatten
    · have hj' : j ∈ acc'.flatten := (mem_flatten_of_forall₂_sameMem hacc j).1 hj
      rw [if_pos hj, if_pos hj']
      exact hacc
    · have hj' : j ∉ acc'.flatten := fun h' => hj ((mem_flatten_of_forall₂_sameMem hacc j).2 h')
      rw [if_neg hj, if_neg hj']
      exact List.rel_append hacc (.cons (h.mem_rawOrbit (hlt j List.mem_cons_self)) .nil)

theorem winOrbits {Δ : List ℕ} (hlt : ∀ u ∈ Δ, u < m) :
    List.Forall₂ SameMem (Algo.winOrbits (gs, Δ)) (Algo.winOrbits (gs', Δ)) :=
  h.winOrbits_forall₂ Δ hlt [] [] .nil

end RawGensSame

/-! ### The family of outcome (2b) -/

theorem aggnPairRel_sameMem (dom : List ℕ) {a b : List ℕ} (h : SameMem a b) :
    aggnPairRel (dom, a) = aggnPairRel (dom, b) := by
  unfold aggnPairRel
  refine List.filter_congr fun row _ => ?_
  simp only [h _]

namespace RawGensSame
variable {m : ℕ} {gs gs' : RawGens} (h : RawGensSame m gs gs')
include h

theorem aggnOrbitals {dom W : List ℕ} (hd : dom.length = m) (hW : ∀ u ∈ W, u < m) :
    Algo.aggnOrbitals ((dom, gs), W) = Algo.aggnOrbitals ((dom, gs'), W) := by
  unfold Algo.aggnOrbitals
  exact map_eq_of_forall₂_sameMem (fun a b hab => aggnPairRel_sameMem dom hab)
    ((h.aggnPairGens hd).winOrbits (aggnPairRow_lt hd hW))

theorem aggnCase2bAt {dom C S : List ℕ} (hd : dom.length = m) (hC : ∀ u ∈ C, u < m)
    (hnd : S.Nodup) (hlt : ∀ u ∈ S, u < m) :
    Algo.aggnCase2bAt ((dom, gs), (C, S)) = Algo.aggnCase2bAt ((dom, gs'), (C, S)) := by
  unfold Algo.aggnCase2bAt
  dsimp only
  have hW : ∀ u ∈ aggnSetDiff (C, S), u < m := fun u hu => hC u (List.mem_of_mem_filter hu)
  rw [(h.aggnPointStab hd hnd hlt).aggnOrbitals hd hW]

theorem aggnCase2bFamily {dom : List ℕ} (hd : dom.length = m) :
    Algo.aggnCase2bFamily (dom, gs) = Algo.aggnCase2bFamily (dom, gs') := by
  unfold Algo.aggnCase2bFamily
  dsimp only
  rw [h.aggnMajorityDegree hd, ← h.aggnLargeOrbitPoints hd]
  refine List.flatMap_congr fun S hS => ?_
  have hS' := List.mem_filter.1 hS
  have hnorm : S = aggNormalizeRow (dom, S) := by
    have h2 := hS'.2
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
    exact h2.2
  have hnd : S.Nodup := by
    rw [hnorm]; exact List.nodup_range.filter _
  have hlt : ∀ u ∈ S, u < m := by
    rw [hnorm]
    intro u hu
    exact hd ▸ List.mem_range.1 (List.mem_of_mem_filter hu)
  exact h.aggnCase2bAt hd (aggnLargeOrbitPoints_lt hd) hnd hlt

end RawGensSame

end Algo
