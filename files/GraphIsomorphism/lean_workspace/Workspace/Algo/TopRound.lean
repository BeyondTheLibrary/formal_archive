import Workspace.Algo.TopStab
import Workspace.Algo.Descent

/-!
# Sec. 12: the top-action tests as a round

The raw lift and the classical lift need not give the same shifted string.
The reduction in this file takes its children from the computed lifts. It
also keeps one kernel call when a lift is absent, discarding that answer.
This preserves the call count of `Babai.TopAction1Reduction`.
-/

namespace Algo

open RAM RAM.Targets
open Equiv (Perm)
open Babai (SIReduction SIInstance)
open scoped Pointwise

/-- A kernel child even when preparation rejects the requested top element. -/
def topLiftChild (p : RawTopLift) : RawSI :=
  (topLiftPrepare p).elim
    (tidyGens (p.1.1.1, actKerGens p.1), p.2.2.1, p.2.2.2) Prod.snd

theorem polyFun_topLiftChild : PolyFun topLiftChild := by
  have h : PolyFun (fun p : RawTopLift =>
      (tidyGens (p.1.1.1, actKerGens p.1), p.2.2.1, p.2.2.2)) :=
    ((((polyFun_fst.comp polyFun_fst).comp polyFun_fst).pair
      (polyFun_fst.comp polyFun_actKerGens)).comp polyFun_tidyGens).pair
        (polyFun_snd.comp polyFun_snd)
  exact ((polyFun_topLiftPrepare.pair h).comp
    (PolyFun.optionElim polyFun_id (polyFun_fst.comp polyFun_snd))).of_eq (fun _ => rfl)

/-- Reconstruct the lifting set using precisely the computed lift. -/
noncomputable def topLiftAnswer (n : ℕ) (p : RawTopLift) (A : Set (Perm (Fin n))) :
    Set (Perm (Fin n)) :=
  (topLiftPrepare p).elim ∅ (fun q => Babai.rightTranslate A (decPerm n q.1))

theorem decCoset_topLiftFinish {n : ℕ} (p : RawTopLift) (hd : p.1.1.1.length = n)
    (a : RawCoset) :
    decCoset n (topLiftFinish (p.1.1.1, topLiftPrepare p, a)) =
      topLiftAnswer n p (decCoset n a) := by
  cases hp : topLiftPrepare p with
  | none => simp [topLiftAnswer, hp, topLiftFinish, decCoset]
  | some q => simpa [topLiftAnswer, hp, topLiftFinish] using decCoset_rawRightTranslate hd q.1 a

/-- The computed lift defines a reduction without a choice of representative. -/
noncomputable def topLiftReduction (n : ℕ) (p : RawTopLift) :
    SIReduction (Fin n) ℕ (Set (Perm (Fin n))) :=
  .call (decFullSI n (topLiftChild p)) (fun a => .done (topLiftAnswer n p a))

theorem run_topLiftReduction {n m : ℕ} {dom gdom : List ℕ}
    {gens : List (Perm (Fin n))} {imgs : List (Perm (Fin m))}
    {ϕ : genGroup gens →* Perm (Fin m)} (hd : dom.length = n) (hm : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (τ : Perm (Fin m)) (x y : Fin n → ℕ) :
    (topLiftReduction n (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))),
      encPerm m τ, encStrN x, encStrN y)).run = Babai.liftingSet ϕ x y τ := by
  rw [topLiftReduction, SIReduction.run_call, SIReduction.run_done]
  cases hp : topLiftPrepare
      (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))),
        encPerm m τ, encStrN x, encStrN y) with
  | none =>
    rw [topLiftAnswer, hp]
    exact (Babai.liftingSet_eq_empty ϕ x y
      ((topLiftPrepare_eq_none_iff hd hm hI τ x y).1 hp)).symm
  | some q =>
    obtain ⟨σ, hσ, hϕ, hc⟩ := topLiftPrepare_child hd hm hI τ x y hp
    simp only [topLiftAnswer, topLiftChild, hp, Option.elim_some]
    rw [hσ, decPerm_encPerm, hc, SIInstance.answer, Babai.wIso_univ, ← hϕ]
    exact (Babai.Proposition_12_0_1_lifting ϕ x y σ).symm

/-- The new lifting reduction has the old value, without asserting that
their chosen children are equal. -/
theorem run_topLiftReduction_eq {n m : ℕ} {dom gdom : List ℕ}
    {gens : List (Perm (Fin n))} {imgs : List (Perm (Fin m))}
    {ϕ : genGroup gens →* Perm (Fin m)} (hd : dom.length = n) (hm : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (τ : Perm (Fin m)) (x y : Fin n → ℕ) :
    (topLiftReduction n (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))),
      encPerm m τ, encStrN x, encStrN y)).run = (Babai.liftingReduction ϕ x y τ).run := by
  rw [run_topLiftReduction hd hm hI, Babai.run_liftingReduction]

/-! ## Raw test inputs and the answer accumulator -/

abbrev RawTop1 := RawAction × RawGens × RawStr × RawStr
abbrev Top1State := Option RawCoset
abbrev RawTop1Node := RawTop1 × Option RawSI

/-- Test the identity first, followed by the supplied target generators. -/
def top1Inputs (p : RawTop1) : List RawTopLift :=
  (rawOne p.1.2.1 :: p.2.1).map (fun r => (p.1, r, p.2.2.1, p.2.2.2))

@[simp] theorem length_top1Inputs (p : RawTop1) : (top1Inputs p).length = p.2.1.length + 1 := by
  simp [top1Inputs]

theorem polyFun_top1Inputs : PolyFun top1Inputs := by
  have hf : PolyFun (fun p : RawTop1 × RawPerm => (p.1.1, p.2, p.1.2.2.1, p.1.2.2.2)) :=
    (polyFun_fst.comp polyFun_fst).pair (polyFun_snd.pair
      (((polyFun_fst.comp polyFun_snd).comp polyFun_snd)))
  have hl : PolyFun (fun p : RawTop1 => rawOne p.1.2.1 :: p.2.1) :=
    ((((polyFun_fst.comp polyFun_snd).comp polyFun_fst).comp polyFun_rawOne).pair
      (polyFun_snd.comp polyFun_fst)).comp polyFun_cons
  exact (polyFun_id.pair hl).comp (PolyFun.mapParam hf)

/-- An absent outer option records a failed test. An empty inner option is
the initial accumulator, before the identity test. -/
def top1Join (p : List ℕ × Top1State × RawCoset) : Top1State :=
  p.2.1.bind (fun s => p.2.2.map (fun q => rawCosetJoin (p.1, s, some q)))

theorem polyFun_top1Join : PolyFun top1Join := by
  have hq : PolyFun (fun z : (RawGens × RawPerm) × (List ℕ × RawCoset) =>
      some (rawCosetJoin (z.2.1, z.2.2, some z.1))) :=
    ((polyFun_snd.comp polyFun_fst).pair
      ((polyFun_snd.comp polyFun_snd).pair (polyFun_fst.comp polyFun_some))).comp
        (polyFun_rawCosetJoin.comp polyFun_some)
  have ha : PolyFun (fun z : RawCoset × (List ℕ × Top1State × RawCoset) =>
      z.2.2.2.map (fun q => rawCosetJoin (z.2.1, z.1, some q))) := by
    exact ((((polyFun_snd.comp polyFun_snd).comp polyFun_snd).pair
      ((polyFun_snd.comp polyFun_fst).pair polyFun_fst)).comp
        (PolyFun.optionElim (polyFun_const none) hq)).of_eq (fun z => by cases z.2.2.2 <;> rfl)
  exact ((((polyFun_snd.comp polyFun_fst).pair polyFun_id).comp
    (PolyFun.optionElim (polyFun_const none) ha))).of_eq (fun p => by unfold top1Join; cases p.2.1 <;> rfl)

noncomputable def decTop1State (n : ℕ) (s : Top1State) : Option (Set (Perm (Fin n))) :=
  s.map (decCoset n)

open scoped Classical in
/-- The mathematical update of the same accumulator. -/
noncomputable def top1JoinSet {Γ : Type*} [Group Γ]
    (s : Option (Set Γ)) (A : Set Γ) : Option (Set Γ) :=
  if A.Nonempty then s.map (fun S => cosetHull (S ∪ A)) else none

theorem decCoset_nonempty {n : ℕ} (a : RawCoset) : (decCoset n a).Nonempty ↔ a.isSome = true := by
  cases a with
  | none => simp [decCoset]
  | some q =>
    rw [decCoset_some]
    simp only [Option.isSome_some, iff_true]
    exact ⟨decPerm n q.2, ⟨1, Subgroup.one_mem _, by simp⟩⟩

theorem decTop1State_top1Join {n : ℕ} {dom : List ℕ} (hd : dom.length = n)
    (s : Top1State) (a : RawCoset) :
    decTop1State n (top1Join (dom, s, a)) = top1JoinSet (decTop1State n s) (decCoset n a) := by
  classical
  cases s with
  | none => simp [top1Join, decTop1State, top1JoinSet]
  | some s =>
    cases a with
    | none => simp [top1Join, decTop1State, top1JoinSet, decCoset]
    | some q =>
      have hne := (decCoset_nonempty (n := n) (some q : RawCoset)).2 rfl
      simp only [top1Join, Option.bind_some, Option.map_some, decTop1State, top1JoinSet,
        if_pos hne]
      rw [decCoset_rawCosetJoin hd]

/-! ## The indexed round -/

def top1Request (p : RawTop1 × ℕ) : RawTopLift :=
  (p.1.1, (rawOne p.1.1.2.1 :: p.1.2.1).getD p.2 (rawOne p.1.1.2.1), p.1.2.2.1, p.1.2.2.2)

theorem top1Request_eq_getElem (p : RawTop1) {j : ℕ} (hj : j < (top1Inputs p).length) :
    top1Request (p, j) = (top1Inputs p)[j] := by
  simp only [top1Inputs, List.getElem_map]
  unfold top1Request
  rw [List.getD_eq_getElem _ _ (by simpa [top1Inputs] using hj)]

def top1Child (p : RawTop1Node × ℕ × Top1State) : Option RawTop1Node :=
  p.1.2.elim
    (if (top1Inputs p.1.1).length ≤ p.2.1 then none
      else some (p.1.1, some (topLiftChild (top1Request (p.1.1, p.2.1)))))
    (fun _ => none)

def top1Combine (p : RawTop1Node × ℕ × Top1State × RawCoset) : Top1State :=
  top1Join (p.1.1.1.1.1, p.2.2.1,
    topLiftFinish (p.1.1.1.1.1, topLiftPrepare (top1Request (p.1.1, p.2.1)), p.2.2.2))

def top1Finish (solve : RawSI → RawCoset) (p : RawTop1Node × Top1State) : RawCoset :=
  p.1.2.elim (p.2.getD none) solve

noncomputable def decTop1Node (n : ℕ) (I : RawTop1Node) : SIInstance (Fin n) ℕ :=
  decFullSI n (I.2.getD (I.1.1.1.2, I.1.2.2.1, I.1.2.2.2))

/-- A leaf stores one of the parent's computed children. This also bounds
its size in terms of the parent data. -/
def Top1WF (n : ℕ) (I : RawTop1Node) : Prop :=
  I.1.1.1.1.length = n ∧ ∀ q, I.2 = some q →
    ∃ j, j < (top1Inputs I.1).length ∧ q = topLiftChild (top1Request (I.1, j))

/-- Proposition 12.0.5 as a raw round. The phase marker gives the strict
measure drop. The parent data are retained so the common ground bound is
unchanged at each child. -/
def top1Round (n : ℕ) (solve : RawSI → RawCoset) : Round RawTop1Node Top1State RawCoset where
  WF := Top1WF n
  ground := fun I => Enc.size I.1
  measure := fun I => I.2.elim 1 (fun _ => 0)
  width := fun I => I.2.elim (top1Inputs I.1).length (fun _ => 0)
  child := top1Child
  init := fun _ => some none
  combine := top1Combine
  finish := top1Finish solve
  bot := none
  child_eq_none := by
    rintro ⟨p, o⟩ j s hj
    cases o with
    | none => simp only [Option.elim_none] at hj; simp only [top1Child, Option.elim_none, if_pos hj]
    | some q => rfl
  child_wf := by
    rintro ⟨p, o⟩ j s J hI hc
    cases o with
    | some q => simp [top1Child] at hc
    | none =>
      simp only [top1Child, Option.elim_none] at hc
      by_cases hj : (top1Inputs p).length ≤ j
      · rw [if_pos hj] at hc; simp at hc
      · rw [if_neg hj] at hc; cases hc
        exact ⟨hI.1, fun q hq => ⟨j, Nat.lt_of_not_ge hj, (Option.some.inj hq).symm⟩⟩
  child_measure := by
    rintro ⟨p, o⟩ j s J hI hc
    cases o with
    | some q => simp [top1Child] at hc
    | none =>
      simp only [top1Child, Option.elim_none] at hc
      by_cases hj : (top1Inputs p).length ≤ j
      · rw [if_pos hj] at hc; simp at hc
      · rw [if_neg hj] at hc; cases hc; exact Nat.zero_lt_one
  child_ground := by
    rintro ⟨p, o⟩ j s J hI hc
    cases o with
    | some q => simp [top1Child] at hc
    | none =>
      simp only [top1Child, Option.elim_none] at hc
      by_cases hj : (top1Inputs p).length ≤ j
      · rw [if_pos hj] at hc; simp at hc
      · rw [if_neg hj] at hc; cases hc; exact le_refl _

theorem polyFun_top1Request : PolyFun top1Request := by
  have hbase : PolyFun (fun p : RawTop1 × ℕ => p.1.1) := polyFun_fst.comp polyFun_fst
  have hstr : PolyFun (fun p : RawTop1 × ℕ => p.1.2.2) :=
    (polyFun_fst.comp polyFun_snd).comp polyFun_snd
  have hone : PolyFun (fun p : RawTop1 × ℕ => rawOne p.1.1.2.1) :=
    ((hbase.comp polyFun_snd).comp polyFun_fst).comp polyFun_rawOne
  have hlist := (hone.pair ((polyFun_fst.comp polyFun_snd).comp polyFun_fst)).comp polyFun_cons
  exact hbase.pair (((hlist.pair polyFun_snd).pair hone).comp polyFun_getD |>.pair hstr)

theorem polyFun_top1Child : PolyFun top1Child := by
  have hb : PolyFun (fun p : RawTop1Node × ℕ × Top1State => p.1.1) :=
    polyFun_fst.comp polyFun_fst
  have hj : PolyFun (fun p : RawTop1Node × ℕ × Top1State => p.2.1) :=
    polyFun_snd.comp polyFun_fst
  have hn := (hb.comp polyFun_top1Inputs).comp polyFun_length
  have hk := (((hb.pair hj).comp polyFun_top1Request).comp polyFun_topLiftChild).comp polyFun_some
  have h := PolyFun.ite (hn.le hj) (polyFun_const none) ((hb.pair hk).comp polyFun_some)
  refine ((((polyFun_fst.comp polyFun_snd).pair polyFun_id).comp
    (PolyFun.optionElim h (polyFun_const none)))).of_eq ?_
  intro p
  simp [top1Child]

theorem polyFun_top1Combine : PolyFun top1Combine := by
  have hd : PolyFun (fun p : RawTop1Node × ℕ × Top1State × RawCoset => p.1.1.1.1.1) :=
    (((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_fst).comp polyFun_fst
  have hp : PolyFun (fun p : RawTop1Node × ℕ × Top1State × RawCoset =>
      topLiftPrepare (top1Request (p.1.1, p.2.1))) :=
    (((polyFun_fst.comp polyFun_fst).pair (polyFun_snd.comp polyFun_fst)).comp
      polyFun_top1Request).comp polyFun_topLiftPrepare
  have ha := (hd.pair (hp.pair ((polyFun_snd.comp polyFun_snd).comp polyFun_snd))).comp
    polyFun_topLiftFinish
  exact (hd.pair (((polyFun_snd.comp polyFun_snd).comp polyFun_fst).pair ha)).comp polyFun_top1Join

theorem polyFun_top1Finish {solve : RawSI → RawCoset} (hs : PolyFun solve) :
    PolyFun (top1Finish solve) := by
  have hd : PolyFun (fun p : RawTop1Node × Top1State => p.2.getD (none : RawCoset)) :=
    (polyFun_snd.pair (polyFun_const none)).comp polyFun_optionGetD
  exact ((((polyFun_fst.comp polyFun_snd).pair polyFun_id).comp
    (PolyFun.optionElim hd (polyFun_fst.comp hs)))).of_eq (fun _ => rfl)

/-! ## A reduction with the computed lifts -/

noncomputable def top1Fold (n : ℕ) : List RawTopLift → Option (Set (Perm (Fin n))) →
    SIReduction (Fin n) ℕ (Option (Set (Perm (Fin n))))
  | [], s => .done s
  | p :: ps, s => (topLiftReduction n p).bind (fun a => top1Fold n ps (top1JoinSet s a))

noncomputable def top1Chain (n : ℕ) (ps : List RawTopLift) (s : Option (Set (Perm (Fin n)))) :
    SIReduction (Fin n) ℕ (Set (Perm (Fin n))) :=
  (top1Fold n ps s).bind (fun a => .done (a.getD ∅))

noncomputable def top1RoundReduction (n : ℕ) (solve : RawSI → RawCoset) (I : RawTop1Node) :
    SIReduction (Fin n) ℕ (Set (Perm (Fin n))) :=
  I.2.elim (top1Chain n (top1Inputs I.1) (some ∅)) (fun q => .done (decCoset n (solve q)))

theorem top1Chain_cons (n : ℕ) (p : RawTopLift) (ps : List RawTopLift)
    (s : Option (Set (Perm (Fin n)))) :
    top1Chain n (p :: ps) s = .call (decFullSI n (topLiftChild p))
      (fun a => top1Chain n ps (top1JoinSet s (topLiftAnswer n p a))) := rfl

theorem decCoset_top1Finish_parent (n : ℕ) (solve : RawSI → RawCoset)
    (p : RawTop1) (s : Top1State) :
    decCoset n (top1Finish solve ((p, none), s)) = (decTop1State n s).getD ∅ := by
  cases s <;> rfl

theorem decTop1State_top1Combine {n : ℕ} (p : RawTop1) (hd : p.1.1.1.length = n)
    (j : ℕ) (s : Top1State) (a : RawCoset) :
    decTop1State n (top1Combine ((p, none), j, s, a)) =
      top1JoinSet (decTop1State n s)
        (topLiftAnswer n (top1Request (p, j)) (decCoset n a)) := by
  rw [top1Combine, decTop1State_top1Join hd]
  exact congrArg (top1JoinSet (decTop1State n s))
    (decCoset_topLiftFinish (top1Request (p, j)) hd a)

theorem loopMatch_top1Round (n : ℕ) (solve : RawSI → RawCoset) (p : RawTop1)
    (hd : p.1.1.1.length = n) :
    ∀ k j, j + k = (top1Inputs p).length → ∀ s : Top1State,
      LoopMatch (top1Round n solve) (decTop1Node n) (decCoset n) (p, none) k j s
        (top1Chain n ((top1Inputs p).drop j) (decTop1State n s)) := by
  intro k
  induction k with
  | zero =>
    intro j hj s
    have he : (top1Inputs p).drop j = [] := List.drop_eq_nil_iff.2 (by omega)
    rw [he]
    exact LoopMatch.done 0 j s _ (by
      simp only [top1Round, top1Child, Option.elim_none, if_pos (show (top1Inputs p).length ≤ j by omega)])
      (decCoset_top1Finish_parent n solve p s)
  | succ k ih =>
    intro j hj s
    have hjl : j < (top1Inputs p).length := by omega
    rw [List.drop_eq_getElem_cons hjl, top1Chain_cons, ← top1Request_eq_getElem p hjl]
    let J : RawTop1Node := (p, some (topLiftChild (top1Request (p, j))))
    change LoopMatch _ _ _ _ _ _ _ (.call (decTop1Node n J) _)
    refine LoopMatch.call k j s J _ ?_ ?_
    · simp only [top1Round, top1Child, J, Option.elim_none, if_neg (Nat.not_le.mpr hjl)]
    · intro a ha
      have hnext := ih (j + 1) (by omega) (top1Combine ((p, none), j, s, a))
      rw [decTop1State_top1Combine p hd, ha] at hnext
      exact hnext

/-- Proposition 12.0.5: every raw child matches the reduction that uses
the computed lifts, for every raw encoding of its true answer. -/
theorem implements_top1Round (n : ℕ) (solve : RawSI → RawCoset) :
    Implements (top1Round n solve) id (decTop1Node n) (decCoset n)
      (top1RoundReduction n solve) := by
  rintro ⟨p, o⟩ hI
  cases o with
  | none => exact loopMatch_top1Round n solve p hI.1 (top1Inputs p).length 0 (Nat.zero_add _) (some none)
  | some q => exact LoopMatch.done 0 0 _ _ rfl rfl

/-! ## The value is independent of the lift -/

theorem cosetHull_eq_subcosetClosure {Γ : Type*} [Group Γ] {S : Set Γ} (hS : S.Nonempty) :
    cosetHull S = Babai.subcosetClosure S := by
  obtain ⟨t, ht⟩ := hS
  apply Set.Subset.antisymm
  · obtain ⟨H, ρ, he⟩ := Babai.isSubcoset_subcosetClosure ⟨t, ht⟩
    rw [he]
    exact cosetHull_subset_of_subset (he ▸ Babai.subset_subcosetClosure S)
  · exact Babai.subcosetClosure_subset
      ⟨Subgroup.closure (t⁻¹ • S), t, cosetHull_eq ht⟩ (subset_cosetHull S)

theorem top1Fold_run (n : ℕ) (ps : List RawTopLift) (s : Option (Set (Perm (Fin n)))) :
    (top1Fold n ps s).run =
      (ps.map (fun p => (topLiftReduction n p).run)).foldl top1JoinSet s := by
  induction ps generalizing s with
  | nil => rfl
  | cons p ps ih => simp only [top1Fold, SIReduction.run_bind, ih, List.map_cons, List.foldl_cons]

theorem fold_top1JoinSet_none {Γ : Type*} [Group Γ] (L : List (Set Γ)) :
    L.foldl top1JoinSet none = none := by
  classical
  induction L with
  | nil => rfl
  | cons a L ih =>
    have he : top1JoinSet (none : Option (Set Γ)) a = none := by simp [top1JoinSet]
    rw [List.foldl_cons, he, ih]

open scoped Classical in
theorem fold_top1JoinSet_some {Γ : Type*} [Group Γ] (L : List (Set Γ)) (S : Set Γ)
    (hS : cosetHull S = S) :
    L.foldl top1JoinSet (some S) =
      if ∀ A ∈ L, A.Nonempty then some (cosetHull (S ∪ ⋃ A ∈ L, A)) else none := by
  classical
  induction L generalizing S with
  | nil => simp [hS]
  | cons A L ih =>
    rw [List.foldl_cons]
    by_cases hA : A.Nonempty
    · rw [top1JoinSet, if_pos hA, Option.map_some, ih _ (cosetHull_idem _)]
      have hu : (⋃ B ∈ A :: L, B) = A ∪ ⋃ B ∈ L, B := by ext x; simp
      rw [hu, cosetHull_hull_union, Set.union_assoc]
      simp only [List.mem_cons, forall_eq_or_imp, hA, true_and]
    · rw [top1JoinSet, if_neg hA, fold_top1JoinSet_none, if_neg]
      intro h
      exact hA (h A (by simp))

open scoped Classical in
/-- The fold equals the paper's subcoset closure once all tests succeed. -/
theorem fold_top1JoinSet_empty {Γ : Type*} [Group Γ] (L : List (Set Γ)) (hL : L ≠ []) :
    L.foldl top1JoinSet (some ∅) =
      if ∀ A ∈ L, A.Nonempty then some (Babai.subcosetClosure (⋃ A ∈ L, A)) else none := by
  classical
  rw [fold_top1JoinSet_some L ∅ cosetHull_empty, Set.empty_union]
  by_cases h : ∀ A ∈ L, A.Nonempty
  · rw [if_pos h, if_pos h, cosetHull_eq_subcosetClosure]
    obtain ⟨A, hA⟩ := List.exists_mem_of_ne_nil L hL
    obtain ⟨a, ha⟩ := h A hA
    exact ⟨a, Set.mem_iUnion.2 ⟨A, Set.mem_iUnion.2 ⟨hA, ha⟩⟩⟩
  · rw [if_neg h, if_neg h]

theorem top1Inputs_encoded {n m : ℕ} (dom gdom : List ℕ) (hm : gdom.length = m)
    (gens : List (Perm (Fin n))) (imgs S : List (Perm (Fin m))) (x y : Fin n → ℕ) :
    top1Inputs (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))),
      S.map (encPerm m), encStrN x, encStrN y) =
      (1 :: S).map (fun τ => (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))),
        encPerm m τ, encStrN x, encStrN y)) := by
  simp [top1Inputs, rawOne, hm, encPerm_one]

/-- Proposition 12.0.5: replacing the classical lifts by the RAM lifts
preserves the complete decision and answer, including failure. -/
theorem run_top1Fold_eq_TopAction1Reduction {n m : ℕ} {dom gdom : List ℕ}
    {gens : List (Perm (Fin n))} {imgs : List (Perm (Fin m))}
    {ϕ : genGroup gens →* Perm (Fin m)} (hd : dom.length = n) (hm : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (S : List (Perm (Fin m))) (x y : Fin n → ℕ) :
    (top1Fold n (top1Inputs (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))),
      S.map (encPerm m), encStrN x, encStrN y)) (some ∅)).run =
      (Babai.TopAction1Reduction ϕ x y S).run := by
  classical
  rw [top1Fold_run, top1Inputs_encoded dom gdom hm, List.map_map]
  simp only [Function.comp_def]
  have he : ((1 :: S).map fun τ =>
      (topLiftReduction n (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))),
        encPerm m τ, encStrN x, encStrN y)).run) = (1 :: S).map (Babai.liftingSet ϕ x y) := by
    apply List.map_congr_left
    intro τ _
    exact run_topLiftReduction hd hm hI τ x y
  rw [he, fold_top1JoinSet_empty _ (by simp), Babai.TopAction1Reduction,
    SIReduction.run_bind, Babai.run_liftAll, SIReduction.run_done]

theorem calls_top1Fold (n : ℕ) (ps : List RawTopLift) (s : Option (Set (Perm (Fin n)))) :
    (top1Fold n ps s).calls = ps.map (fun p => decFullSI n (topLiftChild p)) := by
  induction ps generalizing s with
  | nil => rfl
  | cons p ps ih => simp [top1Fold, topLiftReduction, ih]

/-- Proposition 12.0.5 retains exactly `|S| + 1` kernel tests. -/
theorem calls_length_top1RoundReduction (n : ℕ) (solve : RawSI → RawCoset) (p : RawTop1) :
    (top1RoundReduction n solve (p, none)).calls.length = p.2.1.length + 1 := by
  simp [top1RoundReduction, top1Chain, calls_top1Fold]

theorem liftingSet_subtype_comp {n m : ℕ} {G : Subgroup (Perm (Fin n))}
    {H : Subgroup (Perm (Fin m))} (ϕ : G →* H) (x y : Fin n → ℕ) (τ : H) :
    Babai.liftingSet (H.subtype.comp ϕ) x y τ.val = Babai.liftingSet ϕ x y τ := by
  ext g
  constructor
  · rintro ⟨⟨hg, he⟩, hi⟩
    exact ⟨⟨hg, Subtype.ext he⟩, hi⟩
  · rintro ⟨⟨hg, he⟩, hi⟩
    exact ⟨⟨hg, congrArg Subtype.val he⟩, hi⟩

/-- Proposition 12.0.5 for an arbitrary target permutation subgroup,
which need not equal the image of the action. -/
theorem run_top1Fold_eq_targetReduction {n m : ℕ} {dom gdom : List ℕ}
    {gens : List (Perm (Fin n))} {imgs : List (Perm (Fin m))}
    {H : Subgroup (Perm (Fin m))} (ϕ : genGroup gens →* H)
    (hd : dom.length = n) (hm : gdom.length = m) (hI : ImgsOf gens imgs (H.subtype.comp ϕ))
    (S : List H) (x y : Fin n → ℕ) :
    (top1Fold n (top1Inputs (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))),
      S.map (fun τ => encPerm m τ.val), encStrN x, encStrN y)) (some ∅)).run =
      (Babai.TopAction1Reduction ϕ x y S).run := by
  classical
  have h := run_top1Fold_eq_TopAction1Reduction hd hm hI (S.map Subtype.val) x y
  rw [List.map_map] at h
  refine h.trans ?_
  simp only [Babai.TopAction1Reduction, SIReduction.run_bind, Babai.run_liftAll,
    SIReduction.run_done]
  have he : (1 :: S.map Subtype.val).map (Babai.liftingSet (H.subtype.comp ϕ) x y) =
      (1 :: S).map (Babai.liftingSet ϕ x y) := by
    have he1 := liftingSet_subtype_comp ϕ x y (1 : H)
    simp only [List.map_cons, List.map_map]
    apply congrArg₂ List.cons he1
    apply List.map_congr_left
    intro τ _
    exact liftingSet_subtype_comp ϕ x y τ
  rw [he]

/-- The `Implements` target has the same run as the original reduction,
after reading a negative decision as the empty answer. -/
theorem run_top1RoundReduction_eq {n m : ℕ} {dom gdom : List ℕ}
    {gens : List (Perm (Fin n))} {imgs : List (Perm (Fin m))}
    {H : Subgroup (Perm (Fin m))} (ϕ : genGroup gens →* H)
    (hd : dom.length = n) (hm : gdom.length = m) (hI : ImgsOf gens imgs (H.subtype.comp ϕ))
    (S : List H) (x y : Fin n → ℕ) (solve : RawSI → RawCoset) :
    (top1RoundReduction n solve ((((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))),
      S.map (fun τ => encPerm m τ.val), encStrN x, encStrN y), none)).run =
      ((Babai.TopAction1Reduction ϕ x y S).run).getD ∅ := by
  simp only [top1RoundReduction, Option.elim_none, top1Chain, SIReduction.run_bind,
    SIReduction.run_done, run_top1Fold_eq_targetReduction ϕ hd hm hI S x y]

/-- Every computed child, including a discarded failed lift, is a full
window instance for the kernel. -/
theorem topLiftChild_group {n m : ℕ} {dom gdom : List ℕ}
    {gens : List (Perm (Fin n))} {imgs : List (Perm (Fin m))}
    {ϕ : genGroup gens →* Perm (Fin m)} (hd : dom.length = n) (hm : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (τ : Perm (Fin m)) (x y : Fin n → ℕ) :
    (decFullSI n (topLiftChild (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))),
      encPerm m τ, encStrN x, encStrN y))).K = (Babai.kerSubgroup ϕ : Set (Perm (Fin n))) ∧
    (decFullSI n (topLiftChild (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))),
      encPerm m τ, encStrN x, encStrN y))).Δ = Set.univ := by
  refine ⟨?_, rfl⟩
  cases hp : topLiftPrepare
      (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))),
        encPerm m τ, encStrN x, encStrN y) with
  | none =>
    simp only [topLiftChild, hp, Option.elim_none, decFullSI,
      decGroup_tidyGens hd, decGroup_actKerGens hd hm hI]
    rfl
  | some q =>
    obtain ⟨σ, _, _, hc⟩ := topLiftPrepare_child hd hm hI τ x y hp
    simp only [topLiftChild, hp, Option.elim_some, hc]

/-- One complete raw round has the specified run when the child solver
answers each instance correctly. -/
theorem top1Round_value_two (n : ℕ) (solve : RawSI → RawCoset)
    (hs : ∀ q, decCoset n (solve q) = (decFullSI n q).answer)
    (p : RawTop1) (hd : p.1.1.1.length = n) :
    decCoset n ((top1Round n solve).value 2 (p, none)) =
      (top1RoundReduction n solve (p, none)).run := by
  have himpl := implements_top1Round n solve (p, none) ⟨hd, by simp⟩
  have h := (top1Round n solve).loopAux_eq
    (rec := (top1Round n solve).value 1)
    (Good := fun J : RawTop1Node => ∃ q, J.2 = some q)
    (fun j s J hc => by
      change top1Child ((p, none), j, s) = some J at hc
      simp only [top1Child, Option.elim_none] at hc
      by_cases hj : (top1Inputs p).length ≤ j
      · rw [if_pos hj] at hc; simp at hc
      · rw [if_neg hj] at hc
        cases hc
        exact ⟨_, rfl⟩)
    (fun J hJ => by
      obtain ⟨q, hq⟩ := hJ
      have hv : (top1Round n solve).value 1 J = solve q := by
        rw [Round.value_succ]
        change (top1Round n solve).loopAux _ (J.2.elim _ _) J 0 _ = _
        rw [hq]
        change top1Finish solve (J, some none) = solve q
        simp [top1Finish, hq]
      rw [hv]
      simpa [decTop1Node, hq] using hs q)
    _ _ _ _ himpl
  exact h.1

open scoped Classical in
/-- The raw round decides surjectivity onto the supplied target group.
On a positive decision it returns the full string-isomorphism coset. -/
theorem top1Round_spec {n m : ℕ} {dom gdom : List ℕ}
    {gens : List (Perm (Fin n))} {imgs : List (Perm (Fin m))}
    {H : Subgroup (Perm (Fin m))} (ϕ : genGroup gens →* H)
    (hd : dom.length = n) (hm : gdom.length = m) (hI : ImgsOf gens imgs (H.subtype.comp ϕ))
    (S : List H) (hS : Subgroup.closure {σ : H | σ ∈ S} = ⊤)
    (x y : Fin n → ℕ) (solve : RawSI → RawCoset)
    (hs : ∀ q, decCoset n (solve q) = (decFullSI n q).answer) :
    decCoset n ((top1Round n solve).value 2
      ((((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))),
        S.map (fun τ => encPerm m τ.val), encStrN x, encStrN y), none)) =
      if Babai.MapsOnto ϕ x y then Babai.strIso (genGroup gens : Set (Perm (Fin n))) x y else ∅ := by
  rw [top1Round_value_two n solve hs _ hd, run_top1RoundReduction_eq ϕ hd hm hI,
    Babai.run_TopAction1Reduction ϕ x y S hS]
  split_ifs <;> rfl

theorem decCoset_eq_empty_iff (n : ℕ) (a : RawCoset) : decCoset n a = ∅ ↔ a = none := by
  cases a with
  | none => simp [decCoset]
  | some q =>
    have hn := (decCoset_nonempty (n := n) (some q)).2 rfl
    simp only [Option.some_ne_none, iff_false]
    exact hn.ne_empty

/-- The raw `none` result is precisely the negative decision in
Proposition 12.0.5. A positive decision has a nonempty isomorphism coset. -/
theorem top1Round_eq_none_iff {n m : ℕ} {dom gdom : List ℕ}
    {gens : List (Perm (Fin n))} {imgs : List (Perm (Fin m))}
    {H : Subgroup (Perm (Fin m))} (ϕ : genGroup gens →* H)
    (hd : dom.length = n) (hm : gdom.length = m) (hI : ImgsOf gens imgs (H.subtype.comp ϕ))
    (S : List H) (hS : Subgroup.closure {σ : H | σ ∈ S} = ⊤)
    (x y : Fin n → ℕ) (solve : RawSI → RawCoset)
    (hs : ∀ q, decCoset n (solve q) = (decFullSI n q).answer) :
    (top1Round n solve).value 2
      ((((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))),
        S.map (fun τ => encPerm m τ.val), encStrN x, encStrN y), none) = none ↔
      ¬ Babai.MapsOnto ϕ x y := by
  classical
  rw [← decCoset_eq_empty_iff n, top1Round_spec ϕ hd hm hI S hS x y solve hs]
  by_cases h : Babai.MapsOnto ϕ x y
  · have hn : (Babai.strIso (genGroup gens : Set (Perm (Fin n))) x y).Nonempty :=
      (h 1).mono Set.inter_subset_right
    simp [h, hn.ne_empty]
  · simp [h]

/-- All the calls of the round use the kernel and the full domain. -/
theorem calls_top1RoundReduction_kernel {n m : ℕ} {dom gdom : List ℕ}
    {gens : List (Perm (Fin n))} {imgs : List (Perm (Fin m))}
    {ϕ : genGroup gens →* Perm (Fin m)} (hd : dom.length = n) (hm : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (S : List (Perm (Fin m))) (x y : Fin n → ℕ)
    (solve : RawSI → RawCoset) :
    ∀ I ∈ (top1RoundReduction n solve
      ((((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))),
        S.map (encPerm m), encStrN x, encStrN y), none)).calls,
      I.K = (Babai.kerSubgroup ϕ : Set (Perm (Fin n))) ∧ I.Δ = Set.univ := by
  intro I hI'
  simp only [top1RoundReduction, Option.elim_none, top1Chain, SIReduction.calls_bind,
    SIReduction.calls_done, List.append_nil, calls_top1Fold,
    top1Inputs_encoded dom gdom hm, List.map_map, List.mem_map] at hI'
  obtain ⟨τ, _, rfl⟩ := hI'
  exact topLiftChild_group hd hm hI τ x y

end Algo
