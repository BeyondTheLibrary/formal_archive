/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5): node carriers bounded at the
degree under a condition on their fold states. Not part of the faithful formalization.
-/
import Workspace.Explicit.CarriersDispatch

/-!
# Carriers with a state invariant

`Explicit.CarrierTN` asks the routines of a carrier to be bounded at the degree on every fold
state, and `Explicit.StateBoundsXR` bounds the states that `init` and `combine` return, whatever
state `combine` starts from. Some carriers only meet such bounds on the states a run reaches
(lines 5–7: `Algo.aggnAggregatePack` caps its phase states at `2^{(log |x| + 2)^{dc}}` with an
existential `dc`). Here the fold state carries an invariant `J n P s`, at the root degree `n`.

* `Explicit.CarrierTNJ a b F R J`: the width and the four routines of `F` bounded at the degree
  with exponent 5, where `child`, `combine` and `finish` may assume `J`. The width is needed:
  the round's child is guarded by it (`Algo.masterGuardedChild`).
* `Explicit.StateInvXR a b K F R J`: `init` establishes `J`, `combine` keeps it (on answers of
  size at most `Algo.masterInputCap a b n`), and `J` bounds the state by `2^{K (log₂ n+2)^5}` and
  the answer by the input cap and by `2^{K (log₂ n+2)^5}`; all at nodes of degree exactly `n`
  (`Explicit.NodeAt`).
* Bridges: `Explicit.CarrierTN.toJ` (any `J`, given the width), `Explicit.StateBoundsXR.toInv`
  (the states one step from `init`, `Explicit.ReachJ`).
* Combinators: `pairIteG` (a test bounded at the degree, branch predicates), `pairIte`,
  `pairIteR`, `withHint`, for both; the invariant of two carriers side by side is
  `Explicit.pairJ`.
-/

set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1000000

namespace Explicit

open RAM Algo

private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd

namespace TN

variable {α β : Type*} [Enc α] [Enc β]

/-- **A test bounded at the degree, with branch preconditions.** -/
theorem iteTR {p : α → Bool} {f g : α → β} {Pre Pf Pg : ℕ → α → Prop} {k : ℕ}
    (hp : TN p Pre k) (hf : TN f Pf k) (hg : TN g Pg k)
    (hPf : ∀ n a, Pre n a → p a = true → Pf n a) (hPg : ∀ n a, Pre n a → p a = false → Pg n a) :
    TN (fun a => if p a then f a else g a) Pre k :=
  ((hp.pair (id' Pre k)).comp (ite (Pre := fun n (q : Bool × α) => Pre n q.2 ∧ q.1 = p q.2)
    polyFun_fst (poly_comp polyFun_snd hf) (poly_comp polyFun_snd hg)
    (fun n q h hq => hPf n q.2 h.1 (h.2.symm.trans hq))
    (fun n q h hq => hPg n q.2 h.1 (h.2.symm.trans hq))) (fun _ _ h => ⟨h, rfl⟩)).of_eq
    (fun _ => rfl)

end TN

/-! ## The interface -/

/-- **An admitted node of degree exactly `n`** with the node predicate `R`. -/
def NodeAt (a b : ℕ) (R : RawMasterSI → Prop) (n : ℕ) (P : RawMasterSI) : Prop :=
  MasterInputWF a b P ∧ masterDegree P = n ∧ R P

theorem NodeAt.pre {a b n : ℕ} {R : RawMasterSI → Prop} {P : RawMasterSI}
    (h : NodeAt a b R n P) : CarrierPre a b R n P :=
  ⟨h.1, h.2.1.le, h.2.2⟩

/-- A condition on the fold state `s` at the fold index `j` of the node `P`, in a run from a
root of degree `n`: `J n P j s`. -/
abbrev StInv (S : Type) : Type := ℕ → RawMasterSI → ℕ → S → Prop

/-- **A carrier bounded at the degree under a state invariant `J`**: its width and its four
routines, with exponent 5; `child`, `combine` and `finish` assume `J` of the state they read
(`finish` at some fold index). -/
structure CarrierTNJ {S : Type} [Enc S] (a b : ℕ) (F : MasterOps S) (R : RawMasterSI → Prop)
    (J : StInv S) : Prop where
  width : TN F.width (CarrierPre a b R) 5
  child : TN F.child (fun n z => CarrierPre a b R n z.1 ∧ J n z.1 z.2.1 z.2.2) 5
  init : TN F.init (CarrierPre a b R) 5
  combine : TN F.combine (fun n z => CarrierPre a b R n z.1 ∧ J n z.1 z.2.1 z.2.2.1 ∧
    Enc.size z.2.2.2 ≤ masterInputCap a b n) 5
  finish : TN F.finish (fun n z => CarrierPre a b R n z.1 ∧ ∃ j, J n z.1 j z.2) 5

/-- **The fold states under an invariant, with an explicit exponent**, at the nodes of degree
exactly `n` with `R`: `init` establishes `J` at index 0; `combine` at index `j` keeps it (at
index `j + 1`) when the round asked a child there (`j` below the width, `child` returned one)
and the answer is within the input cap; under `J` the state has size at most
`2^{K (log₂ n+2)^5}`, and the answer fits the input cap and `2^{K (log₂ n+2)^5}`. -/
def StateInvXR {S : Type} [Enc S] (a b K : ℕ) (F : MasterOps S) (R : RawMasterSI → Prop)
    (J : StInv S) : Prop :=
  (∀ n P, NodeAt a b R n P → J n P 0 (F.init P)) ∧
  (∀ n P j s C A, NodeAt a b R n P → J n P j s → j < F.width P → F.child (P, j, s) = some C →
    Enc.size A ≤ masterInputCap a b n → J n P (j + 1) (F.combine (P, j, s, A))) ∧
  (∀ n P j s, NodeAt a b R n P → J n P j s → Enc.size s ≤ 2 ^ (K * lg n ^ 5)) ∧
  (∀ n P j s, NodeAt a b R n P → J n P j s →
    Enc.size (F.finish (P, s)) ≤ masterInputCap a b n) ∧
  (∀ n P j s, NodeAt a b R n P → J n P j s →
    Enc.size (F.finish (P, s)) ≤ 2 ^ (K * lg n ^ 5))

/-- **The states one step from `init`**: `init P`, or a `combine` of any state with an answer
within the input cap. The invariant of the carriers whose `combine` is bounded on every
state (`Explicit.StateBoundsXR`). -/
def ReachJ {S : Type} [Enc S] (a b : ℕ) (F : MasterOps S) : StInv S := fun n P _ s =>
  s = F.init P ∨ ∃ j s' A, Enc.size A ≤ masterInputCap a b n ∧ s = F.combine (P, j, s', A)

/-- **The invariant of two carriers side by side** (`Algo.MasterOps.pairIte`): the taken
component satisfies its invariant, the other one is its default. -/
def pairJ {S T : Type} (sel : RawMasterSI → Bool) (dS : S) (dT : T) (J1 : StInv S)
    (J2 : StInv T) : StInv (S × T) := fun n P j s =>
  (sel P = true → J1 n P j s.1 ∧ s.2 = dT) ∧ (sel P = false → J2 n P j s.2 ∧ s.1 = dS)

/-! ## Bridges -/

/-- **A carrier bounded on every state is bounded under every invariant**, given its width. -/
theorem CarrierTN.toJ {S : Type} [Enc S] {a b : ℕ} {F : MasterOps S} {R : RawMasterSI → Prop}
    (h : CarrierTN a b F R) (hw : TN F.width (CarrierPre a b R) 5) (J : StInv S) :
    CarrierTNJ a b F R J :=
  ⟨hw, h.child.restrict (fun _ _ h => h.1), h.init,
    h.combine.restrict (fun _ _ h => ⟨h.1, h.2.2⟩), h.finish.restrict (fun _ _ h => h.1)⟩

/-- **Bounds on every state give an invariant**: the states one step from `init`. -/
theorem StateBoundsXR.toInv {S : Type} [Enc S] {a b K : ℕ} {F : MasterOps S}
    {R : RawMasterSI → Prop} (h : StateBoundsXR a b K F R) :
    StateInvXR a b K F R (ReachJ a b F) := by
  refine ⟨fun n P _ => Or.inl rfl,
    fun n P j s _ A _ _ _ _ hA => Or.inr ⟨j, s, A, hA, rfl⟩,
    fun n P j s hP hJ => ?_, fun n P j s hP _ => ?_, fun n P j s hP _ => ?_⟩
  · obtain ⟨hw, rfl, hR⟩ := hP
    rcases hJ with rfl | ⟨j', s', A, hA, rfl⟩
    · exact h.1 P hw hR
    · exact h.2.1 P j' s' A hw hR hA
  · obtain ⟨hw, rfl, hR⟩ := hP
    exact h.2.2.1 P s hw hR
  · obtain ⟨hw, rfl, hR⟩ := hP
    exact h.2.2.2 P s hw hR

/-! ## Combinators for `CarrierTNJ` -/

namespace CarrierTNJ

variable {a b : ℕ}

theorem restrict {S : Type} [Enc S] {F : MasterOps S} {R R' : RawMasterSI → Prop}
    {J : StInv S} (h : CarrierTNJ a b F R J) (hR : ∀ P, R' P → R P) :
    CarrierTNJ a b F R' J :=
  ⟨h.width.restrict fun _ _ h' => ⟨h'.1, h'.2.1, hR _ h'.2.2⟩,
    h.child.restrict fun _ _ h' => ⟨⟨h'.1.1, h'.1.2.1, hR _ h'.1.2.2⟩, h'.2⟩,
    h.init.restrict fun _ _ h' => ⟨h'.1, h'.2.1, hR _ h'.2.2⟩,
    h.combine.restrict fun _ _ h' => ⟨⟨h'.1.1, h'.1.2.1, hR _ h'.1.2.2⟩, h'.2⟩,
    h.finish.restrict fun _ _ h' => ⟨⟨h'.1.1, h'.1.2.1, hR _ h'.1.2.2⟩, h'.2⟩⟩

/-- **Two carriers side by side, with a branch test bounded at the degree**; each carrier
needs its node predicate only at the nodes where it is taken. -/
theorem pairIteG {S T : Type} [Enc S] [Enc T] {sel : RawMasterSI → Bool}
    {R RF RG : RawMasterSI → Prop} (hsel : TN sel (CarrierPre a b R) 5) {F : MasterOps S}
    {G : MasterOps T} {dS : S} {dT : T} {J1 : StInv S} {J2 : StInv T}
    (hF : CarrierTNJ a b F RF J1) (hG : CarrierTNJ a b G RG J2)
    (hRF : ∀ P, R P → sel P = true → RF P) (hRG : ∀ P, R P → sel P = false → RG P) :
    CarrierTNJ a b (MasterOps.pairIte sel F G dS dT) R (pairJ sel dS dT J1 J2) := by
  have hPF : ∀ n P, CarrierPre a b R n P → sel P = true → CarrierPre a b RF n P :=
    fun _ P h hs => ⟨h.1, h.2.1, hRF P h.2.2 hs⟩
  have hPG : ∀ n P, CarrierPre a b R n P → sel P = false → CarrierPre a b RG n P :=
    fun _ P h hs => ⟨h.1, h.2.1, hRG P h.2.2 hs⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (TN.iteTR hsel hF.width hG.width hPF hPG).of_eq (fun _ => rfl)
  · have hs : TN (fun z : RawMasterSI × ℕ × S × T => sel z.1)
        (fun n z => CarrierPre a b R n z.1 ∧ pairJ sel dS dT J1 J2 n z.1 z.2.1 z.2.2) 5 :=
      (TN.poly_comp polyFun_fst hsel).restrict (fun _ _ h => h.1)
    have h1 : TN (fun z : RawMasterSI × ℕ × S × T => F.child (z.1, z.2.1, z.2.2.1))
        (fun n z => CarrierPre a b RF n z.1 ∧ J1 n z.1 z.2.1 z.2.2.1) 5 :=
      (TN.poly_comp (polyFun_fst.pair ((pfst polyFun_snd).pair (pfst (psnd polyFun_snd))))
        hF.child).restrict (fun _ _ h => h)
    have h2 : TN (fun z : RawMasterSI × ℕ × S × T => G.child (z.1, z.2.1, z.2.2.2))
        (fun n z => CarrierPre a b RG n z.1 ∧ J2 n z.1 z.2.1 z.2.2.2) 5 :=
      (TN.poly_comp (polyFun_fst.pair ((pfst polyFun_snd).pair (psnd (psnd polyFun_snd))))
        hG.child).restrict (fun _ _ h => h)
    exact (TN.iteTR hs h1 h2 (fun n z h hz => ⟨hPF n z.1 h.1 hz, (h.2.1 hz).1⟩)
      (fun n z h hz => ⟨hPG n z.1 h.1 hz, (h.2.2 hz).1⟩)).of_eq (fun _ => rfl)
  · exact (TN.iteTR hsel (hF.init.pair (TN.const' dT _ 5)) ((TN.const' dS _ 5).pair hG.init)
      hPF hPG).of_eq (fun _ => rfl)
  · have hs : TN (fun z : RawMasterSI × ℕ × (S × T) × RawCoset => sel z.1)
        (fun n z => CarrierPre a b R n z.1 ∧ pairJ sel dS dT J1 J2 n z.1 z.2.1 z.2.2.1 ∧
          Enc.size z.2.2.2 ≤ masterInputCap a b n) 5 :=
      (TN.poly_comp polyFun_fst hsel).restrict (fun _ _ h => h.1)
    have h1 : TN (fun z : RawMasterSI × ℕ × (S × T) × RawCoset =>
        F.combine (z.1, z.2.1, z.2.2.1.1, z.2.2.2))
        (fun n z => CarrierPre a b RF n z.1 ∧ J1 n z.1 z.2.1 z.2.2.1.1 ∧
          Enc.size z.2.2.2 ≤ masterInputCap a b n) 5 :=
      (TN.poly_comp (polyFun_fst.pair ((pfst polyFun_snd).pair
        ((pfst (pfst (psnd polyFun_snd))).pair (psnd (psnd polyFun_snd))))) hF.combine).restrict
        (fun _ _ h => h)
    have h2 : TN (fun z : RawMasterSI × ℕ × (S × T) × RawCoset =>
        G.combine (z.1, z.2.1, z.2.2.1.2, z.2.2.2))
        (fun n z => CarrierPre a b RG n z.1 ∧ J2 n z.1 z.2.1 z.2.2.1.2 ∧
          Enc.size z.2.2.2 ≤ masterInputCap a b n) 5 :=
      (TN.poly_comp (polyFun_fst.pair ((pfst polyFun_snd).pair
        ((psnd (pfst (psnd polyFun_snd))).pair (psnd (psnd polyFun_snd))))) hG.combine).restrict
        (fun _ _ h => h)
    exact (TN.iteTR hs (h1.pair (TN.const' dT _ 5)) ((TN.const' dS _ 5).pair h2)
      (fun n z h hz => ⟨hPF n z.1 h.1 hz, (h.2.1.1 hz).1, h.2.2⟩)
      (fun n z h hz => ⟨hPG n z.1 h.1 hz, (h.2.1.2 hz).1, h.2.2⟩)).of_eq (fun _ => rfl)
  · have hs : TN (fun z : RawMasterSI × S × T => sel z.1)
        (fun n z => CarrierPre a b R n z.1 ∧ ∃ j, pairJ sel dS dT J1 J2 n z.1 j z.2) 5 :=
      (TN.poly_comp polyFun_fst hsel).restrict (fun _ _ h => h.1)
    have h1 : TN (fun z : RawMasterSI × S × T => F.finish (z.1, z.2.1))
        (fun n z => CarrierPre a b RF n z.1 ∧ ∃ j, J1 n z.1 j z.2.1) 5 :=
      (TN.poly_comp (polyFun_fst.pair (pfst polyFun_snd)) hF.finish).restrict (fun _ _ h => h)
    have h2 : TN (fun z : RawMasterSI × S × T => G.finish (z.1, z.2.2))
        (fun n z => CarrierPre a b RG n z.1 ∧ ∃ j, J2 n z.1 j z.2.2) 5 :=
      (TN.poly_comp (polyFun_fst.pair (psnd polyFun_snd)) hG.finish).restrict (fun _ _ h => h)
    refine (TN.iteTR hs h1 h2 (fun n z h hz => ⟨hPF n z.1 h.1 hz, ?_⟩)
      (fun n z h hz => ⟨hPG n z.1 h.1 hz, ?_⟩)).of_eq (fun _ => rfl)
    · obtain ⟨j, hj⟩ := h.2
      exact ⟨j, (hj.1 hz).1⟩
    · obtain ⟨j, hj⟩ := h.2
      exact ⟨j, (hj.2 hz).1⟩

/-- **Two carriers side by side, with a branch test bounded at the degree.** -/
theorem pairIte {S T : Type} [Enc S] [Enc T] {sel : RawMasterSI → Bool} {R : RawMasterSI → Prop}
    (hsel : TN sel (CarrierPre a b R) 5) {F : MasterOps S} {G : MasterOps T} {dS : S} {dT : T}
    {J1 : StInv S} {J2 : StInv T} (hF : CarrierTNJ a b F R J1) (hG : CarrierTNJ a b G R J2) :
    CarrierTNJ a b (MasterOps.pairIte sel F G dS dT) R (pairJ sel dS dT J1 J2) :=
  pairIteG hsel hF hG (fun _ h _ => h) (fun _ h _ => h)

/-- **Two carriers side by side, with a polynomial branch test and branch predicates.** -/
theorem pairIteR {S T : Type} [Enc S] [Enc T] {sel : RawMasterSI → Bool} (hsel : PolyFun sel)
    {R RF RG : RawMasterSI → Prop} {F : MasterOps S} {G : MasterOps T} {dS : S} {dT : T}
    {J1 : StInv S} {J2 : StInv T} (hF : CarrierTNJ a b F RF J1) (hG : CarrierTNJ a b G RG J2)
    (hRF : ∀ P, R P → sel P = true → RF P) (hRG : ∀ P, R P → sel P = false → RG P) :
    CarrierTNJ a b (MasterOps.pairIte sel F G dS dT) R (pairJ sel dS dT J1 J2) :=
  pairIteG (TN.ofPoly hsel _ 5) hF hG hRF hRG

/-- **A carrier with a hint routine bounded at the degree** (the routine may assume the
invariant of the state it reads). -/
theorem withHint {S : Type} [Enc S] {F : MasterOps S} {R : RawMasterSI → Prop} {J : StInv S}
    {H : (RawMasterSI × ℕ × S) × RawMasterSI → Option RawMasterHint}
    (hF : CarrierTNJ a b F R J)
    (hH : TN H (fun n w => CarrierPre a b R n w.1.1 ∧ J n w.1.1 w.1.2.1 w.1.2.2) 5) :
    CarrierTNJ a b (F.withHint H) R J := by
  refine ⟨hF.width, ?_, hF.init, hF.combine, hF.finish⟩
  have hH' : TN (fun w : RawMasterSI × (RawMasterSI × ℕ × S) => H (w.2, w.1))
      (fun n w => CarrierPre a b R n w.2.1 ∧ J n w.2.1 w.2.2.1 w.2.2.2) 5 :=
    (TN.poly_comp (polyFun_snd.pair polyFun_fst) hH).restrict (fun _ _ h => h)
  have hh : TN (fun w : RawMasterSI × (RawMasterSI × ℕ × S) =>
      some (masterAttachHint (w.1, H (w.2, w.1))))
      (fun n w => CarrierPre a b R n w.2.1 ∧ J n w.2.1 w.2.2.1 w.2.2.2) 5 :=
    ((TN.ofPoly polyFun_fst _ 5).pair hH').comp_poly
      (polyFun_masterAttachHint.comp polyFun_some)
  have ho := TN.optionElim
    (Pre := fun n (p : Option RawMasterSI × (RawMasterSI × ℕ × S)) =>
      CarrierPre a b R n p.2.1 ∧ J n p.2.1 p.2.2.1 p.2.2.2)
    (TN.const' (none : Option RawMasterSI) (fun _ (_ : RawMasterSI × ℕ × S) => True) 5) hh
    (fun _ _ _ => trivial) (fun _ _ _ h => h)
  refine ((hF.child.pair (TN.id' _ 5)).comp ho (fun _ _ h => h)).of_eq (fun z => ?_)
  change Option.elim (F.child z) none
      (fun C => some (masterAttachHint (C, H (z, C)))) =
    Option.map (fun C => masterAttachHint (C, H (z, C))) (F.child z)
  cases F.child z <;> rfl

end CarrierTNJ

/-! ## Combinators for `StateInvXR` -/

namespace StateInvXR

variable {a b : ℕ}

theorem mono {S : Type} [Enc S] {F : MasterOps S} {R : RawMasterSI → Prop} {J : StInv S}
    {K K' : ℕ} (h : StateInvXR a b K F R J) (hK : K ≤ K') : StateInvXR a b K' F R J :=
  ⟨h.1, h.2.1,
    fun n P j s hP hJ => (h.2.2.1 n P j s hP hJ).trans (StateBoundsX.two_pow_mono hK _),
    h.2.2.2.1,
    fun n P j s hP hJ => (h.2.2.2.2 n P j s hP hJ).trans (StateBoundsX.two_pow_mono hK _)⟩

theorem restrict {S : Type} [Enc S] {F : MasterOps S} {R R' : RawMasterSI → Prop} {J : StInv S}
    {K : ℕ} (h : StateInvXR a b K F R J) (hR : ∀ P, R' P → R P) : StateInvXR a b K F R' J := by
  have hN : ∀ n P, NodeAt a b R' n P → NodeAt a b R n P :=
    fun _ P h => ⟨h.1, h.2.1, hR P h.2.2⟩
  exact ⟨fun n P hP => h.1 n P (hN n P hP),
    fun n P j s C A hP => h.2.1 n P j s C A (hN n P hP),
    fun n P j s hP => h.2.2.1 n P j s (hN n P hP),
    fun n P j s hP => h.2.2.2.1 n P j s (hN n P hP),
    fun n P j s hP => h.2.2.2.2 n P j s (hN n P hP)⟩

theorem withHint {S : Type} [Enc S] {F : MasterOps S} {R : RawMasterSI → Prop} {J : StInv S}
    {K : ℕ} (H : (RawMasterSI × ℕ × S) × RawMasterSI → Option RawMasterHint)
    (h : StateInvXR a b K F R J) : StateInvXR a b K (F.withHint H) R J := by
  refine ⟨h.1, fun n P j s C A hP hJ hw hc hA => ?_, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  change Option.map _ (F.child (P, j, s)) = some C at hc
  cases hF : F.child (P, j, s) with
  | none => rw [hF] at hc; simp at hc
  | some C' => exact h.2.1 n P j s C' A hP hJ hw hF hA

/-- **Two carriers side by side, with branch predicates**: the default states add a constant
to the exponent. -/
theorem pairIteR {S T : Type} [Enc S] [Enc T] (sel : RawMasterSI → Bool) {F : MasterOps S}
    {G : MasterOps T} (dS : S) (dT : T) {K K' : ℕ} {R RF RG : RawMasterSI → Prop}
    {J1 : StInv S} {J2 : StInv T}
    (hF : StateInvXR a b K F RF J1) (hG : StateInvXR a b K' G RG J2)
    (hRF : ∀ P, R P → sel P = true → RF P) (hRG : ∀ P, R P → sel P = false → RG P) :
    StateInvXR a b (K + K' + (Enc.size dS + Enc.size dT) + 1)
      (MasterOps.pairIte sel F G dS dT) R (pairJ sel dS dT J1 J2) := by
  have hF' := hF.mono (Nat.le_add_right K K')
  have hG' := hG.mono (Nat.le_add_left K' K)
  have hL : ∀ n : ℕ, 1 ≤ lg n ^ 5 := fun n => one_le_lg5 _
  have hK : K + K' ≤ K + K' + (Enc.size dS + Enc.size dT) + 1 := by omega
  have hNF : ∀ n P, NodeAt a b R n P → sel P = true → NodeAt a b RF n P :=
    fun _ P h hs => ⟨h.1, h.2.1, hRF P h.2.2 hs⟩
  have hNG : ∀ n P, NodeAt a b R n P → sel P = false → NodeAt a b RG n P :=
    fun _ P h hs => ⟨h.1, h.2.1, hRG P h.2.2 hs⟩
  refine ⟨fun n P hP => ?_, fun n P j s C A hP hJ hw hc hA => ?_, fun n P j s hP hJ => ?_,
    fun n P j s hP hJ => ?_, fun n P j s hP hJ => ?_⟩
  · show pairJ sel dS dT J1 J2 n P 0 (if sel P then (F.init P, dT) else (dS, G.init P))
    cases hs : sel P
    · rw [if_neg (by decide)]
      exact ⟨fun h => absurd (hs.symm.trans h) (by decide),
        fun _ => ⟨hG.1 n P (hNG n P hP hs), rfl⟩⟩
    · rw [if_pos rfl]
      exact ⟨fun _ => ⟨hF.1 n P (hNF n P hP hs), rfl⟩,
        fun h => absurd (hs.symm.trans h) (by decide)⟩
  · show pairJ sel dS dT J1 J2 n P (j + 1) (if sel P then (F.combine (P, j, s.1, A), dT)
      else (dS, G.combine (P, j, s.2, A)))
    change j < (if sel P then F.width P else G.width P) at hw
    change (if sel P then F.child (P, j, s.1) else G.child (P, j, s.2)) = some C at hc
    cases hs : sel P
    · rw [hs, if_neg (by decide)] at hw hc
      rw [if_neg (by decide)]
      exact ⟨fun h => absurd (hs.symm.trans h) (by decide),
        fun _ => ⟨hG.2.1 n P j s.2 C A (hNG n P hP hs) (hJ.2 hs).1 hw hc hA, rfl⟩⟩
    · rw [hs, if_pos rfl] at hw hc
      rw [if_pos rfl]
      exact ⟨fun _ => ⟨hF.2.1 n P j s.1 C A (hNF n P hP hs) (hJ.1 hs).1 hw hc hA, rfl⟩,
        fun h => absurd (hs.symm.trans h) (by decide)⟩
  · obtain ⟨s1, s2⟩ := s
    have := Combine.size_pair_le s1 s2
    cases hs : sel P
    · obtain ⟨h2, he⟩ := hJ.2 hs
      change s1 = dS at he
      rw [he] at this ⊢
      have h3 := pair_le_two_pow (e := Enc.size dS) (d := Enc.size dS + Enc.size dT)
        (hG'.2.2.1 n P j s2 (hNG n P hP hs) h2) (by omega) (hL n)
      omega
    · obtain ⟨h1, he⟩ := hJ.1 hs
      change s2 = dT at he
      rw [he] at this ⊢
      exact this.trans (pair_le_two_pow (hF'.2.2.1 n P j s1 (hNF n P hP hs) h1) (by omega)
        (hL n))
  · show Enc.size (if sel P then F.finish (P, s.1) else G.finish (P, s.2)) ≤ _
    cases hs : sel P
    · rw [if_neg (by decide)]; exact hG.2.2.2.1 n P j s.2 (hNG n P hP hs) (hJ.2 hs).1
    · rw [if_pos rfl]; exact hF.2.2.2.1 n P j s.1 (hNF n P hP hs) (hJ.1 hs).1
  · show Enc.size (if sel P then F.finish (P, s.1) else G.finish (P, s.2)) ≤ _
    cases hs : sel P
    · rw [if_neg (by decide)]
      exact (hG'.2.2.2.2 n P j s.2 (hNG n P hP hs) (hJ.2 hs).1).trans
        (StateBoundsX.two_pow_mono hK _)
    · rw [if_pos rfl]
      exact (hF'.2.2.2.2 n P j s.1 (hNF n P hP hs) (hJ.1 hs).1).trans
        (StateBoundsX.two_pow_mono hK _)

/-- **Two carriers side by side**, with one node predicate. -/
theorem pairIte {S T : Type} [Enc S] [Enc T] (sel : RawMasterSI → Bool) {F : MasterOps S}
    {G : MasterOps T} (dS : S) (dT : T) {K K' : ℕ} {R : RawMasterSI → Prop}
    {J1 : StInv S} {J2 : StInv T} (hF : StateInvXR a b K F R J1) (hG : StateInvXR a b K' G R J2) :
    StateInvXR a b (K + K' + (Enc.size dS + Enc.size dT) + 1)
      (MasterOps.pairIte sel F G dS dT) R (pairJ sel dS dT J1 J2) :=
  pairIteR sel dS dT hF hG (fun _ h _ => h) (fun _ h _ => h)

end StateInvXR

end Explicit
