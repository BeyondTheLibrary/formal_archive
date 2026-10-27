/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the phase rules of `Algo.PhaseMatch` with a condition at every step.
-/
import Workspace.Algo.TopMasterHintedL57
import Workspace.Algo.AggNodeCertRun

/-!
# Phases with a condition at every step

`Algo.LoopMatchS` (`Workspace/Algo/TopMasterHintedL57.lean`) is `Algo.LoopMatch` with a
condition `C j s J` at every call, on the index, the fold state and the child.  The hint
routine of lines 5–7 reads the fold state, so the condition cannot always be proved from the
child alone (`Algo.LoopMatch.toS`): at some steps it needs to know which state the fold is in.
That is known phase by phase.  This file gives the phase rules of `Workspace/Algo/PhaseMatch.lean`
with the condition carried along:

* `Algo.LoopMatchKS`, `Algo.PhaseMatchS`: `Algo.LoopMatchK` and `Algo.PhaseMatch` with the
  condition at each call;
* `Algo.phaseMatchS_bind`, `Algo.loopMatchS_of_phaseMatchS`: the bind rule and the phase that
  ends the round;
* `Algo.PhaseMatch.toS`: a phase all of whose calls have a property `V`, when `V` gives the
  condition at every state;
* `Algo.phaseMatchS_sim`: a phase of a round `R` read on a round `M` that simulates it
  (`Algo.aggnPhaseMatch_sim`), with the condition proved from the simulation relation, which
  records the state `M` is in.
-/

namespace Algo

open Babai

section MatchKS
variable {ι ω α β Ω A : Type} [Fintype Ω] [DecidableEq Ω]

/-- `Algo.LoopMatchK` with a condition `C j s J` at every call. -/
inductive LoopMatchKS (R : Round ι ω α) (C : ℕ → ω → ι → Prop) (decI : ι → SIInstance Ω A)
    (decA : α → Set (Equiv.Perm Ω)) (I : ι) :
    ℕ → ℕ → ω → SIReduction Ω A β → (β → ℕ → ℕ → ω → Prop) → Prop where
  | done (w j : ℕ) (s : ω) (b : β) (Q : β → ℕ → ℕ → ω → Prop) (hq : Q b w j s) :
      LoopMatchKS R C decI decA I w j s (.done b) Q
  | call (w j : ℕ) (s : ω) (J : ι) (k : Set (Equiv.Perm Ω) → SIReduction Ω A β)
      (Q : β → ℕ → ℕ → ω → Prop) (hc : R.child (I, j, s) = some J) (hC : C j s J)
      (hnext : ∀ a : α, decA a = (decI J).answer →
        LoopMatchKS R C decI decA I w (j + 1) (R.combine (I, j, s, a)) (k (decI J).answer) Q) :
      LoopMatchKS R C decI decA I (w + 1) j s (.call (decI J) k) Q

/-- `Algo.PhaseMatch` with a condition at every call. -/
def PhaseMatchS (R : Round ι ω α) (C : ℕ → ω → ι → Prop) (decI : ι → SIInstance Ω A)
    (decA : α → Set (Equiv.Perm Ω)) (I : ι) (c j : ℕ) (s : ω) (T : SIReduction Ω A β)
    (P : β → ℕ → ω → Prop) : Prop :=
  ∀ r : ℕ, LoopMatchKS R C decI decA I (c + r) j s T (fun b w' j' s' => r ≤ w' ∧ P b j' s')

variable {R : Round ι ω α} {C : ℕ → ω → ι → Prop} {decI : ι → SIInstance Ω A}
  {decA : α → Set (Equiv.Perm Ω)} {I : ι}

theorem loopMatchKS_weaken {Q Q' : β → ℕ → ℕ → ω → Prop} (d : ℕ)
    (hQ : ∀ b w' j' s', Q b w' j' s' → Q' b (w' + d) j' s') :
    ∀ {w j : ℕ} {s : ω} {T : SIReduction Ω A β},
      LoopMatchKS R C decI decA I w j s T Q → LoopMatchKS R C decI decA I (w + d) j s T Q' := by
  intro w j s T h
  induction h with
  | done w j s b Q hq => exact .done (w + d) j s b Q' (hQ b w j s hq)
  | call w j s J k Q hc hC hnext ih =>
    rw [show w + 1 + d = w + d + 1 by omega]
    exact .call (w + d) j s J k Q' hc hC fun a ha => ih a ha hQ

theorem loopMatchKS_mono_Q {Q Q' : β → ℕ → ℕ → ω → Prop}
    (hQ : ∀ b w' j' s', Q b w' j' s' → Q' b w' j' s') {w j : ℕ} {s : ω}
    {T : SIReduction Ω A β} (h : LoopMatchKS R C decI decA I w j s T Q) :
    LoopMatchKS R C decI decA I w j s T Q' := by
  have := loopMatchKS_weaken (R := R) (C := C) (decI := decI) (decA := decA) (I := I) (Q := Q)
    (Q' := Q') 0 (fun b w' j' s' hb => by simpa using hQ b w' j' s' hb) h
  simpa using this

theorem loopMatchKS_mono_C {C' : ℕ → ω → ι → Prop} (hCC : ∀ j s J, C j s J → C' j s J)
    {Q : β → ℕ → ℕ → ω → Prop} :
    ∀ {w j : ℕ} {s : ω} {T : SIReduction Ω A β},
      LoopMatchKS R C decI decA I w j s T Q → LoopMatchKS R C' decI decA I w j s T Q := by
  intro w j s T h
  induction h with
  | done w j s b Q hq => exact .done w j s b Q hq
  | call w j s J k Q hc hC _ ih => exact .call w j s J k Q hc (hCC j s J hC) ih

/-- The bind rule into a match that ends the round. -/
theorem loopMatchS_bind {Q : β → ℕ → ℕ → ω → Prop}
    {k : β → SIReduction Ω A (Set (Equiv.Perm Ω))}
    (hk : ∀ (b : β) (w' j' : ℕ) (s' : ω), Q b w' j' s' →
      LoopMatchS R C decI decA I w' j' s' (k b)) :
    ∀ {w j : ℕ} {s : ω} {T : SIReduction Ω A β},
      LoopMatchKS R C decI decA I w j s T Q → LoopMatchS R C decI decA I w j s (T.bind k) := by
  intro w j s T h
  induction h with
  | done w j s b Q hq => exact hk b w j s hq
  | call w j s J k' Q hc hC hnext ih =>
    exact LoopMatchS.call w j s J (fun a => (k' a).bind k) hc hC fun a ha => ih a ha hk

theorem loopMatchKS_bind {γ : Type} {Q : β → ℕ → ℕ → ω → Prop} {Q' : γ → ℕ → ℕ → ω → Prop}
    {k : β → SIReduction Ω A γ}
    (hk : ∀ (b : β) (w' j' : ℕ) (s' : ω), Q b w' j' s' →
      LoopMatchKS R C decI decA I w' j' s' (k b) Q') :
    ∀ {w j : ℕ} {s : ω} {T : SIReduction Ω A β},
      LoopMatchKS R C decI decA I w j s T Q →
        LoopMatchKS R C decI decA I w j s (T.bind k) Q' := by
  intro w j s T h
  induction h with
  | done w j s b Q hq => exact hk b w j s hq
  | call w j s J k' Q hc hC hnext ih =>
    exact LoopMatchKS.call w j s J (fun a => (k' a).bind k) Q' hc hC fun a ha => ih a ha hk

theorem phaseMatchS_mono {P : β → ℕ → ω → Prop} {c c' j : ℕ} {s : ω}
    {T : SIReduction Ω A β} (h : PhaseMatchS R C decI decA I c j s T P) (hc : c ≤ c') :
    PhaseMatchS R C decI decA I c' j s T P := by
  intro r
  have he : c' + r = c + ((c' - c) + r) := by omega
  rw [he]
  exact loopMatchKS_mono_Q (fun b w' j' s' hb => ⟨by omega, hb.2⟩) (h ((c' - c) + r))

theorem phaseMatchS_weaken {P P' : β → ℕ → ω → Prop} {c j : ℕ} {s : ω}
    {T : SIReduction Ω A β} (h : PhaseMatchS R C decI decA I c j s T P)
    (hP : ∀ b j' s', P b j' s' → P' b j' s') : PhaseMatchS R C decI decA I c j s T P' :=
  fun r => loopMatchKS_mono_Q (fun b _w' j' s' hb => ⟨hb.1, hP b j' s' hb.2⟩) (h r)

theorem phaseMatchS_mono_C {C' : ℕ → ω → ι → Prop} (hCC : ∀ j s J, C j s J → C' j s J)
    {P : β → ℕ → ω → Prop} {c j : ℕ} {s : ω} {T : SIReduction Ω A β}
    (h : PhaseMatchS R C decI decA I c j s T P) : PhaseMatchS R C' decI decA I c j s T P :=
  fun r => loopMatchKS_mono_C hCC (h r)

/-- **Two phases one after the other**, with the condition at every step. -/
theorem phaseMatchS_bind {γ : Type} {P : β → ℕ → ω → Prop} {P' : γ → ℕ → ω → Prop}
    {c₁ c₂ j : ℕ} {s : ω} {T : SIReduction Ω A β} {k : β → SIReduction Ω A γ}
    (h : PhaseMatchS R C decI decA I c₁ j s T P)
    (hk : ∀ (b : β) (j' : ℕ) (s' : ω), P b j' s' →
      PhaseMatchS R C decI decA I c₂ j' s' (k b) P') :
    PhaseMatchS R C decI decA I (c₁ + c₂) j s (T.bind k) P' := by
  intro r
  have he : c₁ + c₂ + r = c₁ + (c₂ + r) := by omega
  rw [he]
  refine loopMatchKS_bind (Q := fun b w' j' s' => c₂ + r ≤ w' ∧ P b j' s') ?_ (h (c₂ + r))
  rintro b w' j' s' ⟨hw, hp⟩
  have he' : w' = c₂ + (w' - c₂) := by omega
  rw [he']
  exact loopMatchKS_mono_Q (fun b' w'' j'' s'' hb => ⟨by omega, hb.2⟩) (hk b j' s' hp (w' - c₂))

/-- **A phase that ends the round**, with the condition at every step. -/
theorem loopMatchS_of_phaseMatchS {P : Set (Equiv.Perm Ω) → ℕ → ω → Prop} {c j w : ℕ} {s : ω}
    {T : SIReduction Ω A (Set (Equiv.Perm Ω))} (h : PhaseMatchS R C decI decA I c j s T P)
    (hfin : ∀ (b : Set (Equiv.Perm Ω)) (j' : ℕ) (s' : ω), P b j' s' →
      R.child (I, j', s') = none ∧ decA (R.finish (I, s')) = b)
    (hw : c ≤ w) : LoopMatchS R C decI decA I w j s T := by
  have hb := loopMatchS_bind (k := fun b => (.done b : SIReduction Ω A (Set (Equiv.Perm Ω))))
    (Q := fun b w' j' s' => w - c ≤ w' ∧ P b j' s')
    (fun b w' j' s' hb => LoopMatchS.done w' j' s' b (hfin b j' s' hb.2).1
      (hfin b j' s' hb.2).2) (h (w - c))
  rw [bind_done] at hb
  have he : c + (w - c) = w := by omega
  rw [he] at hb
  exact hb

/-- `Algo.LoopMatchK` gives `Algo.LoopMatchKS` when the condition holds at every step whose
call has the property `V`, and every call of the tree has `V`. -/
theorem LoopMatchK.toS (V : SIInstance Ω A → Prop)
    (hC : ∀ j s J, R.child (I, j, s) = some J → V (decI J) → C j s J)
    {Q : β → ℕ → ℕ → ω → Prop} :
    ∀ {w j : ℕ} {s : ω} {T : SIReduction Ω A β},
      LoopMatchK R decI decA I w j s T Q → (∀ K ∈ T.calls, V K) →
        LoopMatchKS R C decI decA I w j s T Q := by
  intro w j s T h
  induction h with
  | done w j s b Q hq => exact fun _ => .done w j s b Q hq
  | call w j s J k Q hc _ ih =>
    intro hV
    have hvJ : V (decI J) := hV _ (by simp [SIReduction.calls])
    refine .call w j s J k Q hc (hC j s J hc hvJ) fun a ha => ih a ha fun K hK => ?_
    apply hV K
    simp only [SIReduction.calls, List.mem_cons]
    right
    exact hK

/-- `Algo.PhaseMatch` gives `Algo.PhaseMatchS` when the condition holds at every step whose
call has the property `V`, and every call of the phase has `V`. -/
theorem PhaseMatch.toS (V : SIInstance Ω A → Prop)
    (hC : ∀ j s J, R.child (I, j, s) = some J → V (decI J) → C j s J)
    {P : β → ℕ → ω → Prop} {c j : ℕ} {s : ω} {T : SIReduction Ω A β}
    (h : PhaseMatch R decI decA I c j s T P) (hV : ∀ K ∈ T.calls, V K) :
    PhaseMatchS R C decI decA I c j s T P :=
  fun r => LoopMatchK.toS V hC (h r) hV

/-- **A match with a condition at every step makes at most its budget of calls**, when the
answer of every call of the tree has a raw form (as in `Algo.LoopMatch.calls_length_le`, with
the oracle asked only on the calls of the tree). -/
theorem LoopMatchS.calls_length_le :
    ∀ {w j : ℕ} {s : ω} {T : SIReduction Ω A (Set (Equiv.Perm Ω))},
      LoopMatchS R C decI decA I w j s T → (∀ K ∈ T.calls, ∃ a : α, decA a = K.answer) →
        T.calls.length ≤ w := by
  intro w j s T h
  induction h with
  | done => simp
  | call w j s J k hc hC hnext ih =>
    intro hrec
    rw [SIReduction.calls_call] at hrec
    obtain ⟨a, ha⟩ := hrec _ List.mem_cons_self
    rw [SIReduction.calls_call, List.length_cons]
    exact Nat.succ_le_succ (ih a ha fun K hK => hrec K (List.mem_cons_of_mem _ hK))

end MatchKS

section Sim

variable {ι ω ι' ω' α β Ω A : Type} [Fintype Ω] [DecidableEq Ω]
  {R : Round ι ω α} {M : Round ι' ω' α}
  {decI : ι → SIInstance Ω A} {decI' : ι' → SIInstance Ω A}
  {decA : α → Set (Equiv.Perm Ω)} {I : ι} {I' : ι'} {CM : ℕ → ω' → ι' → Prop}

/-- `Algo.aggnLoopMatchK_sim` with the condition of `M` at every step, proved from the
simulation relation and a property `V` of every call. -/
theorem loopMatchKS_sim (V : SIInstance Ω A → Prop)
    (Rel : ℕ → ω → ℕ → ω' → Prop)
    (hc : ∀ j s k t, Rel j s k t → ∀ J, R.child (I, j, s) = some J → V (decI J) →
      ∃ J', M.child (I', k, t) = some J' ∧ decI' J' = decI J ∧ CM k t J' ∧
        ∀ a, Rel (j + 1) (R.combine (I, j, s, a)) (k + 1) (M.combine (I', k, t, a)))
    {w j : ℕ} {s : ω} {S : SIReduction Ω A β}
    {Q : β → ℕ → ℕ → ω → Prop} (h : LoopMatchK R decI decA I w j s S Q) :
    (∀ K ∈ S.calls, V K) → ∀ k t, Rel j s k t → LoopMatchKS M CM decI' decA I' w k t S
      (fun b w' k' t' => ∃ j' s', Q b w' j' s' ∧ Rel j' s' k' t') := by
  induction h with
  | done w j s b Q hQ =>
    intro _ k t hr
    exact .done w k t b _ ⟨j, s, hQ, hr⟩
  | call w j s J cont Q hJ hn ih =>
    intro hV k t hr
    have hvJ : V (decI J) := hV _ (by simp [SIReduction.calls])
    obtain ⟨J', hc', hd, hCM, hnext⟩ := hc j s k t hr J hJ hvJ
    have hh := LoopMatchKS.call (R := M) (C := CM) (decI := decI') (decA := decA) (I := I')
      w k t J' cont (fun b w' k' t' => ∃ j' s', Q b w' j' s' ∧ Rel j' s' k' t') hc' hCM
      (fun a ha => by
        rw [hd] at ha ⊢
        refine ih a ha (fun K hK => hV K ?_) (k + 1) _ (hnext a)
        simp only [SIReduction.calls, List.mem_cons]
        exact Or.inr hK)
    simpa only [hd] using hh

/-- `Algo.aggnPhaseMatch_sim` with the condition of `M` at every step. -/
theorem phaseMatchS_sim (V : SIInstance Ω A → Prop)
    (Rel : ℕ → ω → ℕ → ω' → Prop)
    (hc : ∀ j s k t, Rel j s k t → ∀ J, R.child (I, j, s) = some J → V (decI J) →
      ∃ J', M.child (I', k, t) = some J' ∧ decI' J' = decI J ∧ CM k t J' ∧
        ∀ a, Rel (j + 1) (R.combine (I, j, s, a)) (k + 1) (M.combine (I', k, t, a)))
    {c j k : ℕ} {s : ω} {t : ω'} {S : SIReduction Ω A β}
    {Q : β → ℕ → ω → Prop} (h : PhaseMatch R decI decA I c j s S Q)
    (hV : ∀ K ∈ S.calls, V K) (hr : Rel j s k t) :
    PhaseMatchS M CM decI' decA I' c k t S
      (fun b k' t' => ∃ j' s', Q b j' s' ∧ Rel j' s' k' t') := by
  intro r
  apply loopMatchKS_mono_Q _ (loopMatchKS_sim V Rel hc (h r) hV k t hr)
  rintro b w' k' t' ⟨j', s', ⟨hw, hq⟩, hr'⟩
  exact ⟨hw, j', s', hq, hr'⟩

end Sim

end Algo
