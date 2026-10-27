/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 15: the Master Algorithm run along a family of choices, one choice per node.
-/
import Workspace.Master.Sec15Value

/-!
# The round of Sec. 15 along a family of choices

`Babai.Theorem_1_1_1_math` holds for every `ch : Babai.Sec15Choices Ω A q923 c923`, that is,
for one choice fixed once for the whole run: line 1 takes the same branch of Procedure
Reduce-to-Johnson at every instance, lines 4c–4d run Procedure Align on the same geometric
data at every instance, and so on.  That is faithful to the paper, which lets the algorithm
pick at each round and proves the bound for whatever it picks.

A machine that carries the recursion out picks per **raw node**, not per typed instance.
The minimal block system it finds depends on the generator list it was handed, and two raw
nodes with different generator lists can decode to the same String Isomorphism instance.  So
the machine's picks are a function `κ' → Sec15Choices Ω A q923 c923` on the raw nodes and
cannot in general be collapsed to one `ch`.

This file reindexes the round along such a family.  The point is that the choice enters only
`Babai.MasterStep.step` and `Babai.MasterStep.lift`: `inst`, `param`, `roundCost` and `top`
of `Babai.sec15MasterStep Ω A ch` do not mention `ch` at all
(`Babai.sec15MasterStep_inst`, `Babai.sec15MasterStep_param`,
`Babai.sec15MasterStep_roundCost`, `Babai.sec15MasterStep_top`).  So a family of choices,
with a map `p` from raw nodes to typed hinted instances and the machine's own `lift'` and
`top'`, gives a `Babai.MasterStep Ω A κ'` whose every field is inherited pointwise
(`Babai.masterStepOfFamily`), and Theorem 1.1.1 holds for it with the same constant
(`Babai.Theorem_1_1_1_math_family`).

Taking `κ'` to be the typed hinted instances and the family to be constant gives the old
round back, so nothing has been generalized away (`Babai.masterStepOfFamily_const`).
-/

universe u v w

namespace Babai

open scoped Classical

/-! ### The fields of the round that do not depend on the choice -/

section Independent

variable {Ω : Type u} {A : Type v} [Fintype Ω] [DecidableEq Ω] [Fintype A] [DecidableEq A]

/-- §15: the instance underneath a hinted instance does not depend on the choices the round
makes.  It is `Babai.HintedInstance.inst`, read off the hinted instance alone. -/
theorem sec15MasterStep_inst (ch : Sec15Choices Ω A q923 c923) :
    (sec15MasterStep Ω A ch).inst = HintedInstance.inst := rfl

/-- §15, line 2: the Johnson parameter `m` does not depend on the choices the round makes.
It is `Babai.param`, read off the hint the instance carries. -/
theorem sec15MasterStep_param (ch : Sec15Choices Ω A q923 c923) :
    (sec15MasterStep Ω A ch).param = (param : HintedInstance Ω A → ℕ) := rfl

/-- §15: the number of instances one round produces does not depend on the choices the round
makes.  It is `Babai.sec15RoundCost`, the sum of the costs of the six branches that make
calls. -/
theorem sec15MasterStep_roundCost (ch : Sec15Choices Ω A q923 c923) :
    (sec15MasterStep Ω A ch).roundCost = sec15RoundCost q923 c923 := rfl

/-- §15: the instance Theorem 1.1.1 starts from — the group `G` with the full window and no
hint — does not depend on the choices the round makes. -/
theorem sec15MasterStep_top (ch : Sec15Choices Ω A q923 c923) :
    (sec15MasterStep Ω A ch).top = fun I => (⟨I, none⟩ : HintedInstance Ω A) := rfl

end Independent

/-! ### Transferring the two forms of progress along a reindexing

Both `Babai.MakesProgress` and `Babai.IsChainRuleRound` look only at the window size and the
Johnson parameter of the instances involved.  So they transfer along any reindexing that
keeps those two numbers, which is what a family of choices does: a node and the hinted
instance it decodes to have the same window and the same Johnson parameter. -/

section Transfer

variable {ι : Type*} {κ : Type*}

/-- §11.4, recurrences (ii) and (v): the progress of one shrinking call depends on the two
instances only through their window size and their Johnson parameter. -/
theorem makesProgress_congr {win param : ι → ℕ} {win' param' : κ → ℕ}
    {i j : ι} {i' j' : κ} (hi : win' i' = win i) (hj : win' j' = win j)
    (pi : param' i' = param i) (pj : param' j' = param j)
    (h : MakesProgress win param i j) : MakesProgress win' param' i' j' := by
  rw [MakesProgress, hi, hj, pi, pj]
  exact h

/-- §11.4, recurrence (i): a Chain Rule round stays one when both the instance and the list
of its calls are reindexed by maps that keep the window size and the Johnson parameter.  The
two lists are the image of one and the same list of String Isomorphism instances, which is
what the two `∀ a ∈ L` hypotheses pair up. -/
theorem isChainRuleRound_congr_map {α : Type*} {win param : ι → ℕ} {win' param' : κ → ℕ}
    {i : ι} {i' : κ} (L : List α) (f : α → ι) (g : α → κ)
    (hi : win' i' = win i) (pi : param' i' = param i)
    (hw : ∀ a ∈ L, win' (g a) = win (f a)) (hp : ∀ a ∈ L, param' (g a) = param (f a))
    (h : IsChainRuleRound win param i (L.map f)) :
    IsChainRuleRound win' param' i' (L.map g) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by rw [hi]; exact h1, ?_, ?_⟩
  · intro j hj
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hj
    have hmem := h2 (f a) (List.mem_map_of_mem ha)
    rw [hw a ha, hp a ha, hi, pi]
    exact hmem
  · rw [List.map_map] at h3 ⊢
    rw [hi, show (L.map (win' ∘ g)).sum = (L.map (win ∘ f)).sum from
      congrArg List.sum (List.map_congr_left fun a ha => hw a ha)]
    exact h3

end Transfer

/-! ### The round along a family of choices -/

section Family

variable {Ω : Type u} {A : Type v} [Fintype Ω] [DecidableEq Ω] [Fintype A] [DecidableEq A]
  {κ' : Type w}

/-- §15, **one round of the Master Algorithm along a family of choices**.

`κ'` is the index type of the nodes the machine really has — a raw node, say.  `chOf r` is
what the machine picked at the node `r`, `p r` the typed hinted instance the node decodes
to, `lift' r J` the node the machine builds for the call `J`, and `top' I` the node it starts
from.

The two hypotheses say that decoding commutes with building children and with starting: the
node the machine attaches to a call decodes to the hinted instance the round of `chOf r`
attaches to that call, and the node the machine starts from decodes to the hinted instance
the round starts from.  The first is asked only for the calls the round really makes, which
is all `Babai.MasterStep.lift_inst` asks as well.

Every field is then inherited pointwise from `Babai.sec15MasterStep Ω A (chOf r)` at `p r`.
That is possible because `inst`, `param`, `roundCost` and `top` of that round do not mention
the choice (`Babai.sec15MasterStep_inst` and the three lemmas beside it), so the four of them
are the same function of `p r` at every node, whatever the node picked. -/
noncomputable def masterStepOfFamily
    (chOf : κ' → Sec15Choices Ω A q923 c923) (p : κ' → HintedInstance Ω A)
    (lift' : κ' → SIInstance Ω A → κ') (top' : SIInstance Ω A → κ')
    (hlift : ∀ (r : κ') (J : SIInstance Ω A),
      J ∈ ((sec15MasterStep Ω A (chOf r)).step (p r)).calls →
      p (lift' r J) = (sec15MasterStep Ω A (chOf r)).lift (p r) J)
    (htop : ∀ I : SIInstance Ω A, p (top' I) = (sec15MasterStep Ω A (chOf (top' I))).top I) :
    MasterStep Ω A κ' where
  inst r := (sec15MasterStep Ω A (chOf r)).inst (p r)
  step r := (sec15MasterStep Ω A (chOf r)).step (p r)
  lift := lift'
  top := top'
  inst_top I := by
    show (sec15MasterStep Ω A (chOf (top' I))).inst (p (top' I)) = I
    rw [htop I]
    exact (sec15MasterStep Ω A (chOf (top' I))).inst_top I
  lift_inst r J hJ := by
    show (sec15MasterStep Ω A (chOf (lift' r J))).inst (p (lift' r J)) = J
    rw [sec15MasterStep_inst, hlift r J hJ, ← sec15MasterStep_inst (chOf r)]
    exact (sec15MasterStep Ω A (chOf r)).lift_inst (p r) J hJ
  param r := (sec15MasterStep Ω A (chOf r)).param (p r)
  roundCost := sec15RoundCost q923 c923
  param_le r := (sec15MasterStep Ω A (chOf r)).param_le (p r)
  calls_isGroupInstance r hg := (sec15MasterStep Ω A (chOf r)).calls_isGroupInstance (p r) hg
  round_correct r hg := (sec15MasterStep Ω A (chOf r)).round_correct (p r) hg
  decreases r hg := by
    -- the window size and the Johnson parameter of a node are read through `p`, and `p`
    -- takes the machine's child to the child of the round of `chOf r`
    have hwin : ∀ J ∈ ((sec15MasterStep Ω A (chOf r)).step (p r)).calls,
        ((sec15MasterStep Ω A (chOf (lift' r J))).inst (p (lift' r J))).windowSize
          = ((sec15MasterStep Ω A (chOf r)).inst
              ((sec15MasterStep Ω A (chOf r)).lift (p r) J)).windowSize := by
      intro J hJ
      rw [sec15MasterStep_inst, hlift r J hJ, ← sec15MasterStep_inst (chOf r)]
    have hpar : ∀ J ∈ ((sec15MasterStep Ω A (chOf r)).step (p r)).calls,
        (sec15MasterStep Ω A (chOf (lift' r J))).param (p (lift' r J))
          = (sec15MasterStep Ω A (chOf r)).param
              ((sec15MasterStep Ω A (chOf r)).lift (p r) J) := by
      intro J hJ
      rw [sec15MasterStep_param, hlift r J hJ, ← sec15MasterStep_param (chOf r)]
    rcases (sec15MasterStep Ω A (chOf r)).decreases (p r) hg with hsh | hchain
    · exact Or.inl fun J hJ =>
        makesProgress_congr (win := fun j => ((sec15MasterStep Ω A (chOf r)).inst j).windowSize)
          (param := (sec15MasterStep Ω A (chOf r)).param)
          rfl (hwin J hJ) rfl (hpar J hJ) (hsh J hJ)
    · exact Or.inr (isChainRuleRound_congr_map
        (win := fun j => ((sec15MasterStep Ω A (chOf r)).inst j).windowSize)
        (param := (sec15MasterStep Ω A (chOf r)).param)
        _ ((sec15MasterStep Ω A (chOf r)).lift (p r)) (lift' r) rfl rfl hwin hpar hchain)
  calls_length_le r hg := by
    have h := (sec15MasterStep Ω A (chOf r)).calls_length_le (p r) hg
    rwa [sec15MasterStep_roundCost] at h

/-- **Theorem 1.1.1** (Sec. 1.1), the mathematical half, for the Master Algorithm of Sec. 15
run along a **family** of choices: one choice per node, not one choice for the whole run.

The statement is `Babai.Theorem_1_1_1_math` word for word, with `Babai.sec15MasterStep Ω A ch`
replaced by `Babai.masterStepOfFamily`.  The constant `c₁` is the same one: it comes from the
quasipolynomial bound on the round cost (`Babai.quasiPolyBound_sec15RoundCost`), and the
round cost of the family is `Babai.sec15RoundCost q923 c923`, the round cost of every member
of the family.  So `c₁` is quantified before the ground set, before the alphabet and before
the family, exactly as in `Babai.Theorem_1_1_1_math`.

This is what a machine layer needs: it may pick a different branch at each node, and the
count of String Isomorphism instances is still at most `exp(30 (log₂ n + 2)^{c₁+2})`.

The first half of the conclusion is the one of `Babai.Theorem_1_1_1_math`: there is at least
one `Babai.Sec15Choices`, so families are not made of nothing. -/
theorem Theorem_1_1_1_math_family :
    ∃ c₁ : ℕ, ∀ (Ω : Type u) [Fintype Ω] [DecidableEq Ω] (A : Type v) [Fintype A]
      [DecidableEq A],
      Nonempty (Sec15Choices Ω A q923 c923) ∧
      ∀ (κ' : Type w) (chOf : κ' → Sec15Choices Ω A q923 c923)
      (p : κ' → HintedInstance Ω A) (lift' : κ' → SIInstance Ω A → κ')
      (top' : SIInstance Ω A → κ')
      (hlift : ∀ (r : κ') (J : SIInstance Ω A),
        J ∈ ((sec15MasterStep Ω A (chOf r)).step (p r)).calls →
        p (lift' r J) = (sec15MasterStep Ω A (chOf r)).lift (p r) J)
      (htop : ∀ I : SIInstance Ω A,
        p (top' I) = (sec15MasterStep Ω A (chOf (top' I))).top I)
      (G : Subgroup (Equiv.Perm Ω)) (x y : Ω → A),
      let M := masterStepOfFamily chOf p lift' top' hlift htop
      let I : SIInstance Ω A := ⟨(G : Set (Equiv.Perm Ω)), Set.univ, x, y⟩
      let i := M.top I
      let f := M.rank i + 1
      M.solve f i = strIso (G : Set (Equiv.Perm Ω)) x y ∧
        M.count f i ≤ 2 ^ (30 * (Nat.log 2 I.windowSize + 2) ^ (c₁ + 2)) := by
  obtain ⟨c₁, hc₁⟩ := quasiPolyBound_sec15RoundCost quasiPolyBound_q923 c923
  refine ⟨c₁, fun Ω _ _ A _ _ => ⟨⟨sec15Choices theorem923Uniform_q923⟩,
    fun κ' chOf p lift' top' hlift htop G x y => ?_⟩⟩
  exact Theorem_1_1_1_math_of_masterStep (masterStepOfFamily chOf p lift' top' hlift htop)
    (sec15RoundCost_mono q923 c923) c₁ hc₁ G x y

/-- §15: **the family is a generalization and not a replacement**.  Taking the nodes to be
the typed hinted instances themselves, the family to be the constant family at `ch`, and the
machine's `lift'` and `top'` to be the round's own, gives back the round
`Babai.sec15MasterStep Ω A ch`, on the nose. -/
theorem masterStepOfFamily_const (ch : Sec15Choices Ω A q923 c923) :
    masterStepOfFamily (κ' := HintedInstance Ω A) (fun _ => ch) id
      (sec15MasterStep Ω A ch).lift (sec15MasterStep Ω A ch).top
      (fun r J _ => rfl) (fun _ => rfl) = sec15MasterStep Ω A ch := rfl

end Family

end Babai
