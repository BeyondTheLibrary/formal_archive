/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the cost data of the master round, kind by kind.
-/
import Workspace.Algo.A15Kinds

/-!
# The cost of a family of kinds

`Workspace/Algo/A15Kinds.lean` builds one `Algo.Round` from a list of kinds.  This file does
the same for `Algo.Round.CostQ` and `Algo.Round.RunCostQ`: a package proves the cost of its
own kind, in the **master** domain size `ground`, and the cost of the master round follows.

## What a kind owes

`Algo.A15.KindCost` asks, of one kind:

* `RAM.PolyFun` of the two projections `proj` and `projω` — reading a tag is cheap;
* `RAM.QuasiFun` of `child`, of `finish`, and of `init` and `combine` *composed with* the
  injection `u` of states.  The composite is what the master round runs, so it is what has to
  be paid for; a kind whose `u` is cheap (it always is: it fills one slot of a product) gets
  this from `RAM.QuasiFun` of its own `init` and `combine`;
* the size clauses of `Algo.Round.CostQ`, restricted to the kind and stated at `ground (e i)`;
* one clause that has no counterpart in `Algo.Round.CostQ`: `u_projω_le`, the fact that
  reading a master state as a state of this kind and putting it back does not make it
  larger.  It is needed because `Algo.Round.CostQ.combine_le` bounds the *master* state `s`,
  while the kind works on `w` with `projω s = some w`, and the two need not be equal — `s`
  may carry junk in the slots of other kinds.

## What the family owes

Three clauses of `Algo.Round.CostQ` are not about any kind and are taken as hypotheses of
`Algo.A15.famCostQ`: `ground x ≤ Enc.size x`, the polynomial bound on a well-formed node, and
the bound on the two defaults `bot` and `botS`.  The defaults are what a routine answers on a
node no kind claims, and bounding them is what makes the routines cheap on junk.

## Main definitions

* `Algo.A15.KindCost` — the cost data of one kind;
* `Algo.A15.famCostQ`, `Algo.A15.famRunCostQ` — the cost data of the master round.

## Main results

* `Algo.A15.quasiFun_dispatch1`, `Algo.A15.quasiFun_dispatch2` — a one- and a two-level
  dispatch on an `Option` tag is a `RAM.QuasiFun`;
* `Algo.A15.quasiFun_famChild`, `quasiFun_famInit`, `quasiFun_famCombine`,
  `quasiFun_famFinish` — the four routines of the master round, by induction on the list.

No axiom, no `sorry`.
-/

namespace Algo.A15

open RAM Babai

variable {N S α : Type} {WF : N → Prop} {ground measure : N → ℕ}

/-! ## Dispatching on an `Option` tag

`RAM.QuasiFun.optionElim` is the one dispatcher the machine layer has.  The two lemmas below
put it in the shape the family routines have: read a tag off the input, and either take a
default or run a routine on the tag and the input.  The two-level form reads a second tag off
the state, with its own default. -/

/-- **A one-level dispatch is a `RAM.QuasiFun`.** -/
theorem quasiFun_dispatch1 {X Y B : Type} [Enc X] [Enc Y] [Enc B] {pb : X → Option B}
    {d : X → Y} {f : B × X → Y} (hpb : PolyFun pb) (hd : QuasiFun d) (hf : QuasiFun f) :
    QuasiFun (fun x : X => (pb x).elim (d x) (fun b => f (b, x))) := by
  have hpair : PolyFun (fun x : X => (pb x, x)) := hpb.pair polyFun_id
  exact (hpair.comp_quasiFun (hd.optionElim hf)).of_eq (fun x => rfl)

/-- **A two-level dispatch is a `RAM.QuasiFun`.** -/
theorem quasiFun_dispatch2 {X Y B C : Type} [Enc X] [Enc Y] [Enc B] [Enc C]
    {pb : X → Option B} {pc : X → Option C} {d₁ d₂ : X → Y} {f : B × C × X → Y}
    (hpb : PolyFun pb) (hpc : PolyFun pc) (hd₁ : QuasiFun d₁) (hd₂ : QuasiFun d₂)
    (hf : QuasiFun f) :
    QuasiFun (fun x : X =>
      (pb x).elim (d₁ x) (fun b => (pc x).elim (d₂ x) (fun c => f (b, c, x)))) := by
  have hinner : QuasiFun (fun q : B × X => (pc q.2).elim (d₂ q.2) (fun c => f (q.1, c, q.2))) := by
    have h1 : QuasiFun (fun q : B × X => d₂ q.2) := polyFun_snd.comp_quasiFun hd₂
    have h2 : QuasiFun (fun z : C × (B × X) => f (z.2.1, z.1, z.2.2)) :=
      (PolyFun.pair (polyFun_snd.comp polyFun_fst)
        (PolyFun.pair polyFun_fst (polyFun_snd.comp polyFun_snd))).comp_quasiFun hf
    have hpair : PolyFun (fun q : B × X => (pc q.2, q)) := (polyFun_snd.comp hpc).pair polyFun_id
    exact (hpair.comp_quasiFun (h1.optionElim h2)).of_eq (fun q => rfl)
  exact quasiFun_dispatch1 hpb hd₁ hinner

/-! ## The cost of one kind -/

/-- **What a kind owes the cost of the master round.**  Every bound is in the master domain
size `ground (e i)`, which is what makes the bounds compose: `ground` does not grow along the
recursion. -/
structure KindCost [Enc N] [Enc S] [Enc α] (bound stateBound widthBound : ℕ → ℕ)
    (k : Kind N S α WF ground measure) : Prop where
  /-- Reading the tag of a node is cheap. -/
  polyFun_proj : PolyFun k.proj
  /-- Reading the tag of a state is cheap. -/
  polyFun_projω : PolyFun k.projω
  /-- The child routine. -/
  quasiFun_child : QuasiFun k.child
  /-- The empty partial answer, as a master state. -/
  quasiFun_init : QuasiFun (fun i : k.ι => k.u (k.init i))
  /-- The fold, as a master state. -/
  quasiFun_combine : QuasiFun (fun q : k.ι × ℕ × k.ω × α => k.u (k.combine q))
  /-- The answer routine. -/
  quasiFun_finish : QuasiFun k.finish
  /-- **Reading a master state and putting it back does not make it larger.**  A master state
  may carry junk in the slots of the other kinds; `u (projω s)` drops that junk. -/
  u_projω_le : ∀ s w, k.projω s = some w → Enc.size (k.u w) ≤ Enc.size s
  /-- The empty partial answer is quasipolynomially small. -/
  init_le : ∀ i, WF (k.e i) → Enc.size (k.u (k.init i)) ≤ stateBound (ground (k.e i))
  /-- The state does not grow along the fold. -/
  combine_le : ∀ i j w a, WF (k.e i) → Enc.size (k.u w) ≤ stateBound (ground (k.e i)) →
    Enc.size a ≤ bound (ground (k.e i)) →
    Enc.size (k.u (k.combine (i, j, w, a))) ≤ stateBound (ground (k.e i))
  /-- The answer of a node is polynomially small. -/
  finish_le : ∀ i w, WF (k.e i) → Enc.size (k.u w) ≤ stateBound (ground (k.e i)) →
    Enc.size (k.finish (i, w)) ≤ bound (ground (k.e i))
  /-- The number of children is quasipolynomially bounded. -/
  width_le : ∀ i, WF (k.e i) → k.width i ≤ widthBound (ground (k.e i))

/-! ## The four routines of the master round

One induction on the list each.  The step is `Algo.A15.quasiFun_dispatch1` or
`quasiFun_dispatch2` with the induction hypothesis as the default. -/

variable [Enc N] [Enc S] [Enc α]

theorem quasiFun_famChild {b sb wb : ℕ → ℕ} (ks : List (Kind N S α WF ground measure))
    (h : ∀ k ∈ ks, KindCost b sb wb k) : QuasiFun (famChild ks) := by
  induction ks with
  | nil => exact (quasiFun_const (α := N × ℕ × S) (none : Option N)).of_eq (fun p => rfl)
  | cons k r ih =>
      have hk := h k (by simp)
      have hrest := ih (fun k' hk' => h k' (by simp [hk']))
      have hf : QuasiFun (fun z : k.ι × k.ω × (N × ℕ × S) =>
          k.child (z.1, z.2.2.2.1, z.2.1)) :=
        (PolyFun.pair polyFun_fst
          (PolyFun.pair
            (polyFun_snd.comp (polyFun_snd.comp (polyFun_snd.comp polyFun_fst)))
            (polyFun_snd.comp polyFun_fst))).comp_quasiFun hk.quasiFun_child
      have hd := quasiFun_dispatch2 (X := N × ℕ × S) (Y := Option N)
        (pb := fun p => k.proj p.1) (pc := fun p => k.projω p.2.2)
        (d₁ := famChild r) (d₂ := fun _ => none)
        (f := fun z : k.ι × k.ω × (N × ℕ × S) => k.child (z.1, z.2.2.2.1, z.2.1))
        (polyFun_fst.comp hk.polyFun_proj)
        ((polyFun_snd.comp polyFun_snd).comp hk.polyFun_projω)
        hrest (quasiFun_const _) hf
      refine hd.of_eq (fun p => ?_)
      obtain ⟨x, j, s⟩ := p
      rw [famChild_cons]

theorem quasiFun_famInit {b sb wb : ℕ → ℕ} (botS : S)
    (ks : List (Kind N S α WF ground measure)) (h : ∀ k ∈ ks, KindCost b sb wb k) :
    QuasiFun (famInit botS ks) := by
  induction ks with
  | nil => exact (quasiFun_const (α := N) botS).of_eq (fun x => rfl)
  | cons k r ih =>
      have hk := h k (by simp)
      have hrest := ih (fun k' hk' => h k' (by simp [hk']))
      have hd := quasiFun_dispatch1 (X := N) (Y := S) (pb := k.proj)
        (d := famInit botS r) (f := fun q : k.ι × N => k.u (k.init q.1))
        hk.polyFun_proj hrest (polyFun_fst.comp_quasiFun hk.quasiFun_init)
      refine hd.of_eq (fun x => ?_)
      rw [famInit_cons]

theorem quasiFun_famCombine {b sb wb : ℕ → ℕ} (ks : List (Kind N S α WF ground measure))
    (h : ∀ k ∈ ks, KindCost b sb wb k) : QuasiFun (famCombine ks) := by
  induction ks with
  | nil =>
      exact ((polyFun_snd.comp (polyFun_snd.comp polyFun_fst) :
        PolyFun (fun p : N × ℕ × S × α => p.2.2.1)).quasiFun).of_eq (fun p => rfl)
  | cons k r ih =>
      have hk := h k (by simp)
      have hrest := ih (fun k' hk' => h k' (by simp [hk']))
      have hf : QuasiFun (fun z : k.ι × k.ω × (N × ℕ × S × α) =>
          k.u (k.combine (z.1, z.2.2.2.1, z.2.1, z.2.2.2.2.2))) :=
        (PolyFun.pair polyFun_fst
          (PolyFun.pair
            (polyFun_snd.comp (polyFun_snd.comp (polyFun_snd.comp polyFun_fst)))
            (PolyFun.pair (polyFun_snd.comp polyFun_fst)
              (polyFun_snd.comp (polyFun_snd.comp (polyFun_snd.comp
                (polyFun_snd.comp polyFun_snd))))))).comp_quasiFun hk.quasiFun_combine
      have hd := quasiFun_dispatch2 (X := N × ℕ × S × α) (Y := S)
        (pb := fun p => k.proj p.1) (pc := fun p => k.projω p.2.2.1)
        (d₁ := famCombine r) (d₂ := fun p => p.2.2.1)
        (f := fun z : k.ι × k.ω × (N × ℕ × S × α) =>
          k.u (k.combine (z.1, z.2.2.2.1, z.2.1, z.2.2.2.2.2)))
        (polyFun_fst.comp hk.polyFun_proj)
        ((polyFun_snd.comp (polyFun_snd.comp polyFun_fst)).comp hk.polyFun_projω)
        hrest (polyFun_snd.comp (polyFun_snd.comp polyFun_fst) :
          PolyFun (fun p : N × ℕ × S × α => p.2.2.1)).quasiFun hf
      refine hd.of_eq (fun p => ?_)
      obtain ⟨x, j, s, a⟩ := p
      rw [famCombine_cons]

theorem quasiFun_famFinish {b sb wb : ℕ → ℕ} (bot : α)
    (ks : List (Kind N S α WF ground measure)) (h : ∀ k ∈ ks, KindCost b sb wb k) :
    QuasiFun (famFinish bot ks) := by
  induction ks with
  | nil => exact (quasiFun_const (α := N × S) bot).of_eq (fun p => rfl)
  | cons k r ih =>
      have hk := h k (by simp)
      have hrest := ih (fun k' hk' => h k' (by simp [hk']))
      have hf : QuasiFun (fun z : k.ι × k.ω × (N × S) => k.finish (z.1, z.2.1)) :=
        (PolyFun.pair polyFun_fst (polyFun_snd.comp polyFun_fst)).comp_quasiFun
          hk.quasiFun_finish
      have hd := quasiFun_dispatch2 (X := N × S) (Y := α)
        (pb := fun p => k.proj p.1) (pc := fun p => k.projω p.2)
        (d₁ := famFinish bot r) (d₂ := fun _ => bot)
        (f := fun z : k.ι × k.ω × (N × S) => k.finish (z.1, z.2.1))
        (polyFun_fst.comp hk.polyFun_proj) (polyFun_snd.comp hk.polyFun_projω)
        hrest (quasiFun_const _) hf
      refine hd.of_eq (fun p => ?_)
      obtain ⟨x, s⟩ := p
      rw [famFinish_cons]

/-! ## The size clauses

The same four inductions, on sizes instead of running times.  At a kind that claims the node
the kind's own clause applies, after `eq_e_of_proj` has identified the node with `e i`; at the
end of the list the default answers, which is where the two hypotheses on `bot` and `botS`
are used. -/

theorem size_famInit_le {b sb wb : ℕ → ℕ} (botS : S) (hbotS : ∀ m, Enc.size botS ≤ sb m)
    (ks : List (Kind N S α WF ground measure)) (h : ∀ k ∈ ks, KindCost b sb wb k)
    (x : N) (hx : WF x) : Enc.size (famInit botS ks x) ≤ sb (ground x) := by
  induction ks with
  | nil => exact hbotS _
  | cons k r ih =>
      rw [famInit_cons]
      cases hp : k.proj x with
      | none => exact ih (fun k' hk' => h k' (by simp [hk']))
      | some i =>
          have hk := h k (by simp)
          have hxe : x = k.e i := k.eq_e_of_proj x i hx hp
          rw [hxe]
          exact hk.init_le i (hxe ▸ hx)

theorem size_famCombine_le {b sb wb : ℕ → ℕ} (ks : List (Kind N S α WF ground measure))
    (h : ∀ k ∈ ks, KindCost b sb wb k) (x : N) (j : ℕ) (s : S) (a : α) (hx : WF x)
    (hs : Enc.size s ≤ sb (ground x)) (ha : Enc.size a ≤ b (ground x)) :
    Enc.size (famCombine ks (x, j, s, a)) ≤ sb (ground x) := by
  induction ks with
  | nil => exact hs
  | cons k r ih =>
      rw [famCombine_cons]
      cases hp : k.proj x with
      | none => exact ih (fun k' hk' => h k' (by simp [hk']))
      | some i =>
          have hk := h k (by simp)
          have hxe : x = k.e i := k.eq_e_of_proj x i hx hp
          cases hw : k.projω s with
          | none => exact hs
          | some w =>
              have huw : Enc.size (k.u w) ≤ Enc.size s := hk.u_projω_le s w hw
              rw [hxe] at hs ha ⊢
              exact hk.combine_le i j w a (hxe ▸ hx) (le_trans huw hs) ha

theorem size_famFinish_le {b sb wb : ℕ → ℕ} (bot : α) (hbot : ∀ m, Enc.size bot ≤ b m)
    (ks : List (Kind N S α WF ground measure)) (h : ∀ k ∈ ks, KindCost b sb wb k)
    (x : N) (s : S) (hx : WF x) (hs : Enc.size s ≤ sb (ground x)) :
    Enc.size (famFinish bot ks (x, s)) ≤ b (ground x) := by
  induction ks with
  | nil => exact hbot _
  | cons k r ih =>
      rw [famFinish_cons]
      cases hp : k.proj x with
      | none => exact ih (fun k' hk' => h k' (by simp [hk']))
      | some i =>
          have hk := h k (by simp)
          have hxe : x = k.e i := k.eq_e_of_proj x i hx hp
          cases hw : k.projω s with
          | none => exact hbot _
          | some w =>
              have huw : Enc.size (k.u w) ≤ Enc.size s := hk.u_projω_le s w hw
              rw [hxe] at hs ⊢
              exact hk.finish_le i w (hxe ▸ hx) (le_trans huw hs)

theorem famWidth_le {b sb wb : ℕ → ℕ} (ks : List (Kind N S α WF ground measure))
    (h : ∀ k ∈ ks, KindCost b sb wb k) (x : N) (hx : WF x) :
    famWidth ks x ≤ wb (ground x) := by
  induction ks with
  | nil => exact Nat.zero_le _
  | cons k r ih =>
      rw [famWidth_cons]
      cases hp : k.proj x with
      | none => exact ih (fun k' hk' => h k' (by simp [hk']))
      | some i =>
          have hk := h k (by simp)
          have hxe : x = k.e i := k.eq_e_of_proj x i hx hp
          rw [hxe]
          exact hk.width_le i (hxe ▸ hx)

/-! ## The cost data of the master round -/

/-- **The cost data of a family of kinds.**  The three hypotheses that are not about any kind
are `hground`, `hsize` and the two bounds on the defaults. -/
def famCostQ (bot : α) (botS : S) (ks : List (Kind N S α WF ground measure))
    (bound stateBound widthBound : ℕ → ℕ)
    (hb : PolyBound bound) (hbm : Monotone bound)
    (hsb : QuasiPolyBound stateBound) (hsbm : Monotone stateBound)
    (hwb : QuasiPolyBound widthBound)
    (hground : ∀ x : N, ground x ≤ Enc.size x)
    (hsize : ∀ x : N, WF x → Enc.size x ≤ bound (ground x))
    (hbot : ∀ m, Enc.size bot ≤ bound m) (hbotS : ∀ m, Enc.size botS ≤ stateBound m)
    (h : ∀ k ∈ ks, KindCost bound stateBound widthBound k) :
    Round.CostQ (famRound bot botS ks) where
  bound := bound
  polyBound_bound := hb
  mono_bound := hbm
  stateBound := stateBound
  quasiPolyBound_stateBound := hsb
  mono_stateBound := hsbm
  widthBound := widthBound
  quasiPolyBound_widthBound := hwb
  quasiFun_child := quasiFun_famChild ks h
  quasiFun_init := quasiFun_famInit botS ks h
  quasiFun_combine := quasiFun_famCombine ks h
  quasiFun_finish := quasiFun_famFinish bot ks h
  ground_le := hground
  size_le := hsize
  init_le := fun I hI => size_famInit_le botS hbotS ks h I hI
  combine_le := fun I j s a hI hs ha => size_famCombine_le ks h I j s a hI hs ha
  finish_le := fun I s hI hs => size_famFinish_le bot hbot ks h I s hI hs
  bot_le := hbot
  width_le := fun I hI => famWidth_le ks h I hI

/-- **The packaging the machine needs.**  The three extra fields of `Algo.Round.RunCostQ` are
about the master node type only, so they are hypotheses, not per-kind data. -/
def famRunCostQ (bot : α) (botS : S) (ks : List (Kind N S α WF ground measure))
    (bound stateBound widthBound : ℕ → ℕ)
    (hb : PolyBound bound) (hbm : Monotone bound)
    (hsb : QuasiPolyBound stateBound) (hsbm : Monotone stateBound)
    (hwb : QuasiPolyBound widthBound)
    (hground : ∀ x : N, ground x ≤ Enc.size x)
    (hsize : ∀ x : N, WF x → Enc.size x ≤ bound (ground x))
    (hbot : ∀ m, Enc.size bot ≤ bound m) (hbotS : ∀ m, Enc.size botS ≤ stateBound m)
    (h : ∀ k ∈ ks, KindCost bound stateBound widthBound k)
    (hgroundFun : PolyFun ground) (wfCheck : N → Bool) (hwfCheck : PolyFun wfCheck)
    (hwfCheck_eq : ∀ x, wfCheck x = true ↔ WF x)
    (measureBound : ℕ → ℕ) (hmb : PolyBound measureBound) (hmbm : Monotone measureBound)
    (hmeasure : ∀ x, WF x → measure x ≤ measureBound (ground x)) :
    Round.RunCostQ (famRound bot botS ks) where
  toCostQ := famCostQ bot botS ks bound stateBound widthBound hb hbm hsb hsbm hwb hground
    hsize hbot hbotS h
  polyFun_ground := hgroundFun
  wfCheck := wfCheck
  polyFun_wfCheck := hwfCheck
  wfCheck_eq_true := hwfCheck_eq
  measureBound := measureBound
  polyBound_measureBound := hmb
  mono_measureBound := hmbm
  measure_le := hmeasure

end Algo.A15
