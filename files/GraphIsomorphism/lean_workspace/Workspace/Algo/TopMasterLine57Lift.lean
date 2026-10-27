import Workspace.Algo.TopMasterWinLift
import Workspace.Algo.TopMasterL57Norm
import Workspace.Algo.AggNodeLine57RAM
import Workspace.Algo.TopMasterHintCarrier
import Workspace.Algo.AggNodeLine57GiantRAM
import Workspace.Algo.AggNodeLine57GiantMatch

/-! # Lines 5–7 of the Master Algorithm on the master carrier
Section 15, lines 5–7: at a hinted node that is not a primitive case, the algorithm runs
Procedure AggregateCertificates on the window `Δ` with test sets of size
`t = 10 + log |Δ|` (`Babai.testSetSize`), and then the Chain Rule of line 5 on the
certificates found, with Cor. 12.0.10 at outcome (2a) (`Algo.aggnL57GRound`). This file puts
that round on the master carrier through the window lift (`Algo.masterWinLiftOps`).

The round runs on the window's data in the window's own size (`Algo.masterL57Ctx`, see
`Workspace/Algo/TopMasterL57Norm.lean`), with the letters of the two strings renamed by one
injective map; the carrier renames the letters of each call back before lifting it
(`Algo.masterL57Read`), so the node's calls are on the node's letters and have the same answers
(`Algo.masterL57Unl_match`).

The round's own width reserves room for every header its states may produce, and for the
giant branch; those reserves (`Algo.aggnL57Cap`, `Algo.aggnL57GCap`) are only analysis bounds.
The carrier runs with a computed width instead: the width of the two phases plus a
quasipolynomial `2 ^ ((log |Δ| + 2) ^ E)` that bounds the reserves (`Algo.aggnL57GCap_quasi`).

The giant branch runs the carrier of Cor. 12.0.10 with constants `u v` for which the nodes it
builds pass their well-formedness test (`Algo.L57GWFOK`); such constants exist for all
`e f` (`Algo.exists_l57GWFOK`), and the carrier uses a fixed choice of them (`Algo.l57UV`).
-/
set_option synthInstance.maxSize 2048
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Pointwise

/-- **The context of lines 5–7 at a hinted node**, in the window's own size
(`Workspace/Algo/TopMasterL57Norm.lean`): the action of `G_Δ` on `0, …, |Δ|-1` and of its
image on `0, …, m-1` (`Algo.masterL57Action`), the two strings on the window with their
letters renamed by one injective map onto `0, …, k-1` (`Algo.masterL57Relabel`), and a list of
length `t = 10 + log |Δ|` (cut at `|Δ|`), which fixes the size of the test sets. -/
def masterL57Ctx (P : RawMasterSI) : AggnPhaseCtx :=
  (masterL57Action P, masterL57Relabel (masterL57Order P, masterL57XW P),
    masterL57Relabel (masterL57Order P, masterL57YW P),
    List.range (min (10 + Nat.log 2 P.1.1.length) P.1.1.length))

/-- The node of the round of lines 5–7 at a hinted node. -/
def masterL57Enter (P : RawMasterSI) : AggnPhaseNode := (masterL57Ctx P, none)

/-- The computed guard: the node of lines 5–7 is well formed. -/
def masterL57Guard (P : RawMasterSI) : Bool := aggnUniformWfCheck (masterL57Enter P)

/-- The window instance a child of the round asks for, with its letters renamed back
(`Algo.masterL57Unlabel`): the calls of the node are on the node's letters. -/
def masterL57Read (P : RawMasterSI) (J : AggnPhaseNode) : RawWinSI :=
  masterL57UnlabelWin (masterL57Order P, J.2.getD default)

/-- The computed width: that of the two phases, and a quasipolynomial reserve for the
Chain Rule of line 5. -/
def masterL57Width (c E : ℕ) (P : RawMasterSI) : ℕ :=
  aggnAggregateWidth c (masterL57Ctx P) + 2 ^ ((Nat.log 2 P.1.1.length + 2) ^ E)

/-- The constants `u v` of the giant branch: a fixed choice for which the nodes of
Cor. 12.0.10 built by the round pass their test (`Algo.exists_l57GWFOK`). -/
noncomputable def l57UV (e f : ℕ) : ℕ × ℕ :=
  ((exists_l57GWFOK e f).choose, (exists_l57GWFOK e f).choose_spec.choose)

theorem l57UV_spec (e f : ℕ) : L57GWFOK (l57UV e f).1 (l57UV e f).2 e f :=
  (exists_l57GWFOK e f).choose_spec.choose_spec

/-- The round of lines 5–7 that the carrier runs, with the giant branch of outcome (2a). -/
noncomputable abbrev masterL57Round (c b t d dc dp e f : ℕ) :
    Round AggnPhaseNode AggnL57GState RawCoset :=
  aggnL57GRound c b t d dc dp (l57UV e f).1 (l57UV e f).2 e f

/-- **The carrier of lines 5–7.** -/
noncomputable def masterL57Ops (c b t d dc dp e f E : ℕ) : MasterOps AggnL57GState :=
  masterShiftOps (masterWinLiftOps (masterL57Round c b t d dc dp e f) masterL57Read
    masterL57Enter masterL57Guard (masterL57Width c E) default)

theorem masterL57Ctx_length (P : RawMasterSI) :
    (masterL57Ctx P).2.1.length = P.1.1.length := by
  simp [masterL57Ctx, masterL57Relabel, length_masterL57XW]

theorem masterL57Ctx_length_y (P : RawMasterSI) :
    (masterL57Ctx P).2.2.1.length = P.1.1.length := by
  simp [masterL57Ctx, masterL57Relabel, length_masterL57YW]

/-- The letters of the first string of the context are below `2|Δ| + 1`. -/
theorem masterL57Ctx_letters_x (P : RawMasterSI) :
    ∀ u, decStrN P.1.1.length (masterL57Ctx P).2.1 u < 2 * P.1.1.length + 1 := fun u => by
  have h1 := masterL57Rank_lt_letters (length_masterL57XW P) (masterL57XW_letters P) u
  have h2 := length_masterL57Letters_le P
  change decStrN P.1.1.length (masterL57Relabel (masterL57Order P, masterL57XW P)) u < _
  omega

/-- The letters of the second string of the context are below `2|Δ| + 1`. -/
theorem masterL57Ctx_letters_y (P : RawMasterSI) :
    ∀ u, decStrN P.1.1.length (masterL57Ctx P).2.2.1 u < 2 * P.1.1.length + 1 := fun u => by
  have h1 := masterL57Rank_lt_letters (length_masterL57YW P) (masterL57YW_letters P) u
  have h2 := length_masterL57Letters_le P
  change decStrN P.1.1.length (masterL57Relabel (masterL57Order P, masterL57YW P)) u < _
  omega

/-- The group of the context is the window's group `G_Δ`: shortening the generators does not
change the group they generate. -/
theorem masterL57Ctx_group (P : RawMasterSI) :
    decGroup P.1.1.length (masterL57Ctx P).1.1.2 =
      decGroup P.1.1.length (masterHintTop (masterHintGet P)).1.1.2 :=
  decGroup_tidyGens (length_masterL57XW P) _

/-- **The context has the isomorphisms of the window**: `Iso_{G_Δ}` of the two renamed strings
of the context is `Iso_{G_Δ}(x_Δ, y_Δ)`, since one injective renaming of the letters changes no
isomorphism. -/
theorem masterL57Ctx_strIso (P : RawMasterSI) (K : Set (Perm (Fin P.1.1.length))) :
    strIso K (decStrN P.1.1.length (masterL57Ctx P).2.1)
        (decStrN P.1.1.length (masterL57Ctx P).2.2.1) =
      strIso K (decStrN P.1.1.length (masterHintTop (masterHintGet P)).2.1)
        (decStrN P.1.1.length (masterHintTop (masterHintGet P)).2.2) :=
  strIso_masterL57Relabel K (length_masterL57XW P) (length_masterL57YW P)
    (masterL57XW_letters P) (masterL57YW_letters P)

/-! ### The routines -/

private theorem pfst' {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem psnd' {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd

private theorem polyFun_powConst' {α : Type*} [Enc α] {f : α → ℕ} (hf : PolyFun f) (c : ℕ) :
    PolyFun (fun a => f a ^ c) := by
  induction c with
  | zero => exact (polyFun_const 1).of_eq (fun a => (pow_zero _).symm)
  | succ c ih => exact (ih.mul hf).of_eq (fun a => (pow_succ _ _).symm)

theorem polyFun_masterL57Ctx : PolyFun masterL57Ctx := by
  have hΔ : PolyFun (fun P : RawMasterSI => P.1.1) := polyFun_fst.comp polyFun_fst
  have hts : PolyFun (fun P : RawMasterSI =>
      List.range (min (10 + Nat.log 2 P.1.1.length) P.1.1.length)) :=
    (hΔ.pair (((polyFun_const 10).add ((hΔ.comp polyFun_length).comp polyFun_log2)))).comp
      polyFun_rangeTake
  exact polyFun_masterL57Action.pair
    (((polyFun_masterL57Order.pair polyFun_masterL57XW).comp polyFun_masterL57Relabel).pair
      (((polyFun_masterL57Order.pair polyFun_masterL57YW).comp polyFun_masterL57Relabel).pair
        hts))

theorem polyFun_masterL57Enter : PolyFun masterL57Enter :=
  polyFun_masterL57Ctx.pair (polyFun_const none)

theorem polyFun_masterL57Guard : PolyFun masterL57Guard :=
  polyFun_masterL57Enter.comp aggnPolyFun_uniformWfCheck

theorem polyFun_masterL57Read :
    PolyFun (fun q : RawMasterSI × AggnPhaseNode => masterL57Read q.1 q.2) := by
  have hget : PolyFun (fun J : AggnPhaseNode => J.2.getD default) := by
    refine ((polyFun_snd.pair polyFun_id).comp
      (PolyFun.optionElim (β := RawWinSI) (σ := AggnPhaseNode) (polyFun_const default)
        polyFun_fst)).of_eq (fun J => ?_)
    cases J.2 <;> rfl
  exact ((polyFun_fst.comp polyFun_masterL57Order).pair (polyFun_snd.comp hget)).comp
    polyFun_masterL57UnlabelWin

/-- The reserve `n ↦ 2 ^ ((log n + 2) ^ E)` is computed in polynomial time: its exponent is
polylogarithmic, so it has polynomially many bits. -/
theorem polyFun_twoPowLog {α : Type*} [Enc α] {f : α → ℕ} (hf : PolyFun f)
    (hfs : ∀ a, f a ≤ Enc.size a) (E : ℕ) :
    PolyFun (fun a => 2 ^ ((Nat.log 2 (f a) + 2) ^ E)) := by
  have hg : PolyFun (fun a => (Nat.log 2 (f a) + 2) ^ E) :=
    polyFun_powConst' ((hf.comp polyFun_log2).add (polyFun_const 2)) E
  refine PolyFun.pow (polyFun_const 2) hg (q := fun n => 2 ^ E * (n + 1) ^ E) (fun a => ?_)
    (polyBound_witness (2 ^ E) E)
  have h1 : Nat.log 2 (f a) ≤ f a := Nat.log_le_self 2 _
  have h2 : Nat.log 2 (f a) + 2 ≤ 2 * (Enc.size a + 1) := by
    have := hfs a
    have : 1 ≤ Enc.size a + 1 := Nat.le_add_left 1 _
    omega
  calc (Nat.log 2 (f a) + 2) ^ E ≤ (2 * (Enc.size a + 1)) ^ E := Nat.pow_le_pow_left h2 E
    _ = 2 ^ E * (Enc.size a + 1) ^ E := mul_pow _ _ _

theorem quasiFun_masterL57Width (c E : ℕ) : QuasiFun (masterL57Width c E) := by
  have hlen : PolyFun (fun P : RawMasterSI => P.1.1.length) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_length
  have hr := polyFun_twoPowLog hlen (fun P => (length_le_size _).trans
    ((size_fst_le' _).trans (size_fst_le' _))) E
  exact ((polyFun_masterL57Ctx.quasiFun.comp (aggnQuasiFun_aggregateWidth c)).pair
    hr.quasiFun).comp_poly polyFun_add

/-! ### The bounds of the round of lines 5–7, uniform in the fold state -/

attribute [local irreducible] Enc.size aggnBoundedInit aggnCompareBoundedInit
  aggnBoundedCombine aggnCompareBoundedCombine

/-- **The reserve is quasipolynomial.** At a well-formed node on `n` points, the width the
round reserves for the Chain Rule of line 5 is at most `2 ^ ((log n + 2) ^ E)`, for one `E`. -/
theorem aggnL57Cap_quasi (c b t d dc dp : ℕ) : ∃ E : ℕ, ∀ I : AggnPhaseNode,
    AggnCheckedWF I.1.2.1.length I →
      aggnL57Cap c b t d dc dp I.1 ≤ 2 ^ ((Nat.log 2 I.1.2.1.length + 2) ^ E) := by
  obtain ⟨Wp, hWp, hWpm, hpw⟩ := aggnCompareChecked_width_bound c
  obtain ⟨Kc, hKc, hKcm, he2⟩ := aggnL57Cap_le c b t d dc dp
  let B := fun n => 16 * (aggnStateCap dc n + aggnCompareStateCap dp n + Wp n + 2)
  have hB : QuasiPolyBound B := (polyBound_const 16).quasiPoly.mul
    ((((aggnQuasiPolyBound_stateCap dc).add (aggnQuasiPolyBound_compareStateCap dp)).add hWp).add
      (polyBound_const 2).quasiPoly)
  let Q := aggnL57InBound dc dp Wp
  have hQ : QuasiPolyBound Q :=
    ((polyBound_const 2).quasiPoly.mul aggnPolyBound_checked.quasiPoly).add
      ((polyBound_const 2).quasiPoly.mul hB)
  obtain ⟨E, hE⟩ := hKc.comp hQ
  refine ⟨E, fun I hI => ?_⟩
  have hwidth : aggnCompareWidth c I.1 ≤ Wp I.1.2.1.length :=
    hpw (I.1, none) ⟨rfl, hI.2.1, by simp⟩
  have hsizeC : Enc.size I.1 ≤ aggnCheckedBound I.1.2.1.length :=
    (size_fst_le' I).trans (aggnCheckedRound_size c I.1.2.1.length I hI)
  have hin : 2 * Enc.size I.1 + 2 * (16 * (aggnStateCap dc I.1.2.1.length +
      aggnCompareStateCap dp I.1.2.1.length + aggnCompareWidth c I.1 + 2)) ≤
      Q I.1.2.1.length := by
    dsimp only [Q, aggnL57InBound]
    omega
  exact ((he2 I.1).trans (hKcm hin)).trans (hE I.1.2.1.length)

/-- **The states of the round of lines 5–7 are small**, at every well-formed node, whatever
the fold state and the answer fed to the update. -/
theorem aggnL57_uniform_state (c b t d dc dp : ℕ) : ∃ S : ℕ → ℕ,
    QuasiPolyBound S ∧ Monotone S ∧ ∀ I : AggnPhaseNode, AggnCheckedWF I.1.2.1.length I →
      Enc.size ((aggnL57Round c b t d dc dp).init I) ≤ S I.1.2.1.length ∧
      ∀ j s a, Enc.size ((aggnL57Round c b t d dc dp).combine (I, j, s, a)) ≤
        S I.1.2.1.length := by
  obtain ⟨Wp, hWp, hWpm, hpw⟩ := aggnCompareChecked_width_bound c
  obtain ⟨e1, he1⟩ := (quasiFun_aggnL57HdrCore c b t d).size
  obtain ⟨F, hF, hFm, hFs⟩ := adStep_size_bdd
  let B := fun n => 16 * (aggnStateCap dc n + aggnCompareStateCap dp n + Wp n + 2)
  have hB : QuasiPolyBound B := (polyBound_const 16).quasiPoly.mul
    ((((aggnQuasiPolyBound_stateCap dc).add (aggnQuasiPolyBound_compareStateCap dp)).add hWp).add
      (polyBound_const 2).quasiPoly)
  have hBm : Monotone B := by
    intro a b hab
    exact Nat.mul_le_mul_left 16 (Nat.add_le_add_right
      (Nat.add_le_add (Nat.add_le_add (aggnMono_stateCap dc hab)
        (aggnMono_compareStateCap dp hab)) (hWpm hab)) 2)
  let Q := aggnL57InBound dc dp Wp
  have hQ : QuasiPolyBound Q :=
    ((polyBound_const 2).quasiPoly.mul aggnPolyBound_checked.quasiPoly).add
      ((polyBound_const 2).quasiPoly.mul hB)
  have hQm : Monotone Q := by
    intro a b hab
    have := aggnMono_checkedBound hab
    have := hBm hab
    dsimp only [Q, aggnL57InBound]
    dsimp only [B] at this
    omega
  let H := fun n => 2 ^ ((Nat.log 2 (Q n) + 2) ^ e1)
  have hH : QuasiPolyBound H := (quasiPolyBound_witness e1).comp hQ
  have hHm : Monotone H := fun a b hab => quasiPolyBound_witness_mono e1 (hQm hab)
  let V := fun n => F (H n + chainBound n) + 32 * (H n + chainBound n + 2) + 22
  have hV : QuasiPolyBound V := ((hF.comp (hH.add polyBound_chainBound.quasiPoly)).add
    ((polyBound_const 32).quasiPoly.mul
      ((hH.add polyBound_chainBound.quasiPoly).add (polyBound_const 2).quasiPoly))).add
      (polyBound_const 22).quasiPoly
  have hVm : Monotone V := by
    intro a b hab
    have h1 := hHm hab
    have h2 := mono_chainBound hab
    have h3 := hFm (Nat.add_le_add h1 h2)
    dsimp only [V]
    omega
  have hwidth : ∀ I : AggnPhaseNode, AggnCheckedWF I.1.2.1.length I →
      aggnCompareWidth c I.1 ≤ Wp I.1.2.1.length := fun I hI =>
    hpw (I.1, none) ⟨rfl, hI.2.1, by simp⟩
  have hsizeC : ∀ I : AggnPhaseNode, AggnCheckedWF I.1.2.1.length I →
      Enc.size I.1 ≤ aggnCheckedBound I.1.2.1.length := fun I hI =>
    (size_fst_le' I).trans (aggnCheckedRound_size c I.1.2.1.length I hI)
  have hpack : ∀ I : AggnPhaseNode, AggnCheckedWF I.1.2.1.length I → ∀ s,
      Enc.size (aggnAggregatePack c dc dp I.1 s) ≤ B I.1.2.1.length := by
    intro I hI s
    dsimp only [aggnAggregatePack]
    exact aggnAggregateState_size (dc := dc) (dp := dp) (n := I.1.2.1.length)
      (w := Wp I.1.2.1.length) (aggnCapState_size dc _ _)
      ((Nat.min_le_right _ _).trans (hwidth I hI)) (aggnCompareCapState_size dp _ _)
  have hin : ∀ I : AggnPhaseNode, AggnCheckedWF I.1.2.1.length I →
      2 * Enc.size I.1 + 2 * (16 * (aggnStateCap dc I.1.2.1.length +
        aggnCompareStateCap dp I.1.2.1.length + aggnCompareWidth c I.1 + 2)) ≤
        Q I.1.2.1.length := by
    intro I hI
    have := hsizeC I hI
    have := hwidth I hI
    dsimp only [Q, aggnL57InBound]
    omega
  have hhdr : ∀ I : AggnPhaseNode, AggnCheckedWF I.1.2.1.length I → ∀ s,
      Enc.size (aggnL57Hdr c b t d dc dp (I.1, s)) ≤ H I.1.2.1.length := by
    intro I hI s
    have h1 : Enc.size (I.1, aggnAggregatePack c dc dp I.1 s) ≤ Q I.1.2.1.length := by
      have := Combine.size_pair_le I.1 (aggnAggregatePack c dc dp I.1 s)
      have := aggnAggregatePack_size c dc dp I.1 s
      have := hin I hI
      omega
    exact (he1 _).trans (quasiPolyBound_witness_mono e1 h1)
  refine ⟨fun n => 2 * B n + 2 * V n, ((polyBound_const 2).quasiPoly.mul hB).add
      ((polyBound_const 2).quasiPoly.mul hV),
    fun _ _ h => Nat.add_le_add (Nat.mul_le_mul_left 2 (hBm h)) (Nat.mul_le_mul_left 2 (hVm h)),
    fun I hI => ⟨?_, ?_⟩⟩
  · -- the initial state
    show Enc.size ((aggnAggregateInit c dc dp I, none) : AggnL57State) ≤
      2 * B I.1.2.1.length + 2 * V I.1.2.1.length
    have hc : Enc.size ((aggnUniformRound c dc).init I) ≤ aggnStateCap dc I.1.2.1.length := by
      dsimp only [aggnUniformRound]
      unfold aggnBoundedInit
      exact aggnCapState_size dc I.1.2.1.length _
    have hp : Enc.size ((aggnCompareBoundedRound c dp).init I) ≤
        aggnCompareStateCap dp I.1.2.1.length := by
      dsimp only [aggnCompareBoundedRound]
      unfold aggnCompareBoundedInit
      exact aggnCompareCapState_size dp I.1.2.1.length _
    have h1 : Enc.size (aggnAggregateInit c dc dp I) ≤ B I.1.2.1.length := by
      dsimp only [aggnAggregateInit]
      exact aggnAggregateState_size (dc := dc) (dp := dp) (n := I.1.2.1.length)
          (w := Wp I.1.2.1.length)
          (s := ((aggnUniformRound c dc).init I, 0, (aggnCompareBoundedRound c dp).init I))
          hc (Nat.zero_le _) hp
    have h2 := Combine.size_pair_le (aggnAggregateInit c dc dp I) (none : Option ADState)
    have h3 : Enc.size (none : Option ADState) = 2 := size_none
    have h4 : 2 ≤ V I.1.2.1.length := by dsimp only [V]; omega
    omega
  · -- the update, for every state and every answer
    intro j s a
    show Enc.size (aggnL57Combine c b t d dc dp (I, j, s, a)) ≤
      2 * B I.1.2.1.length + 2 * V I.1.2.1.length
    unfold aggnL57Combine
    cases aggnAggregateChild c (I, j, s.1) with
    | some J =>
      simp only [Option.elim_some]
      have h1 : Enc.size (aggnAggregateCombine c dc dp (I, j, s.1, a)) ≤ B I.1.2.1.length := by
        unfold aggnAggregateCombine
        exact hpack I hI _
      have h2 := Combine.size_pair_le (aggnAggregateCombine c dc dp (I, j, s.1, a))
        (none : Option ADState)
      have h3 : Enc.size (none : Option ADState) = 2 := size_none
      have h4 : 2 ≤ V I.1.2.1.length := by dsimp only [V]; omega
      omega
    | none =>
      simp only [Option.elim_none]
      set h := aggnL57Hdr c b t d dc dp (I.1, s.1)
      have hx : h.2.2.2.2.1.length ≤ I.1.2.1.length := le_rfl
      have h1 := hpack I hI s.1
      set st := l57Step (h, s.2.getD (l57Init h), a)
      have h2 : Enc.size st ≤ F (Enc.size h + chainBound I.1.2.1.length) +
          32 * (Enc.size h + chainBound I.1.2.1.length + 2) + 20 :=
        l57Step_size hFs h hx _ a
      have h3 : Enc.size h ≤ H I.1.2.1.length := hhdr I hI s.1
      have h3' := hFm (Nat.add_le_add_right h3 (chainBound I.1.2.1.length))
      have h4 : Enc.size (some st) = Enc.size st + 2 := size_some_eq _
      have h5 := Combine.size_pair_le (aggnAggregatePack c dc dp I.1 s.1) (some st)
      show Enc.size ((aggnAggregatePack c dc dp I.1 s.1, some st) : AggnL57State) ≤ _
      dsimp only [V]
      omega

/-- **The two reserves are quasipolynomial.** At a well-formed node on `n` points, the width
the round reserves for the Chain Rule of line 5 and for the giant branch of outcome (2a) is at
most `2 ^ ((log n + 2) ^ E)`, for one `E`. -/
theorem aggnL57GCap_quasi (c b t d dc dp u v e f : ℕ) : ∃ E : ℕ, ∀ I : AggnPhaseNode,
    AggnCheckedWF I.1.2.1.length I →
      aggnL57Cap c b t d dc dp I.1 + aggnL57GCap c b t d dc dp u v e f I.1 ≤
        2 ^ ((Nat.log 2 I.1.2.1.length + 2) ^ E) := by
  obtain ⟨E1, h1⟩ := aggnL57Cap_quasi c b t d dc dp
  obtain ⟨GK, hGK, hGKm, hGKs⟩ := aggnL57GCap_le c b t d dc dp u v e f
  obtain ⟨E, hE⟩ := (quasiPolyBound_witness E1).add (hGK.comp aggnPolyBound_checked).quasiPoly
  refine ⟨E, fun I hI => le_trans (Nat.add_le_add (h1 I hI) ?_) (hE _)⟩
  have hs : Enc.size I.1 ≤ aggnCheckedBound I.1.2.1.length :=
    (size_fst_le' I).trans (aggnCheckedRound_size c I.1.2.1.length I hI)
  exact (hGKs I.1).trans (hGKm hs)

/-- **The states of the round of lines 5–7 with the giant branch are small**, at every
well-formed node, whatever the fold state and the answer fed to the update. The bounds are
those of `Algo.aggnL57G_hasRunCostQ`, whose update bound does not use its hypotheses on the
state and the answer. -/
theorem aggnL57G_uniform_state (c b t d dc dp u v e f : ℕ) : ∃ S : ℕ → ℕ,
    QuasiPolyBound S ∧ Monotone S ∧ ∀ I : AggnPhaseNode, AggnCheckedWF I.1.2.1.length I →
      Enc.size ((aggnL57GRound c b t d dc dp u v e f).init I) ≤ S I.1.2.1.length ∧
      ∀ j s a, Enc.size ((aggnL57GRound c b t d dc dp u v e f).combine (I, j, s, a)) ≤
        S I.1.2.1.length := by
  obtain ⟨RC, hRCc, -⟩ := aggnL57_hasRunCostQ_strong c b t d dc dp
  obtain ⟨Wp, hWp, hWpm, hpw⟩ := aggnCompareChecked_width_bound c
  obtain ⟨K0, hK0, hK0m, hK0s⟩ := top4AggregateInput_size_bdd
  obtain ⟨F, hF, hFm, hFs⟩ := polyFun_top4AutoEnter.size.exists_polyBound
  let Q4 : ℕ → ℕ := fun n => F (K0 (aggnCheckedBound n))
  have hQ4 : PolyBound Q4 := hF.comp (hK0.comp aggnPolyBound_checked)
  have hQ4m : Monotone Q4 := fun a b hab => hFm _ _ (hK0m (aggnMono_checkedBound hab))
  let B : ℕ → ℕ := fun n => 16 * (aggnStateCap dc n + aggnCompareStateCap dp n + Wp n + 2)
  have hB : QuasiPolyBound B := (polyBound_const 16).quasiPoly.mul
    ((((aggnQuasiPolyBound_stateCap dc).add (aggnQuasiPolyBound_compareStateCap dp)).add hWp).add
      (polyBound_const 2).quasiPoly)
  have hBm : Monotone B := by
    intro a b hab
    exact Nat.mul_le_mul_left 16 (Nat.add_le_add_right
      (Nat.add_le_add (Nat.add_le_add (aggnMono_stateCap dc hab)
        (aggnMono_compareStateCap dp hab)) (hWpm hab)) 2)
  let TB : ℕ → ℕ := fun n => l57gW4Bound u v (Q4 n) + top4Bound u v e f (Q4 n)
  have hTB : PolyBound TB := ((polyBound_l57gW4Bound u v).comp hQ4).add
    ((polyBound_top4Bound u v e f).comp hQ4)
  have hTBm : Monotone TB := fun a b hab => Nat.add_le_add
    (mono_l57gW4Bound u v (hQ4m hab)) (mono_top4Bound u v e f (hQ4m hab))
  have hsizeC : ∀ I : AggnPhaseNode, AggnCheckedWF I.1.2.1.length I →
      Enc.size I.1 ≤ aggnCheckedBound I.1.2.1.length := fun I hI =>
    (size_fst_le' I).trans (aggnCheckedRound_size c I.1.2.1.length I hI)
  have hwidth : ∀ I : AggnPhaseNode, AggnCheckedWF I.1.2.1.length I →
      aggnCompareWidth c I.1 ≤ Wp I.1.2.1.length := fun I hI =>
    hpw (I.1, none) ⟨rfl, hI.2.1, by simp⟩
  have hpack : ∀ I : AggnPhaseNode, AggnCheckedWF I.1.2.1.length I → ∀ s,
      Enc.size (aggnAggregatePack c dc dp I.1 s) ≤ B I.1.2.1.length := by
    intro I hI s
    dsimp only [aggnAggregatePack]
    exact aggnAggregateState_size (dc := dc) (dp := dp) (n := I.1.2.1.length)
      (w := Wp I.1.2.1.length) (aggnCapState_size dc _ _)
      ((Nat.min_le_right _ _).trans (hwidth I hI)) (aggnCompareCapState_size dp _ _)
  have hnode : ∀ I : AggnPhaseNode, AggnCheckedWF I.1.2.1.length I → ∀ s,
      aggnL57GOn c b t d dc dp u v e f (I.1, s) = true →
        Top4aWF u v e f (aggnL57GNode c dc dp (I.1, s)) ∧
          (top4X (aggnL57GNode c dc dp (I.1, s)).1.1).length ≤ Q4 I.1.2.1.length := by
    intro I hI s hon
    have hwf : Top4aWF u v e f (aggnL57GNode c dc dp (I.1, s)) :=
      (top4aCheck_spec u v e f _).1 (by
        unfold aggnL57GOn at hon
        simp only [Bool.and_eq_true] at hon
        exact hon.2)
    refine ⟨hwf, ?_⟩
    have hg := (top4aRunCostQ u v e f l57gSolve (quasiFun_const _)).ground_le
      (aggnL57GNode c dc dp (I.1, s))
    have hsz : Enc.size (aggnL57GNode c dc dp (I.1, s)) ≤ Q4 I.1.2.1.length :=
      (hFs _).trans (hFm _ _ ((hK0s _ _).trans (hK0m (hsizeC I hI))))
    exact hg.trans hsz
  have hnone2 : ∀ {α : Type} [Enc α], Enc.size (none : Option α) = 2 := fun {_} _ => size_none
  refine ⟨fun n => 2 * RC.stateBound n + 4 * B n + 8 * TB n + 64,
    ((((polyBound_const 2).quasiPoly.mul RC.quasiPolyBound_stateBound).add
      ((polyBound_const 4).quasiPoly.mul hB)).add ((polyBound_const 8).mul hTB).quasiPoly).add
      (polyBound_const 64).quasiPoly,
    fun _ _ h => Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add
      (Nat.mul_le_mul_left 2 (RC.mono_stateBound h)) (Nat.mul_le_mul_left 4 (hBm h)))
      (Nat.mul_le_mul_left 8 (hTBm h))) 64, fun I hI => ⟨?_, ?_⟩⟩
  · -- the initial state
    have h1 := RC.init_le I hI
    have h2 := Combine.size_pair_le ((aggnL57Round c b t d dc dp).init I)
      (none : Option (ℕ × Top4State))
    have h3 : Enc.size (none : Option (ℕ × Top4State)) = 2 := hnone2
    change Enc.size (((aggnL57Round c b t d dc dp).init I, none) : AggnL57GState) ≤
      2 * RC.stateBound I.1.2.1.length + 4 * B I.1.2.1.length + 8 * TB I.1.2.1.length + 64
    change Enc.size ((aggnL57Round c b t d dc dp).init I) ≤ RC.stateBound I.1.2.1.length at h1
    omega
  · -- the update, for every state and every answer
    intro j s a
    change Enc.size (aggnL57GCombine c b t d dc dp u v e f (I, j, s, a)) ≤
      2 * RC.stateBound I.1.2.1.length + 4 * B I.1.2.1.length + 8 * TB I.1.2.1.length + 64
    unfold aggnL57GCombine
    split
    next hact =>
      have hon : aggnL57GOn c b t d dc dp u v e f (I.1, s.1.1) = true := by
        unfold aggnL57GActive at hact
        simp only [Bool.and_eq_true] at hact
        exact hact.2
      obtain ⟨hwf, hlen⟩ := hnode I hI s.1.1 hon
      set N := aggnL57GNode c dc dp (I.1, s.1.1) with hN
      set p := aggnL57GPos c dc dp (I.1, s)
      have hk : min (p.1 + 1) (l57gW4 N) ≤ l57gW4Bound u v (Q4 I.1.2.1.length) := by
        have hw := (top4aRunCostQ u v e f l57gSolve (quasiFun_const _)).width_le N hwf
        change l57gW4 N ≤ l57gW4Bound u v (top4X N.1.1).length at hw
        exact (Nat.min_le_right _ _).trans (hw.trans (mono_l57gW4Bound u v hlen))
      have hst : Enc.size (top4aCombine (N, p.1, p.2, a)) ≤
          top4Bound u v e f (Q4 I.1.2.1.length) :=
        (top4Stored_size (e := e) (f := f) hwf.1.1 (top4Combine_stored (N.1, p.1, p.2, a))).trans
          (mono_top4Bound u v e f hlen)
      have hks := size_nat_le_self (min (p.1 + 1) (l57gW4 N))
      have hpk := hpack I hI s.1.1
      have e1 := Combine.size_pair_le (min (p.1 + 1) (l57gW4 N)) (top4aCombine (N, p.1, p.2, a))
      have e2 : Enc.size (some (min (p.1 + 1) (l57gW4 N), top4aCombine (N, p.1, p.2, a))) =
          Enc.size (min (p.1 + 1) (l57gW4 N), top4aCombine (N, p.1, p.2, a)) + 2 :=
        size_some_eq _
      have e3 := Combine.size_pair_le (aggnAggregatePack c dc dp I.1 s.1.1)
        (none : Option ADState)
      have e4 : Enc.size (none : Option ADState) = 2 := hnone2
      have e5 := Combine.size_pair_le
        (aggnAggregatePack c dc dp I.1 s.1.1, (none : Option ADState))
        (some (min (p.1 + 1) (l57gW4 N), top4aCombine (N, p.1, p.2, a)))
      show Enc.size (((aggnAggregatePack c dc dp I.1 s.1.1, none),
        some (min (p.1 + 1) (l57gW4 N), top4aCombine (N, p.1, p.2, a))) : AggnL57GState) ≤ _
      dsimp only [TB]
      omega
    next =>
      have h1 := hRCc I j s.1 a hI
      have h2 := Combine.size_pair_le (aggnL57Combine c b t d dc dp (I, j, s.1, a))
        (none : Option (ℕ × Top4State))
      have h3 : Enc.size (none : Option (ℕ × Top4State)) = 2 := hnone2
      show Enc.size ((aggnL57Combine c b t d dc dp (I, j, s.1, a), none) : AggnL57GState) ≤ _
      omega

/-- The reserve exponent `E` of the carrier bounds the two reserves of the round at every
well-formed node (`Algo.aggnL57GCap_quasi`: some `E` does). -/
def MasterL57EOK (c b t d dc dp e f E : ℕ) : Prop :=
  ∀ I : AggnPhaseNode, AggnCheckedWF I.1.2.1.length I →
    aggnL57Cap c b t d dc dp I.1 + aggnL57GCap c b t d dc dp (l57UV e f).1 (l57UV e f).2 e f I.1
      ≤ 2 ^ ((Nat.log 2 I.1.2.1.length + 2) ^ E)

theorem exists_masterL57EOK (c b t d dc dp e f : ℕ) : ∃ E, MasterL57EOK c b t d dc dp e f E :=
  aggnL57GCap_quasi c b t d dc dp _ _ e f

/-! ### The local costs of the carrier of lines 5–7 -/

theorem masterL57Guard_wf {P : RawMasterSI} (h : masterL57Guard P = true) :
    AggnCheckedWF (masterL57Enter P).1.2.1.length (masterL57Enter P) :=
  (aggnUniformWfCheck_spec 0 0 _).mp h

/-- **The carrier of lines 5–7 has local costs**, for every choice of the reserve exponent
`E`. -/
theorem masterL57_cost (a b : ℕ) (c b' t d dc dp e f E : ℕ) :
    Nonempty (MasterOpsCost a b (masterL57Ops c b' t d dc dp e f E)) := by
  obtain ⟨S, hS, hSm, hU⟩ := aggnL57G_uniform_state c b' t d dc dp (l57UV e f).1 (l57UV e f).2 e f
  have RQ := aggnL57GRunCostQ c b' t d dc dp (l57UV e f).1 (l57UV e f).2 e f
  obtain ⟨Wc, hWc, hWcm, hcw⟩ := aggnChecked_width_bound c
  obtain ⟨Wp, hWp, hWpm, hpw⟩ := aggnCompareChecked_width_bound c
  have hground : ∀ P, MasterInputWF a b P →
      (masterL57Enter P).1.2.1.length ≤ masterDegree P := fun P hP => by
    change (masterL57Ctx P).2.1.length ≤ _
    rw [masterL57Ctx_length]
    exact hP.2.1
  refine masterWinLift_cost a b RQ.quasiFun_child RQ.quasiFun_init RQ.quasiFun_combine
    RQ.quasiFun_finish
    polyFun_masterL57Read polyFun_masterL57Enter polyFun_masterL57Guard
    (quasiFun_masterL57Width c E) S (fun n => Wc n + Wp n + 2 ^ ((Nat.log 2 n + 2) ^ E)) hS hSm
    ((hWc.add hWp).add (quasiPolyBound_witness E)) ?_ ?_ ?_
  · intro P hP hg
    exact ((hU _ (masterL57Guard_wf hg)).1).trans (hSm (hground P hP))
  · intro P j s A hP hg
    exact ((hU _ (masterL57Guard_wf hg)).2 j s A).trans (hSm (hground P hP))
  · intro P hP hg
    have hI := masterL57Guard_wf hg
    have h1 : aggnPhaseWidth c (masterL57Ctx P) ≤ Wc (masterL57Ctx P).2.1.length :=
      hcw _ (masterL57Enter P) hI
    have h2 : aggnCompareWidth c (masterL57Ctx P) ≤ Wp (masterL57Ctx P).2.1.length :=
      hpw (masterL57Enter P) hI
    have hn := hground P hP
    change (masterL57Ctx P).2.1.length ≤ _ at hn
    have h3 := hWcm hn
    have h4 := hWpm hn
    rw [masterL57Ctx_length] at hn
    have h5 := quasiPolyBound_witness_mono E hn
    change aggnPhaseWidth c (masterL57Ctx P) + aggnCompareWidth c (masterL57Ctx P) +
      2 ^ ((Nat.log 2 P.1.1.length + 2) ^ E) ≤ Wc (masterDegree P) + Wp (masterDegree P) +
        2 ^ ((Nat.log 2 (masterDegree P) + 2) ^ E)
    omega

/-! ### Matching -/

section Match
variable {c b' t d dc dp e f E : ℕ}
    (hE : MasterL57EOK c b' t d dc dp e f E)
    {n : ℕ} {P : RawMasterSI} {gens : List (Perm (Fin n))}
    (hg : masterL57Guard P = true) (hx : P.1.2.2.2.1.length = n)
    (hgens : P.1.2.1 = gens.map (encPerm n))
    (hnd : P.1.1.Nodup) (hlt : ∀ u ∈ P.1.1, u < n)
    (hinv : IsInvariant (genGroup gens) (winSet n P.1.1))

include hE hg in
/-- The computed width covers the round's own width. -/
theorem masterL57Width_ge :
    (masterL57Round c b' t d dc dp e f).width (masterL57Enter P) ≤ masterL57Width c E P := by
  change aggnAggregateWidth c (masterL57Ctx P) + aggnL57Cap c b' t d dc dp (masterL57Ctx P) +
    aggnL57GCap c b' t d dc dp (l57UV e f).1 (l57UV e f).2 e f (masterL57Ctx P) ≤ _
  have h' := hE (masterL57Enter P) (masterL57Guard_wf hg)
  change aggnL57Cap c b' t d dc dp (masterL57Ctx P) +
    aggnL57GCap c b' t d dc dp (l57UV e f).1 (l57UV e f).2 e f (masterL57Ctx P) ≤
    2 ^ ((Nat.log 2 (masterL57Ctx P).2.1.length + 2) ^ E) at h'
  rw [masterL57Ctx_length] at h'
  change _ ≤ aggnAggregateWidth c (masterL57Ctx P) + _
  omega

/-- The calls of a window tree of the round of lines 5–7, with their letters renamed back
(`Algo.siUnlabel`). -/
def masterL57Unl (P : RawMasterSI) {N : ℕ} :
    SIReduction (Fin N) ℕ (Set (Perm (Fin N))) → SIReduction (Fin N) ℕ (Set (Perm (Fin N))) :=
  redMapCalls (siUnlabel (masterL57Order P))

/-- A letter of a decoded string of bounded letters is bounded. -/
theorem decStrN_lt_of_wf {N k : ℕ} {xs : RawStr} (h : RawStr.WF N k xs) (hk : 0 < k)
    (u : Fin N) : decStrN N xs u < k := by
  simp only [decStrN]
  rcases lt_or_ge (u : ℕ) xs.length with hu | hu
  · rw [List.getD_eq_getElem _ _ hu]
    exact h.2 _ (List.getElem_mem hu)
  · rw [List.getD_eq_default _ _ hu]
    exact hk

/-- **A child of the round of lines 5–7, read by the carrier.** Its instance, read by the
carrier, is the round's instance with the letters renamed back; the round's instance has
letters at most `2|Δ|`. -/
theorem masterL57_child_decode {c b' t d dc dp e f : ℕ} {P : RawMasterSI} {j : ℕ}
    {s : AggnL57GState} {J : AggnPhaseNode}
    (hJ : (masterL57Round c b' t d dc dp e f).child (masterL57Enter P, j, s) = some J) :
    decWinSI P.1.1.length (masterL57Read P J) =
        siUnlabel (masterL57Order P) (aggnPhaseDecode P.1.1.length J) ∧
      MasterCallLetters (2 * P.1.1.length + 1) (aggnPhaseDecode P.1.1.length J) := by
  obtain ⟨_, W, rfl⟩ := aggnL57GChild_some hJ
  have hwf := aggnCheckedWindow_wf (masterL57Enter P).1.2.1 W
  rw [show (masterL57Enter P).1.2.1.length = P.1.1.length from masterL57Ctx_length P] at hwf
  exact ⟨decWinSI_masterL57UnlabelWin _ hwf.2.2.2.2.2.1.1 hwf.2.2.2.2.2.2.1,
    fun u => decStrN_lt_of_wf hwf.2.2.2.2.2.1 (Nat.succ_pos _) u,
    fun u => decStrN_lt_of_wf hwf.2.2.2.2.2.2 (Nat.succ_pos _) u⟩

/-- Renaming back keeps the answer of an instance with letters at most `2|Δ|`, at a node
whose window lies in its domain. -/
theorem masterL57_unlabel_answer {P : RawMasterSI}
    (hN : P.1.1.length ≤ P.1.2.2.2.1.length) {I : SIInstance (Fin P.1.1.length) ℕ}
    (hI : MasterCallLetters (2 * P.1.1.length + 1) I) :
    (siUnlabel (masterL57Order P) I).answer = I.answer := by
  have hM := le_length_masterL57Order P
  exact siUnlabel_answer (nodup_masterL57Order P) (fun u => by have := hI.1 u; omega)
    (fun u => by have := hI.2 u; omega)

/-- **The window tree, renamed back.** A match of the round of lines 5–7 with its own decoding
is a match with the carrier's reading of its children (`Algo.masterL57Read`), for the tree with
its calls renamed back. When the calls have letters at most `2|Δ|`, that tree has the same
value, and its calls are the calls renamed back. -/
theorem masterL57Unl_match {c b' t d dc dp e f : ℕ} {P : RawMasterSI}
    (hN : P.1.1.length ≤ P.1.2.2.2.1.length) {w j : ℕ} {s : AggnL57GState}
    {T₀ : SIReduction (Fin P.1.1.length) ℕ (Set (Perm (Fin P.1.1.length)))}
    (h : LoopMatch (masterL57Round c b' t d dc dp e f) (aggnPhaseDecode P.1.1.length)
      (decCoset P.1.1.length) (masterL57Enter P) w j s T₀) :
    LoopMatch (masterL57Round c b' t d dc dp e f)
      (fun J => decWinSI P.1.1.length (masterL57Read P J))
      (decCoset P.1.1.length) (masterL57Enter P) w j s (masterL57Unl P T₀) :=
  loopMatch_redMapCalls _ (fun _ _ _ hJ => by
    obtain ⟨h1, h2⟩ := masterL57_child_decode hJ
    exact ⟨h1, masterL57_unlabel_answer hN h2⟩) h

theorem masterL57Unl_run {P : RawMasterSI} (hN : P.1.1.length ≤ P.1.2.2.2.1.length)
    {T₀ : SIReduction (Fin P.1.1.length) ℕ (Set (Perm (Fin P.1.1.length)))}
    (hlet : ∀ J ∈ T₀.calls, MasterCallLetters (2 * P.1.1.length + 1) J) :
    (masterL57Unl P T₀).run = T₀.run :=
  run_redMapCalls _ T₀ fun J hJ => masterL57_unlabel_answer hN (hlet J hJ)

theorem masterL57Unl_calls {P : RawMasterSI} (hN : P.1.1.length ≤ P.1.2.2.2.1.length)
    {T₀ : SIReduction (Fin P.1.1.length) ℕ (Set (Perm (Fin P.1.1.length)))}
    (hlet : ∀ J ∈ T₀.calls, MasterCallLetters (2 * P.1.1.length + 1) J) :
    (masterL57Unl P T₀).calls = T₀.calls.map (siUnlabel (masterL57Order P)) :=
  calls_redMapCalls _ T₀ fun J hJ => masterL57_unlabel_answer hN (hlet J hJ)

include hE hg hx hgens in
/-- **Lines 5–7 on the master carrier.** At a hinted node whose lines-5–7 node is well
formed, a fold of the round of lines 5–7 on the window that walks `T₀` gives a fold of the
carrier that walks the lift to the ambient domain of `T₀` with its letters renamed back
(`Algo.masterL57Unl`), its full preimage, and the shift back to the node's frame; provided the
calls of `T₀` have letters at most `2|Δ|`, the calls of `T₀` and its answer lie in the
restricted group, and every lifted call is admitted. -/
theorem masterL57_match (a b : ℕ)
    {T₀ : SIReduction (Fin P.1.1.length) ℕ (Set (Perm (Fin P.1.1.length)))}
    (h : LoopMatch (masterL57Round c b' t d dc dp e f) (aggnPhaseDecode P.1.1.length)
      (decCoset P.1.1.length) (masterL57Enter P)
      ((masterL57Round c b' t d dc dp e f).width (masterL57Enter P)) 0
      ((masterL57Round c b' t d dc dp e f).init (masterL57Enter P)) T₀)
    (hlet : ∀ J ∈ T₀.calls, MasterCallLetters (2 * P.1.1.length + 1) J)
    (hK : ∀ J ∈ T₀.calls, J.K ⊆ ((winRestrictHom n P.1.1 hnd hlt (genGroup gens) hinv).range :
      Set (Perm (Fin P.1.1.length))))
    (hRun : T₀.run ⊆ ((winRestrictHom n P.1.1 hnd hlt (genGroup gens) hinv).range :
      Set (Perm (Fin P.1.1.length))))
    (hL : ∀ J ∈ (top4wTree P.1.1 hnd hlt (genGroup gens) hinv (decStrN n P.1.2.2.2.1)
        (masterL57Unl P T₀)).calls,
      MasterCallLetters (2 * n + 1) J ∧ J.windowSize < P.1.1.length ∧
        ∃ G : Subgroup (Perm (Fin n)), IsCosetInstance G J) :
    LoopMatch (masterAdmittedRound a b (masterL57Ops c b' t d dc dp e f E))
      (fun J => decWinSI n J.1) (decCoset n) P
      ((masterL57Ops c b' t d dc dp e f E).width P) 0
      ((masterL57Ops c b' t d dc dp e f E).init P)
      ((top4wTree P.1.1 hnd hlt (genGroup gens) hinv (decStrN n P.1.2.2.2.1)
        (masterL57Unl P T₀)).bind (fun A => .done (decPerm n P.1.2.2.1 • A))) := by
  have hN : P.1.1.length ≤ P.1.2.2.2.1.length := by
    rw [hx]; exact length_le_of_nodup_lt hnd hlt
  have hK' : ∀ J ∈ (masterL57Unl P T₀).calls, J.K ⊆
      ((winRestrictHom n P.1.1 hnd hlt (genGroup gens) hinv).range :
        Set (Perm (Fin P.1.1.length))) := by
    rw [masterL57Unl_calls hN hlet]
    intro J hJ
    obtain ⟨J₀, hJ₀, rfl⟩ := List.mem_map.1 hJ
    exact hK J₀ hJ₀
  have hRun' : (masterL57Unl P T₀).run ⊆
      ((winRestrictHom n P.1.1 hnd hlt (genGroup gens) hinv).range :
        Set (Perm (Fin P.1.1.length))) := by
    rw [masterL57Unl_run hN hlet]
    exact hRun
  exact masterShiftOps_match a b _ hx (masterWinLift_start (d := default) hg
    (masterL57Width_ge hE hg) hx hgens hnd hlt hinv
    (fun J => decWinSI P.1.1.length (masterL57Read P J)) (fun _ _ _ _ => rfl) a b
    (masterL57Unl_match hN h) hK' hRun' hL)
end Match

end Algo
