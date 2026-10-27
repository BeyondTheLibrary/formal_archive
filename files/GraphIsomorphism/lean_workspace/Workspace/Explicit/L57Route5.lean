/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5): the carrier of lines 5–7 of the
Master Algorithm (Sec. 15) bounded at the degree under its state invariant, and Theorem 1.1.1
with exponent 5. Not part of the faithful formalization.
-/
import Workspace.Explicit.L57Inv
import Workspace.Explicit.AssemblyInv

/-!
# The carrier of lines 5–7 under its state invariant

`Explicit.l57J` is the invariant of the fold states of the carrier of lines 5–7
(`Algo.masterL57Ops`): at a node where the round runs (`Algo.masterL57Guard`), the state satisfies
`Explicit.L57GInv` at the context of the node; elsewhere it is the default state.

* `Explicit.stateInvXR_masterL57Ops`: `init` establishes it, `combine` keeps it, and it bounds
  the states by `2^{K (log₂ n + 2)^5}` (`Explicit.StateInvXR`);
* `Explicit.carrierTNJ_masterL57Ops`: the width and the four routines are bounded at the degree
  with exponent 5 under it (`Explicit.CarrierTNJ`), from `Workspace/Explicit/L57Master.lean`;
  `combine` only needs the loops of the stored phase states to be short, which the invariant
  gives (`Explicit.l57J_stOK`).
* `Explicit.route5Bounds`: the bounds of route 5 (`Explicit.Route5Bounds`) at every parameter
  set with `t + 2 ≤ 5`, and so Theorem 1.1.1 with exponent 5
  (`Explicit.theorem_1_1_1_exponent5`).
-/

set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1000000

namespace Explicit

open RAM Algo

/-- **The invariant of the carrier of lines 5–7.** -/
def l57J (c b t d dc dp K0 K1 : ℕ) : StInv AggnL57GState := fun n P j s =>
  (masterL57Guard P = true → L57GInv c b t d dc dp K0 K1 n (masterL57Ctx P) j s) ∧
    (masterL57Guard P = false → s = default)

theorem aggInv_stOK {c n : ℕ} {C : AggnPhaseCtx} {B : PhaseEnv c n C} {B' : CompEnv c n C}
    {j : ℕ} {s : AggnAggregateState} (h : AggInv B B' j s) : AggStOK n s := by
  refine ⟨?_, ?_⟩
  · rcases h.1 with hB | hz
    · exact hB.stOK
    · rw [PhaseStOK, hz]; exact Nat.zero_le _
  · rcases h.2.2 with hB | hz
    · exact hB.stOK
    · rw [CompStOK, hz]; exact Nat.zero_le _

theorem l57J_stOK {c b t d dc dp K0 K1 n j : ℕ} {P : RawMasterSI} {s : AggnL57GState}
    (h : l57J c b t d dc dp K0 K1 n P j s) : TN.L57StOK n s := by
  cases hg : masterL57Guard P
  · rw [h.2 hg]; exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  · obtain ⟨-, -, ⟨B, B', -, hI⟩, -, -⟩ := h.1 hg
    exact aggInv_stOK hI

variable {c b t d dc dp e f E : ℕ}

theorem masterL57Ops_init_eq (P : RawMasterSI) :
    (masterL57Ops c b t d dc dp e f E).init P = if masterL57Guard P then
      ((aggnAggregateInit c dc dp (masterL57Enter P), none), none) else default := rfl

theorem masterL57Ops_combine_eq (z : RawMasterSI × ℕ × AggnL57GState × RawCoset) :
    (masterL57Ops c b t d dc dp e f E).combine z = if masterL57Guard z.1 then
      aggnL57GCombine c b t d dc dp (l57UV e f).1 (l57UV e f).2 e f (masterL57Enter z.1, z.2.1,
        z.2.2.1, topwCosetImage (z.1.1.2.2.2.1, z.1.1.1, z.2.2.2)) else default := rfl

theorem masterL57Ops_width_eq (P : RawMasterSI) :
    (masterL57Ops c b t d dc dp e f E).width P =
      if masterL57Guard P then masterL57Width c E P else 0 := rfl

/-- **The fold states of the carrier of lines 5–7 under `Explicit.l57J`, with an explicit
exponent.** -/
theorem stateInvXR_masterL57Ops (a b' : ℕ) (hc2 : 2 ≤ c) (hc : c + 2 ≤ 5) (hb : b + 2 ≤ 5)
    (ht : t + 2 ≤ 5) : ∃ K0 K1 K, StateInvXR a b' K (masterL57Ops c b t d dc dp e f E) R5
      (l57J c b t d dc dp K0 K1) := by
  obtain ⟨r0, r, hctx⟩ := master_size_poly polyFun_masterL57Ctx.size a b'
  obtain ⟨K0, hK0⟩ := q5_poly r0 r
  obtain ⟨K1, hK1⟩ := env_exists c hc K0
  obtain ⟨Ks, hKs⟩ := l57GInv_size (b := b) (t := t) (d := d) (dc := dc) (dp := dp) hc hb ht K0 K1
  obtain ⟨Kd, hKd⟩ := q5_const (Enc.size (default : AggnL57GState))
  obtain ⟨Kc, hKc⟩ := q5_masterInputCap a b'
  refine ⟨K0, K1, Ks + Kd + Kc, ?_, ?_, ?_, ?_, ?_⟩
  · -- `init`
    intro n P hP
    have hpre := hP.pre
    rw [masterL57Ops_init_eq]
    refine ⟨fun hg => ?_, fun hg => by rw [hg]; rfl⟩
    rw [hg, if_pos rfl]
    have hL := l57CtxOK_of hc2 hpre
    have hs : Enc.size (masterL57Ctx P) ≤ 2 ^ (K0 * lg n ^ 5) :=
      (hctx n P hpre.1 hpre.2.1).trans (hK0 n)
    exact l57GInv_init hL hs (hK1 n _ hL.1 hs)
  · -- `combine`
    intro n P j s C A hP hJ _ _ _
    rw [masterL57Ops_combine_eq]
    refine ⟨fun hg => ?_, fun hg => by rw [hg]; rfl⟩
    rw [hg, if_pos rfl]
    exact (hJ.1 hg).combine _ _ e f _
  · -- the size of the states
    intro n P j s hP hJ
    cases hg : masterL57Guard P
    · rw [hJ.2 hg]
      exact (hKd n).trans (StateBoundsX.two_pow_mono (by omega) n)
    · exact (hKs n _ j s (hJ.1 hg)).trans (StateBoundsX.two_pow_mono (by omega) n)
  · -- the answer, within the input cap
    intro n P j s hP _
    obtain ⟨-, rfl, -⟩ := hP
    exact (masterShiftOps_finish_size _ P s).trans (by unfold masterInputCap; omega)
  · intro n P j s hP _
    obtain ⟨-, rfl, -⟩ := hP
    exact ((masterShiftOps_finish_size _ P s).trans (by unfold masterInputCap; omega)).trans
      ((hKc _).trans (StateBoundsX.two_pow_mono (by omega) _))

/-- **The width of the carrier of lines 5–7 at the degree**: the width of the two phases
(`Explicit.TN.aggnAggregateWidth`) and the reserve `2^{(log₂ |Δ| + 2)^E}`, which has
polynomially many bits. -/
theorem tn_width_masterL57Ops (a b' : ℕ) (hc2 : 2 ≤ c) (hc : c + 2 ≤ 5) :
    TN (masterL57Ops c b t d dc dp e f E).width (CarrierPre a b' R5) 5 := by
  have hw : TN (fun P : RawMasterSI => aggnAggregateWidth c (masterL57Ctx P))
      (CarrierPre a b' R5) 5 :=
    (TN.poly_comp polyFun_masterL57Ctx ((TN.aggnAggregateWidth c).mono_k (by omega))).restrict
      (fun n P hP => (l57CtxOK_of hc2 hP).1.1)
  have hlen : PolyFun (fun P : RawMasterSI => P.1.1.length) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_length
  have hr := polyFun_twoPowLog hlen (fun P => (length_le_size _).trans
    ((size_fst_le' _).trans (size_fst_le' _))) E
  have hsum : TN (masterL57Width c E) (CarrierPre a b' R5) 5 :=
    ((hw.pair (TN.ofPoly hr _ 5)).comp_poly polyFun_add).of_eq (fun _ => rfl)
  exact (TN.ite polyFun_masterL57Guard hsum (TN.const' 0 _ 5) (fun _ _ h _ => h)
    (fun _ _ h _ => h)).of_eq (fun P => (masterL57Ops_width_eq P).symm)

/-- **The carrier of lines 5–7 bounded at the degree under `Explicit.l57J`.** -/
theorem carrierTNJ_masterL57Ops (a b' K0 K1 : ℕ) (hc2 : 2 ≤ c) (hc : c + 2 ≤ 5)
    (hb : b + 2 ≤ 5) (ht : t + 2 ≤ 5) :
    CarrierTNJ a b' (masterL57Ops c b t d dc dp e f E) R5 (l57J c b t d dc dp K0 K1) :=
  ⟨tn_width_masterL57Ops a b' hc2 hc,
    (TN.masterL57Ops_child dc dp e f E a b' hc2 hc hb ht).restrict (fun _ _ h => h.1),
    TN.masterL57Ops_init dc dp e f E a b' hc2 hc,
    (TN.masterL57Ops_combine dc dp e f E a b' hc2 hc hb ht).restrict
      (fun _ _ h => ⟨h.1, l57J_stOK h.2.1⟩),
    (TN.masterL57Ops_finish dc dp e f E a b' hc2 hc hb ht).restrict (fun _ _ h => h.1)⟩

/-- **The bounds of route 5**, at every parameter set with `t + 2 ≤ 5`. -/
theorem route5Bounds (p : Params) (ht : p.t + 2 ≤ 5) : Route5Bounds p := by
  obtain ⟨K0, K1, K, hS⟩ := stateInvXR_masterL57Ops (c := 2) (b := 0) (t := p.t) (d := p.d)
    (dc := p.dc) (dp := p.dp) (e := p.e) (f := p.f) (E := p.E) p.a p.b le_rfl (by norm_num)
    (by norm_num) ht
  refine ⟨R5, l57J 2 0 p.t p.d p.dc p.dp K0 K1, K, ?_, hS.withHint (hint5E p), ?_⟩
  · exact (carrierTNJ_masterL57Ops p.a p.b K0 K1 le_rfl (by norm_num) (by norm_num) ht).withHint
      ((TN.masterL57Hint p.a p.b p.dc p.dp p.u' p.v' p.e p.f le_rfl
        (by norm_num) (by norm_num) ht).restrict (fun _ _ h => h.1))
  · exact fun n P hG _ hr => ⟨hr, hG.2⟩

/-- **Theorem 1.1.1 with exponent 5, with an explicit constant.** -/
theorem theorem_1_1_1_exponent5 : ∃ c, Theorem_1_1_1_exponent5_numeral c := by
  obtain ⟨_, _, -, -, h⟩ :=
    theorem_1_1_1_exponent5_of_route5 (fun p _ _ _ h3 _ _ _ => route5Bounds p (by omega))
  exact ⟨_, h⟩

end Explicit
