import Workspace.Algo.TopMasterChainOpenBounds

/-! # Executable admission of master calls
A raw fold state need not encode a correct answer. Every proposed child
therefore passes a polynomial size, degree, and decreasing-measure check.
The check is redundant on the calls of a valid branch. Its purpose is to
make the evaluator's structural laws hold on arbitrary raw states.
-/
namespace Algo
open RAM RAM.Targets Babai

def masterInputCap (a b n : ℕ) : ℕ :=
  4 * (topcsContextCap a b n + aggnCheckedWindowBound n + chainBound n + 1)

def MasterInputWF (a b : ℕ) (p : RawMasterSI) : Prop :=
  Enc.size p ≤ masterInputCap a b (masterDegree p) ∧
    masterWindowSize p ≤ masterDegree p ∧ masterParameter p ≤ 2 * masterWindowSize p

def masterInputCheck (a b : ℕ) (p : RawMasterSI) : Bool :=
  decide (Enc.size p ≤ masterInputCap a b (masterDegree p)) &&
    decide (masterWindowSize p ≤ masterDegree p) &&
    decide (masterParameter p ≤ 2 * masterWindowSize p)

/-- The admission test of a proposed child `z.2` of the node `z.1`: the input bounds, the
same ambient degree, a smaller measure, and **an invariant window** — the child's window is
invariant under the group its generators generate (`Algo.rawIsInvariant`).

The last test is an input-validity check of the machine, not a step of the paper.  Every call
the paper's algorithm makes is a coset instance `⟨σN, Δ, x, y⟩` with `Δ` invariant under `N`
(`Babai.IsCosetInstance`), and its raw form passes the test, so on the calls of a valid
branch the test is redundant.  This is proved for every kind of child the carrier makes:
normalized window calls (`Algo.masterCheckedCall_rawIsInvariant`, with the coset property of
the calls of lines 4b, 4d, 5–7 and of the descents: `Algo.master4Tree_calls_coset`,
`Algo.top4wTree_calls_isCosetInstance`, `Algo.masterDescStrongTree_coset`), the orbit-chain
children of line 1 (`Algo.masterChainOpen_admitted` with `Algo.masterChainReturn_calls_coset`)
and the Cameron children (`Algo.masterCameronChildInput_rawIsInvariant`).  It is there so that every admitted child, whatever raw fold state produced it,
has an invariant window, which the recursion needs of every node it reaches. -/
def masterAdmit (a b : ℕ) (z : RawMasterSI × RawMasterSI) : Bool :=
  masterInputCheck a b z.2 && decide (masterDegree z.2 = masterDegree z.1) &&
    decide (masterRawMeasure z.2 < masterRawMeasure z.1) &&
    rawIsInvariant (z.2.1.2.1, z.2.1.1)

def masterAdmitChild (a b : ℕ) (z : RawMasterSI × Option RawMasterSI) : Option RawMasterSI :=
  z.2.bind fun q => if masterAdmit a b (z.1, q) then some q else none

 theorem polyFun_masterInputCap (a b : ℕ) : PolyFun (masterInputCap a b) := by
  have hg : PolyFun gensBound := (polyFun_const 1).add ((polyFun_id.mul polyFun_id).mul
    (((polyFun_const 2).mul polyFun_top4aStrBound).add (polyFun_const 1)))
  have hw : PolyFun aggnCheckedWindowBound :=
    (polyFun_const 32).mul ((hg.add
      ((((polyFun_const 2).mul polyFun_id).add (polyFun_const 1)).comp
        polyFun_top4aStrBound)).add (polyFun_const 1))
  exact (polyFun_const 4).mul ((((polyFun_topcsContextCap a b).add
    hw).add polyFun_topcsChainBound).add (polyFun_const 1))

 theorem polyBound_masterInputCap (a b : ℕ) : PolyBound (masterInputCap a b) :=
  (polyBound_const 4).mul ((((polyBound_topcsContextCap a b).add
    aggnPolyBound_checkedWindow).add polyBound_chainBound).add (polyBound_const 1))

 theorem mono_masterInputCap (a b : ℕ) : Monotone (masterInputCap a b) := by
  intro m n h
  have hc := mono_topcsContextCap a b h
  have hw := aggnMono_checkedWindowBound h
  have hs := mono_chainBound h
  unfold masterInputCap
  omega

 theorem polyFun_masterInputCheck (a b : ℕ) : PolyFun (masterInputCheck a b) :=
  wftPolyFun_and (wftPolyFun_and
    (AggnSizeRoutine.polyFun_size.le (polyFun_masterDegree.comp (polyFun_masterInputCap a b)))
    (polyFun_masterWindowSize.le polyFun_masterDegree))
    (polyFun_masterParameter.le ((polyFun_const 2).mul polyFun_masterWindowSize))

 theorem masterInputCheck_spec (a b : ℕ) (p : RawMasterSI) :
    masterInputCheck a b p = true ↔ MasterInputWF a b p := by
  simp only [masterInputCheck, MasterInputWF, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

 theorem polyFun_masterAdmit (a b : ℕ) : PolyFun (masterAdmit a b) :=
  wftPolyFun_and (wftPolyFun_and (wftPolyFun_and (polyFun_snd.comp (polyFun_masterInputCheck a b))
    ((polyFun_snd.comp polyFun_masterDegree).natEq (polyFun_fst.comp polyFun_masterDegree)))
    (((polyFun_snd.comp polyFun_masterRawMeasure).add (polyFun_const 1)).le
      (polyFun_fst.comp polyFun_masterRawMeasure)))
    ((((polyFun_snd.comp polyFun_fst).comp polyFun_snd).comp polyFun_fst).pair
      ((polyFun_snd.comp polyFun_fst).comp polyFun_fst) |>.comp polyFun_rawIsInvariant)

 theorem masterAdmit_spec (a b : ℕ) (p q : RawMasterSI) :
    masterAdmit a b (p, q) = true ↔ MasterInputWF a b q ∧
      masterDegree q = masterDegree p ∧ masterRawMeasure q < masterRawMeasure p ∧
        rawIsInvariant (q.1.2.1, q.1.1) = true := by
  simp only [masterAdmit, Bool.and_eq_true, masterInputCheck_spec, decide_eq_true_eq, and_assoc]

 theorem polyFun_masterAdmitChild (a b : ℕ) : PolyFun (masterAdmitChild a b) := by
  have hbody : PolyFun (fun z : RawMasterSI × RawMasterSI =>
      if masterAdmit a b (z.2, z.1) then some z.1 else none) :=
    PolyFun.ite ((polyFun_snd.pair polyFun_fst).comp (polyFun_masterAdmit a b))
      (polyFun_fst.comp polyFun_some) (polyFun_const none)
  exact ((polyFun_snd.pair polyFun_fst).comp
    (PolyFun.optionElim (polyFun_const none) hbody)).of_eq
      (fun z => by unfold masterAdmitChild; cases z.2 <;> rfl)

 theorem masterAdmitChild_some {a b : ℕ} {p J : RawMasterSI} {o : Option RawMasterSI} :
    masterAdmitChild a b (p, o) = some J ↔ o = some J ∧ MasterInputWF a b J ∧
      masterDegree J = masterDegree p ∧ masterRawMeasure J < masterRawMeasure p ∧
        rawIsInvariant (J.1.2.1, J.1.1) = true := by
  cases o with
  | none => simp [masterAdmitChild]
  | some q =>
    simp only [masterAdmitChild, Option.bind_some]
    by_cases h : masterAdmit a b (p, q) = true
    · simp only [h, ↓reduceIte, Option.some.injEq]
      constructor
      · intro he; subst J; exact ⟨rfl, (masterAdmit_spec a b p q).mp h⟩
      · exact fun hh => hh.1
    · rw [if_neg h]
      simp only [reduceCtorEq, false_iff, Option.some.injEq]
      rintro ⟨rfl, hW, hn, hm, hi⟩
      exact h ((masterAdmit_spec a b p q).mpr ⟨hW, hn, hm, hi⟩)

 theorem masterAdmitChild_eq {a b : ℕ} {p : RawMasterSI} {o : Option RawMasterSI}
    (h : ∀ q, o = some q → MasterInputWF a b q ∧ masterDegree q = masterDegree p ∧
      masterRawMeasure q < masterRawMeasure p ∧ rawIsInvariant (q.1.2.1, q.1.1) = true) :
    masterAdmitChild a b (p, o) = o := by
  cases o with
  | none => rfl
  | some q => exact masterAdmitChild_some.mpr ⟨rfl, h q rfl⟩

 open scoped Pointwise in
/-- Two descriptions of one coset by subgroups: if `τ H = σ N` as sets, then `H = N`. -/
theorem coset_subgroup_eq {Ω : Type*} {H N : Subgroup (Equiv.Perm Ω)} {τ σ : Equiv.Perm Ω}
    (h : {κ : Equiv.Perm Ω | ∃ g ∈ H, κ = τ * g} = σ • (N : Set (Equiv.Perm Ω))) : H = N := by
  have hτ : τ ∈ σ • (N : Set (Equiv.Perm Ω)) := h ▸ ⟨1, H.one_mem, (mul_one τ).symm⟩
  obtain ⟨ν, hν, hντ⟩ := Set.mem_smul_set.mp hτ
  change σ * ν = τ at hντ
  ext g
  constructor
  · intro hg
    have : τ * g ∈ σ • (N : Set (Equiv.Perm Ω)) := h ▸ ⟨g, hg, rfl⟩
    obtain ⟨μ, hμ, hμe⟩ := Set.mem_smul_set.mp this
    change σ * μ = τ * g at hμe
    have : g = ν⁻¹ * μ := by
      rw [← hντ, mul_assoc] at hμe
      have := mul_left_cancel hμe
      rw [this, inv_mul_cancel_left]
    rw [this]
    exact N.mul_mem (N.inv_mem hν) hμ
  · intro hg
    have : σ * (ν * g) ∈ {κ : Equiv.Perm Ω | ∃ g ∈ H, κ = τ * g} :=
      h ▸ Set.mem_smul_set.mpr ⟨ν * g, N.mul_mem hν hg, rfl⟩
    obtain ⟨k, hk, hke⟩ := this
    rw [← hντ, ← mul_assoc] at hke
    rw [mul_left_cancel hke]
    exact hk

/-- A raw window whose decoded instance is a coset instance passes the raw invariance
check: the generators generate the group of the coset, and that group preserves the
window. -/
 theorem rawIsInvariant_of_isCosetInstance {n : ℕ} {W : RawWinSI} (hW : AggnCheckedWindowWF n W)
    {G : Subgroup (Equiv.Perm (Fin n))} (hC : IsCosetInstance G (decWinSI n W)) :
    rawIsInvariant (W.2.1, W.1) = true := by
  obtain ⟨N, σ, -, -, hK, hinv⟩ := hC
  have hN : decGroup n W.2.1 = N := coset_subgroup_eq hK
  rw [rawIsInvariant_eq_true_iff hW.2.2.1 hW.2.1, hN]
  exact hinv

 theorem masterChainOpen_admitted (a b : ℕ) {n : ℕ} {W : RawWinSI}
    (hW : AggnCheckedWindowWF n W) (hinv : rawIsInvariant (W.2.1, W.1) = true)
    (h2 : 1 < (winOrbits (W.2.1, W.1)).length) (j : ℕ) (s : RawCoset)
    (hcos : ∀ J, masterChainOpenChild (W, j, s) = some J →
      ∃ G : Subgroup (Equiv.Perm (Fin n)), IsCosetInstance G (decWinSI n J.1)) :
    masterAdmitChild a b ((W, none), masterChainOpenChild (W, j, s)) =
      masterChainOpenChild (W, j, s) := by
  apply masterAdmitChild_eq
  intro J hJ
  obtain ⟨hshape, hnone⟩ := masterChainOpenChild_wf hW hinv hJ
  have hn := masterChainOpenChild_degree hJ
  have hm := masterChainOpenChild_measure hW.2.2.2.2.2.1.1 hW.2.2.1 hW.1 hW.2.1 hinv h2 hJ
  obtain ⟨G, hG⟩ := hcos J hJ
  refine ⟨⟨?_, ?_, ?_⟩, hn, hm, rawIsInvariant_of_isCosetInstance hshape hG⟩
  · have hs := masterChainOpenChild_size hW hinv hJ
    change Enc.size J ≤ masterInputCap a b (masterDegree J)
    rw [hn]
    change Enc.size J ≤ masterInputCap a b W.2.2.2.1.length
    rw [hW.2.2.2.2.2.1.1]
    unfold masterInputCap
    omega
  · change J.1.1.length ≤ J.1.2.2.2.1.length
    rw [hshape.2.2.2.2.2.1.1]
    exact length_le_of_nodup_lt hshape.1 hshape.2.1
  · simp only [masterParameter, hnone, Option.elim_none, le_refl]
end Algo
