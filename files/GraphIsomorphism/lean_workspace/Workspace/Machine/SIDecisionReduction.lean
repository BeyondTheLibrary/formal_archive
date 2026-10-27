import Workspace.Machine.Final
import Workspace.Machine.Transfer
import Workspace.Algo.Encodings

/-!
# Uniform decision reductions to the SI workspace routine

The raw constructor must be polynomial on all inputs. Its encoding specification
is needed only on the typed inputs. This rule keeps one program and one bound for
the whole family of input types.
-/

namespace RAM

open Algo Targets Classical

namespace SIDecision

/-- Read the answer tag after the SI routine returns. -/
theorem polyFun_answerTag : PolyFun (fun a : RawCoset => a.isSome) := by
  have h : PolyFun (fun p : RawCoset × ℕ => p.1.elim false (fun _ => true)) :=
    PolyFun.optionElim (polyFun_const false) (polyFun_const true)
  exact ((polyFun_id.pair (polyFun_const (0 : ℕ))).comp h).of_eq (fun a => by cases a <;> rfl)

/-- The raw answer has the same register encoding as a typed answer. -/
def rawAnswer {n : ℕ} (b : Option (List (Equiv.Perm (Fin n)) × Equiv.Perm (Fin n))) : RawCoset :=
  b.map fun p => (p.1.map (encPerm n), encPerm n p.2)

theorem encode_rawAnswer {n : ℕ} (b : Option (List (Equiv.Perm (Fin n)) × Equiv.Perm (Fin n))) :
    Enc.encode (rawAnswer b) = Enc.encode b := by
  cases b with
  | none => rfl
  | some p =>
    change 1 :: (frame (Enc.encode (p.1.map (encPerm n))) ++ frame (Enc.encode (encPerm n p.2))) =
      1 :: (frame (Enc.encode p.1) ++ frame (Enc.encode p.2))
    rw [← encode_gens_eq, ← encode_perm_eq]

/-- The search specification determines the answer tag. -/
theorem answerTag_correct {n s : ℕ} {a : SIInput n s}
    {b : Option (List (Equiv.Perm (Fin n)) × Equiv.Perm (Fin n))} (h : SIRel n s a b) :
    b.isSome = true ↔ (IsoSet a.1 a.2.1 a.2.2).Nonempty := by
  cases b with
  | none =>
    change IsoSet a.1 a.2.1 a.2.2 = ∅ at h
    simp [h]
  | some b =>
    exact iff_of_true rfl ⟨b.2, h.1⟩

end SIDecision

open SIDecision

/-- A uniform polynomial constructor followed by the SI workspace routine and
its answer-tag reader gives a uniform quasipolynomial decision routine. -/
theorem siDecision_of_polyReduction {ι α : Type*} {A : ι → Type*}
    [Enc α] [∀ i, Enc (A i)] (raw : ∀ i, A i → α)
    (hraw : ∀ i a, Enc.encode (raw i a) = Enc.encode a)
    (buildRaw : α → RawSI) (hbuild : PolyFun buildRaw)
    (m s : ι → ℕ) (inst : ∀ i, A i → SIInput (m i) (s i))
    (hinst : ∀ i a, Enc.encode (inst i a) = Enc.encode (buildRaw (raw i a)))
    (h : SIWorkspaceRoutine) :
    ∃ (P : Program) (T : ℕ → ℕ), QuasiPolyBound T ∧ ∀ i,
      ∃ f : A i → Bool,
        (∀ a, f a = true ↔ (IsoSet (inst i a).1 (inst i a).2.1 (inst i a).2.2).Nonempty) ∧
          ComputesInTime P f T := by
  obtain ⟨P, T, S, hT, hS, hSmono, hP⟩ := h
  obtain ⟨c, hc⟩ := hT
  let U := fun k => 2 ^ ((Nat.log 2 k + 2) ^ c)
  have hU : QuasiPolyBound U := quasiPolyBound_witness c
  have hUmono : ∀ k k', k ≤ k' → U k ≤ U k' := fun _ _ h => quasiPolyBound_witness_mono c h
  obtain ⟨B, TB, hTB, hB⟩ := hbuild.time
  obtain ⟨SB, hSB, _, hSBle⟩ := hbuild.size.exists_polyBound
  obtain ⟨D, TD, hTD, hD⟩ := polyFun_answerTag.time
  obtain ⟨d, e, hde⟩ := hTD
  let V := fun k => d * (k + 1) ^ e
  have hV : PolyBound V := polyBound_witness d e
  have hVmono : ∀ k k', k ≤ k' → V k ≤ V k' := fun _ _ h => polyBound_witness_mono d e h
  let W := fun k => TB k + U (SB k) + V (S (SB k))
  have hW : QuasiPolyBound W :=
    (hTB.quasiPoly.add (hU.comp_poly hSB)).add ((hV.comp (hS.comp hSB)).quasiPoly)
  let Q := seq (seq B P) D
  let answer := fun i (a : A i) => decide (IsoSet (inst i a).1 (inst i a).2.1 (inst i a).2.2).Nonempty
  have hQ : ∀ i, CleanComputeAt 16 Q (answer i) W := by
    intro i a
    have hb : CleanComputeAt 16 B (inst i) TB :=
      hB.transfer (e := raw i) (f' := buildRaw) (hraw i) (hinst i)
    have hsz : Enc.size (inst i a) ≤ SB (Enc.size a) := by
      have heq := size_eq_of_encode_eq (hinst i a)
      have hin := size_eq_of_encode_eq (hraw i a)
      rw [heq, ← hin]
      exact hSBle (raw i a)
    obtain ⟨b, ⟨hbrel, hbsize⟩, hbRun⟩ := hP (m i) (s i) (inst i a)
    have htag : CleanComputeAt 16 D
        (fun b : Option (List (Equiv.Perm (Fin (m i))) × Equiv.Perm (Fin (m i))) => b.isSome) TD :=
      hD.transfer encode_rawAnswer (fun b => by cases b <;> rfl)
    have hbool : b.isSome = answer i a := by
      apply Bool.eq_iff_iff.mpr
      simpa only [answer, decide_eq_true_eq] using answerTag_correct hbrel
    have hrun := ((hb a).seq hbRun).seq (htag b)
    dsimp only at hrun
    rw [hbool] at hrun
    apply hrun.mono
    have h₁ := (hc (Enc.size (inst i a))).trans (hUmono _ _ hsz)
    have h₂ := (hde (Enc.size b)).trans (hVmono _ _ (hbsize.trans (hSmono _ _ hsz)))
    change TB (Enc.size a) + T (Enc.size (inst i a)) + TD (Enc.size b) ≤ W (Enc.size a)
    dsimp only [W]
    omega
  refine ⟨seq Bridge.up (seq Q Bridge.down), bridgeTime W (fun _ => 3),
    quasiPolyBound_bridgeTime hW (polyBound_const 3), fun i => ?_⟩
  refine ⟨answer i, fun a => by simp [answer], ?_⟩
  exact computesInTime_of_cleanComputeAt (hQ i) (fun _ _ _ => le_rfl)
    (fun a => Combine.size_bool_le _)

end RAM
