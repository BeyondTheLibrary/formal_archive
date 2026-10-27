/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5): Theorems 9.2.1–9.2.3 on the
RAM, bounded at an external degree. Not part of the faithful formalization.
-/
import Workspace.Explicit.S9Run
import Workspace.Explicit.NodeMap
import Workspace.Algo.SplitExtendedRunSpec

/-!
# Theorems 9.2.1–9.2.3, bounded at the degree

* `Explicit.TN.bipInputRun`: Theorem 9.2.2 (`Algo.bipInputRun`) on a represented bipartite
  input of size at most `n`;
* `Explicit.TN.upccSplitFamily`: Theorem 9.2.1 (`Algo.upccSplitFamily`) on a represented UPCC
  of size at most `n`;
* `Explicit.TN.extendedSplitFamily`: Theorem 9.2.3 (`Algo.extendedSplitFamily`) on a
  represented input (`Algo.ExtendedInputRep`) of size at most `n`.

The time of the run of Sec. 9 is quasipolynomial in the size of its root, so the root must be
polynomially small in the degree. Every root is: the inputs of Theorem 9.2.1 that Theorem 9.2.3
builds are binary tables on at most `n` points (`Algo.sbipBinary_size`), with the threshold of
the original input (`Explicit.extendedUpccInput_size_le`).
-/

namespace Explicit

open RAM Algo Babai

variable {α β : Type*}

/-- A property of the input together with a size bound at the degree. -/
def Sized [Enc α] (P : α → Prop) (n : ℕ) (a : α) : Prop := P a ∧ Enc.size a ≤ n

/-- A polynomial routine has a polynomially bounded answer. -/
theorem exists_poly_size [Enc α] [Enc β] {f : α → β} (hf : PolyFun f) :
    ∃ A b, ∀ a, Enc.size (f a) ≤ 2 ^ A * (Enc.size a + 1) ^ b := by
  obtain ⟨A, b, -, hs⟩ := TN.ofPoly hf (fun _ _ => True) 0
  refine ⟨A, b, fun a => (hs 0 a trivial).trans (le_of_eq ?_)⟩
  simp [tsB]

namespace TN

/-- A polynomial routine before a routine with a sized precondition. -/
theorem sized_comp_poly [Enc α] [Enc β] {γ : Type*} [Enc γ] {f : α → β} {g : β → γ}
    {P : β → Prop} {k : ℕ} (hf : PolyFun f) (hg : TN g (Sized P) k) :
    TN (fun a => g (f a)) (Sized (fun a => P (f a))) k := by
  obtain ⟨A, b, hs⟩ := exists_poly_size hf
  exact (poly_comp hf hg).scale A b (fun n a ha =>
    ⟨Enc.size (f a), (hs a).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
      (Nat.add_le_add_right ha.2 1) b)), ha.1, le_rfl⟩)

/-! ## Theorem 9.2.2 -/

/-- A represented bipartite input. -/
def BipOK (r : RawBipInput) : Prop := ∃ m, ∃ X : Pt (BipInputs (Fin m)), BipInputRep m r X

/-- **Theorem 9.2.2 on the RAM** (`Algo.bipInputRun`), bounded at the degree. -/
theorem bipInputRun (c t d k : ℕ) (hk : max (c + 2) 4 ≤ k) (ht : t + 2 ≤ k) :
    TN (Algo.bipInputRun c t d) (Sized BipOK) k :=
  ((sized_comp_poly polyFun_bipInputNode
    ((TN.sbipRun c t d k hk ht).restrict (Pre' := Sized (fun I => ∃ m, SbipNodeValid m I))
      (fun n I h => h))).restrict
    (fun n r h => ⟨by obtain ⟨m, X, hX⟩ := h.1; exact ⟨m, _, hX.node⟩, h.2⟩)).of_eq
    (fun r => rfl)

/-! ## Theorem 9.2.1 -/

theorem upccSplitBipAnswers (c t d k : ℕ) (hk : max (c + 2) 4 ≤ k) (ht : t + 2 ≤ k) :
    TN (Algo.upccSplitBipAnswers c t d) (Sized (fun z => BipOK (upccSplitBipInput z))) k := by
  have ha : TN (fun z : ((ℕ × ℕ) × RawUpccBip) × RawUpccSplitBranch =>
      (Algo.bipInputRun c t d (upccSplitBipInput z)).getD [])
      (Sized (fun z => BipOK (upccSplitBipInput z))) k :=
    ((sized_comp_poly polyFun_upccSplitBipInput (bipInputRun c t d k hk ht)).pair
      (ofPoly (polyFun_const []) _ _)).comp_poly polyFun_optionGetD
  have hn : PolyFun (fun z : ((ℕ × ℕ) × RawUpccBip) × RawUpccSplitBranch =>
      (z.2.1.1.1, z.1.2.1)) :=
    ((((polyFun_snd.comp polyFun_fst).comp polyFun_fst).comp polyFun_fst).pair
      ((polyFun_fst.comp polyFun_snd).comp polyFun_fst))
  exact (((ofPoly hn _ _).pair ha).comp_poly (PolyFun.mapParam polyFun_splitFullLift)).of_eq
    (fun z => by unfold Algo.upccSplitBipAnswers; rfl)

/-- A branch of Theorem 9.2.1 whose bipartite input, if any, is represented. -/
def BranchOK (z : RawUpccSplitBranch) : Prop :=
  ∀ g, z.2.2 = some g → BipOK (upccSplitBipInput (g, z))

theorem upccSplitBranch (c t d k : ℕ) (hk : max (c + 2) 4 ≤ k) (ht : t + 2 ≤ k) :
    TN (Algo.upccSplitBranch c t d) (Sized BranchOK) k := by
  have hans := (upccSplitBipAnswers c t d k hk ht).scale 2 1
    (Pre' := fun n (w : ((ℕ × ℕ) × RawUpccBip) × RawUpccSplitBranch) =>
      BipOK (upccSplitBipInput w) ∧ Enc.size w.1 ≤ n ∧ Enc.size w.2 ≤ n)
    (fun n w hw => ⟨Enc.size w, by
      have := Combine.size_pair_le w.1 w.2
      change Enc.size w ≤ _ at this
      have := hw.2.1
      have := hw.2.2
      rw [pow_one]; omega, hw.1, le_rfl⟩)
  have hg : TN (fun s : RawUpccSplitBranch => [rawAlignPartition s.2.1]) (fun _ _ => True) k :=
    ofPoly (((polyFun_snd.comp polyFun_fst).comp polyFun_rawAlignPartition).comp
      polyFun_singleton) _ k
  have hel := optionElim (Pre := fun n (p : Option ((ℕ × ℕ) × RawUpccBip) × RawUpccSplitBranch) =>
      (∀ g, p.1 = some g → BipOK (upccSplitBipInput (g, p.2))) ∧
        Enc.size p.1 ≤ n ∧ Enc.size p.2 ≤ n) hg hans (fun _ _ _ => trivial)
    (fun n g s h => by
      obtain ⟨h1, h2, h3⟩ := h
      refine ⟨h1 g rfl, ?_, h3⟩
      change Enc.size (some g) ≤ n at h2
      change Enc.size g ≤ n
      rw [size_some_eq] at h2
      omega)
  have hpre : TN (fun z : RawUpccSplitBranch => (z.2.2, z)) (fun _ _ => True) k :=
    ofPoly ((polyFun_snd.comp polyFun_snd).pair polyFun_id) _ k
  refine ((hpre.restrict (Pre' := Sized BranchOK) (fun _ _ _ => trivial)).comp hel ?_).of_eq ?_
  · intro n z hz
    exact ⟨hz.1, ((size_snd_le' z.2).trans (size_snd_le' z)).trans hz.2, hz.2⟩
  · intro z
    unfold Algo.upccSplitBranch
    rfl

/-- A version of Theorem 9.2.1: a represented UPCC and a vertex. -/
def VersionOK (z : RawUpcc × ℕ) : Prop :=
  ∃ m, ∃ C : (UPCCs (Fin m)).Obj Set.univ, UpccInputRep m z.1 C ∧ z.2 < m

theorem VersionOK.branchOK {z : RawUpcc × ℕ} (h : VersionOK z) :
    BranchOK (z.1, Upcc.versionF z) := by
  obtain ⟨m, C, h, hi⟩ := h
  have hd : z.1.1.1.length = m := card_eq_length_dom h.table
  have hi' : z.2 < Upcc.widthF z.1 := by
    simpa only [Upcc.widthF, card_eq_length_dom h.table] using hi
  obtain ⟨Z, hr, -⟩ := Upcc.versionF_spec_index (⟨Set.univ, C⟩ : Pt (UPCCs (Fin m)))
    h.table (Equiv.Set.univ (Fin m)) h.names h.denominator h.lower hi'
  intro g hg
  rcases hq : Upcc.versionF z with ⟨q, qb⟩
  rw [hq] at hr hg
  change qb = some g at hg
  subst hg
  rcases Z with ⟨s, P | Y⟩
  · simp [UpccOutcomeRep] at hr
  · exact ⟨m, ⟨s, Y⟩, upccSplitBipInput_rep hd hr⟩

theorem upccSplitVersion (c t d k : ℕ) (hk : max (c + 2) 4 ≤ k) (ht : t + 2 ≤ k) :
    TN (Algo.upccSplitVersion c t d)
      (fun n z => VersionOK z ∧ Enc.size z.1 ≤ n) k := by
  have h := sized_comp_poly (polyFun_fst.pair Upcc.polyFun_versionF)
    (upccSplitBranch c t d k hk ht)
  refine (h.scale 2 1 (fun n z hz => ⟨Enc.size z, ?_, hz.1.branchOK, le_rfl⟩)).of_eq
    (fun z => rfl)
  obtain ⟨⟨m, C, hC, hi⟩, hs⟩ := hz
  have hd : z.1.1.1.length = m := card_eq_length_dom hC.table
  have h1 := Combine.size_pair_le z.1 z.2
  have h2 : Enc.size z.1.1.1 ≤ Enc.size z.1 :=
    (size_fst_le' z.1.1).trans (size_fst_le' z.1)
  have h3 := length_le_size z.1.1.1
  have h4 := size_le_self z.2
  rw [Small.size_nat] at h1
  change Enc.size z ≤ 2 * Enc.size z.1 + 2 * (Nat.size z.2 + 2) at h1
  rw [pow_one]
  omega

/-- A represented UPCC. -/
def UpccOK (r : RawUpcc) : Prop := ∃ m, ∃ C : (UPCCs (Fin m)).Obj Set.univ, UpccInputRep m r C

/-- **Theorem 9.2.1 on the RAM** (`Algo.upccSplitFamily`), bounded at the degree. -/
theorem upccSplitFamily (c t d k : ℕ) (hk : max (c + 2) 4 ≤ k) (ht : t + 2 ≤ k) :
    TN (Algo.upccSplitFamily c t d) (Sized UpccOK) k := by
  have hf := flatMapParam (upccSplitVersion c t d k hk ht)
  refine ((ofPoly (polyFun_id.pair ((polyFun_fst.comp polyFun_fst).comp polyFun_rangeLength))
    _ _).comp hf (fun n r hr x hx => ?_)).of_eq (fun r => rfl)
  obtain ⟨⟨m, C, hC⟩, hs⟩ := hr
  refine ⟨⟨m, C, hC, ?_⟩, hs⟩
  have hd : r.1.1.length = m := card_eq_length_dom hC.table
  simpa only [List.mem_range, hd] using hx

/-! ## Theorem 9.2.3 -/

theorem extendedUpccAnswers (c t d k : ℕ) (hk : max (c + 2) 4 ≤ k) (ht : t + 2 ≤ k) :
    TN (Algo.extendedUpccAnswers c t d)
      (fun n z => Sized UpccOK n (extendedUpccInput (z.2, z.1))) k := by
  have ha : TN (fun z : RawConfig × RawExtendedBranch =>
      Algo.upccSplitFamily c t d (extendedUpccInput (z.2, z.1)))
      (fun n z => Sized UpccOK n (extendedUpccInput (z.2, z.1))) k :=
    poly_comp (polyFun_swap.comp polyFun_extendedUpccInput) (upccSplitFamily c t d k hk ht)
  have hd : PolyFun (fun z : RawConfig × RawExtendedBranch => (z.2.1.1.1.2.2, z.2.2.2.1)) := by
    have hg : PolyFun (fun z : RawConfig × RawExtendedBranch => z.2.1) :=
      polyFun_snd.comp polyFun_fst
    have ho : PolyFun (fun z : RawConfig × RawExtendedBranch => z.2.2) :=
      polyFun_snd.comp polyFun_snd
    exact ((((hg.comp polyFun_fst).comp polyFun_fst).comp polyFun_snd).comp polyFun_snd).pair
      ((ho.comp polyFun_snd).comp polyFun_fst)
  exact (((ofPoly hd _ _).pair ha).comp_poly aggnPolyFun_restoreFamily).of_eq
    (fun z => by unfold Algo.extendedUpccAnswers; rfl)

/-- The precondition of a branch of Theorem 9.2.3 at degree `n`: its UPCC, if any, is
represented and has size at most `n`. -/
def ExtBranchPre (n : ℕ) (z : RawExtendedBranch) : Prop :=
  ∀ q, z.2.1 = none → z.2.2.2 = some q → Sized UpccOK n (extendedUpccInput (z, q))

theorem extendedSplitBranch (c t d k : ℕ) (hk : max (c + 2) 4 ≤ k) (ht : t + 2 ≤ k) :
    TN (Algo.extendedSplitBranch c t d) ExtBranchPre k := by
  have hnone0 := optionElim (Pre := fun n (p : Option RawConfig × RawExtendedBranch) =>
      ∀ q, p.1 = some q → Sized UpccOK n (extendedUpccInput (p.2, q)))
    (ofPoly (polyFun_const ([] : List RawAlignOutcome)) (fun _ _ => True) k)
    (extendedUpccAnswers c t d k hk ht) (fun _ _ _ => trivial) (fun n q s h => h q rfl)
  have hpre1 : TN (fun z : RawExtendedBranch => (z.2.2.2, z)) (fun _ _ => True) k :=
    ofPoly (((polyFun_snd.comp polyFun_snd).comp polyFun_snd).pair polyFun_id) _ k
  have hnone : TN (fun z : RawExtendedBranch =>
      z.2.2.2.elim [] (fun q => Algo.extendedUpccAnswers c t d (q, z)))
      (fun n z => ∀ q, z.2.2.2 = some q → Sized UpccOK n (extendedUpccInput (z, q))) k := by
    refine ((hpre1.restrict (Pre' := fun n z => ∀ q, z.2.2.2 = some q →
      Sized UpccOK n (extendedUpccInput (z, q))) (fun _ _ _ => trivial)).comp hnone0 ?_).of_eq ?_
    · exact fun n z hz => hz
    · intro z; rfl
  have hsome : TN (fun z : RawColPart × RawExtendedBranch => [rawAlignPartition z.1])
      (fun _ _ => True) k :=
    ofPoly ((polyFun_fst.comp polyFun_rawAlignPartition).comp polyFun_singleton) _ k
  have hel := optionElim (Pre := fun n (p : Option RawColPart × RawExtendedBranch) =>
      p.1 = none → ∀ q, p.2.2.2.2 = some q → Sized UpccOK n (extendedUpccInput (p.2, q)))
    hnone hsome (fun n s h => h rfl) (fun _ _ _ _ => trivial)
  have hpre2 : TN (fun z : RawExtendedBranch => (z.2.1, z)) (fun _ _ => True) k :=
    ofPoly ((polyFun_snd.comp polyFun_fst).pair polyFun_id) _ k
  refine ((hpre2.restrict (Pre' := ExtBranchPre) (fun _ _ _ => trivial)).comp hel ?_).of_eq ?_
  · exact fun n z hz h0 q hq => hz q h0 hq
  · intro z
    unfold Algo.extendedSplitBranch
    rfl

/-- The input facts of Theorem 9.2.3 that the RAM run needs: `Algo.ExtendedInputRep` without
the defect hypothesis. The defect hypothesis is what makes the answers valid; the machine runs
on the structure in any case (line 4c builds the structures of `H(x)` and `H(y)` together,
and only `H(x)` is known to have a large defect), and its cost does not depend on it. -/
structure ExtRepW (c n : ℕ) (g : AmbientGIn) : Prop where
  nodup : g.1.1.2.2.Nodup
  domain : ∀ i, i ∈ g.1.1.2.2 ↔ i < n
  guard : g.1.1.1.length ≤ guardBound c g.1.1.2.1.length
  denominator : 0 < g.2.2
  lower : (3 : ℝ)/4 ≤ sbipAlphaValue g.2

theorem ExtRepW.of_rep {c n : ℕ} {g : AmbientGIn} (h : ExtendedInputRep c n g) :
    ExtRepW c n g :=
  ⟨h.nodup, h.domain, h.guard, h.denominator, h.lower⟩

namespace ExtRepW
variable {c n : ℕ} {g : AmbientGIn} (h : ExtRepW c n g)
include h

/-- As `Algo.ExtendedInputRep.domain_length`. -/
theorem domain_length : g.1.1.2.2.length = n := by
  simpa only [fst_ambientPipeline321] using
    card_eq_length_dom (ambientPipeline321_wf (n := n) (c := c) (a := g.1)
      h.nodup h.domain h.guard)

/-- As `Algo.ExtendedInputRep.upcc_storage`. -/
theorem upcc_storage {xs : List ℕ} {o : RawDesignReadOut}
    (ho : (xs,o) ∈ Algo.ambientDesignReadFamily c g) {q : RawConfig} (hq : o.2.2 = some q) :
    o.2.1.Nodup ∧ (∀ a ∈ o.2.1,a < n) ∧ RawWL.WF o.2.1.length 2 q := by
  obtain ⟨_,rfl⟩ := (ambientDesignReadFamily_mem c g xs o).1 ho
  exact designReadExit_upcc_storage
    (ambientPipeline321_wf (n := n) (c := c) (a := g.1) h.nodup h.domain h.guard) hq

/-- As `Algo.ExtendedInputRep.upcc_admissible` (the first conjunct). -/
theorem upcc_admissible {xs : List ℕ} {o : RawDesignReadOut}
    (ho : (xs,o) ∈ Algo.ambientDesignReadFamily c g) {q : RawConfig} (hq : o.2.2 = some q) :
    ∃ C : (UPCCs (Fin o.2.1.length)).Obj Set.univ,
      UpccInputRep o.2.1.length (extendedUpccInput ((g,o),q)) C := by
  have hhalf : 1/2 ≤ sbipAlphaValue g.2 := by have hh := h.lower; linarith
  obtain ⟨_,hdom,P,hcoh,huni,hcols⟩ := ambientDesignReadFamily_upcc_valid
    h.nodup h.domain rfl h.guard h.denominator rfl hhalf ho hq
  obtain ⟨hnd,hlt,hw⟩ := h.upcc_storage ho hq
  have hlarge : sbipAlphaValue g.2 * n < o.2.1.length := by
    simpa only [IsDominant,Fintype.card_fin,ncard_winSet _ hnd hlt] using hdom
  have hsmall : o.2.1.length ≤ n := length_le_of_nodup_lt hnd hlt
  have hpos : 0 < o.2.1.length := by
    have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hh := h.lower
    have : (0 : ℝ) < o.2.1.length := by nlinarith
    exact_mod_cast this
  have hposR : (0 : ℝ) < o.2.1.length := by exact_mod_cast hpos
  have he : sbipAlphaValue (extendedUpccInput ((g,o),q)).2 =
      sbipAlphaValue g.2 * n / o.2.1.length := by
    dsimp only [extendedUpccInput,sbipAlphaValue]
    rw [h.domain_length]
    push_cast
    ring
  have hlow : (2 : ℝ)/3 ≤ sbipAlphaValue (extendedUpccInput ((g,o),q)).2 := by
    rw [he,le_div_iff₀ hposR]
    have hh := h.lower
    have hs : (o.2.1.length : ℝ) ≤ n := by exact_mod_cast hsmall
    have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    nlinarith
  let e := (Equiv.Set.univ (Fin o.2.1.length)).symm
  let C : (UPCCs (Fin o.2.1.length)).Obj Set.univ :=
    ⟨fun u v => binColor (q,(u.val,v.val)),P.congrEquiv e,
      PartitionStructure.congrEquiv_isCoherent e hcoh,
      PartitionStructure.congrEquiv_isUniprimitive e huni,
      by funext u v; exact (hcols u.val v.val).symm⟩
  exact ⟨C,⟨hw,fun _ _ => rfl,Nat.mul_pos h.denominator hpos,hlow⟩⟩

end ExtRepW

/-- The precondition of Theorem 9.2.3 at degree `n`: a represented input on at most `n` points,
with a threshold and a guard string of size at most `n`. The relational structure itself may
be large (it lists tuples of arity up to `log n`); only these parts must be small. -/
def ExtPre (a n : ℕ) (g : AmbientGIn) : Prop :=
  (∃ n0, n0 ≤ n ∧ ExtRepW a n0 g) ∧ Enc.size g.2 ≤ n ∧ g.1.1.2.1.length ≤ n

/-- The UPCC inputs that Theorem 9.2.3 builds are polynomially small in the number of points
and the size of the threshold: a binary table on at most `n` points, and the threshold of the
input times at most `n`. -/
theorem extendedUpccInput_size_le :
    ∃ r₀ r, ∀ a n0 g xs (o : RawDesignReadOut) q, ExtRepW a n0 g →
      (xs, o) ∈ Algo.ambientDesignReadFamily a g → o.2.2 = some q →
      Enc.size (extendedUpccInput ((g, o), q)) ≤ 2 ^ r₀ * (n0 + Enc.size g.2 + 1) ^ r := by
  obtain ⟨C, D, hC⟩ := polyBound_sbipBinaryBound
  refine ⟨2 * C + 32, D + 1, fun a n0 g xs o q h ho hq => ?_⟩
  obtain ⟨hnd, hlt, hw⟩ := h.upcc_storage ho hq
  have hlen : o.2.1.length ≤ n0 := length_le_of_nodup_lt hnd hlt
  set S := n0 + Enc.size g.2 with hS
  have hq1 : Enc.size q ≤ C * (S + 1) ^ D :=
    (sbipBinary_size hw).trans ((hC _).trans (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_left (by omega) D)))
  have ha1 : Nat.size g.2.1 + 2 ≤ Enc.size g.2 := by
    have := size_fst_le' g.2
    rw [Small.size_nat] at this; exact this
  have hb1 : Nat.size g.2.2 + 2 ≤ Enc.size g.2 := by
    have := size_snd_le' g.2
    rw [Small.size_nat] at this; exact this
  have hA : Enc.size (g.2.1 * g.1.1.2.2.length) ≤ 2 * S + 2 := by
    rw [Small.size_nat]
    have := size_mul_le g.2.1 g.1.1.2.2.length
    have := size_le_self g.1.1.2.2.length
    rw [h.domain_length] at *
    omega
  have hB : Enc.size (g.2.2 * o.2.1.length) ≤ 2 * S + 2 := by
    rw [Small.size_nat]
    have := size_mul_le g.2.2 o.2.1.length
    have := size_le_self o.2.1.length
    omega
  have h1 := Combine.size_pair_le q (g.2.1 * g.1.1.2.2.length, g.2.2 * o.2.1.length)
  have h2 := Combine.size_pair_le (g.2.1 * g.1.1.2.2.length) (g.2.2 * o.2.1.length)
  change Enc.size (extendedUpccInput ((g, o), q)) ≤ _ at h1
  have hp : (S + 1) ^ D ≤ (S + 1) ^ (D + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hS1 : S + 1 ≤ (S + 1) ^ (D + 1) := Nat.le_self_pow (by omega) _
  have hC2 : 2 * C + 32 ≤ 2 ^ (2 * C + 32) := Nat.lt_two_pow_self.le
  have hm := Nat.mul_le_mul_right ((S + 1) ^ (D + 1)) hC2
  have hCm : C * (S + 1) ^ D ≤ C * (S + 1) ^ (D + 1) := Nat.mul_le_mul_left C hp
  nlinarith

/-- **Theorem 9.2.3 on the RAM** (`Algo.extendedSplitFamily`), bounded at the degree, on a
represented input on at most `n` points. -/
theorem extendedSplitFamily (a c t d k : ℕ) (ha : a + 1 ≤ k) (hk : max (c + 2) 4 ≤ k)
    (ht : t + 2 ≤ k) :
    TN (Algo.extendedSplitFamily a c t d) (ExtPre a) k := by
  have hf : TN (fun z : AmbientGIn × (List ℕ × RawDesignReadOut) =>
      Algo.extendedSplitBranch c t d (z.1, z.2.2))
      (fun n z => ExtBranchPre n (z.1, z.2.2)) k :=
    poly_comp (polyFun_fst.pair (polyFun_snd.comp polyFun_snd))
      (extendedSplitBranch c t d k hk ht)
  have hfam : TN (fun g : AmbientGIn => (g, Algo.ambientDesignReadFamily a g)) AmbPre k :=
    (ofPoly polyFun_id _ _).pair ((ambientDesignReadFamily a).mono_k ha)
  have hall := (hfam.restrict (Pre' := fun n g => AmbPre n g ∧
      ∀ o ∈ Algo.ambientDesignReadFamily a g, ExtBranchPre n (g, o.2))
    (fun _ _ h => h.1)).comp (flatMapParam hf) (fun n g h => h.2)
  obtain ⟨r₀, r, hs⟩ := extendedUpccInput_size_le
  refine (hall.scale (r₀ + r) (r + 1)
    (fun n g hg => ⟨2 ^ (r₀ + r) * (n + 1) ^ (r + 1), le_rfl, ?_⟩)).of_eq
    (fun g => rfl)
  obtain ⟨⟨n0, hn0, h⟩, hg2, hl1⟩ := hg
  have hp : (2 * n + 1) ^ r ≤ 2 ^ r * (n + 1) ^ r := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) r
  have h1 : n ≤ 2 ^ (r₀ + r) * (n + 1) ^ (r + 1) :=
    ((Nat.le_succ n).trans (Nat.le_self_pow (by omega) _)).trans
      (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _))
  have hl2 : g.1.1.2.2.length ≤ n := h.domain_length ▸ hn0
  refine ⟨⟨by omega, by omega⟩, fun o ho q h0 hq => ?_⟩
  obtain ⟨xs, o⟩ := o
  obtain ⟨C, hC⟩ := h.upcc_admissible ho hq
  refine ⟨⟨_, C, hC⟩, (hs a n0 g xs o q h ho hq).trans ?_⟩
  calc 2 ^ r₀ * (n0 + Enc.size g.2 + 1) ^ r ≤ 2 ^ r₀ * (2 ^ r * (n + 1) ^ r) :=
        Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (by omega) r).trans hp)
    _ ≤ 2 ^ (r₀ + r) * (n + 1) ^ (r + 1) := by
        rw [← mul_assoc, ← pow_add]
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))

end TN

end Explicit
