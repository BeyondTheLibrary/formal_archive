/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the running time `q(n) n^{O(k)}` of Theorem 9.2.3 for every arity.
-/
import Workspace.Algo.ExtendedDesignAll
import Workspace.Algo.ListMapRAM
import Workspace.Algo.Agg1321Iter

/-!
# Theorem 9.2.3 on the RAM for every arity

Theorem 9.2.3 says the objectives are reached *"at a multiplicative cost of `q(n) n^{O(k)}`,
where `q(n)` is a quasipolynomial function"*.  The routine `Algo.extendedSplitAll`
(`Workspace/Algo/ExtendedDesignAll.lean`) has two parts.

1. **The Design Lemma family**, on the input padded with `n^k` zeros: a `RAM.PolyFun` of the
   padded input.  Its time is `poly(size) · n^{O(k)}` (`Algo.exists_padProgGen`).
2. **One UPCC per outcome**, solved by Theorem 9.2.1.  The UPCC handed over is small: its
   vertices are the dominant points (at most `n`), its colors are ranks (at most `n²`), and the
   threshold is the input threshold scaled by `n` (`Algo.size_job_le`).  So each call costs a
   quasipolynomial of `n` and of the length of the threshold, whatever `k` and the size of the
   relations.

The number of outcomes is at most `n^k`.  The total time is therefore

```
C · (size + 1)^E · (n + 1)^{E·k} · Q(D),
```

where `D` is the length of the encodings of the domain list and of the threshold (`O(n log n)`
plus the length of the threshold), and `Q` is quasipolynomial (`Algo.theorem_9_2_3_ram_all`).
The factor `(size + 1)^E` is the reading of the input, which the paper does not count (see
the corrected paper entry on §8).

No axiom and no `sorry`.
-/

namespace Algo
open Babai RAM RAM.Targets

/-! ## The routine split into a polynomial part and the UPCC calls -/

/-- One call of Theorem 9.2.1: the UPCC with its threshold, and the dictionary back to the
original names (the domain and the dominant points). -/
abbrev UpccJob := RawUpcc × (List ℕ × List ℕ)

/-- One outcome of the Design Lemma: the answers already found (the partition, if any) and the
UPCC calls still to be made (none or one). -/
abbrev ExtItem := List RawAlignOutcome × List UpccJob

/-- The UPCC call at a dominant configuration `q`. -/
def upccJob (z : RawExtendedBranch × RawConfig) : UpccJob :=
  (extendedUpccInput z, (z.1.1.1.1.2.2, z.1.2.2.1))

/-- The outcome of the Design Lemma, split. -/
def extItem (z : RawExtendedBranch) : ExtItem :=
  z.2.1.elim ([], z.2.2.2.elim [] (fun q => [upccJob (z, q)]))
    (fun P => ([rawAlignPartition P], []))

/-- One call of Theorem 9.2.1, with the answers restored to the original names. -/
def jobRun (c t d : ℕ) (j : UpccJob) : List RawAlignOutcome :=
  aggnRestoreFamily (j.2, upccSplitFamily c t d j.1)

/-- The answers of one outcome. -/
def itemRun (c t d : ℕ) (it : ExtItem) : List RawAlignOutcome :=
  it.1 ++ (it.2.map (jobRun c t d)).flatten

theorem itemRun_extItem (c t d : ℕ) (z : RawExtendedBranch) :
    itemRun c t d (extItem z) = extendedSplitBranch c t d z := by
  obtain ⟨g, P, dl, q⟩ := z
  cases P with
  | some P => simp [itemRun, extItem, extendedSplitBranch]
  | none =>
      cases q with
      | none => simp [itemRun, extItem, extendedSplitBranch]
      | some q =>
          simp [itemRun, extItem, extendedSplitBranch, extendedUpccAnswers, jobRun,
            aggnRestoreFamily, upccJob]

/-- The polynomial part: the Design Lemma family on the padded input, each outcome split. -/
def stageA (x : AmbientGIn × List ℕ) : List ExtItem :=
  (padReadFamily (ambToG x.1, x.2)).map (fun o => extItem (x.1, o.2))

theorem extendedSplitAll_eq_stages (c t d : ℕ) (g : AmbientGIn) :
    extendedSplitAll c t d g = ((stageA (g, ambPad g)).map (itemRun c t d)).flatten := by
  rw [extendedSplitAll, stageA, List.flatMap_def, List.map_map]
  congr 1
  refine List.map_congr_left (fun o _ => ?_)
  simp only [Function.comp_apply, itemRun_extItem]

theorem polyFun_ambToG : PolyFun ambToG :=
  ((((polyFun_fst.comp polyFun_fst).comp polyFun_fst).pair
    (((polyFun_fst.comp polyFun_fst).comp polyFun_snd).comp polyFun_snd)).pair
    (polyFun_fst.comp polyFun_snd)).pair polyFun_snd

theorem polyFun_upccJob : PolyFun upccJob := by
  have hdom : PolyFun (fun z : RawExtendedBranch × RawConfig => z.1.1.1.1.2.2) :=
    ((((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_fst).comp
      polyFun_snd).comp polyFun_snd
  have hdl : PolyFun (fun z : RawExtendedBranch × RawConfig => z.1.2.2.1) :=
    ((polyFun_fst.comp polyFun_snd).comp polyFun_snd).comp polyFun_fst
  exact polyFun_extendedUpccInput.pair (hdom.pair hdl)

theorem polyFun_extItem : PolyFun extItem := by
  have hq : PolyFun (fun y : RawConfig × RawExtendedBranch => [upccJob (y.2, y.1)]) :=
    (((polyFun_snd.pair polyFun_fst).comp polyFun_upccJob).pair (polyFun_const [])).comp
      polyFun_cons
  have hnone : PolyFun (fun z : RawExtendedBranch =>
      (([] : List RawAlignOutcome), z.2.2.2.elim [] (fun q => [upccJob (z, q)]))) :=
    (polyFun_const []).pair ((((polyFun_snd.comp polyFun_snd).comp polyFun_snd).pair
      polyFun_id).comp (PolyFun.optionElim (polyFun_const []) hq))
  have hsome : PolyFun (fun y : RawColPart × RawExtendedBranch =>
      (([rawAlignPartition y.1], []) : ExtItem)) :=
    ((((polyFun_fst.comp polyFun_rawAlignPartition).pair (polyFun_const [])).comp
      polyFun_cons).pair (polyFun_const []))
  refine ((((polyFun_snd.comp polyFun_fst).pair polyFun_id).comp
    (PolyFun.optionElim hnone hsome))).of_eq (fun z => ?_)
  unfold extItem
  cases z.2.1 <;> rfl

theorem polyFun_stageA : PolyFun stageA := by
  have hin : PolyFun (fun x : AmbientGIn × List ℕ =>
      (x.1, padReadFamily (ambToG x.1, x.2))) :=
    polyFun_fst.pair (((polyFun_fst.comp polyFun_ambToG).pair polyFun_snd).comp
      polyFun_padReadFamily)
  have hm : PolyFun (fun y : AmbientGIn × (List ℕ × RawDesignReadOut) => extItem (y.1, y.2.2)) :=
    (polyFun_fst.pair (polyFun_snd.comp polyFun_snd)).comp polyFun_extItem
  exact (hin.comp (PolyFun.mapParam hm)).of_eq (fun _ => rfl)

theorem quasiFun_jobRun (c t d : ℕ) : QuasiFun (jobRun c t d) :=
  (polyFun_snd.quasiFun.pair (polyFun_fst.comp_quasiFun (quasiFun_upccSplitFamily c t d))).comp_poly
    aggnPolyFun_restoreFamily

/-! ## The UPCC calls are small -/

/-- A bound on the encoding of `[0, m)`. -/
def rangeB (m : ℕ) : ℕ := 1 + m * (2 * (m + 2) + 1)

/-- A bound on the encoding of the pairs of `[0, m)`. -/
def pairsB (m : ℕ) : ℕ := 1 + m ^ 2 * (2 * (1 + 2 * (2 * rangeB m + 1)) + 1)

/-- A bound on the encoding of a recoded configuration on `[0, m)`. -/
def recodeB (m : ℕ) : ℕ := 2 * rangeB m + 2 * (1 + m ^ 2 * (2 * (2 * pairsB m + 2 * (m * m + 2)) + 1))

theorem size_range_le (m : ℕ) : Enc.size (List.range m) ≤ rangeB m :=
  size_natList_le (by simp) (fun a ha => List.mem_range.1 ha)

theorem size_pairs_le (m : ℕ) : Enc.size (tuplesOf (List.range m) 2) ≤ pairsB m := by
  have h := size_tuplesOf_le (List.range m) 2
  rw [List.length_range] at h
  have h2 := size_range_le m
  unfold pairsB
  refine h.trans ?_
  gcongr

/-- **The recoded configuration is small**: its colors are ranks among at most `m²` codes. -/
theorem size_sbipRecode_le {p : RawConfig} {m : ℕ} (hp : p.1 = List.range m) :
    Enc.size (sbipRecode p) ≤ recodeB m := by
  have hcodes : (sbipCodes p).length ≤ m * m := by
    unfold sbipCodes
    refine (length_dedupG_le _).trans ?_
    rw [List.length_map, hp]
    change (List.range m ×ˢ List.range m).length ≤ m * m
    rw [List.length_product, List.length_range]
  have hrow : ∀ r ∈ (tuplesOf p.1 2).map (fun t => sbipRecodeRow (p, t)),
      Enc.size r ≤ 2 * pairsB m + 2 * (m * m + 2) := by
    intro r hr
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hr
    have h1 := size_pair_le' (sbipRecodeRow (p, t))
    have h2 : Enc.size (sbipRecodeRow (p, t)).1 ≤ pairsB m := by
      show Enc.size t ≤ _
      rw [hp] at ht
      exact (size_mem_le ht).trans (size_pairs_le m)
    have h3 : Enc.size (sbipRecodeRow (p, t)).2 ≤ m * m + 2 := by
      show Enc.size (rankIn (sbipCodes p, [tblGet (p.2, t)])) ≤ _
      have hr : rankIn (sbipCodes p, [tblGet (p.2, t)]) ≤ m * m := by
        unfold rankIn
        exact (List.length_filter_le _ _).trans hcodes
      exact (size_nat_le_add_two _).trans (by omega)
    omega
  have hlen : ((tuplesOf p.1 2).map (fun t => sbipRecodeRow (p, t))).length = m ^ 2 := by
    rw [List.length_map, length_tuplesOf, hp, List.length_range]
  have hrows := size_list_le_of_entries _ _ hrow
  rw [hlen] at hrows
  have hpair := size_pair_le' (sbipRecode p)
  have hfst : Enc.size (sbipRecode p).1 ≤ rangeB m := by
    show Enc.size p.1 ≤ _
    rw [hp]; exact size_range_le m
  have hsnd : Enc.size (sbipRecode p).2 ≤
      1 + m ^ 2 * (2 * (2 * pairsB m + 2 * (m * m + 2)) + 1) := hrows
  unfold recodeB
  omega

/-- The length of the encodings of the domain list and of the threshold. -/
def domThrSize (g : AmbientGIn) : ℕ := Enc.size g.1.1.2.2 + Enc.size g.2

/-- A bound on the encoding of a UPCC call, in terms of `domThrSize`. -/
def jobB (D : ℕ) : ℕ :=
  2 * (2 * recodeB D + 2 * (2 * (2 * D + 2) + 2 * (2 * D + 2))) +
    2 * (2 * D + 2 * (1 + D * (2 * D + 1)))

theorem size_mul_nat_le {B : ℕ} (a b : ℕ) (hb : b ≤ B) : Enc.size (a * b) ≤ Enc.size a + B := by
  have h1 := size_mul_le a b
  have h2 := size_le_self b
  rw [Small.size_nat, Small.size_nat]
  omega

set_option maxHeartbeats 1000000 in
/-- **Every UPCC call is small**: its encoding is polynomial in the lengths of the domain list
and of the threshold, whatever the arity and the relations. -/
theorem size_job_le (g : AmbientGIn) {it : ExtItem} (hit : it ∈ stageA (g, ambPad g))
    {j : UpccJob} (hj : j ∈ it.2) : Enc.size j ≤ jobB (domThrSize g) := by
  obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hit
  obtain ⟨xs, hxs, rfl⟩ := List.mem_map.1 ho
  set z := padDesignAt (ambToG g, ambPad g) xs with hz
  set O := designReadExit z with hO
  change j ∈ (extItem (g, O)).2 at hj
  unfold extItem at hj
  cases hP : O.1 with
  | some P => rw [hP] at hj; simp at hj
  | none =>
    rw [hP] at hj
    cases hq : O.2.2 with
    | none => rw [hq] at hj; simp at hj
    | some q =>
      rw [hq] at hj
      simp only [Option.elim_none, Option.elim_some, List.mem_singleton] at hj
      subst hj
      obtain ⟨-, -, hdl, hqe⟩ := designReadExit_upcc (z := z) hq
      have hdomD : Enc.size g.1.1.2.2 ≤ domThrSize g := Nat.le_add_right _ _
      have hthD : Enc.size g.2 ≤ domThrSize g := Nat.le_add_left _ _
      set D := domThrSize g with hD
      set dom := g.1.1.2.2 with hdom
      have hnD : dom.length ≤ D := (length_le_size dom).trans hdomD
      -- the dominant points are domain points
      have hzdom : z.1.2.1 = dom := by
        rw [hz]
        show (padPipeline321 ((ambToG g).1, ambPad g)).1 = _
        rw [fst_padPipeline321]; rfl
      have hsub : ∀ a ∈ O.2.1, a ∈ dom := by
        intro a ha
        rw [hdl] at ha
        unfold dominantList at ha
        rw [hzdom] at ha
        exact List.mem_of_mem_filter ha
      have hmlen : O.2.1.length ≤ dom.length := by
        rw [hdl]; unfold dominantList; rw [hzdom]; exact List.length_filter_le _ _
      have hmD : O.2.1.length ≤ D := hmlen.trans hnD
      -- the configuration
      have hqsize : Enc.size q ≤ recodeB D := by
        rw [hqe]
        refine (size_sbipRecode_le (m := O.2.1.length) ?_).trans ?_
        · rw [hdl]; rfl
        · unfold recodeB pairsB rangeB; gcongr
      -- the threshold
      have ha : Enc.size g.2.1 ≤ D := (size_fst_le' g.2).trans hthD
      have hb : Enc.size g.2.2 ≤ D := (size_snd_le' g.2).trans hthD
      have hthr : Enc.size ((g.2.1 * dom.length, g.2.2 * O.2.1.length) : ℕ × ℕ) ≤
          2 * (2 * D + 2) + 2 * (2 * D + 2) := by
        have h1 := size_pair_le' ((g.2.1 * dom.length, g.2.2 * O.2.1.length) : ℕ × ℕ)
        have h2 := size_mul_nat_le g.2.1 dom.length hnD
        have h3 := size_mul_nat_le g.2.2 O.2.1.length hmD
        simp only at h1
        omega
      -- the dictionary
      have hdl' : Enc.size O.2.1 ≤ 1 + D * (2 * D + 1) := by
        have h1 := size_list_le_of_entries O.2.1 D (fun a ha => (size_mem_le (hsub a ha)).trans
          hdomD)
        refine h1.trans ?_
        gcongr
      have hdict : Enc.size ((dom, O.2.1) : List ℕ × List ℕ) ≤
          2 * D + 2 * (1 + D * (2 * D + 1)) := by
        have h1 := size_pair_le' ((dom, O.2.1) : List ℕ × List ℕ)
        simp only at h1
        omega
      have hin : Enc.size (extendedUpccInput ((g, O), q)) ≤
          2 * recodeB D + 2 * (2 * (2 * D + 2) + 2 * (2 * D + 2)) := by
        have h1 := size_pair_le' (extendedUpccInput ((g, O), q))
        have e : (extendedUpccInput ((g, O), q)).2 =
            ((g.2.1 * dom.length, g.2.2 * O.2.1.length) : ℕ × ℕ) := rfl
        have e1 : (extendedUpccInput ((g, O), q)).1 = q := rfl
        rw [e, e1] at h1
        omega
      have h1 := size_pair_le' (upccJob ((g, O), q))
      have e : (upccJob ((g, O), q)).2 = ((dom, O.2.1) : List ℕ × List ℕ) := rfl
      have e1 : (upccJob ((g, O), q)).1 = extendedUpccInput ((g, O), q) := rfl
      rw [e, e1] at h1
      unfold jobB
      omega

theorem polyBound_jobB : PolyBound jobB := by
  have hr : PolyBound rangeB :=
    (polyBound_const 1).add (polyBound_id.mul (((polyBound_const 2).mul
      (polyBound_id.add (polyBound_const 2))).add (polyBound_const 1)))
  have hsq : PolyBound (fun m : ℕ => m ^ 2) :=
    (polyBound_id.mul polyBound_id).mono (fun m => by rw [sq])
  have hp : PolyBound pairsB :=
    (polyBound_const 1).add (hsq.mul (((polyBound_const 2).mul ((polyBound_const 1).add
      ((polyBound_const 2).mul (((polyBound_const 2).mul hr).add (polyBound_const 1))))).add
      (polyBound_const 1)))
  have hrc : PolyBound recodeB :=
    ((polyBound_const 2).mul hr).add ((polyBound_const 2).mul ((polyBound_const 1).add
      (hsq.mul (((polyBound_const 2).mul (((polyBound_const 2).mul hp).add
        ((polyBound_const 2).mul ((polyBound_id.mul polyBound_id).add (polyBound_const 2))))).add
        (polyBound_const 1)))))
  have hlin : PolyBound (fun D : ℕ => 2 * D + 2) :=
    ((polyBound_const 2).mul polyBound_id).add (polyBound_const 2)
  exact ((polyBound_const 2).mul (((polyBound_const 2).mul hrc).add ((polyBound_const 2).mul
    (((polyBound_const 2).mul hlin).add ((polyBound_const 2).mul hlin))))).add
    ((polyBound_const 2).mul (((polyBound_const 2).mul polyBound_id).add
      ((polyBound_const 2).mul ((polyBound_const 1).add (polyBound_id.mul
        (((polyBound_const 2).mul polyBound_id).add (polyBound_const 1)))))))

/-! ## The machine -/

/-- The quasipolynomial witness form `2^{(log₂ m + 2)^c}`. -/
def qw (c m : ℕ) : ℕ := 2 ^ ((Nat.log 2 m + 2) ^ c)

theorem qw_mono (c : ℕ) : Monotone (qw c) := fun _ _ h => quasiPolyBound_witness_mono c h

theorem QuasiPolyBound.pow_const {T : ℕ → ℕ} (h : QuasiPolyBound T) :
    ∀ e : ℕ, QuasiPolyBound (fun n => T n ^ e)
  | 0 => (polyBound_const 1).quasiPoly.mono (fun n => by simp)
  | e + 1 => ((QuasiPolyBound.pow_const h e).mul h).mono (fun n => by rw [pow_succ])

set_option maxHeartbeats 1000000 in
/-- **A polynomial routine of the input padded with `n^k` zeros runs in time
`poly(size) · n^{O(k)}` on the input**, with an answer of the same size.  The general form of
`Algo.exists_designPadProg`: `n` and `k` are any two polynomial functions of the input, `k`
bounded by the size. -/
theorem exists_padProgGen {α β : Type} [Enc α] [Inhabited α] [Enc β] (nf kf : α → ℕ)
    (hn : PolyFun nf) (hk : PolyFun kf) (hkle : ∀ a, kf a ≤ Enc.size a)
    (f : α × List ℕ → β) (hf : PolyFun f) :
    ∃ (P : Program) (C d : ℕ), Wf P ∧ ∀ a : α,
      RunsOn 16 P a (f (a, List.replicate (nf a ^ kf a) 0))
        (C * (Enc.size a + 1) ^ d * (nf a + 1) ^ (d * kf a)) ∧
      Enc.size (f (a, List.replicate (nf a ^ kf a) 0)) ≤
        C * (Enc.size a + 1) ^ d * (nf a + 1) ^ (d * kf a) := by
  have hN : PolyFun (fun a : α => nf a ^ kf a) :=
    PolyFun.pow hn hk (q := id) hkle polyBound_id
  have h1 : PolyFun (fun a : α => ((nf a ^ kf a, (a, ([] : List ℕ))) : ℕ × (α × List ℕ))) :=
    hN.pair (polyFun_id.pair (polyFun_const []))
  obtain ⟨P1, c1, d1, hP1, -⟩ := polyFun_witness h1
  obtain ⟨Ppad, ca, da, hPadwf, hPad⟩ := exists_padProg α
  have h2 : PolyFun (fun x : ℕ × (α × List ℕ) => f x.2) := polyFun_snd.comp hf
  obtain ⟨P2, c2, d2, hP2, hS2⟩ := polyFun_witness h2
  obtain ⟨G, hGd⟩ : ∃ G : ℕ → ℕ, ∀ t, G t = pw c1 d1 t + pw ca da t + pw c2 d2 (20 * t + 10) :=
    ⟨_, fun _ => rfl⟩
  have hG : PolyBound G := by
    rw [show G = fun t => pw c1 d1 t + pw ca da t + pw c2 d2 (20 * t + 10) from funext hGd]
    exact ((polyBound_pw c1 d1).add (polyBound_pw ca da)).add ((polyBound_pw c2 d2).comp
      (((polyBound_const 20).mul polyBound_id).add (polyBound_const 10)))
  obtain ⟨c, d, hcd⟩ := hG
  refine ⟨RAM.seq P1 (RAM.seq Ppad P2), c * 2 ^ d, d,
    wf_seq (hP1.runsOn default).wf (wf_seq hPadwf (hP2.runsOn default).wf), fun g => ?_⟩
  set n := nf g with hn
  set k := kf g with hk
  set N := n ^ k with hNdef
  have r1 : RunsOn 16 P1 g ((N, (g, ([] : List ℕ))) : ℕ × (α × List ℕ))
      (c1 * (Enc.size g + 1) ^ d1) := hP1.runsOn g
  have r2 := hPad g N
  have r3 : RunsOn 16 P2 ((0, (g, List.replicate N 0)) : ℕ × (α × List ℕ))
      (f (g, List.replicate N 0))
      (c2 * (Enc.size ((0, (g, List.replicate N 0)) : ℕ × (α × List ℕ)) + 1) ^ d2) :=
    hP2.runsOn ((0, (g, List.replicate N 0)) : ℕ × (α × List ℕ))
  have r := r1.seq (r2.seq r3)
  obtain ⟨t, ht⟩ : ∃ t, t = Enc.size g + N := ⟨_, rfl⟩
  have hs0 : Enc.size ((0, (g, List.replicate N 0)) : ℕ × (α × List ℕ)) ≤ 20 * t + 10 := by
    have e1 := size_pair_le' ((0, (g, List.replicate N 0)) : ℕ × (α × List ℕ))
    have e2 := size_pair_le' ((g, List.replicate N 0) : α × List ℕ)
    have e3 := size_replicate_zero_le N
    have e4 : Enc.size (0 : ℕ) = 2 := by rw [Small.size_nat]; simp
    simp only at e1 e2
    omega
  have t1 : pw c1 d1 (Enc.size g) ≤ pw c1 d1 t := pw_mono c1 d1 (by omega)
  have t2 : pw ca da (Enc.size g + N) ≤ pw ca da t := pw_mono ca da (by omega)
  have t3 : pw c2 d2 (Enc.size ((0, (g, List.replicate N 0)) : ℕ × (α × List ℕ)))
      ≤ pw c2 d2 (20 * t + 10) := pw_mono c2 d2 hs0
  have t5 := hcd t
  rw [hGd] at t5
  have t6 : c * (t + 1) ^ d ≤ c * 2 ^ d * (Enc.size g + 1) ^ d * (n + 1) ^ (d * k) := by
    have hle : t + 1 ≤ 2 * ((Enc.size g + 1) * (n + 1) ^ k) := by
      rw [ht]; exact add_pow_le _ _ _
    have hp := Nat.pow_le_pow_left hle d
    rw [mul_pow, mul_pow, ← pow_mul, mul_comm k d] at hp
    calc c * (t + 1) ^ d ≤ c * (2 ^ d * ((Enc.size g + 1) ^ d * (n + 1) ^ (d * k))) :=
          Nat.mul_le_mul_left c hp
      _ = c * 2 ^ d * (Enc.size g + 1) ^ d * (n + 1) ^ (d * k) := by ring
  have e1 : pw c1 d1 (Enc.size g) = c1 * (Enc.size g + 1) ^ d1 := rfl
  have e3 : pw c2 d2 (Enc.size ((0, (g, List.replicate N 0)) : ℕ × (α × List ℕ)))
      = c2 * (Enc.size ((0, (g, List.replicate N 0)) : ℕ × (α × List ℕ)) + 1) ^ d2 := rfl
  refine ⟨r.mono ?_, ?_⟩
  · show c1 * (Enc.size g + 1) ^ d1 + (pw ca da (Enc.size g + N)
        + c2 * (Enc.size ((0, (g, List.replicate N 0)) : ℕ × (α × List ℕ)) + 1) ^ d2)
      ≤ c * 2 ^ d * (Enc.size g + 1) ^ d * (n + 1) ^ (d * k)
    omega
  · have hs := hS2 ((0, (g, List.replicate N 0)) : ℕ × (α × List ℕ))
    simp only at hs
    omega

set_option maxHeartbeats 4000000 in
/-- **One outcome on the RAM.**  The answers of an outcome whose UPCC calls have encodings at
most `J` are computed in time polynomial in the size of the outcome and in the time and output
bounds `qw cT J`, `qw cS J` of Theorem 9.2.1 at size `J`. -/
theorem exists_itemProg (c t d : ℕ) :
    ∃ (P : Program) (cT cS cG dG : ℕ), Wf P ∧ ∀ (it : ExtItem) (J : ℕ),
      (∀ j ∈ it.2, Enc.size j ≤ J) →
      RunsOn 16 P it (itemRun c t d it) (cG * (Enc.size it + qw cT J + qw cS J + 1) ^ dG) ∧
      Enc.size (itemRun c t d it) ≤ cG * (Enc.size it + qw cT J + qw cS J + 1) ^ dG := by
  obtain ⟨⟨Pj, Tj, ⟨cT, hTj⟩, hPj⟩, ⟨cS, hSj⟩⟩ := quasiFun_jobRun c t d
  obtain ⟨Pf, cf, df, hPf, -⟩ :=
    polyFun_witness (polyFun_fst : PolyFun (fun it : ExtItem => it.1))
  obtain ⟨Ps, cs, ds, hPs, -⟩ :=
    polyFun_witness (polyFun_snd : PolyFun (fun it : ExtItem => it.2))
  obtain ⟨Pl, cl, dl, hPl, -⟩ := polyFun_witness
    (polyFun_flatten : PolyFun (fun l : List (List RawAlignOutcome) => l.flatten))
  obtain ⟨Pa, ca, da, hPa, -⟩ := polyFun_witness
    (polyFun_append : PolyFun (fun p : List RawAlignOutcome × List RawAlignOutcome => p.1 ++ p.2))
  obtain ⟨FM, cM, dM, hFM⟩ := MapFold.exists_mapProg (α := UpccJob) (β := List RawAlignOutcome)
  have hPjwf : Wf Pj := (hPj.runsOn default).wf
  obtain ⟨hFMwf, hFMrun⟩ := hFM Pj hPjwf
  obtain ⟨B1, hB1⟩ : ∃ B1 : ℕ → ℕ, ∀ Y, B1 Y = 1 + Y * (2 * Y + 1) := ⟨_, fun _ => rfl⟩
  obtain ⟨B2, hB2⟩ : ∃ B2 : ℕ → ℕ, ∀ Y, B2 Y = 1 + B1 Y * (2 * B1 Y + 1) := ⟨_, fun _ => rfl⟩
  have hB1p : PolyBound B1 := by
    rw [show B1 = fun Y => 1 + Y * (2 * Y + 1) from funext hB1]
    exact (polyBound_const 1).add (polyBound_id.mul (((polyBound_const 2).mul polyBound_id).add
      (polyBound_const 1)))
  have hB2p : PolyBound B2 := by
    rw [show B2 = fun Y => 1 + B1 Y * (2 * B1 Y + 1) from funext hB2]
    exact (polyBound_const 1).add (hB1p.mul (((polyBound_const 2).mul hB1p).add
      (polyBound_const 1)))
  obtain ⟨G, hGd⟩ : ∃ G : ℕ → ℕ, ∀ Y, G Y = 38 * Y + 19 * B2 Y + 10 * pw cf df Y
      + 10 * (pw cs ds Y + (100 * (Y * Y) + (Y + 2) * pw cM dM (Y + B1 Y)) + pw cl dl (B1 Y))
      + 376 + pw ca da (2 * Y + 2 * B2 Y) + (Y + B2 Y) := ⟨_, fun _ => rfl⟩
  have hG : PolyBound G := by
    rw [show G = fun Y => 38 * Y + 19 * B2 Y + 10 * pw cf df Y
      + 10 * (pw cs ds Y + (100 * (Y * Y) + (Y + 2) * pw cM dM (Y + B1 Y)) + pw cl dl (B1 Y))
      + 376 + pw ca da (2 * Y + 2 * B2 Y) + (Y + B2 Y) from funext hGd]
    have hid := polyBound_id
    have a1 := ((polyBound_const 38).mul hid).add ((polyBound_const 19).mul hB2p)
    have a2 := a1.add ((polyBound_const 10).mul (polyBound_pw cf df))
    have a3 : PolyBound (fun Y => pw cs ds Y + (100 * (Y * Y) + (Y + 2) * pw cM dM (Y + B1 Y))
        + pw cl dl (B1 Y)) :=
      ((polyBound_pw cs ds).add (((polyBound_const 100).mul (hid.mul hid)).add
        ((hid.add (polyBound_const 2)).mul ((polyBound_pw cM dM).comp (hid.add hB1p))))).add
        ((polyBound_pw cl dl).comp hB1p)
    have a4 := (a2.add ((polyBound_const 10).mul a3)).add (polyBound_const 376)
    have a5 := a4.add ((polyBound_pw ca da).comp (((polyBound_const 2).mul hid).add
      ((polyBound_const 2).mul hB2p)))
    exact a5.add (hid.add hB2p)
  obtain ⟨cG, dG, hcG⟩ := hG
  refine ⟨RAM.seq (Pairing.pairProg 16 Pf (RAM.seq Ps (RAM.seq (FM Pj) Pl))) Pa, cT, cS, cG, dG,
    wf_seq (Pairing.wf_pairProg 16 (hPf.runsOn default).wf
      (wf_seq (hPs.runsOn default).wf (wf_seq hFMwf (hPl.runsOn default).wf)))
      (hPa.runsOn default).wf, fun it J hJ => ?_⟩
  set X := Enc.size it with hX
  set Qt := qw cT J with hQt
  set Qs := qw cS J with hQs
  set M := it.2.map (jobRun c t d) with hM
  set V := M.flatten with hV
  -- the runs
  have rf : RunsOn 16 Pf it it.1 (pw cf df X) := hPf.runsOn it
  have rs : RunsOn 16 Ps it it.2 (pw cs ds X) := hPs.runsOn it
  have rm : RunsOn 16 (FM Pj) it.2 M (100 * (it.2.map (fun j => Tj (Enc.size j))).sum
      + (it.2.length + 2) * pw cM dM (Enc.size it.2 + Enc.size M)) :=
    hFMrun (jobRun c t d) (fun j => Tj (Enc.size j)) it.2 (fun j _ => hPj.runsOn j)
  have rl : RunsOn 16 Pl M V (pw cl dl (Enc.size M)) := hPl.runsOn M
  have rg := rs.seq (rm.seq rl)
  have rp := RunsOn.pair (K := 16) (by norm_num) rf rg
  have ra : RunsOn 16 Pa ((it.1, V) : List RawAlignOutcome × List RawAlignOutcome) (it.1 ++ V)
      (pw ca da (Enc.size ((it.1, V) : List RawAlignOutcome × List RawAlignOutcome))) :=
    hPa.runsOn _
  have r := rp.seq ra
  -- the sizes
  have hX1 : Enc.size it.1 ≤ X := size_fst_le' it
  have hX2 : Enc.size it.2 ≤ X := size_snd_le' it
  have hlen : it.2.length ≤ X := (length_le_size _).trans hX2
  have hτ : ∀ j ∈ it.2, Tj (Enc.size j) ≤ Qt := fun j hj =>
    (hTj _).trans (qw_mono cT (hJ j hj))
  have hsum : (it.2.map (fun j => Tj (Enc.size j))).sum ≤ X * Qt := by
    have h := List.sum_le_card_nsmul (it.2.map (fun j => Tj (Enc.size j))) Qt (by
      intro x hx
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
      exact hτ j hj)
    rw [List.length_map, smul_eq_mul] at h
    exact h.trans (Nat.mul_le_mul_right _ hlen)
  have hent : ∀ b ∈ M, Enc.size b ≤ Qs := by
    intro b hb
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hb
    exact (hSj j).trans (qw_mono cS (hJ j hj))
  set Y := X + Qt + Qs with hY
  have hMs : Enc.size M ≤ B1 Y := by
    have h := size_list_le_of_entries M Qs hent
    rw [List.length_map] at h
    rw [hB1]
    refine h.trans ?_
    have : it.2.length * (2 * Qs + 1) ≤ Y * (2 * Y + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  have hVs : Enc.size V ≤ B2 Y := by
    have h := size_flatten_le M
    rw [hB2]
    refine h.trans ?_
    have : Enc.size M * (2 * Enc.size M + 1) ≤ B1 Y * (2 * B1 Y + 1) :=
      Nat.mul_le_mul hMs (by omega)
    omega
  have hpair : Enc.size ((it.1, V) : List RawAlignOutcome × List RawAlignOutcome)
      ≤ 2 * Y + 2 * B2 Y := by
    have h := size_pair_le' ((it.1, V) : List RawAlignOutcome × List RawAlignOutcome)
    simp only at h
    omega
  have p1 : pw cf df X ≤ pw cf df Y := pw_mono _ _ (by omega)
  have p2 : pw cs ds X ≤ pw cs ds Y := pw_mono _ _ (by omega)
  have p3 : (it.2.length + 2) * pw cM dM (Enc.size it.2 + Enc.size M) ≤
      (Y + 2) * pw cM dM (Y + B1 Y) :=
    Nat.mul_le_mul (by omega) (pw_mono _ _ (by omega))
  have p4 : pw cl dl (Enc.size M) ≤ pw cl dl (B1 Y) := pw_mono _ _ hMs
  have p5 : pw ca da (Enc.size ((it.1, V) : List RawAlignOutcome × List RawAlignOutcome)) ≤
      pw ca da (2 * Y + 2 * B2 Y) := pw_mono _ _ hpair
  have p6 : X * Qt ≤ Y * Y := Nat.mul_le_mul (by omega) (by omega)
  have hGY := hcG Y
  rw [hGd] at hGY
  have hout : Enc.size (it.1 ++ V) ≤ Y + B2 Y := by
    have := size_append_le it.1 V
    omega
  have e : Y + 1 = Enc.size it + qw cT J + qw cS J + 1 := rfl
  refine ⟨r.mono ?_, ?_⟩
  · rw [← e]
    omega
  · show Enc.size (it.1 ++ V) ≤ _
    rw [← e]
    omega

set_option maxHeartbeats 4000000 in
/-- **The routine of Theorem 9.2.3 for every arity, on the RAM.**  One program computes
`Algo.extendedSplitAll c t d` on every input within
`C · (size + 1)^E · (n + 1)^{E·k} · Q(D)` steps, with `Q` quasipolynomial and `D = domThrSize`,
the length of the encodings of the domain list and of the threshold. -/
theorem exists_extendedSplitAllProg (c t d : ℕ) :
    ∃ (P : Program) (C E : ℕ) (Q : ℕ → ℕ), QuasiPolyBound Q ∧ Wf P ∧ ∀ g : AmbientGIn,
      RunsOn 16 P g (extendedSplitAll c t d g)
        (C * (Enc.size g + 1) ^ E * (g.1.1.2.2.length + 1) ^ (E * g.1.1.1.length) *
          Q (domThrSize g)) := by
  have hn : PolyFun (fun g : AmbientGIn => g.1.1.2.2.length) :=
    ((((polyFun_fst.comp polyFun_fst).comp polyFun_snd).comp polyFun_snd).comp polyFun_length)
  have hk : PolyFun (fun g : AmbientGIn => g.1.1.1.length) :=
    (((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_length)
  have hkle : ∀ g : AmbientGIn, g.1.1.1.length ≤ Enc.size g := fun g =>
    (length_le_size _).trans ((size_fst_le' g.1.1).trans ((size_fst_le' g.1).trans
      (size_fst_le' g)))
  obtain ⟨PA, CA, eA, hPAwf, hA⟩ := exists_padProgGen (fun g : AmbientGIn => g.1.1.2.2.length)
    (fun g : AmbientGIn => g.1.1.1.length) hn hk hkle stageA polyFun_stageA
  obtain ⟨PI, cT, cS, cG, dG, hPIwf, hI⟩ := exists_itemProg c t d
  obtain ⟨FB, cB, dB, hFB⟩ := MapFold.exists_mapProg (α := ExtItem) (β := List RawAlignOutcome)
  obtain ⟨hFBwf, hFBrun⟩ := hFB PI hPIwf
  obtain ⟨Pl, cl, dl, hPl, -⟩ := polyFun_witness
    (polyFun_flatten : PolyFun (fun l : List (List RawAlignOutcome) => l.flatten))
  obtain ⟨Ti, hTi⟩ : ∃ Ti : ℕ → ℕ, ∀ Y, Ti Y = cG * (Y + 1) ^ dG := ⟨_, fun _ => rfl⟩
  obtain ⟨Mb, hMb⟩ : ∃ Mb : ℕ → ℕ, ∀ Y, Mb Y = 1 + Y * (2 * Ti Y + 1) := ⟨_, fun _ => rfl⟩
  obtain ⟨H, hHd⟩ : ∃ H : ℕ → ℕ, ∀ Y, H Y = Y + (100 * (Y * Ti Y)
      + (Y + 2) * pw cB dB (Y + Mb Y)) + pw cl dl (Mb Y) := ⟨_, fun _ => rfl⟩
  have hTip : PolyBound Ti := by
    rw [show Ti = fun Y => cG * (Y + 1) ^ dG from funext hTi]; exact polyBound_witness cG dG
  have hMbp : PolyBound Mb := by
    rw [show Mb = fun Y => 1 + Y * (2 * Ti Y + 1) from funext hMb]
    exact (polyBound_const 1).add (polyBound_id.mul (((polyBound_const 2).mul hTip).add
      (polyBound_const 1)))
  have hH : PolyBound H := by
    rw [show H = fun Y => Y + (100 * (Y * Ti Y) + (Y + 2) * pw cB dB (Y + Mb Y))
      + pw cl dl (Mb Y) from funext hHd]
    exact (polyBound_id.add (((polyBound_const 100).mul (polyBound_id.mul hTip)).add
      ((polyBound_id.add (polyBound_const 2)).mul ((polyBound_pw cB dB).comp
        (polyBound_id.add hMbp))))).add ((polyBound_pw cl dl).comp hMbp)
  obtain ⟨cH, dH, hcH⟩ := hH
  refine ⟨RAM.seq PA (RAM.seq (FB PI) Pl), cH * (CA + 1) ^ dH, eA * dH,
    fun D => (qw cT (jobB D) + qw cS (jobB D) + 1) ^ dH, ?_,
    wf_seq hPAwf (wf_seq hFBwf (hPl.runsOn default).wf), fun g => ?_⟩
  · have h1 : QuasiPolyBound (fun D => qw cT (jobB D)) :=
      (quasiPolyBound_witness cT).comp_poly polyBound_jobB
    have h2 : QuasiPolyBound (fun D => qw cS (jobB D)) :=
      (quasiPolyBound_witness cS).comp_poly polyBound_jobB
    exact QuasiPolyBound.pow_const ((h1.add h2).add (polyBound_const 1).quasiPoly) dH
  · rw [extendedSplitAll_eq_stages]
    obtain ⟨rA, hsA⟩ := hA g
    set n := g.1.1.2.2.length with hn'
    set k := g.1.1.1.length with hk'
    set S := Enc.size g with hS
    set TA := CA * (S + 1) ^ eA * (n + 1) ^ (eA * k) with hTA
    set l := stageA (g, ambPad g) with hl
    change RunsOn 16 PA g l TA at rA
    change Enc.size l ≤ TA at hsA
    set J := jobB (domThrSize g) with hJ
    set Qt := qw cT J with hQt
    set Qs := qw cS J with hQs
    set L := Enc.size l with hL
    set Y := TA + Qt + Qs with hY
    have hitem : ∀ it ∈ l, RunsOn 16 PI it (itemRun c t d it)
        (cG * (Enc.size it + Qt + Qs + 1) ^ dG) ∧
        Enc.size (itemRun c t d it) ≤ cG * (Enc.size it + Qt + Qs + 1) ^ dG :=
      fun it hit => hI it J (fun j hj => size_job_le g hit hj)
    have hitY : ∀ it ∈ l, cG * (Enc.size it + Qt + Qs + 1) ^ dG ≤ Ti Y := by
      intro it hit
      rw [hTi]
      have := size_mem_le hit
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    set R := l.map (itemRun c t d) with hR
    have rB : RunsOn 16 (FB PI) l R
        (100 * (l.map (fun it => cG * (Enc.size it + Qt + Qs + 1) ^ dG)).sum
          + (l.length + 2) * pw cB dB (L + Enc.size R)) :=
      hFBrun _ _ l (fun it hit => (hitem it hit).1)
    have rC : RunsOn 16 Pl R R.flatten (pw cl dl (Enc.size R)) := hPl.runsOn R
    have r := rA.seq (rB.seq rC)
    have hlen : l.length ≤ Y := (length_le_size l).trans (by omega)
    have hsum : (l.map (fun it => cG * (Enc.size it + Qt + Qs + 1) ^ dG)).sum ≤ Y * Ti Y := by
      have h := List.sum_le_card_nsmul (l.map (fun it => cG * (Enc.size it + Qt + Qs + 1) ^ dG))
        (Ti Y) (by
          intro x hx
          obtain ⟨it, hit, rfl⟩ := List.mem_map.1 hx
          exact hitY it hit)
      rw [List.length_map, smul_eq_mul] at h
      exact h.trans (Nat.mul_le_mul_right _ hlen)
    have hRs : Enc.size R ≤ Mb Y := by
      have h := size_list_le_of_entries R (Ti Y) (by
        intro b hb
        obtain ⟨it, hit, rfl⟩ := List.mem_map.1 hb
        exact (hitem it hit).2.trans (hitY it hit))
      rw [List.length_map] at h
      rw [hMb]
      refine h.trans ?_
      have : l.length * (2 * Ti Y + 1) ≤ Y * (2 * Ti Y + 1) := Nat.mul_le_mul_right _ hlen
      omega
    have p1 : (l.length + 2) * pw cB dB (L + Enc.size R) ≤ (Y + 2) * pw cB dB (Y + Mb Y) :=
      Nat.mul_le_mul (by omega) (pw_mono _ _ (by omega))
    have p2 : pw cl dl (Enc.size R) ≤ pw cl dl (Mb Y) := pw_mono _ _ hRs
    have hHY := hcH Y
    rw [hHd] at hHY
    refine r.mono ?_
    have hmain : TA + (100 * (l.map (fun it => cG * (Enc.size it + Qt + Qs + 1) ^ dG)).sum
        + (l.length + 2) * pw cB dB (L + Enc.size R)) + pw cl dl (Enc.size R)
        ≤ cH * (Y + 1) ^ dH := by
      have : 100 * (l.map (fun it => cG * (Enc.size it + Qt + Qs + 1) ^ dG)).sum
          ≤ 100 * (Y * Ti Y) := by omega
      omega
    have hY1 : Y + 1 ≤ (TA + 1) * (Qt + Qs + 1) := by
      have := Nat.zero_le (TA * (Qt + Qs))
      nlinarith
    have hW : 1 ≤ (S + 1) ^ eA * (n + 1) ^ (eA * k) :=
      Nat.one_le_iff_ne_zero.2 (by positivity)
    have hTA1 : TA + 1 ≤ (CA + 1) * ((S + 1) ^ eA * (n + 1) ^ (eA * k)) := by
      rw [hTA]; nlinarith
    have hexp : eA * k * dH = eA * dH * k := by ring
    show _ ≤ cH * (CA + 1) ^ dH * (S + 1) ^ (eA * dH) * (n + 1) ^ (eA * dH * k) *
      (Qt + Qs + 1) ^ dH
    refine le_trans (by omega) (?_ : cH * (Y + 1) ^ dH ≤ _)
    calc cH * (Y + 1) ^ dH
        ≤ cH * ((CA + 1) * ((S + 1) ^ eA * (n + 1) ^ (eA * k)) * (Qt + Qs + 1)) ^ dH := by
          gcongr
          exact hY1.trans (Nat.mul_le_mul_right _ hTA1)
      _ = cH * (CA + 1) ^ dH * (S + 1) ^ (eA * dH) * (n + 1) ^ (eA * dH * k) *
            (Qt + Qs + 1) ^ dH := by
          rw [mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul, hexp]
          ring

/-! ## The multiplicative cost -/

theorem length_padReadFamily_le {g : AmbientGIn} (hkn : g.1.1.1.length ≤ g.1.1.2.2.length) :
    (padReadFamily (ambToG g, ambPad g)).length ≤ (g.1.1.2.2.length + 1) ^ g.1.1.1.length := by
  rw [padReadFamily, List.length_map, padVersions]
  cases padDesignProcedure (ambToG g, ambPad g) with
  | none => simp
  | some xs =>
      simp only [Option.elim_some]
      refine (List.length_filter_le _ _).trans ?_
      rw [padVersionRows_ambToG hkn]
      have hj : (g.1.1.1.take xs.length).length ≤ g.1.1.1.length := by
        rw [List.length_take]; exact min_le_right _ _
      show ((aggTable g.1.1.1.length (g.1.1.1.take xs.length, g.1.1.2.2, g.1.1.2.2)).2.map
        Prod.fst).length ≤ _
      rw [aggTable_of_guard (a := (g.1.1.1.take xs.length, g.1.1.2.2, g.1.1.2.2))
        (hj.trans (le_guardBound_self hkn)), keys_tupleTable, length_tuplesOf]
      exact (pow_le_pow_of_le_of_le hj hkn).trans (Nat.pow_le_pow_left (by omega) _)

theorem length_itemRun_extItem_le (c t d : ℕ) (z : RawExtendedBranch) {B : ℕ}
    (hB : ∀ q, z.2.1 = none → z.2.2.2 = some q → (jobRun c t d (upccJob (z, q))).length ≤ B) :
    (itemRun c t d (extItem z)).length ≤ 1 + B := by
  obtain ⟨g, P, dl, q⟩ := z
  cases P with
  | some P => simp [itemRun, extItem]
  | none =>
      cases q with
      | none => simp [itemRun, extItem]
      | some q =>
          have := hB q rfl rfl
          simp only [itemRun, extItem, Option.elim_none, Option.elim_some, List.map_cons,
            List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, List.nil_append]
          omega

/-- **The multiplicative cost `q(n) n^{O(k)}`**: the family has at most `(n + 1)^k · Q(D)`
members, with `Q` quasipolynomial. -/
theorem exists_length_extendedSplitAll_le (c t d : ℕ) :
    ∃ Q : ℕ → ℕ, QuasiPolyBound Q ∧ ∀ g : AmbientGIn, g.1.1.1.length ≤ g.1.1.2.2.length →
      (extendedSplitAll c t d g).length ≤
        (g.1.1.2.2.length + 1) ^ g.1.1.1.length * Q (domThrSize g) := by
  obtain ⟨-, ⟨cS, hSj⟩⟩ := quasiFun_jobRun c t d
  refine ⟨fun D => 1 + qw cS (jobB D), ((polyBound_const 1).quasiPoly.add
    ((quasiPolyBound_witness cS).comp_poly polyBound_jobB)), fun g hkn => ?_⟩
  rw [extendedSplitAll_eq_stages, List.length_flatten, List.map_map]
  set B := qw cS (jobB (domThrSize g))
  have hitem : ∀ it ∈ stageA (g, ambPad g), (itemRun c t d it).length ≤ 1 + B := by
    intro it hit
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hit
    refine length_itemRun_extItem_le c t d _ (fun q hP hq => ?_)
    have hmem : upccJob ((g, o.2), q) ∈ (extItem (g, o.2)).2 := by
      unfold extItem
      rw [hP]
      simp only [Option.elim_none]
      rw [hq]
      simp
    exact (length_le_size _).trans ((hSj _).trans (qw_mono cS (size_job_le g hit hmem)))
  have h := List.sum_le_card_nsmul ((stageA (g, ambPad g)).map
    ((List.length ∘ itemRun c t d))) (1 + B) (by
      intro x hx
      obtain ⟨it, hit, rfl⟩ := List.mem_map.1 hx
      exact hitem it hit)
  rw [List.length_map, smul_eq_mul] at h
  refine h.trans (Nat.mul_le_mul_right _ ?_)
  rw [stageA, List.length_map]
  exact length_padReadFamily_le hkn

/-! ## Theorem 9.2.3 in the paper's form -/

/-- **Theorem 9.2.3 (Extended Design Lemma), §9.2, on the RAM, for every arity.**
*"Let `3/4 ≤ α < 1` be a threshold parameter.  Let `X = (Ω, R)` be a `k`-ary relational
structure with `n` vertices, `2 ≤ k ≤ n/4`, and relative strong symmetry defect `> 1 − α`.
Then at a multiplicative cost of `q(n) n^{O(k)}`, where `q(n)` is a quasipolynomial function, we
can find either (a) a canonical colored `α`-partition of the vertex set, or (b) a canonically
embedded nontrivial Johnson scheme on a subset `W ⊆ Ω` of size `|W| ≥ αn`.  (The time bounds do
not depend on `α`.)"*

For one choice of the bounds `t`, `d` of Theorem 9.2.2:

* **time**: one program computes the family `Algo.extendedSplitAll c t d g` on every input `g`
  within `C · (size g + 1)^E · (n + 1)^{E·k} · Q(D)` steps, where `Q` is quasipolynomial and
  `D = Algo.domThrSize g` is the length of the encodings of the domain list and of the threshold
  (`O(n log n)` plus the length of the threshold on a represented input);
* **multiplicative cost**: when `k ≤ n` the family has at most `(n + 1)^k · Q'(D)` members, with
  `Q'` quasipolynomial;
* **validity**: on every input satisfying the hypotheses of the theorem
  (`Algo.ExtendedInput`), the family is nonempty and each member is an outcome (a) or (b);
* **canonicity**: an isomorphism of two such inputs with the same arity, domain and threshold
  carries every member of the first family to a member of the second.

The factor `(size g + 1)^E` is the reading of the input (its relations may be arbitrarily many,
see the corrected paper entry on the running time of §8).  The time bound depends on `α` only
through the length of its encoding, as for Theorems 9.2.1 and 9.2.2. -/
theorem theorem_9_2_3_ram_all (c : ℕ) :
    ∃ t d, BipInputRunCanonical c t d ∧
      (∃ (P : Program) (C E : ℕ) (Q : ℕ → ℕ), QuasiPolyBound Q ∧ Wf P ∧ ∀ g : AmbientGIn,
        RunsOn 16 P g (extendedSplitAll c t d g)
          (C * (Enc.size g + 1) ^ E * (g.1.1.2.2.length + 1) ^ (E * g.1.1.1.length) *
            Q (domThrSize g))) ∧
      (∃ Q : ℕ → ℕ, QuasiPolyBound Q ∧ ∀ g : AmbientGIn, g.1.1.1.length ≤ g.1.1.2.2.length →
        (extendedSplitAll c t d g).length ≤
          (g.1.1.2.2.length + 1) ^ g.1.1.1.length * Q (domThrSize g)) ∧
      (∀ n g, ExtendedInput n g →
        (∃ p, p ∈ extendedSplitAll c t d g) ∧
        ∀ p ∈ extendedSplitAll c t d g, ∃ Z, decAlignOutcome n p = some Z ∧
          IsSplitOutcome (sbipAlphaValue g.2) Set.univ Z) ∧
      (∀ n (g g' : AmbientGIn), ExtendedInput n g → ExtendedInput n g' →
        g.1.1.1 = g'.1.1.1 → g.1.1.2.2 = g'.1.1.2.2 → g.2 = g'.2 →
        ∀ f : Equiv.Perm (Fin n),
        f ∈ KAryRelStruct.Iso (decRel n g.1.1.1.length g.1.2) (decRel n g.1.1.1.length g'.1.2) →
        ∀ p ∈ extendedSplitAll c t d g, ∃ p' ∈ extendedSplitAll c t d g',
          RawSplitOutcomeIso n f p p') := by
  obtain ⟨t, d, hcan, hv, hc⟩ := exists_extendedSplitAll_valid_canonical c
  exact ⟨t, d, hcan, exists_extendedSplitAllProg c t d, exists_length_extendedSplitAll_le c t d,
    hv, hc⟩

end Algo
