/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5): the Design Lemma procedure
(Sec. 8.2) bounded at an external degree. Not part of the faithful formalization.
-/
import Workspace.Explicit.NodeBounded
import Workspace.Algo.DesignReadExit
import Workspace.Algo.SplitDesignRun
import Workspace.Algo.SplitDesignCase3

/-!
# The Design Lemma, bounded at the degree

The procedure of Sec. 8.2 on the top domain (`Algo.ambientDesignProcedure`,
`Algo.ambientDesignVersions`, `Algo.ambientDesignReadFamily`), and its call in Sec. 9.7
(`Algo.designCallReadFamily`, `Algo.designCase3Graphs`), in the class `Explicit.TN` with
exponent `c + 1` (`c = 3` in Sec. 9.7, so exponent `4`): the loops enumerate the tuples of
length at most `(log₂ n + 1)^c` over a domain of at most `n` points, and every other step is
polynomial in the size of the data.
-/

namespace Explicit

open RAM Algo

namespace TN

/-! ## The scan of lines 02–08 -/

/-- The precondition of the scan at degree `n`: the ambient domain has at most `n` points, and
so has the vertex list of the table when the arity passes the guard. -/
def ScanPre (c n : ℕ) (a : AmbientDIn) : Prop :=
  a.1.length ≤ n ∧ (a.2.1.1.1.length ≤ guardBound c a.1.length → a.2.1.2.1.length ≤ n)

/-- Every state of the scan, at a degree bounding both domains. -/
theorem scan_state_size (c : ℕ) (a : AmbientDIn) (n : ℕ) (ha : ScanPre c n a) (j : ℕ)
    (hj : j ≤ (ambientScanSetUp c a).1) :
    Enc.size (scanStep^[j] (ambientScanSetUp c a).2) ≤
      4 * Enc.size a + 4 * (1 + 2 ^ (1 * lg n ^ (c + 1)) *
        (2 * (1 + lg n ^ c * (2 * Enc.size a + 1)) + 1)) +
      2 * ((1 + lg n ^ c * (2 * Enc.size a + 1)) + 2) := by
  classical
  obtain ⟨base, z⟩ := a
  obtain ⟨hbase, hdom⟩ := ha
  set S := Enc.size ((base, z) : AmbientDIn) with hS
  have hz : Enc.size z ≤ S := size_snd_le' ((base, z) : AmbientDIn)
  set T := 1 + lg n ^ c * (2 * S + 1) with hT
  set dom := z.1.2.1 with hdomdef
  have hdomS : Enc.size dom ≤ S :=
    ((size_fst_le' z.1.2).trans ((size_snd_le' z.1).trans (size_fst_le' z))).trans hz
  have hset : (ambientScanSetUp c (base, z)).2 = (((z, [[]]), none) : SState) := rfl
  rw [hset, scanStep_iterate, ← hdomdef]
  by_cases hg : z.1.1.1.length ≤ guardBound c base.length
  · have hdn := hdom hg
    have hj' : j ≤ z.1.1.1.length := by
      simpa [ambientScanSetUp, ambientScanRounds, hg] using hj
    have hB' : j ≤ (Nat.log 2 n + 1) ^ c := by
      refine le_trans (le_trans hj' hg) ?_
      rw [guardBound]
      exact Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.log_mono_right hbase) 1) c
    have hB : j ≤ lg n ^ c := le_trans hB' (Nat.pow_le_pow_left (by unfold lg; omega) c)
    have hentm : ∀ m ≤ j, ∀ t ∈ tuplesOf dom m, Enc.size t ≤ T := by
      intro m hm t ht
      obtain ⟨hlen, hmem⟩ := (mem_tuplesOf dom m t).1 ht
      have h := size_list_le_of_entries t S
        (fun x hx => le_trans (size_mem_le (hmem x hx)) hdomS)
      rw [hlen] at h
      have h2 : m * (2 * S + 1) ≤ lg n ^ c * (2 * S + 1) :=
        Nat.mul_le_mul_right _ (le_trans hm hB)
      omega
    have hcount : (tuplesOf dom j).length ≤ 2 ^ (1 * lg n ^ (c + 1)) := by
      rw [length_tuplesOf, one_mul]
      exact pow_le_quasi hdn hB'
    have hlist : Enc.size (tuplesOf dom j) ≤ 1 + 2 ^ (1 * lg n ^ (c + 1)) * (2 * T + 1) := by
      have h := size_list_le_of_entries (tuplesOf dom j) T (hentm j le_rfl)
      have h2 := Nat.mul_le_mul_right (2 * T + 1) hcount
      omega
    have hans : Enc.size (ansUpTo z j) ≤ T + 2 := by
      cases hA : ansUpTo z j with
      | none => rw [size_none]; omega
      | some xs =>
          obtain ⟨l, hl, hmem⟩ := ansUpTo_mem hA
          have hle : Enc.size xs ≤ T := hentm l (le_of_lt hl) xs hmem
          rw [size_some_eq]
          omega
    have hp1 := size_pair_le' ((z, tuplesOf dom j) : DIn × List (List ℕ))
    have hp2 := size_pair_le' (((z, tuplesOf dom j), ansUpTo z j) : SState)
    dsimp only at hp1 hp2
    omega
  · have hj0 : j = 0 := by simpa [ambientScanSetUp, ambientScanRounds, hg] using hj
    subst hj0
    have hp1 := size_pair_le' ((z, tuplesOf dom 0) : DIn × List (List ℕ))
    have hp2 := size_pair_le' (((z, tuplesOf dom 0), ansUpTo z 0) : SState)
    have h0 : Enc.size (tuplesOf dom 0) ≤ 4 := by
      have h := size_list_le_of_entries (tuplesOf dom 0) 1 (fun t ht => by
        rw [(mem_tuplesOf dom 0 t).1 ht |>.1 |> List.eq_nil_of_length_eq_zero, size_nil])
      have hl : (tuplesOf dom 0).length = 1 := by rw [length_tuplesOf]; rfl
      rw [hl] at h
      omega
    have h1 : Enc.size (ansUpTo z 0) = 2 := size_none
    dsimp only at hp1 hp2
    have hP : 1 * 3 ≤ 2 ^ (1 * lg n ^ (c + 1)) * (2 * T + 1) :=
      Nat.mul_le_mul Nat.one_le_two_pow (by omega)
    omega

/-- **The scan of lines 02–08, bounded at the degree** with exponent `c + 1`. -/
theorem ambientDesignScan (c : ℕ) : TN (Algo.ambientDesignScan c) (ScanPre c) (c + 1) := by
  have hstep : TN (fun x : ℕ × SState => (x.1 - 1, scanStep x.2)) (fun _ _ => True) (c + 1) :=
    ofPoly ((polyFun_fst.sub (polyFun_const 1)).pair (polyFun_snd.comp polyFun_scanStep)) _ _
  have hcount : ∀ a : AmbientDIn, (ambientScanSetUp c a).1 ≤ Enc.size a := by
    intro a
    have hk : a.2.1.1.1.length ≤ Enc.size a :=
      (length_le_size _).trans ((size_fst_le' a.2.1.1).trans
        ((size_fst_le' a.2.1).trans ((size_fst_le' a.2).trans (size_snd_le' a))))
    by_cases hg : a.2.1.1.1.length ≤ guardBound c a.1.length <;>
      simp only [ambientScanSetUp, ambientScanRounds, hg, if_true, if_false]
    · exact hk
    · exact Nat.zero_le _
  refine (iterateSetup (ofPoly (polyFun_ambientScanSetUp c) (ScanPre c) (c + 1)) hstep
    (ofPoly (polyFun_snd.comp polyFun_snd) (fun _ _ => True) (c + 1)) (Bounded.size.mono fun n a _ => hcount a) ?_
    (fun _ _ _ _ _ => trivial) (fun _ _ _ => trivial)).of_eq (fun _ => rfl)
  have hs := (Bounded.size (Pre := ScanPre c) (k := c + 1))
  have eT := (Bounded.const 1).add ((Bounded.lg_pow (Pre := ScanPre c) c (by omega)).mul
    (((Bounded.const 2).mul hs).add (Bounded.const 1)))
  have e1 := ((Bounded.const 4).mul hs).add ((Bounded.const 4).mul ((Bounded.const 1).add
    ((Bounded.two_pow_lg 1 (c + 1) le_rfl).mul (((Bounded.const 2).mul eT).add
      (Bounded.const 1)))))
  have e2 := ((Bounded.const 2).mul (hs.add (Bounded.const 2))).add
    ((Bounded.const 2).mul (e1.add ((Bounded.const 2).mul (eT.add (Bounded.const 2)))))
  obtain ⟨A, b, hb⟩ := e2
  refine ⟨A, b, fun n a ha j hj => le_trans ?_ (hb n a ha)⟩
  have h1 := size_pair_le' (((ambientScanSetUp c a).1 - j,
    scanStep^[j] (ambientScanSetUp c a).2) : ℕ × SState)
  have h2 := scan_state_size c a n ha j hj
  have h3 : Enc.size ((ambientScanSetUp c a).1 - j) ≤ Enc.size a + 2 := by
    rw [Small.size_nat]
    have := size_le_self ((ambientScanSetUp c a).1 - j)
    have := hcount a
    omega
  dsimp only at h1 ⊢
  omega

/-! ## Line 01 and the procedure on the top domain -/

/-- The transformation monoid on the arity positions: the ambient domain has at most `n`
points. -/
theorem ambientMon (c : ℕ) :
    TN (Algo.ambientMon c) (fun n (a : AmbientPIn) => a.1.2.1.length ≤ n) (c + 1) := by
  have ht := (aggTable c).scale 1 (c + 1) (Pre' := fun n (x : RawAggTestInput) =>
      x.2.1.length ≤ n ∧ x.2.2 = List.range x.1.length) (fun n x hx => by
    refine ⟨n + (n + 1) ^ c, ?_, ?_, fun hg => ?_⟩
    · have h1 : n ≤ (n + 1) ^ (c + 1) :=
        (Nat.le_succ n).trans (Nat.le_self_pow (by omega) _)
      have h2 : (n + 1) ^ c ≤ (n + 1) ^ (c + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      rw [pow_one]
      omega
    · exact hx.1.trans (Nat.le_add_right _ _)
    · rw [hx.2, List.length_range]
      refine (hg.trans ?_).trans (Nat.le_add_left _ _)
      rw [guardBound]
      exact Nat.pow_le_pow_left ((Nat.add_le_add_right ((Nat.log_mono_right hx.1).trans
        (Nat.log_le_self 2 n)) 1)) c)
  have hk : PolyFun (fun a : AmbientPIn => a.1.1) := polyFun_fst.comp polyFun_fst
  have hn : PolyFun (fun a : AmbientPIn => a.1.2.1) :=
    (polyFun_fst.comp polyFun_snd).comp polyFun_fst
  exact ((ofPoly (hk.pair (hn.pair (hk.comp polyFun_rangeLength))) _ _).comp ht
    (fun n a ha => ⟨ha, rfl⟩)).comp_poly (polyFun_snd.comp (PolyFun.map polyFun_fst))

/-- The precondition of line 01 at degree `n`: both domains have at most `n` points. -/
def PipePre (n : ℕ) (a : AmbientPIn) : Prop := a.1.2.1.length ≤ n ∧ a.1.2.2.length ≤ n

/-- **Line 01**, the relational functors of Sec. 5.2 and `k`-WL. -/
theorem ambientPipeline321 (c : ℕ) : TN (Algo.ambientPipeline321 c) PipePre (c + 1) := by
  have hp : PolyFun (fun a : AmbientPIn => ((a.1.1, a.1.2.2), a.2)) :=
    ((polyFun_fst.comp polyFun_fst).pair
      ((polyFun_fst.comp polyFun_snd).comp polyFun_snd)).pair polyFun_snd
  have hidx : TN (Algo.ambientIdx c) PipePre (c + 1) :=
    (ofPoly (hp.comp polyFun_pairIdxOf) _ _).pair
      ((ambientMon c).restrict fun n a ha => ha.1)
  have htab : TN (fun a : AmbientPIn => Algo.aggTable c a.1) PipePre (c + 1) :=
    (ofPoly polyFun_fst _ _).comp (aggTable c) (fun n a ha => ⟨ha.1, fun _ => ha.2⟩)
  exact (hidx.pair (htab.pair (ofPoly polyFun_snd _ _))).comp_poly polyFun_rawPipelineI

/-- The precondition of the procedure at degree `n`: both domains have at most `n` points. -/
def AmbPre (n : ℕ) (g : AmbientGIn) : Prop := PipePre n g.1

theorem ambientDesignAt (c : ℕ) :
    TN (fun g : AmbientGIn => Algo.ambientDesignAt c g []) AmbPre (c + 1) :=
  ((ofPoly ((((polyFun_fst.comp polyFun_fst).comp polyFun_fst).pair
    (polyFun_const ([] : List ℕ)))) _ _).pair
      ((ofPoly polyFun_fst _ _).comp (ambientPipeline321 c) (fun _ _ h => h))).pair
    (ofPoly polyFun_snd _ _)

/-- **Lines 01–08.** -/
theorem ambientDesignProcedure (c : ℕ) :
    TN (Algo.ambientDesignProcedure c) AmbPre (c + 1) :=
  ((ofPoly ((((polyFun_fst.comp polyFun_fst).comp polyFun_snd).comp polyFun_fst)) _ _).pair
    (ambientDesignAt c)).comp (ambientDesignScan c) (fun n g hg => ⟨hg.1, fun _ => by
      show (Algo.ambientPipeline321 c g.1).1.length ≤ n
      rw [fst_ambientPipeline321]; exact hg.2⟩)

theorem ambientDesignVersionRows (c : ℕ) :
    TN (Algo.ambientDesignVersionRows c) (fun n z => AmbPre n z.1) (c + 1) := by
  have hg : PolyFun (fun z : AmbientGIn × List ℕ => z.1.1.1) :=
    ((polyFun_fst.comp polyFun_fst).comp polyFun_fst)
  have hk := ((hg.comp polyFun_fst).pair (polyFun_snd.comp polyFun_length)).comp polyFun_take
  exact ((ofPoly (hk.pair (hg.comp polyFun_snd)) _ _).comp (aggTable c)
    (fun n z hz => ⟨hz.1, fun _ => hz.2⟩)).comp_poly
    (polyFun_snd.comp (PolyFun.map polyFun_fst))

theorem ambientDesignVersionsAt (c : ℕ) :
    TN (Algo.ambientDesignVersionsAt c) (fun n z => AmbPre n z.1) (c + 1) :=
  (((ofPoly polyFun_fst _ _).comp (ambientDesignAt c) (fun _ _ h => h)).pair
    (ambientDesignVersionRows c)).comp_poly
    (PolyFun.filterParam (polyFun_withStr.comp polyFun_returnsB))

theorem ambientDesignVersions (c : ℕ) :
    TN (Algo.ambientDesignVersions c) AmbPre (c + 1) := by
  have hh : TN (fun z : List ℕ × AmbientGIn => Algo.ambientDesignVersionsAt c (z.2, z.1))
      (fun n z => AmbPre n z.2) (c + 1) :=
    (ofPoly (polyFun_snd.pair polyFun_fst) _ _).comp (ambientDesignVersionsAt c)
      (fun _ _ h => h)
  refine (((ambientDesignProcedure c).pair (ofPoly polyFun_id _ _)).comp
    (optionElim (const' [] (fun _ _ => True) _) hh (fun _ _ _ => trivial)
      (fun n x s h => h) (Pre := fun n p => AmbPre n p.2)) (fun _ _ h => h)).of_eq
    (fun g => by
      unfold Algo.ambientDesignVersions
      cases Algo.ambientDesignProcedure c g <;> rfl)

theorem ambientDesignReadFamily (c : ℕ) :
    TN (Algo.ambientDesignReadFamily c) AmbPre (c + 1) := by
  have hm : PolyFun (fun z : DIn × List ℕ => (z.2, designReadExit (withStr z))) :=
    polyFun_snd.pair (polyFun_withStr.comp polyFun_designReadExit)
  exact ((ambientDesignAt c).pair (ambientDesignVersions c)).comp_poly (PolyFun.mapParam hm)

/-! ## Sec. 9.7: the call on the computed input -/

theorem designRelations (c : ℕ) :
    TN (Algo.designRelations c) (fun n z => AggTablePre c n z.1) (c + 1) := by
  have ht : TN (fun z : RawDesignRelInput => (Algo.aggTable c z.1).2.map Prod.fst)
      (fun n z => AggTablePre c n z.1) (c + 1) :=
    ((ofPoly polyFun_fst _ _).comp (aggTable c) (fun _ _ h => h)).comp_poly
      (polyFun_snd.comp (PolyFun.map polyFun_fst))
  have hf := ((ofPoly polyFun_snd _ _).pair ht).comp_poly
    (PolyFun.filterParam polyFun_designRelTest)
  exact (hf.pair (ofPoly (polyFun_const ([] : RawRelStruct)) _ _)).comp_poly polyFun_cons

/-- The lists of a case are no longer than its size. -/
theorem upccCase_lengths_le (r : RawUpccCase) :
    r.2.1.length ≤ Enc.size r ∧ r.2.2.length ≤ Enc.size r :=
  ⟨(length_le_size _).trans ((size_fst_le' r.2).trans (size_snd_le' r)),
    (length_le_size _).trans ((size_snd_le' r.2).trans (size_snd_le' r))⟩

theorem designCallGIn :
    TN Algo.designCallGIn (fun n r => Enc.size r ≤ n) 4 := by
  have hrel : TN designCallRelations (fun n r => Enc.size r ≤ n) 4 :=
    (ofPoly polyFun_designCallInput _ _).comp (designRelations 3) (fun n r hr => by
      refine ⟨(upccCase_lengths_le r).1.trans hr, fun _ => ?_⟩
      show (List.range r.2.2.length).length ≤ n
      rw [List.length_range]
      exact (upccCase_lengths_le r).2.trans hr)
  exact ((ofPoly (polyFun_designCallInput.comp polyFun_fst) _ _).pair hrel).pair
    (ofPoly (polyFun_const (3, 4)) _ _)

theorem designCallReadFamily :
    TN Algo.designCallReadFamily (fun n r => Enc.size r ≤ n) 4 :=
  designCallGIn.comp (ambientDesignReadFamily 3) (fun n r hr => by
    refine ⟨(upccCase_lengths_le r).1.trans hr, ?_⟩
    show (List.range r.2.2.length).length ≤ n
    rw [List.length_range]
    exact (upccCase_lengths_le r).2.trans hr)

/-- **The recursive graphs of case 3 of Sec. 9.7.** -/
theorem designCase3Graphs :
    TN Algo.designCase3Graphs (fun n r => Enc.size r ≤ n) 4 :=
  ((id' _ _).pair designCallReadFamily).comp_poly polyFun_designCase3GraphMap

end TN

end Explicit
