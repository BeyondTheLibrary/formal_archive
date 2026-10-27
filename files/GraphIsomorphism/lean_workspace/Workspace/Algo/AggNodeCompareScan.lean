import Workspace.Algo.AggNodeComparePhase
import Workspace.Algo.AggNodePairRAM
import Workspace.Algo.AggNodeCheckedTraverse

/-! # The comparison scan on all raw inputs

A consumed prepared job contributes its coset to the answer list. Charge
that stored copy to the removed job. Preparing later jobs does not change
the lazy scan result or issue any recursive calls.
-/
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1000000
namespace Algo
open RAM RAM.Targets

abbrev AggnCompareReadyRow := AggnCompareJob × AggnPairState
abbrev AggnCompareReadyState := List AggnCompareReadyRow × List RawCoset

private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd

def aggnCompareReadyStep (s : AggnCompareReadyState) : AggnCompareReadyState :=
  match s.1 with
  | [] => s
  | r :: rest => if aggnPairActive r.2 then s else (rest, r.2.2.1 :: s.2)

def aggnCompareReadyRead (empty : AggnPairState) (s : AggnCompareReadyState) : AggnCompareState :=
  (s.1.map Prod.fst, s.2, 0, (s.1.head?).elim empty Prod.snd)

def aggnCompareReadyScan (empty : AggnPairState) :
    List AggnCompareReadyRow → List RawCoset → AggnCompareState
  | [], answers => ([], answers, 0, empty)
  | r :: rest, answers =>
    if aggnPairActive r.2 then ((r :: rest).map Prod.fst, answers, 0, r.2)
    else aggnCompareReadyScan empty rest (r.2.2.1 :: answers)

def aggnCompareReadyPotential (s : AggnCompareReadyState) : ℕ :=
  2 * Enc.size s.1 + Enc.size s.2

private theorem size_cons_bounds {α : Type*} [Enc α] (a : α) (l : List α) :
    Enc.size a + Enc.size l ≤ Enc.size (a :: l) ∧
      Enc.size (a :: l) ≤ 2 * Enc.size a + Enc.size l := by
  have he := size_cons_eq a l
  rw [listSize_frame] at he
  have hl := length_lt_listSize (Enc.encode a)
  have hn := size_le_self (Enc.encode a).length
  have hsize : listSize (Enc.encode a) = Enc.size a := rfl
  omega

theorem aggnCompareReadyPotential_step (s : AggnCompareReadyState) :
    aggnCompareReadyPotential (aggnCompareReadyStep s) ≤ aggnCompareReadyPotential s := by
  obtain ⟨rows, answers⟩ := s
  cases rows with
  | nil => exact le_rfl
  | cons r rest =>
    simp only [aggnCompareReadyStep]
    split
    · exact le_rfl
    · have hstore := (size_cons_bounds r.2.2.1 answers).2
      have hr : Enc.size r.2.2.1 ≤ Enc.size r :=
        (size_fst_le' r.2.2).trans ((size_snd_le' r.2).trans (size_snd_le' r))
      have hrest := (size_cons_bounds r rest).1
      dsimp [aggnCompareReadyPotential]
      omega

theorem aggnCompareReadyPotential_iterate (s : AggnCompareReadyState) (j : ℕ) :
    aggnCompareReadyPotential (aggnCompareReadyStep^[j] s) ≤ aggnCompareReadyPotential s := by
  induction j with
  | zero => exact le_rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact (aggnCompareReadyPotential_step _).trans ih

theorem aggnCompareReadySize_iterate (s : AggnCompareReadyState) (j : ℕ) :
    Enc.size (aggnCompareReadyStep^[j] s) ≤ 8 * Enc.size s := by
  let t := aggnCompareReadyStep^[j] s
  have h1 : Enc.size t ≤ 2 * Enc.size t.1 + 2 * Enc.size t.2 := Combine.size_pair_le _ _
  have h2 := aggnCompareReadyPotential_iterate s j
  change aggnCompareReadyPotential t ≤ aggnCompareReadyPotential s at h2
  have h3 : Enc.size s.1 ≤ Enc.size s := size_fst_le' s
  have h4 : Enc.size s.2 ≤ Enc.size s := size_snd_le' s
  dsimp [aggnCompareReadyPotential] at h2
  change Enc.size t ≤ 8 * Enc.size s
  omega

theorem aggnCompareReadyScan_eq_iterate (empty : AggnPairState) :
    ∀ rows answers, aggnCompareReadyRead empty (aggnCompareReadyStep^[rows.length] (rows, answers)) =
      aggnCompareReadyScan empty rows answers := by
  intro rows
  induction rows with
  | nil => intro answers; rfl
  | cons r rest ih =>
    intro answers
    by_cases h : aggnPairActive r.2 = true
    · have hf : aggnCompareReadyStep (r :: rest, answers) = (r :: rest, answers) := by
        simp only [aggnCompareReadyStep, if_pos h]
      rw [Function.iterate_fixed hf]
      simp [aggnCompareReadyRead, aggnCompareReadyScan, h]
    · rw [List.length_cons, Function.iterate_succ_apply]
      simp only [aggnCompareReadyStep, if_neg h, aggnCompareReadyScan]
      exact ih _

theorem aggnPolyFun_compareReadyStep : PolyFun aggnCompareReadyStep := by
  let X := (AggnCompareReadyRow × List AggnCompareReadyRow) × List RawCoset
  have hz : PolyFun (fun z : X => z) := polyFun_id
  have hr := pfst (pfst hz)
  have hs := psnd hz
  have he := (psnd (pfst hz)).pair
    (((pfst (psnd (psnd hr))).pair hs).comp polyFun_cons)
  have hc := (psnd hr).comp aggnPolyFun_pairActive
  have hi := ((pfst hz).comp polyFun_cons).pair hs
  exact (PolyFun.listCases ((polyFun_const []).pair polyFun_id)
    (PolyFun.ite hc hi he)).of_eq (fun ⟨rows, answers⟩ => by cases rows <;> rfl)

theorem aggnPolyFun_compareReadyRead (empty : AggnPairState) : PolyFun (aggnCompareReadyRead empty) := by
  have hz : PolyFun (fun s : AggnCompareReadyState => s) := polyFun_id
  have hout : PolyFun (fun p : Option AggnCompareReadyRow × AggnCompareReadyState =>
      p.1.elim empty Prod.snd) :=
    PolyFun.optionElim (polyFun_const empty) (psnd polyFun_fst)
  have hhead := ((pfst hz).comp polyFun_headOption).pair hz
  exact ((pfst hz).comp (PolyFun.map polyFun_fst)).pair
    ((psnd hz).pair ((polyFun_const 0).pair (hhead.comp hout)))

theorem aggnPolyFun_compareReadyScan (empty : AggnPairState) :
    PolyFun (fun s : AggnCompareReadyState => aggnCompareReadyScan empty s.1 s.2) := by
  have hk : PolyFun (fun s : AggnCompareReadyState => (s.1.length, s)) :=
    (polyFun_fst.comp polyFun_length).pair polyFun_id
  have hs : PolyFun (fun z : ℕ × AggnCompareReadyState => (z.1 - 1, aggnCompareReadyStep z.2)) :=
    ((polyFun_fst.pair (polyFun_const 1)).comp polyFun_sub).pair
      (polyFun_snd.comp aggnPolyFun_compareReadyStep)
  have hcount : ∀ s : AggnCompareReadyState, s.1.length ≤ Enc.size s := fun s =>
    (length_le_size s.1).trans (size_fst_le' s)
  have hi := PolyFun.iterate hs hk hcount polyBound_id
    (p := fun n => 18 * n + 4) (fun s j _ => by
      have h1 := aggnCompareReadySize_iterate s j
      have h2 := hcount s
      have h3 : Enc.size (s.1.length - j) ≤ Enc.size s + 2 := by
        rw [Small.size_nat]
        have := size_le_self (s.1.length - j)
        omega
      have h4 := Combine.size_pair_le (s.1.length - j) (aggnCompareReadyStep^[j] s)
      dsimp only
      omega)
    (((polyBound_const 18).mul polyBound_id).add (polyBound_const 4))
  exact (hi.comp (aggnPolyFun_compareReadyRead empty)).of_eq
    (fun s => aggnCompareReadyScan_eq_iterate empty s.1 s.2)

theorem aggnPolyFun_compareCtx :
    PolyFun (fun p : AggnPhaseCtx × AggnCompareJob => aggnCompareCtx p.1 p.2) := by
  have hz : PolyFun (fun p : AggnPhaseCtx × AggnCompareJob => p) := polyFun_id
  have hC := pfst hz
  have ha := psnd hz
  have hx := pfst (psnd hC)
  have hy := pfst (psnd (psnd hC))
  have ht := PolyFun.ite (pfst ha) hy hx
  exact (((pfst hC).pair (hx.pair (ht.pair (psnd ha)))).comp aggnPolyFun_pairPrepare).of_eq
    (fun p => by unfold aggnCompareCtx; cases p.2.1 <;> rfl)

theorem aggnQuasiFun_compareOpen (c : ℕ) :
    QuasiFun (fun p : AggnPhaseCtx × AggnCompareJob => aggnCompareOpen c p.1 p.2) := by
  have h := aggnPolyFun_compareCtx
  exact ((pfst h).pair ((pfst (psnd h)).pair ((psnd (psnd h)).pair
    (polyFun_const (none : Option RawCoset))))).comp_quasiFun (aggnQuasiFun_pairStart c)

def aggnCompareReadyJob (c : ℕ) (p : AggnPhaseCtx × AggnCompareJob) : AggnCompareReadyRow :=
  (p.2, aggnCompareOpen c p.1 p.2)

theorem aggnQuasiFun_compareReadyJob (c : ℕ) : QuasiFun (aggnCompareReadyJob c) :=
  polyFun_snd.quasiFun.pair (aggnQuasiFun_compareOpen c)

/-- Eager preparation preserves even the untouched suffix of the lazy scan. -/
theorem aggnCompareReadyJob_scan (c : ℕ) (C : AggnPhaseCtx) :
    ∀ jobs answers,
      aggnCompareReadyScan (aggnPairStart c (([], []), ([], [], [])) [] none none)
        (jobs.map fun a => aggnCompareReadyJob c (C, a)) answers =
          aggnCompareScan c C jobs answers := by
  intro jobs
  induction jobs with
  | nil => intro answers; rfl
  | cons a rest ih =>
    intro answers
    simp only [List.map_cons, aggnCompareReadyScan, aggnCompareReadyJob, aggnCompareScan]
    split
    · simp only [List.map_map, Function.comp_def]
      congr 2
      exact List.map_id rest
    · exact ih _

theorem aggnQuasiFun_compareScan (c : ℕ) :
    QuasiFun (fun z : AggnPhaseCtx × List AggnCompareJob × List RawCoset =>
      aggnCompareScan c z.1 z.2.1 z.2.2) := by
  have hz : PolyFun (fun z : AggnPhaseCtx × List AggnCompareJob × List RawCoset => z) := polyFun_id
  have hprep := ((pfst hz).pair (pfst (psnd hz))).comp_quasiFun
    (aggnQuasiFun_mapParam (aggnQuasiFun_compareReadyJob c))
  have hm := (hprep.pair (psnd (psnd hz)).quasiFun).comp_poly
    (aggnPolyFun_compareReadyScan (aggnPairStart c (([], []), ([], [], [])) [] none none))
  exact hm.of_eq (fun z => aggnCompareReadyJob_scan c z.1 z.2.1 z.2.2)

end Algo
