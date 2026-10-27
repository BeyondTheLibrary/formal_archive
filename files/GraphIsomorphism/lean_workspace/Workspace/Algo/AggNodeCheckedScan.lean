import Workspace.Algo.AggNodeCheckedLocal
import Workspace.Algo.AggNodeCheckedTraverse

/-! # A machine bound for the certificate scan

Prepare each supplied job once. The scan then consumes prepared entries until
it reaches an active certificate. A consumed entry is copied into one store.
The size argument charges that copy to the entry removed from the pending list.
This proves a bound on all inputs, including malformed jobs and stores.
-/
set_option synthInstance.maxSize 512
set_option maxHeartbeats 1000000
namespace Algo
open RAM RAM.Targets

/-- A job, its initial certificate state, and the entry used if it has no calls. -/
abbrev AggnReadyRow := AggnJob × AggnCertState × RawAggCert
abbrev AggnReadyState := List AggnReadyRow × AggnStores

private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd

def aggnReadyStep (s : AggnReadyState) : AggnReadyState :=
  match s.1 with
  | [] => s
  | r :: rest =>
    if lcCond r.2.1.1 then s else (rest, aggnStoreEntry r.1 r.2.2 s.2)

def aggnReadyRead (empty : AggnCertState) (s : AggnReadyState) : AggnPhaseState :=
  (s.1.map Prod.fst, s.2, 0, (s.1.head?).elim empty (fun r => r.2.1))

def aggnReadyScan (empty : AggnCertState) : List AggnReadyRow → AggnStores → AggnPhaseState
  | [], stores => ([], stores, 0, empty)
  | r :: rest, stores =>
    if lcCond r.2.1.1 then ((r :: rest).map Prod.fst, stores, 0, r.2.1)
    else aggnReadyScan empty rest (aggnStoreEntry r.1 r.2.2 stores)

/-- Each stored copy is charged once to the pending entry it consumes. -/
def aggnReadyPotential (s : AggnReadyState) : ℕ :=
  2 * Enc.size s.1 + Enc.size s.2.1 + Enc.size s.2.2

private theorem aggnSize_cons_bounds {α : Type*} [Enc α] (a : α) (l : List α) :
    Enc.size a + Enc.size l ≤ Enc.size (a :: l) ∧
      Enc.size (a :: l) ≤ 2 * Enc.size a + Enc.size l := by
  have he := size_cons_eq a l
  rw [listSize_frame] at he
  have hl := length_lt_listSize (Enc.encode a)
  have hn := size_le_self (Enc.encode a).length
  have hsize : listSize (Enc.encode a) = Enc.size a := rfl
  omega

private theorem aggnStoreEntry_size (a : AggnJob) (e : RawAggCert) (s : AggnStores) :
    Enc.size (aggnStoreEntry a e s).1 + Enc.size (aggnStoreEntry a e s).2 ≤
      Enc.size s.1 + Enc.size s.2 + 2 * Enc.size e := by
  have h1 := (aggnSize_cons_bounds e s.1).2
  have h2 := (aggnSize_cons_bounds e s.2).2
  unfold aggnStoreEntry
  cases a.1 <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega

theorem aggnReadyPotential_step (s : AggnReadyState) :
    aggnReadyPotential (aggnReadyStep s) ≤ aggnReadyPotential s := by
  obtain ⟨rows, stores⟩ := s
  cases rows with
  | nil => exact le_rfl
  | cons r rest =>
    simp only [aggnReadyStep]
    split
    · exact le_rfl
    · have hstore := aggnStoreEntry_size r.1 r.2.2 stores
      have hr : Enc.size r.2.2 ≤ Enc.size r :=
        (size_snd_le' r.2).trans (size_snd_le' r)
      have hrest := (aggnSize_cons_bounds r rest).1
      dsimp [aggnReadyPotential]
      omega

theorem aggnReadyPotential_iterate (s : AggnReadyState) (j : ℕ) :
    aggnReadyPotential (aggnReadyStep^[j] s) ≤ aggnReadyPotential s := by
  induction j with
  | zero => exact le_rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact (aggnReadyPotential_step _).trans ih

theorem aggnReadySize_iterate (s : AggnReadyState) (j : ℕ) :
    Enc.size (aggnReadyStep^[j] s) ≤ 16 * Enc.size s := by
  let t := aggnReadyStep^[j] s
  have h1 : Enc.size t ≤ 2 * Enc.size t.1 + 2 * Enc.size t.2 := Combine.size_pair_le _ _
  have h2 : Enc.size t.2 ≤ 2 * Enc.size t.2.1 + 2 * Enc.size t.2.2 := Combine.size_pair_le _ _
  have h3 := aggnReadyPotential_iterate s j
  change aggnReadyPotential t ≤ aggnReadyPotential s at h3
  have h4 : Enc.size s.1 ≤ Enc.size s := size_fst_le' s
  have h5 : Enc.size s.2.1 ≤ Enc.size s := (size_fst_le' s.2).trans (size_snd_le' s)
  have h6 : Enc.size s.2.2 ≤ Enc.size s := (size_snd_le' s.2).trans (size_snd_le' s)
  dsimp [aggnReadyPotential] at h3
  change Enc.size t ≤ 16 * Enc.size s
  omega

theorem aggnReadyScan_eq_iterate (empty : AggnCertState) :
    ∀ rows stores, aggnReadyRead empty (aggnReadyStep^[rows.length] (rows, stores)) =
      aggnReadyScan empty rows stores := by
  intro rows
  induction rows with
  | nil => intro stores; rfl
  | cons r rest ih =>
    intro stores
    by_cases h : lcCond r.2.1.1 = true
    · have hf : aggnReadyStep (r :: rest, stores) = (r :: rest, stores) := by
        simp only [aggnReadyStep, if_pos h]
      rw [Function.iterate_fixed hf]
      simp [aggnReadyRead, aggnReadyScan, h]
    · rw [List.length_cons, Function.iterate_succ_apply]
      simp only [aggnReadyStep, if_neg h, aggnReadyScan]
      exact ih _

theorem aggnPolyFun_readyStep : PolyFun aggnReadyStep := by
  have he : PolyFun (fun z : (AggnReadyRow × List AggnReadyRow) × AggnStores =>
      (z.1.2, aggnStoreEntry z.1.1.1 z.1.1.2.2 z.2)) := by
    have hz : PolyFun (fun z : (AggnReadyRow × List AggnReadyRow) × AggnStores => z) := polyFun_id
    have hr := pfst (pfst hz)
    have hs := psnd hz
    have hentry := psnd (psnd hr)
    have hstore := PolyFun.ite (pfst (pfst hr))
      ((pfst hs).pair ((hentry.pair (psnd hs)).comp polyFun_cons))
      (((hentry.pair (pfst hs)).comp polyFun_cons).pair (psnd hs))
    exact ((psnd (pfst hz)).pair hstore).of_eq (fun z => by
      unfold aggnStoreEntry
      cases z.1.1.1.1 <;> rfl)
  have hc : PolyFun (fun z : (AggnReadyRow × List AggnReadyRow) × AggnStores => lcCond z.1.1.2.1.1) :=
    (pfst (pfst (psnd (pfst polyFun_fst)))).comp polyFun_lcCond
  have hi : PolyFun (fun z : (AggnReadyRow × List AggnReadyRow) × AggnStores =>
      (z.1.1 :: z.1.2, z.2)) :=
    ((polyFun_fst.comp polyFun_cons).pair polyFun_snd)
  exact (PolyFun.listCases ((polyFun_const []).pair polyFun_id)
    (PolyFun.ite hc hi he)).of_eq (fun ⟨rows, stores⟩ => by cases rows <;> rfl)

theorem aggnPolyFun_readyRead (empty : AggnCertState) : PolyFun (aggnReadyRead empty) := by
  have hz : PolyFun (fun s : AggnReadyState => s) := polyFun_id
  have hout : PolyFun (fun p : Option AggnReadyRow × AggnReadyState =>
      p.1.elim empty (fun r => r.2.1)) :=
    PolyFun.optionElim (polyFun_const empty) (pfst (psnd polyFun_fst))
  have hhead := ((pfst hz).comp polyFun_headOption).pair hz
  exact ((pfst hz).comp (PolyFun.map polyFun_fst)).pair
    ((psnd hz).pair ((polyFun_const 0).pair (hhead.comp hout)))

/-- The traversal of prepared jobs is polynomial even on arbitrary rows and stores. -/
theorem aggnPolyFun_readyScan (empty : AggnCertState) :
    PolyFun (fun s : AggnReadyState => aggnReadyScan empty s.1 s.2) := by
  have hk : PolyFun (fun s : AggnReadyState => (s.1.length, s)) :=
    (polyFun_fst.comp polyFun_length).pair polyFun_id
  have hs : PolyFun (fun z : ℕ × AggnReadyState => (z.1 - 1, aggnReadyStep z.2)) :=
    ((polyFun_fst.pair (polyFun_const 1)).comp polyFun_sub).pair
      (polyFun_snd.comp aggnPolyFun_readyStep)
  have hcount : ∀ s : AggnReadyState, s.1.length ≤ Enc.size s := fun s =>
    (length_le_size s.1).trans (size_fst_le' s)
  have hi := PolyFun.iterate hs hk hcount polyBound_id
    (p := fun n => 34 * n + 4) (fun s j _ => by
      have h1 := aggnReadySize_iterate s j
      have h2 := hcount s
      have h3 : Enc.size (s.1.length - j) ≤ Enc.size s + 2 := by
        rw [Small.size_nat]
        have := size_le_self (s.1.length - j)
        omega
      have h4 := Combine.size_pair_le (s.1.length - j) (aggnReadyStep^[j] s)
      dsimp only
      omega)
    (((polyBound_const 34).mul polyBound_id).add (polyBound_const 4))
  exact (hi.comp (aggnPolyFun_readyRead empty)).of_eq
    (fun s => aggnReadyScan_eq_iterate empty s.1 s.2)

end Algo
