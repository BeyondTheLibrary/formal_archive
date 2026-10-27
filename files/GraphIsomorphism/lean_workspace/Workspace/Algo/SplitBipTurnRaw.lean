import Workspace.Algo.SplitBipTurnCases

/-! The full local turn follows Steps 1, 2, 4, 6, and 9 in that order.
The selected case retains all versions. The next threshold is stored
separately and is used only when an entry requests a recursive call. -/
namespace Algo
open RAM Babai
set_option maxHeartbeats 1000000

def sbipTurnPartition (P : RawColPart) : RawSbipTurnEntry :=
  sbipTurnReturn (rawAlignPartition P)

def sbipTurnAfter35 (z : RawSbipTurnInput) : List RawSbipTurnEntry :=
  if sbipImprimitive (sbipGraphComponentTable (sbipTurnGraphInput z)) then
    [sbipTurnPartition (sbipGraphComponentPartition (sbipTurnGraphInput z))]
  else sbipTurnCases (sbipTurnCase z)

def sbipTurnLarge (z : RawSbipTurnInput) : List RawSbipTurnEntry :=
  ((sbipGraphSteps35 (sbipTurnGraphInput z)).2).elim
    [sbipTurnPartition (sbipGraphEarly4 (sbipTurnGraphInput z))]
    (fun _ => sbipTurnAfter35 z)

def sbipTurn (c : ℕ) (z : RawSbipTurnInput) : List RawSbipTurnEntry :=
  if sbipGraphSmall1 c z.2.1.1 then
    (sbipGraphEarly1 c (sbipTurnGraphInput z)).map sbipTurnPartition
  else if sbipGraphSmall2 c z.2.1.1 then
    (sbipGraphEarly2 (c+1) z.2.1.1).map sbipTurnPartition
  else sbipTurnLarge z

theorem polyFun_sbipTurnPartition : PolyFun sbipTurnPartition :=
  polyFun_rawAlignPartition.comp polyFun_sbipTurnReturn

theorem quasiFun_sbipTurnAfter35 : QuasiFun sbipTurnAfter35 := by
  have ht := (polyFun_sbipTurnGraphInput.comp polyFun_sbipGraphComponentTable).comp
    sbipPoly_imprimitive
  have hp := ((polyFun_sbipTurnGraphInput.comp polyFun_sbipGraphComponentPartition).comp
    polyFun_sbipTurnPartition |>.pair (polyFun_const [])).comp polyFun_cons
  exact QuasiFun.ite ht hp.quasiFun (polyFun_sbipTurnCase.comp_quasiFun quasiFun_sbipTurnCases)

theorem quasiFun_sbipTurnLarge : QuasiFun sbipTurnLarge := by
  have hp := ((polyFun_sbipTurnGraphInput.comp polyFun_sbipGraphEarly4).comp
    polyFun_sbipTurnPartition |>.pair (polyFun_const [])).comp polyFun_cons
  have ho := ((polyFun_sbipTurnGraphInput.comp polyFun_sbipGraphSteps35).comp polyFun_snd).pair
    polyFun_id
  exact ho.quasiFun.comp (hp.quasiFun.optionElim
    (polyFun_snd.comp_quasiFun quasiFun_sbipTurnAfter35))

theorem quasiFun_sbipTurn (c : ℕ) : QuasiFun (sbipTurn c) := by
  have hg : PolyFun (fun z : RawSbipTurnInput => z.2.1.1) :=
    (polyFun_snd.comp polyFun_fst).comp polyFun_fst
  have h1 := (polyFun_sbipTurnGraphInput.comp_quasiFun (quasiFun_sbipGraphEarly1 c)).comp_poly
    (PolyFun.map polyFun_sbipTurnPartition)
  have h2 := (hg.comp_quasiFun (quasiFun_sbipGraphEarly2 (c+1))).comp_poly
    (PolyFun.map polyFun_sbipTurnPartition)
  exact QuasiFun.ite (hg.comp (polyFun_sbipGraphSmall1 c)) h1
    (QuasiFun.ite (hg.comp (polyFun_sbipGraphSmall2 c)) h2 quasiFun_sbipTurnLarge)

def sbipTurnIsReturn (e : RawSbipTurnEntry) : Bool := e.2.elim true (fun _ => false)
def sbipTurnStoredChild (e : RawSbipTurnEntry) : RawSbipStored := e.2.getD default

def sbipTurnReturns (L : List RawSbipTurnEntry) : List RawAlignOutcome :=
  (L.filter sbipTurnIsReturn).map Prod.fst

def sbipTurnChildren (L : List RawSbipTurnEntry) : List RawSbipStored :=
  (L.filter (fun e => !sbipTurnIsReturn e)).map sbipTurnStoredChild

theorem polyFun_sbipTurnIsReturn : PolyFun sbipTurnIsReturn :=
  ((polyFun_snd.pair polyFun_id).comp
    (PolyFun.optionElim (polyFun_const true) (polyFun_const false)))

theorem polyFun_sbipTurnStoredChild : PolyFun sbipTurnStoredChild := by
  exact (((polyFun_snd.pair polyFun_id).comp
    (PolyFun.optionElim (polyFun_const default) polyFun_fst))).of_eq
      (fun e => by cases he : e.2 <;> simp [sbipTurnStoredChild,he])

theorem polyFun_sbipTurnReturns : PolyFun sbipTurnReturns :=
  (PolyFun.filter polyFun_sbipTurnIsReturn).comp (PolyFun.map polyFun_fst)

theorem polyFun_sbipTurnChildren : PolyFun sbipTurnChildren :=
  (PolyFun.filter (polyFun_rawJNot polyFun_sbipTurnIsReturn)).comp
    (PolyFun.map polyFun_sbipTurnStoredChild)

theorem sbipTurnReturns_mem (L : List RawSbipTurnEntry) (o : RawAlignOutcome) :
    o ∈ sbipTurnReturns L ↔ (o,none) ∈ L := by
  simp only [sbipTurnReturns,List.mem_map,List.mem_filter]
  constructor
  · rintro ⟨⟨a,g⟩,⟨he,hr⟩,rfl⟩
    cases g <;> simp_all [sbipTurnIsReturn]
  · intro he
    exact ⟨(o,none),⟨he,rfl⟩,rfl⟩

theorem sbipTurnChildren_mem (L : List RawSbipTurnEntry) (g : RawSbipStored) :
    g ∈ sbipTurnChildren L ↔ ∃ o, (o,some g) ∈ L := by
  simp only [sbipTurnChildren,List.mem_map,List.mem_filter]
  constructor
  · rintro ⟨⟨o,q⟩,⟨he,hq⟩,hg⟩
    cases q with
    | none => simp [sbipTurnIsReturn] at hq
    | some q =>
      have heq : q = g := hg
      subst q
      exact ⟨o,he⟩
  · rintro ⟨o,ho⟩
    exact ⟨(o,some g),⟨ho,rfl⟩,rfl⟩

end Algo
