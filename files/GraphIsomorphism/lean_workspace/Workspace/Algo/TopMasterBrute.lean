import Workspace.Algo.TopMasterWindowLeaf
import Workspace.Algo.BruteForce

/-! # The small-group exit on the actual ambient window
Enumerate the restricted group for the fixed small-group cutoff. The
existing brute-force proof also applies to natural-number letters: a
finite alphabet is used only in the proof, without changing the raw strings.
The full preimage and candidate shift then restore the ambient answer.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv

/-- Extend the existing brute-force specification to arbitrary raw alphabet values. -/
theorem masterBrute_spec {n : ℕ} {p : RawSI} {js : List ℕ}
    (hx : p.2.1.length = n) (hy : p.2.2.length = n) (hw : RawGens.WF n p.1)
    (hb : Nat.card (decGroup n p.1) ≤ js.length + 1) :
    decCoset n (rawBrute (((p.2.1, p.1), js), p.2)) =
      strIso (decGroup n p.1 : Set (Perm (Fin n))) (decStrN n p.2.1) (decStrN n p.2.2) := by
  classical
  let s := (Finset.univ.sup (fun i : Fin n => max (decStrN n p.2.1 i) (decStrN n p.2.2 i))) + 1
  let x : Fin n → Fin s := fun i => ⟨decStrN n p.2.1 i, Nat.lt_succ_of_le
    ((le_max_left _ _).trans (Finset.le_sup (f := fun i : Fin n =>
      max (decStrN n p.2.1 i) (decStrN n p.2.2 i)) (Finset.mem_univ i)))⟩
  let y : Fin n → Fin s := fun i => ⟨decStrN n p.2.2 i, Nat.lt_succ_of_le
    ((le_max_right _ _).trans (Finset.le_sup (f := fun i : Fin n =>
      max (decStrN n p.2.1 i) (decStrN n p.2.2 i)) (Finset.mem_univ i)))⟩
  have ex : encStr x = p.2.1 := encStrN_decStrN hx
  have ey : encStr y = p.2.2 := encStrN_decStrN hy
  have hi : IsoSet (p.1.map (decPerm n)) x y =
      strIso (decGroup n p.1 : Set (Perm (Fin n))) (decStrN n p.2.1) (decStrN n p.2.2) := by
    ext g
    rw [strIso_eq_sep]
    change (g ∈ decGroup n p.1 ∧ ∀ u, x u = y (g u)) ↔ _
    simp only [Set.mem_setOf_eq, Fin.ext_iff]
    rfl
  have ha : AutSet (p.1.map (decPerm n)) x =
      strAut (decGroup n p.1 : Set (Perm (Fin n))) (decStrN n p.2.1) := by
    ext g
    rw [strAut, strIso_eq_sep]
    change (g ∈ decGroup n p.1 ∧ ∀ u, x u = x (g u)) ↔ _
    simp only [Set.mem_setOf_eq, Fin.ext_iff]
    rfl
  have he : rawBrute (((p.2.1, (p.1.map (decPerm n)).map (encPerm n)), js), (encStr x, encStr y)) =
      rawBrute (((p.2.1, p.1), js), p.2) := by rw [map_encPerm_decPerm hw, ex, ey]
  cases hr : rawBrute (((p.2.1, p.1), js), p.2) with
  | none =>
    have hn := (rawBrute_eq_none_iff (gens := p.1.map (decPerm n)) (x := x) (y := y) hx hb).mp
      (he.trans hr)
    rw [hi] at hn
    exact hn.symm
  | some q =>
    obtain ⟨hrp, hgen⟩ := rawBrute_spec (gens := p.1.map (decPerm n)) (x := x) (y := y) hx hb
      (he.trans hr)
    rw [hi] at hrp
    rw [ha] at hgen
    rw [decCoset_some, hgen]
    exact (strIso_eq_smul_strAut hrp).symm

def masterBruteLeaf (C₀ : ℕ) (p : RawSI) : RawCoset :=
  rawBrute (((p.2.1, p.1), List.range C₀), p.2)

def masterWindowBruteLeaf (C₀ : ℕ) (W : RawWinSI) : RawCoset :=
  masterWindowReturn (W, masterBruteLeaf C₀ (primitiveWindowInput W))

theorem polyFun_masterBruteLeaf (C₀ : ℕ) : PolyFun (masterBruteLeaf C₀) :=
  (((((polyFun_snd.comp polyFun_fst).pair polyFun_fst).pair (polyFun_const (List.range C₀))).pair
    polyFun_snd).comp polyFun_rawBrute)

theorem polyFun_masterWindowBruteLeaf (C₀ : ℕ) : PolyFun (masterWindowBruteLeaf C₀) :=
  (polyFun_id.pair (polyFun_primitiveWindowInput.comp (polyFun_masterBruteLeaf C₀))).comp
    polyFun_masterWindowReturn

/-- The actual small-group branch meets the enumeration bound and returns the ambient answer. -/
theorem masterWindowBruteLeaf_spec {n B C₀ : ℕ} {W : RawWinSI}
    (hx : W.2.2.2.1.length = n) (hw : RawGens.WF n W.2.1)
    (hnd : W.1.Nodup) (hlt : ∀ u ∈ W.1, u < n)
    (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1))
    (hr : masterReduceRoute B C₀ W = 1) :
    decCoset n (masterWindowBruteLeaf C₀ W) = (decWinSI n W).answer := by
  obtain ⟨_, ho⟩ := (masterReduceRoute_brute B C₀ W).mp hr
  have hgs := rawRestrictGens_wf_of_raw (dom := W.2.2.2.1) hw hnd hlt hinv
  have he := rawOrder_spec W.1 rfl ((primitiveWindowInput W).1.map (decPerm W.1.length))
  rw [map_encPerm_decPerm (show RawGens.WF W.1.length (primitiveWindowInput W).1 from hgs)] at he
  change rawOrder (W.1, (primitiveWindowInput W).1) < C₀ at ho
  rw [he] at ho
  apply masterWindowReturn_spec hx hw hnd hlt hinv
  apply masterBrute_spec (length_rawRestrictStr _ _) (length_rawRestrictStr _ _) hgs
  simpa only [List.length_range] using ho.le.trans (Nat.le_succ C₀)
end Algo
