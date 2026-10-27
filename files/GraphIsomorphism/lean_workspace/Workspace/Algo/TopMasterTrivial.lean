import Workspace.Algo.TopMasterOrder

/-! # The first exit of Reduce-to-Johnson
A group fixes a string precisely when all its stored generators do.
The source and shifted target are compared only after this test succeeds.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Pointwise

def masterAutGenerator (p : RawStr × RawPerm) : Bool := decide (rawStrAct (p.2, p.1) = p.1)
def masterAutTest (p : RawSI) : Bool := p.1.all (fun g => masterAutGenerator (p.2.1, g))
def masterTrivialLeaf (p : RawSI) : RawCoset :=
  if p.2.1 = p.2.2 then top2NormC p.2.1 (some (p.1, rawOne p.2.1)) else none

theorem polyFun_masterAutGenerator : PolyFun masterAutGenerator :=
  ((polyFun_swap.comp polyFun_rawStrAct).pair polyFun_fst).comp polyFun_listNatEq

theorem polyFun_masterAutTest : PolyFun masterAutTest :=
  (((polyFun_snd.comp polyFun_fst).pair polyFun_fst).comp
    (wftPolyFun_all polyFun_masterAutGenerator))

theorem polyFun_masterTrivialLeaf : PolyFun masterTrivialLeaf := by
  have hx : PolyFun (fun p : RawSI => p.2.1) := polyFun_snd.comp polyFun_fst
  have ht := (hx.pair (polyFun_snd.comp polyFun_snd)).comp polyFun_listNatEq
  have hr := (hx.pair ((polyFun_fst.pair (hx.comp polyFun_rawOne)).comp polyFun_some)).comp
    polyFun_top2NormC
  exact (PolyFun.ite ht hr (polyFun_const none)).of_eq
    (fun p => by simp only [masterTrivialLeaf, decide_eq_true_eq])

theorem masterAutGenerator_spec {n : ℕ} {x : RawStr} {g : RawPerm}
    (hx : x.length = n) (hg : RawPerm.WF n g) :
    masterAutGenerator (x, g) = true ↔ strAct (decStrN n x) (decPerm n g) = decStrN n x := by
  unfold masterAutGenerator
  simp only [decide_eq_true_eq]
  conv_lhs => rw [← encPerm_decPerm hg, ← encStrN_decStrN hx, rawStrAct_encStrN]
  constructor
  · intro h
    simpa only [decStrN_encStrN] using congrArg (decStrN n) h
  · exact congrArg encStrN

theorem masterStringAut_mem {n : ℕ} (x : Fin n → ℕ) (g : Perm (Fin n)) :
    g ∈ strAutSubgroup ⊤ x ↔ strAct x g = x := by
  rw [strAct_eq_iff]
  simp [strAutSubgroup, wAutSubgroup, wAut, wIso]

theorem masterAutTest_spec {n : ℕ} {p : RawSI}
    (hx : p.2.1.length = n) (hw : RawGens.WF n p.1) :
    masterAutTest p = true ↔ ∀ g ∈ decGroup n p.1, strAct (decStrN n p.2.1) g = decStrN n p.2.1 := by
  have hgen : masterAutTest p = true ↔ decGroup n p.1 ≤ strAutSubgroup ⊤ (decStrN n p.2.1) := by
    rw [masterAutTest, List.all_eq_true, decGroup, genGroup, Subgroup.closure_le]
    constructor
    · intro h g hg
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hg
      exact (masterStringAut_mem _ _).mpr ((masterAutGenerator_spec hx (hw r hr)).mp (h r hr))
    · intro h r hr
      exact (masterAutGenerator_spec hx (hw r hr)).mpr
        ((masterStringAut_mem _ _).mp (h (List.mem_map_of_mem hr)))
  rw [hgen]
  exact forall₂_congr (fun g _ => masterStringAut_mem _ g)

/-- The returned coset is exact whenever the first test succeeds. -/
theorem masterTrivialLeaf_spec {n : ℕ} {p : RawSI}
    (hx : p.2.1.length = n) (hy : p.2.2.length = n) (hw : RawGens.WF n p.1)
    (ht : masterAutTest p = true) :
    decCoset n (masterTrivialLeaf p) =
      strIso (decGroup n p.1 : Set (Perm (Fin n))) (decStrN n p.2.1) (decStrN n p.2.2) := by
  have ha := (masterAutTest_spec hx hw).mp ht
  unfold masterTrivialLeaf
  split_ifs with he
  · rw [decCoset_top2NormC hx, decCoset_some, rawOne_eq, hx, decPerm_encPerm, one_smul]
    ext g
    exact ⟨fun hg => ⟨hg, he ▸ ha g hg⟩, fun hg => hg.1⟩
  · change ∅ = _
    apply Set.ext
    intro g
    simp only [Set.mem_empty_iff_false, false_iff]
    rintro ⟨hg, hi⟩
    have hs : decStrN n p.2.1 = decStrN n p.2.2 := (ha g hg).symm.trans hi
    have he' := congrArg encStrN hs
    rw [encStrN_decStrN hx, encStrN_decStrN hy] at he'
    exact he he'
end Algo
