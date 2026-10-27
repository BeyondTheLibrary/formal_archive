/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: Theorem 11.2.1 (both halves) as one statement about the RAM.
-/
import Workspace.Algo.CameronNbar
import Workspace.Algo.CameronAxiom

/-!
# Theorem 11.2.1 on the RAM

The paper's Theorem 11.2.1 ends with *"Moreover, `N` and the system of imprimitivity in
question can be found in polynomial time."*  The pieces are proved elsewhere
(`Algo.exists_polyFun_cameronSpec`, which rests on the cited `Babai.cameronStructure_polyTime`;
`Algo.rawNbar_spec`, `Algo.camNbar_normal`, `Algo.camRecognize_index`,
`Algo.camBlocks_system`, `Algo.camBlocks_acts`).  `Algo.theorem_11_2_1_ram` puts them together
in the form of the paper's statement: one `RAM.PolyFun` routine that returns generators of `N`
and the blocks, with every conclusion of `Babai.Theorem_11_2_1` holding for its output.
-/

namespace Algo

open RAM RAM.Targets

/-- The routine: recognize the Cameron structure, then return generators of the base group
`(A_k^{(t)})^s` and the fibres of the first coordinate. -/
def camNbarBlocks (cameron : RawGens × List ℕ → Option RawCameron) (p : RawGens × List ℕ) :
    Option (RawGens × RawBlocks) :=
  (cameron p).map (fun c => (rawNbar (c, p.1), camBlocks c))

theorem polyFun_camNbarBlocks {cameron : RawGens × List ℕ → Option RawCameron}
    (hpoly : PolyFun cameron) : PolyFun (camNbarBlocks cameron) := by
  have hf : PolyFun (fun q : RawCameron × (RawGens × List ℕ) =>
      some (rawNbar (q.1, q.2.1), camBlocks q.1)) :=
    ((((polyFun_fst.pair (polyFun_snd.comp polyFun_fst)).comp camPoly_rawNbar).pair
      (polyFun_fst.comp camPoly_blocks)).comp polyFun_some)
  exact ((hpoly.pair polyFun_id).comp (PolyFun.optionElim (polyFun_const none) hf)).of_eq
    (fun p => by unfold camNbarBlocks; cases cameron p <;> rfl)

/-- **Theorem 11.2.1, §11.2, with its algorithmic half, on the RAM.**  *"Let `G ≤ S_n` be a
primitive group of order `|G| ≥ n^{1+log₂ n}` where `n` is greater than some absolute
constant.  Then `G` has a normal subgroup `N` of index `≤ n` such that `N` has a system of
imprimitivity on which `N` acts as a Johnson group `A_k^{(t)}` with `k ≥ log₂ n`.  Moreover,
`N` and the system of imprimitivity in question can be found in polynomial time."*

There is one `RAM.PolyFun` routine that, on generators of such a group, returns generators of
`N` and the list of blocks, with all the conclusions of `Babai.Theorem_11_2_1` for them.  The
proof uses the cited `Babai.cameronStructure_polyTime` (C16) for the recognition, as the paper
does ("The algorithmic part is well known: Cameron groups can be recognized and their structure
mapped out in polynomial time"). -/
theorem theorem_11_2_1_ram :
    ∃ (n₀ : ℕ) (f : RawGens × List ℕ → Option (RawGens × RawBlocks)), PolyFun f ∧
      ∀ (n : ℕ) (gs : RawGens) (dom : List ℕ), dom.length = n → RawGens.WF n gs →
        n₀ ≤ n → Babai.IsPrimitive (decGroup n gs) →
        (n : ℝ) ^ (1 + Real.logb 2 n) ≤ Nat.card (decGroup n gs) →
        ∃ (ng : RawGens) (bl : RawBlocks), f (gs, dom) = some (ng, bl) ∧ RawGens.WF n ng ∧
          Babai.IsNormalIn (decGroup n ng) (decGroup n gs) ∧
          (decGroup n ng).relIndex (decGroup n gs) ≤ n ∧
          ∃ (hsys : Babai.IsSystemOfImprimitivity (decGroup n ng) Set.univ (blockSets n bl))
            (k t : ℕ), 1 ≤ t ∧ 2 * t < k ∧
            Babai.ActsAsJohnsonA (decGroup n ng) (blockSets n bl) hsys.permutes k t ∧
            Real.logb 2 n ≤ (k : ℝ) := by
  obtain ⟨cameron, hpoly, hspec⟩ := exists_polyFun_cameronSpec
  refine ⟨max 25 camDescentThreshold, camNbarBlocks cameron, polyFun_camNbarBlocks hpoly, ?_⟩
  intro n gs dom hd hw hn hp hb
  have hn25 : 25 ≤ n := le_trans (le_max_left _ _) hn
  have hn0 : camDescentThreshold ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨c, h, he, -, hlo, hhi⟩ := hspec n gs dom hd hw hn25 hp hb
  obtain ⟨c', h', he', hidx, hlog⟩ := camRecognize_index cameron hpoly hspec n gs dom hd hw
    hn25 hn0 hp hb
  have hcc : c' = c := Option.some.inj (he'.symm.trans he)
  subst hcc
  have hN : decGroup n (rawNbar (c', gs)) = camNbar c' h := rawNbar_spec h hw hlo hhi
  have hh : h = h' := rfl
  subst hh
  refine ⟨rawNbar (c', gs), camBlocks c', by simp [camNbarBlocks, he], rawNbar_wf h gs, ?_,
    ?_, ?_⟩
  · rw [hN]; exact camNbar_normal h _ hlo hhi
  · rw [hN]; exact hidx
  · rw [hN]
    exact ⟨camBlocks_system h, c'.k, c'.t, h.t_pos, h.k_gt, camBlocks_acts h, hlog⟩

end Algo

