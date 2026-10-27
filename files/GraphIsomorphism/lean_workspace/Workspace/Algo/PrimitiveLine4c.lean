import Workspace.Algo.PrimitiveRelations
import Workspace.Algo.SplitSolverCanonical
import Workspace.Algo.TopThreeRound

/-! # Section 15, line 4c on the RAM: the Extended Design Lemma on `H(x)` and `H(y)`

> 4c. else (: now their relative symmetry defect is `≥ 1/2` :)
>     (: view these hypergraphs as `t`-ary relational structures :)
>     apply Extended Design Lemma (Theorem 9.2.3)

The node reads the top action `(Ω, G) → (Γ, G^ϕ)` of the primitive case, the two strings
and the arity `t` of the standard blocks. For each string `z ∈ {x, y}` it builds the
`t`-ary relational structure of `H(z)` on `Γ = [m]` (`primitiveRelations`, one relation per
color of the palette) and runs the Extended Design Lemma on it at `α = 3/4`
(`extendedSplitFamily`). The result is the two lists of versions, the canonical family of
Sec. 14.2 at `x` and at `y`.

**The palette.** The paper has one relation per color of the alphabet. The machine's letters
are numbers, so it takes one relation per entry of `0 :: x ++ y`: every letter the two
strings use is listed (the `0` is the letter `decStrN` reads beyond the end of a string),
some more than once, and relations for listed but unused letters are empty. A repeated
relation and an empty relation change neither the isomorphisms nor the automorphism group
of the structure, and the palette is the same list for `x` and for `y`, which is what makes
the two structures comparable relation by relation. Only the relative order of equal
structures matters to Theorem 9.2.3 on the RAM (`extendedSplitFamily_transport`), not a
particular enumeration of the alphabet.

The arity list is `List.range (min t m)`, which is `List.range t` in the primitive case
(`4t < m`) and has at most `m` entries on every input, so the node is quasipolynomial with no
premise.
-/

namespace Algo
open Babai RAM

/-- The node's input: the top action with both strings, and the arity `t`. -/
abbrev RawLine4cIn := RawTop3 × ℕ

/-- Line 4c: the palette, every letter of `x` and `y` and the letter `0`. -/
def line4cPalette (p : RawTop3) : List ℕ := 0 :: (p.2.1 ++ p.2.2)

/-- Line 4c: the arity list, `[0, t)` capped at `m`. -/
def line4cArity (z : RawLine4cIn) : List ℕ := List.range (min z.2 z.1.1.2.1.length)

/-- Line 4c: *"view these hypergraphs as `t`-ary relational structures"* — the admitted
input of Theorem 9.2.3 built from `H(z)` for the string `z`, at `α = 3/4`. The guard string
is `[0, |Ω|)` (the Extended Design Lemma reads only its length, the size of `Ω`; the labels
of `Ω` themselves play no part) and the domain list is `[0, m)`. -/
def line4cAmbient (z : RawLine4cIn × RawStr) : AmbientGIn :=
  (((line4cArity z.1, List.range z.1.1.1.1.1.length, List.range z.1.1.1.2.1.length),
    primitiveRelations 1 (((z.1.1.1, z.2), line4cArity z.1), line4cPalette z.1.1)), (3, 4))

/-- **Section 15, line 4c on the RAM**: *"apply Extended Design Lemma (Theorem 9.2.3)"* to
`H(x)` and to `H(y)`; the two lists of versions. `c`, `tt`, `dd` are the bounds of the
Theorem 9.2.2 solver inside. -/
def line4cVersions (c tt dd : ℕ) (z : RawLine4cIn) :
    List RawAlignOutcome × List RawAlignOutcome :=
  (extendedSplitFamily 1 c tt dd (line4cAmbient (z, z.1.2.1)),
    extendedSplitFamily 1 c tt dd (line4cAmbient (z, z.1.2.2)))

theorem polyFun_line4cPalette : PolyFun line4cPalette :=
  ((polyFun_const 0).pair (((polyFun_snd.comp polyFun_fst).pair
    (polyFun_snd.comp polyFun_snd)).comp polyFun_append)).comp polyFun_cons

theorem polyFun_line4cArity : PolyFun line4cArity :=
  (((((polyFun_fst.comp polyFun_fst).comp polyFun_snd).comp polyFun_fst).pair
    polyFun_snd).comp polyFun_rangeTake).of_eq (fun _ => rfl)

theorem quasiFun_line4cAmbient : QuasiFun line4cAmbient := by
  have hact : PolyFun (fun z : RawLine4cIn × RawStr => z.1.1.1) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_fst
  have hks : PolyFun (fun z : RawLine4cIn × RawStr => line4cArity z.1) :=
    polyFun_fst.comp polyFun_line4cArity
  have hbase : PolyFun (fun z : RawLine4cIn × RawStr => List.range z.1.1.1.1.1.length) :=
    ((hact.comp polyFun_fst).comp polyFun_fst).comp polyFun_rangeLength
  have hdom : PolyFun (fun z : RawLine4cIn × RawStr => List.range z.1.1.1.2.1.length) :=
    ((hact.comp polyFun_snd).comp polyFun_fst).comp polyFun_rangeLength
  have hpal : PolyFun (fun z : RawLine4cIn × RawStr => line4cPalette z.1.1) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_line4cPalette
  have hrel := ((((hact.pair polyFun_snd).pair hks).pair hpal).comp_quasiFun
    (quasiFun_primitiveRelations 1))
  exact (((hks.pair (hbase.pair hdom)).quasiFun.pair hrel).pair
    (polyFun_const ((3, 4) : ℕ × ℕ)).quasiFun).of_eq (fun _ => rfl)

/-- The node is quasipolynomial on the RAM, on every input. -/
theorem quasiFun_line4cVersions (c tt dd : ℕ) : QuasiFun (line4cVersions c tt dd) := by
  have hx := ((polyFun_id.pair ((polyFun_fst.comp polyFun_snd).comp
    polyFun_fst)).comp_quasiFun quasiFun_line4cAmbient).comp
    (quasiFun_extendedSplitFamily 1 c tt dd)
  have hy := ((polyFun_id.pair ((polyFun_fst.comp polyFun_snd).comp
    polyFun_snd)).comp_quasiFun quasiFun_line4cAmbient).comp
    (quasiFun_extendedSplitFamily 1 c tt dd)
  exact (hx.pair hy).of_eq (fun _ => rfl)

/-- **The number of versions**, Sec. 14.2's multiplicative cost of line 4c, is
quasipolynomial in the size of the node's input, with one exponent for every input. -/
theorem line4cVersions_length_le (c tt dd : ℕ) : ∃ e : ℕ, ∀ z : RawLine4cIn,
    (line4cVersions c tt dd z).1.length ≤ 2 ^ ((Nat.log 2 (Enc.size z) + 2) ^ e) ∧
    (line4cVersions c tt dd z).2.length ≤ 2 ^ ((Nat.log 2 (Enc.size z) + 2) ^ e) := by
  obtain ⟨e, he⟩ := (quasiFun_line4cVersions c tt dd).size
  refine ⟨e, fun z => ⟨?_, ?_⟩⟩
  · exact ((length_le_size _).trans (size_fst_le' _)).trans (he z)
  · exact ((length_le_size _).trans (size_snd_le' _)).trans (he z)

end Algo

#print axioms Algo.quasiFun_line4cVersions
#print axioms Algo.line4cVersions_length_le
