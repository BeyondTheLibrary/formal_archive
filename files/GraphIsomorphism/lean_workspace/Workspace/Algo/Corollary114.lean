/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

§1.1, Corollary 1.1.4 on the RAM.
-/
import Workspace.Algo.Corollary113
import Workspace.Machine.ColGIRaw

/-!
# Corollary 1.1.4

> **Corollary 1.1.4.** Isomorphism of vertex-colored graphs (isomorphisms preserve color by
> definition) can be decided in time, polynomial in the number of vertices and quasipolynomial
> in the largest color multiplicity.

The paper states this as a consequence of Corollary 1.1.3 without the reduction. The reduction
used here (`Workspace/Machine/ColGIInstance.lean`) puts the two graphs side by side on `2n`
points, takes for `G` the group of all color-preserving permutations of the `2n` points (given by
the transpositions of equally colored points), and encodes the two graphs as two strings on the
`(2n)²` ordered pairs; the colored graphs are isomorphic exactly when the strings are
`G`-isomorphic, and every orbit of `G` on pairs has at most `(2k)²` points, `k` the largest color
multiplicity. Corollary 1.1.3 (`Algo.orbit_workspace`) then decides the instance in time
polynomial in the instance size, hence in `n`, and quasipolynomial in `(2k)²`, hence in `k`.

## Main results

* `Algo.size_colGIInput_le`: the input size is at most `132 (n + 1)²`;
* `Algo.polyQuasi_absorb'`: `c (N+1)^d · 2^((log M + 2)^{c'}) ≤ polyQuasiBound (c + d + c') N M`
  for every `N`, including `N = 0`;
* `Algo.corollary_1_1_4`: `RAM.Targets.Corollary_1_1_4_statement`.
-/

namespace Algo
open RAM RAM.Targets RAM.ColGIReduction Babai Equiv

/-- **The input size is polynomial in the number of vertices.** -/
theorem size_colGIInput_le {n : ℕ} (a : ColGIInput n) : Enc.size a ≤ pw 132 2 n := by
  have hraw : Enc.size a.raw = Enc.size a := size_eq_of_encode_eq rfl
  have hcol : ∀ c : Fin n → Fin n,
      Enc.size (List.ofFn fun u => (c u : ℕ)) ≤ 1 + n * (2 * (n + 2) + 1) := by
    intro c
    have hent : ∀ x ∈ (List.ofFn fun u => (c u : ℕ)), Enc.size x ≤ n + 2 := by
      intro x hx
      obtain ⟨u, rfl⟩ := List.mem_ofFn.mp hx
      have h1 := size_nat_le_of_le (c u).isLt.le
      have h2 : Enc.size n = Nat.size n + 2 := Small.size_nat n
      have h3 : Nat.size n ≤ n := size_le_self n
      omega
    simpa using size_list_le_of_entries _ (n + 2) hent
  have hX := graphMatrix_size a.X
  have hY := graphMatrix_size a.Y
  have hcX := hcol a.cX
  have hcY := hcol a.cY
  have p1 := size_pair_le' a.raw
  have p2 := size_pair_le' a.raw.2
  have p3 := size_pair_le' a.raw.2.2
  simp only [ColGIInput.raw] at p1 p2 p3
  rw [← hraw]
  simp only [ColGIInput.raw]
  unfold pw
  nlinarith

/-- `c + y ≤ 2^c · y` for `y ≥ 1`. -/
theorem add_le_two_pow_mul {c y : ℕ} (hy : 1 ≤ y) : c + y ≤ 2 ^ c * y := by
  have h : c + 1 ≤ 2 ^ c := Nat.lt_two_pow_self
  nlinarith

/-- **Absorbing the constants**, for every `N`. -/
theorem polyQuasi_absorb' {c d c' N M : ℕ} :
    pw c d N * 2 ^ ((Nat.log 2 M + 2) ^ c') ≤ polyQuasiBound (c + d + c') N M := by
  unfold pw polyQuasiBound
  set L := Nat.log 2 M + 2
  have hL : 2 ≤ L := by omega
  have hy : 1 ≤ L ^ c' := Nat.one_le_pow _ _ (by omega)
  have hc : c ≤ 2 ^ c := (Nat.lt_two_pow_self).le
  have hexp : c + L ^ c' ≤ L ^ (c + d + c') := by
    calc c + L ^ c' ≤ 2 ^ c * L ^ c' := add_le_two_pow_mul hy
      _ ≤ L ^ c * L ^ c' := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hL c)
      _ = L ^ (c + c') := by rw [pow_add]
      _ ≤ L ^ (c + d + c') := Nat.pow_le_pow_right (by omega) (by omega)
  calc c * (N + 1) ^ d * 2 ^ L ^ c' = (N + 1) ^ d * (c * 2 ^ L ^ c') := by ring
    _ ≤ (N + 1) ^ d * (2 ^ c * 2 ^ L ^ c') := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hc)
    _ = (N + 1) ^ d * 2 ^ (c + L ^ c') := by rw [pow_add]
    _ ≤ (N + 1) ^ (c + d + c') * 2 ^ L ^ (c + d + c') :=
        Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) (by omega))
          (Nat.pow_le_pow_right (by norm_num) hexp)

/-- The arithmetic of the last step of `Algo.corollary_1_1_4`. -/
theorem cor114_arith {m Mn t1 T1 P2 P2' Q0 Q t3 T3 fb : ℕ} (hQ : 1 ≤ Q) (hm : m ≤ Mn)
    (h1 : t1 ≤ T1) (h2 : P2 ≤ P2') (hQ0 : Q0 ≤ Q) (h3 : t3 ≤ T3) (hfb : fb ≤ 3) :
    18 * m + 78 + (t1 + P2 * Q0 + t3 + (7 * fb + 34)) ≤
      (18 * Mn + (112 + 7 * 3) + T1 + P2' + T3) * Q := by
  have a1 : P2 * Q0 ≤ P2' * Q := Nat.mul_le_mul h2 hQ0
  have a2 : 18 * Mn + 133 + T1 + T3 ≤ (18 * Mn + 133 + T1 + T3) * Q := Nat.le_mul_of_pos_right _ hQ
  have e : (18 * Mn + (112 + 7 * 3) + T1 + P2' + T3) * Q =
      (18 * Mn + 133 + T1 + T3) * Q + P2' * Q := by ring
  omega

/-- **Corollary 1.1.4** (§1.1): isomorphism of vertex-colored graphs is decided on the RAM model
of `Workspace/Machine/` within a time polynomial in the number `n` of vertices and
quasipolynomial in the largest color multiplicity, by one program for all `n`. The route: the
reduction of `RAM.ColGIReduction.instanceSI` (built on the machine by
`RAM.ColGIReduction.build`), then Corollary 1.1.3 (`Algo.orbit_workspace`), then reading the
answer tag. -/
theorem corollary_1_1_4 : Corollary_1_1_4_statement := by
  obtain ⟨Prog, c, d, c', hrun⟩ := orbit_workspace
  obtain ⟨B, cB, dB, hB, hBsz⟩ := polyFun_witness polyFun_build
  obtain ⟨D, cD, dD, hD, -⟩ := polyFun_witness SIDecision.polyFun_answerTag
  obtain ⟨cc, dc, hcc⟩ := polyBound_chainBound
  -- the quasipolynomial of `(2k)²` as a quasipolynomial of `k`
  have hsq : PolyBound (fun k => (2 * k) * (2 * k)) :=
    ((polyBound_const 2).mul polyBound_id).mul ((polyBound_const 2).mul polyBound_id)
  obtain ⟨c'', hc''⟩ := (quasiPolyBound_witness c').comp_poly hsq
  -- the polynomial part, as a function of `n`
  have hF : PolyBound (fun n => 18 * pw 132 2 n + (112 + 7 * 3) + pw cB dB (pw 132 2 n) +
      pw c d (pw cB dB (pw 132 2 n)) + pw cD dD (pw cc dc (pw cB dB (pw 132 2 n)))) := by
    have hM : PolyBound (pw 132 2) := polyBound_pw 132 2
    have hI : PolyBound (fun n => pw cB dB (pw 132 2 n)) := (polyBound_pw cB dB).comp hM
    exact (((((polyBound_const 18).mul hM).add (polyBound_const (112 + 7 * 3))).add
      hI).add ((polyBound_pw c d).comp hI)).add
      ((polyBound_pw cD dD).comp ((polyBound_pw cc dc).comp hI))
  obtain ⟨cF, dF, hFb⟩ := hF
  refine ⟨RAM.seq Bridge.up (RAM.seq (RAM.seq (RAM.seq B Prog) D) Bridge.down),
    cF + dF + c'', fun n => ?_⟩
  let f : ColGIInput n → Bool := fun a => @decide (ColIso a).Nonempty (Classical.propDecidable _)
  refine ⟨f, fun a => by simp [f], fun a => ?_⟩
  have hBt : CleanComputeAt 16 B (instanceSI (n := n)) (fun m => cB * (m + 1) ^ dB) :=
    hB.transfer (e := fun a : ColGIInput n => a.raw) (fun _ => rfl)
      (fun a => encode_instanceSI a)
  obtain ⟨b, hb, hbsz, hr⟩ := hrun _ _ (instanceSI a)
  have hDt : CleanComputeAt 16 D
      (fun b : Option (List (Perm (Fin ((n + n) * (n + n)))) × Perm (Fin ((n + n) * (n + n)))) =>
        b.isSome) (fun m => cD * (m + 1) ^ dD) :=
    hD.transfer SIDecision.encode_rawAnswer (fun b => by cases b <;> rfl)
  have htag : b.isSome = f a := by
    apply Bool.eq_iff_iff.mpr
    simpa [f] using (SIDecision.answerTag_correct hb).trans (instanceSI_correct a)
  have hall := ((hBt.runsOn a).seq hr).seq (hDt.runsOn b)
  rw [htag] at hall
  obtain ⟨k, hk, hhalt, hout⟩ := hall.bridge
  refine ⟨k, le_trans hk ?_, hhalt, hout⟩
  -- the bounds
  have hm : Enc.size a ≤ pw 132 2 n := size_colGIInput_le a
  have hs1 : Enc.size (instanceSI a) ≤ pw cB dB (pw 132 2 n) := by
    have e1 : Enc.size (instanceSI a) = Enc.size (build a.raw) :=
      size_eq_of_encode_eq (encode_instanceSI a)
    have e2 : Enc.size a.raw = Enc.size a := size_eq_of_encode_eq rfl
    rw [e1]
    refine le_trans (hBsz a.raw) ?_
    rw [e2]
    exact pw_mono cB dB hm
  have hbs : Enc.size b ≤ pw cc dc (pw cB dB (pw 132 2 n)) :=
    le_trans hbsz (le_trans (hcc _) (pw_mono cc dc hs1))
  have hQ0 : 2 ^ ((Nat.log 2 (maxOrbitLength (instanceSI a).1) + 2) ^ c') ≤
      2 ^ ((Nat.log 2 (maxColorMultiplicity a) + 2) ^ c'') := by
    have horb := (maxOrbitLength_instanceSI_le a).trans (le_of_eq (sq _))
    exact le_trans (quasiPolyBound_witness_mono c' horb) (hc'' _)
  have hmain := cor114_arith (Nat.one_le_two_pow) hm (pw_mono cB dB hm) (pw_mono c d hs1) hQ0
    (pw_mono cD dD hbs) (Combine.size_bool_le (f a))
  refine le_trans hmain (le_trans (Nat.mul_le_mul_right _ (hFb n)) polyQuasi_absorb')

end Algo

#print axioms Algo.corollary_1_1_4
