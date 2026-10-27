import Workspace.Algo.AggNodeCompareRAM
import Workspace.Algo.AggNodeStateBounds

/-! # The comparison cache is independent of coset encoding size

Both the stored comparison coset and its canonical representative are
normalized before use. The number of representatives comes from the source
cache. Thus preparing a new cache does not feed a previous coset's size
back into its own bound.
-/
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1000000
namespace Algo
open RAM RAM.Targets

def aggnCompareCacheBound (b : ℕ) : ℕ :=
  256 * (b + chainBound b + (1 + b * (2 * strBound b + 1)) + 1)

theorem aggnPolyBound_compareCache : PolyBound aggnCompareCacheBound :=
  (polyBound_const 256).mul (((polyBound_id.add polyBound_chainBound).add
    ((polyBound_const 1).add (polyBound_id.mul
      (((polyBound_const 2).mul polyBound_strBound).add (polyBound_const 1))))).add
        (polyBound_const 1))

theorem aggnTranslateReps_wf (xs : RawStr) (q : RawCoset) (rs : RawGens) :
    RawGens.WF xs.length (aggnTranslateReps (xs, q, rs)) := by
  cases q with
  | none => intro r hr; simp [aggnTranslateReps] at hr
  | some q =>
    exact wf_rawGensMul (aggnCanonCoset_spec rfl q.1 q.2).1 (wf_normGens rfl rs)

theorem aggnTranslateReps_length (xs : RawStr) (q : RawCoset) (rs : RawGens) :
    (aggnTranslateReps (xs, q, rs)).length ≤ rs.length := by
  cases q <;> simp [aggnTranslateReps, rawGensMul, normGens]

/-- No size or validity premise is imposed on the current comparison coset. -/
theorem aggnCompareInput_size {c b : ℕ} (p : RawLCLoop) (ys : RawStr) (q : RawCoset)
    (hp : Enc.size (aggnrInputOf c p) ≤ b) (hx : Enc.size p.1.1 ≤ b)
    (hy : Enc.size ys ≤ b) :
    Enc.size (aggnCompareInputOf c (p, ys, q)) ≤ aggnCompareCacheBound b := by
  let P := aggnrInputOf c p
  let rs := aggnTranslateReps (p.1.1, q, P.2.2.1)
  let raw := q.getD ([], rawOne p.1.1)
  let gs := tidyGens (p.1.1, raw.1)
  let r := normPerm (p.1.1, raw.2)
  have hd : p.1.1.length ≤ b := (length_le_size p.1.1).trans hx
  have hcos : Enc.size (some (gs, r) : RawCoset) ≤ chainBound b :=
    size_coset_le' hd (wf_tidyGens rfl _) (length_tidyGens rfl _) (wf_normPerm rfl _)
  rw [size_some_eq] at hcos
  have hg : Enc.size gs ≤ chainBound b := (size_fst_le' (gs, r)).trans (by omega)
  have hr : Enc.size r ≤ chainBound b := (size_snd_le' (gs, r)).trans (by omega)
  have hwin : Enc.size (lcInst p).1.1 ≤ b :=
    ((size_fst_le' P.1).trans (size_fst_le' P)).trans hp
  have hker : Enc.size P.2.1 ≤ b :=
    ((size_fst_le' P.2).trans (size_snd_le' P)).trans hp
  have hwins : Enc.size P.2.2.2 ≤ b :=
    ((size_snd_le' P.2.2).trans ((size_snd_le' P.2).trans (size_snd_le' P))).trans hp
  have hn : rs.length ≤ b := (aggnTranslateReps_length p.1.1 q P.2.2.1).trans
    ((length_le_size P.2.2.1).trans
      (((size_fst_le' P.2.2).trans ((size_snd_le' P.2).trans (size_snd_le' P))).trans hp))
  have hrs : Enc.size rs ≤ 1 + b * (2 * strBound b + 1) := by
    apply (size_list_le_of_entries rs (strBound b) ?_).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_right _ hn) 1)
    intro a ha
    have hw := aggnTranslateReps_wf p.1.1 q P.2.2.1 a ha
    exact size_natList_le (hw.length ▸ hd) (fun u hu => (hw.lt hu).trans_le hd)
  have h0 := Combine.size_pair_le (aggnCompareWindow (p, ys, q)) (P.2.1, rs, P.2.2.2)
  have h1 := Combine.size_pair_le P.2.1 (rs, P.2.2.2)
  have h2 := Combine.size_pair_le rs P.2.2.2
  have h3 := Combine.size_pair_le (lcInst p).1.1 (gs, r, p.1.1, ys)
  have h4 := Combine.size_pair_le gs (r, p.1.1, ys)
  have h5 := Combine.size_pair_le r (p.1.1, ys)
  have h6 := Combine.size_pair_le p.1.1 ys
  change Enc.size ((lcInst p).1.1, gs, r, p.1.1, ys) ≤ _ at h3
  change Enc.size (aggnCompareWindow (p, ys, q)) ≤ _ at h3
  change Enc.size (aggnCompareWindow (p, ys, q), P.2.1, rs, P.2.2.2) ≤ _
  unfold aggnCompareCacheBound
  omega

end Algo
