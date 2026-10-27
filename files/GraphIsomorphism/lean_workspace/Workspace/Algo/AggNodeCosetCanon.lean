import Workspace.Algo.Luks
import Workspace.Algo.ChainTransversal

/-! # Choosing a coset representative by its successive images

Section 13.1, Proposition 13.1.11 permits any element of the current
comparison coset. To obtain one computation tree for every encoding of an
answer, we choose the least image at each successive point. A row of the
stabilizer chain supplies all possible images at that point.
-/
namespace Algo
open RAM RAM.Targets Equiv
open scoped Pointwise

/-- Choose the candidate with the smaller image at one point. -/
def aggnChooseAt (p : ℕ × (RawPerm × RawPerm)) : RawPerm :=
  if rawApply (p.2.1, p.1) ≤ rawApply (p.2.2, p.1) then p.2.1 else p.2.2

private theorem aggnFoldMin_spec {α : Type*} (key : α → ℕ) (l : List α) (a : α) :
    let r := l.foldl (fun x y => if key x ≤ key y then x else y) a
    r ∈ a :: l ∧ key r ≤ key a ∧ ∀ b ∈ l, key r ≤ key b := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
    dsimp only at ih ⊢
    rw [List.foldl_cons]
    by_cases h : key a ≤ key b
    · rw [if_pos h]
      obtain ⟨hm, ha, hl⟩ := ih a
      refine ⟨?_, ha, ?_⟩
      · rcases List.mem_cons.mp hm with hm | hm
        · exact List.mem_cons.mpr (Or.inl hm)
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm)
      · intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact ha.trans h
        · exact hl c hc
    · rw [if_neg h]
      obtain ⟨hm, hb, hl⟩ := ih b
      refine ⟨List.mem_cons_of_mem _ hm, hb.trans (by omega), ?_⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact hb
      · exact hl c hc

/-- One row of the chain, with products formed on the current coset. -/
def aggnCanonStep (p : (RawTable × RawStr) × (RawPerm × ℕ)) : RawPerm :=
  normPerm (p.1.2,
    ((rawRowAt (p.1.1, p.2.2)).map (fun r => rawMul (p.2.1, r))).foldl
      (fun a b => aggnChooseAt (p.2.2, (a, b))) p.2.1)

/-- The complete image scan, using the original source names in order. -/
def aggnCanonCoset (p : (RawStr × RawGens) × RawPerm) : RawPerm :=
  (List.range p.1.1.length).foldl
    (fun r i => aggnCanonStep ((rawBuildTable (p.1.1, normGens p.1), p.1.1), (r, i)))
    (normPerm (p.1.1, p.2))

/-- The prefix of the lexicographically least element of a coset. -/
def AggnPrefixMin {n : ℕ} (K : Set (Perm (Fin n))) (r : Perm (Fin n)) (k : ℕ) : Prop :=
  r ∈ K ∧ ∀ i < k, ∀ q ∈ K,
    (∀ j < i, evalAt q j = evalAt r j) → evalAt r i ≤ evalAt q i

private theorem aggnCoset_residual {n i : ℕ} {G : Subgroup (Perm (Fin n))}
    {σ r q : Perm (Fin n)} (hr : r ∈ σ • (G : Set (Perm (Fin n))))
    (hq : q ∈ σ • (G : Set (Perm (Fin n))))
    (he : ∀ j < i, evalAt q j = evalAt r j) : r⁻¹ * q ∈ chainStab G i := by
  refine ⟨?_, fixes_of_evalAt ?_⟩
  · obtain ⟨a, ha, rfl⟩ := hr
    obtain ⟨b, hb, rfl⟩ := hq
    simpa only [smul_eq_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left] using
      G.mul_mem (G.inv_mem ha) hb
  · intro j hj
    rw [evalAt_mul, he j hj, evalAt_inv_left]

/-- At level `i`, the chosen product has the least possible image in the
current coset of the prefix stabilizer. -/
theorem aggnCanonStep_spec {n : ℕ} (dom : RawStr) (hd : dom.length = n)
    (gens : List (Perm (Fin n))) (r : Perm (Fin n)) {i : ℕ} (hi : i < n) :
    ∃ h ∈ chainStab (genGroup gens) i,
      aggnCanonStep ((rawBuildTable (dom, gens.map (encPerm n)), dom), (encPerm n r, i)) =
        encPerm n (r * h) ∧
      ∀ q ∈ chainStab (genGroup gens) i, evalAt (r * h) i ≤ evalAt (r * q) i := by
  have hrows := rawRow_spec dom hd gens i
  rw [rawRow_eq_rawRowAt] at hrows
  let cs := (rowPerms n gens i).map (fun τ => encPerm n (r * τ))
  let a := cs.foldl (fun a b => aggnChooseAt (i, (a, b))) (encPerm n r)
  have hm := aggnFoldMin_spec (fun p => rawApply (p, i)) cs (encPerm n r)
  change a ∈ encPerm n r :: cs ∧ rawApply (a, i) ≤ rawApply (encPerm n r, i) ∧
    ∀ b ∈ cs, rawApply (a, i) ≤ rawApply (b, i) at hm
  have hex : ∃ h ∈ chainStab (genGroup gens) i, a = encPerm n (r * h) := by
    rcases List.mem_cons.mp hm.1 with he | he
    · exact ⟨1, (chainStab _ i).one_mem, by simpa using he⟩
    · obtain ⟨τ, hτ, he⟩ := List.mem_map.mp he
      exact ⟨τ, rowPerms_subset_chainStab n gens i hτ, he.symm⟩
  obtain ⟨h, hh, he⟩ := hex
  refine ⟨h, hh, ?_, ?_⟩
  · unfold aggnCanonStep
    rw [hrows, List.map_map]
    dsimp only [Function.comp_def, Prod.fst, Prod.snd]
    have hc : (List.map (fun x => rawMul (encPerm n r, encPerm n x)) (rowPerms n gens i)) = cs := by
      exact List.map_congr_left (fun τ _ => rawMul_encPerm n r τ)
    rw [hc]
    change normPerm (dom, a) = _
    rw [he]
    apply (encPerm_decPerm (wf_normPerm hd _)).symm.trans
    rw [decPerm_normPerm hd, decPerm_encPerm]
  · intro q hq
    obtain ⟨p, ⟨hp, hu, hprod⟩, -⟩ := rowPerms_transversal n gens
      (i := i) (k := n - i - 1) (by omega) hq
    have hmin := hm.2.2 (encPerm n (r * p.1)) (List.mem_map.mpr ⟨p.1, hp, rfl⟩)
    rw [he, rawApply_encPerm n _ hi, rawApply_encPerm n _ hi] at hmin
    have hfix : evalAt p.2 i = i := (mem_chainStab.mp hu).2.evalAt (by omega)
    have heval : evalAt (r * q) i = evalAt (r * p.1) i := by
      rw [hprod, ← mul_assoc, evalAt_mul (r * p.1), hfix]
    rw [heval]
    simpa only [evalAt_of_lt _ hi] using hmin

/-- A greedy image step preserves all earlier choices. -/
theorem AggnPrefixMin.step {n i : ℕ} {G : Subgroup (Perm (Fin n))}
    {σ r h : Perm (Fin n)} (hr : AggnPrefixMin (σ • (G : Set (Perm (Fin n)))) r i)
    (hh : h ∈ chainStab G i)
    (hmin : ∀ q ∈ chainStab G i, evalAt (r * h) i ≤ evalAt (r * q) i) :
    AggnPrefixMin (σ • (G : Set (Perm (Fin n)))) (r * h) (i + 1) := by
  have hsame : ∀ j < i, evalAt (r * h) j = evalAt r j := by
    intro j hj
    rw [evalAt_mul, (mem_chainStab.mp hh).2.evalAt hj]
  refine ⟨?_, ?_⟩
  · obtain ⟨a, ha, rfl⟩ := hr.1
    exact ⟨a * h, G.mul_mem ha hh.1, by simp [smul_eq_mul, mul_assoc]⟩
  · intro j hj q hq he
    by_cases hji : j < i
    · rw [hsame j hji]
      exact hr.2 j hji q hq (fun k hk => (he k hk).trans (hsame k (by omega)))
    · have hji : j = i := by omega
      subst j
      have hres := aggnCoset_residual hr.1 hq (fun k hk => (he k hk).trans (hsame k hk))
      simpa only [mul_inv_cancel_left] using hmin (r⁻¹ * q) hres

/-- Full greedy prefixes determine one permutation, independently of how
the coset is represented. -/
theorem AggnPrefixMin.unique {n : ℕ} {K : Set (Perm (Fin n))} {r s : Perm (Fin n)}
    (hr : AggnPrefixMin K r n) (hs : AggnPrefixMin K s n) : r = s := by
  have he : ∀ i < n, evalAt r i = evalAt s i := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
      intro hi
      exact le_antisymm (hr.2 i hi s hs.1 (fun j hj => (ih j hj (by omega)).symm))
        (hs.2 i hi r hr.1 (fun j hj => ih j hj (by omega)))
  apply Equiv.ext
  intro i
  exact Fin.ext (by simpa only [evalAt_of_lt _ i.isLt] using he i i.isLt)

private theorem aggnCanonFold_spec {n : ℕ} (dom : RawStr) (hd : dom.length = n)
    (gens : List (Perm (Fin n))) (σ : Perm (Fin n)) :
    ∀ k i, i + k ≤ n → ∀ r, AggnPrefixMin (σ • (genGroup gens : Set (Perm (Fin n)))) r i →
      ∃ s, (List.range' i k).foldl
        (fun r j => aggnCanonStep ((rawBuildTable (dom, gens.map (encPerm n)), dom), (r, j)))
        (encPerm n r) = encPerm n s ∧
        AggnPrefixMin (σ • (genGroup gens : Set (Perm (Fin n)))) s (i + k) := by
  intro k
  induction k with
  | zero => intro i _ r hr; exact ⟨r, rfl, by simpa using hr⟩
  | succ k ih =>
    intro i hik r hr
    obtain ⟨h, hh, he, hmin⟩ := aggnCanonStep_spec dom hd gens r (i := i) (by omega)
    obtain ⟨s, hs, hspec⟩ := ih (i + 1) (by omega) (r * h) (hr.step hh hmin)
    refine ⟨s, ?_, by simpa only [Nat.add_assoc, Nat.add_comm 1 k] using hspec⟩
    rw [List.range'_succ, List.foldl_cons, he]
    exact hs

/-- The full scan is canonical for every raw encoding of a nonempty coset.
The generator and representative sanitizers keep the decoded coset fixed. -/
theorem aggnCanonCoset_spec {n : ℕ} {dom : RawStr} (hd : dom.length = n)
    (gs : RawGens) (r : RawPerm) :
    RawPerm.WF n (aggnCanonCoset ((dom, gs), r)) ∧
    AggnPrefixMin (decCoset n (some (gs, r)))
      (decPerm n (aggnCanonCoset ((dom, gs), r))) n := by
  let gens := (normGens (dom, gs)).map (decPerm n)
  let σ := decPerm n r
  have hgs : gens.map (encPerm n) = normGens (dom, gs) :=
    map_encPerm_decPerm (wf_normGens hd gs)
  have hr : normPerm (dom, r) = encPerm n σ := by
    rw [← encPerm_decPerm (wf_normPerm hd r), decPerm_normPerm hd]
  have hinit : AggnPrefixMin (σ • (genGroup gens : Set (Perm (Fin n)))) σ 0 :=
    ⟨⟨1, (genGroup gens).one_mem, by simp⟩, by simp⟩
  obtain ⟨s, hs, hspec⟩ := aggnCanonFold_spec dom hd gens σ n 0 (by omega) σ hinit
  have hout : aggnCanonCoset ((dom, gs), r) = encPerm n s := by
    unfold aggnCanonCoset
    dsimp only
    rw [hd, hr, ← hgs]
    simpa only [List.range_eq_range'] using hs
  rw [hout, decPerm_encPerm]
  refine ⟨wf_encPerm n s, ?_⟩
  have hG : genGroup gens = decGroup n gs := decGroup_normGens hd gs
  simpa only [Nat.zero_add, hG, decCoset_some] using hspec

/-- Equal decoded cosets give exactly the same raw representative, even
when their raw generators or representatives differ. -/
theorem aggnCanonCoset_eq_of_decode_eq {n : ℕ} {dom dom' : RawStr}
    (hd : dom.length = n) (hd' : dom'.length = n)
    {gs gs' : RawGens} {r r' : RawPerm}
    (he : decCoset n (some (gs, r)) = decCoset n (some (gs', r'))) :
    aggnCanonCoset ((dom, gs), r) = aggnCanonCoset ((dom', gs'), r') := by
  obtain ⟨hw, hm⟩ := aggnCanonCoset_spec hd gs r
  obtain ⟨hw', hm'⟩ := aggnCanonCoset_spec hd' gs' r'
  rw [he] at hm
  rw [← encPerm_decPerm hw, ← encPerm_decPerm hw', hm.unique hm']

theorem aggnPolyFun_chooseAt : PolyFun aggnChooseAt := by
  have ha : PolyFun (fun p : ℕ × (RawPerm × RawPerm) => rawApply (p.2.1, p.1)) :=
    ((polyFun_snd.comp polyFun_fst).pair polyFun_fst).comp polyFun_rawApply
  have hb : PolyFun (fun p : ℕ × (RawPerm × RawPerm) => rawApply (p.2.2, p.1)) :=
    ((polyFun_snd.comp polyFun_snd).pair polyFun_fst).comp polyFun_rawApply
  exact (PolyFun.ite ((ha.pair hb).comp polyFun_le)
    (polyFun_snd.comp polyFun_fst) (polyFun_snd.comp polyFun_snd)).of_eq
      (fun p => by simp [aggnChooseAt])

private theorem aggnPolyFun_minFold :
    PolyFun (fun p : ℕ × (RawPerm × RawGens) =>
      p.2.2.foldl (fun a b => aggnChooseAt (p.1, (a, b))) p.2.1) := by
  apply PolyFun.foldlParam aggnPolyFun_chooseAt polyBound_id
  intro i a l j
  have hm := (aggnFoldMin_spec (fun p => rawApply (p, i)) (l.take j) a).1
  rcases List.mem_cons.mp hm with hm | hm
  · change Enc.size (List.foldl (fun x y => if rawApply (x, i) ≤ rawApply (y, i) then x else y) a (l.take j)) ≤ _
    rw [hm]
    exact (size_fst_le' (a, l)).trans (size_snd_le' (i, (a, l)))
  · exact ((size_mem_le hm).trans (size_take_le j l)).trans
      ((size_snd_le' (a, l)).trans (size_snd_le' (i, (a, l))))

theorem aggnPolyFun_canonStep : PolyFun aggnCanonStep := by
  have hr : PolyFun (fun p : (RawTable × RawStr) × (RawPerm × ℕ) =>
      rawRowAt (p.1.1, p.2.2)) :=
    ((polyFun_fst.comp polyFun_fst).pair (polyFun_snd.comp polyFun_snd)).comp polyFun_rawRowAt
  have hc : PolyFun (fun p : (RawTable × RawStr) × (RawPerm × ℕ) =>
      (rawRowAt (p.1.1, p.2.2)).map (fun r => rawMul (p.2.1, r))) :=
    ((polyFun_snd.comp polyFun_fst).pair hr).comp polyFun_rawGensMul
  have hm := (((polyFun_snd.comp polyFun_snd).pair
    ((polyFun_snd.comp polyFun_fst).pair hc)).comp aggnPolyFun_minFold)
  exact ((polyFun_fst.comp polyFun_snd).pair hm).comp polyFun_normPerm

private theorem aggnCanonFold_wf (t : RawTable) (dom : RawStr) (l : List ℕ) (a : RawPerm) :
    let r := l.foldl (fun r i => aggnCanonStep ((t, dom), (r, i))) a
    r = a ∨ RawPerm.WF dom.length r := by
  induction l generalizing a with
  | nil => exact Or.inl rfl
  | cons i l ih =>
    dsimp only
    rw [List.foldl_cons]
    rcases ih (aggnCanonStep ((t, dom), (a, i))) with h | h
    · apply Or.inr
      rw [h]
      exact wf_normPerm rfl _
    · exact Or.inr h

private theorem aggnPolyFun_canonFold :
    PolyFun (fun p : (RawTable × RawStr) × (RawPerm × List ℕ) =>
      p.2.2.foldl (fun r i => aggnCanonStep (p.1, (r, i))) p.2.1) := by
  have hpoly : PolyBound (fun m => m + (1 + m * (2 * (m + 2) + 1))) :=
    polyBound_id.add ((polyBound_const 1).add
      (polyBound_id.mul (((polyBound_const 2).mul (polyBound_id.add (polyBound_const 2))).add
        (polyBound_const 1))))
  apply PolyFun.foldlParam aggnPolyFun_canonStep hpoly
  rintro ⟨t, dom⟩ a l j
  set N := Enc.size ((t, dom), (a, l))
  have ha : Enc.size a ≤ N :=
    (size_fst_le' (a, l)).trans (size_snd_le' ((t, dom), (a, l)))
  have hd : dom.length ≤ N := (length_le_size dom).trans
    ((size_snd_le' (t, dom)).trans (size_fst_le' ((t, dom), (a, l))))
  rcases aggnCanonFold_wf t dom (l.take j) a with h | h
  · rw [h]
    omega
  · have hs := size_natList_le (L := N) (m := N)
      (h.length.le.trans hd) (fun u hu => (h.lt hu).trans_le hd)
    exact hs.trans (Nat.le_add_left _ _)

/-- The canonical representative is computed in polynomial RAM time,
including on malformed inputs. All loops traverse stored lists. -/
theorem aggnPolyFun_canonCoset : PolyFun aggnCanonCoset := by
  have hd : PolyFun (fun p : (RawStr × RawGens) × RawPerm => p.1.1) :=
    polyFun_fst.comp polyFun_fst
  have ht : PolyFun (fun p : (RawStr × RawGens) × RawPerm =>
      rawBuildTable (p.1.1, normGens p.1)) :=
    (hd.pair (polyFun_fst.comp polyFun_normGens)).comp polyFun_rawBuildTable
  have hr : PolyFun (fun p : (RawStr × RawGens) × RawPerm => normPerm (p.1.1, p.2)) :=
    (hd.pair polyFun_snd).comp polyFun_normPerm
  exact ((ht.pair hd).pair (hr.pair (hd.comp polyFun_rangeLength))).comp aggnPolyFun_canonFold


/-- The mathematical representative fixed by the ambient point order.
The default is relevant only to sets without a full greedy prefix. -/
noncomputable def aggnLeastPerm {n : ℕ} (K : Set (Perm (Fin n))) : Perm (Fin n) := by
  classical
  exact if h : ∃ r, AggnPrefixMin K r n then h.choose else 1

theorem aggnLeastPerm_eq {n : ℕ} {K : Set (Perm (Fin n))} {r : Perm (Fin n)}
    (h : AggnPrefixMin K r n) : aggnLeastPerm K = r := by
  classical
  have he : ∃ r, AggnPrefixMin K r n := ⟨r, h⟩
  rw [aggnLeastPerm, dif_pos he]
  exact AggnPrefixMin.unique he.choose_spec h

/-- Every nonempty coset has the full greedy prefix supplied by the scan. -/
theorem aggnLeastPerm_coset {n : ℕ} (H : Subgroup (Perm (Fin n))) (σ : Perm (Fin n)) :
    AggnPrefixMin (σ • (H : Set (Perm (Fin n)))) (aggnLeastPerm (σ • (H : Set (Perm (Fin n))))) n := by
  classical
  let gs : List (Perm (Fin n)) := (Finset.univ : Finset H).toList.map Subtype.val
  have hgs : genGroup gs = H := by
    have he : {g | g ∈ gs} = (H : Set (Perm (Fin n))) := by
      ext g
      simp [gs]
    rw [genGroup, he, Subgroup.closure_eq]
  have hc := (aggnCanonCoset_spec (n := n) (dom := List.range n) (by simp)
    (gs.map (encPerm n)) (encPerm n σ)).2
  have hG : decGroup n (gs.map (encPerm n)) = H := by
    rw [decGroup, List.map_map]
    simpa only [Function.comp_def, decPerm_encPerm, List.map_id_fun', id_eq] using hgs
  rw [decCoset_some, decPerm_encPerm, hG] at hc
  rw [aggnLeastPerm_eq hc]
  exact hc

/-- The mathematical representative and the executable one coincide for
all encodings of a nonempty coset. -/
theorem aggnCanonCoset_eq_least {n : ℕ} {dom : RawStr} (hd : dom.length = n)
    (gs : RawGens) (r : RawPerm) :
    aggnCanonCoset ((dom, gs), r) = encPerm n (aggnLeastPerm (decCoset n (some (gs, r)))) := by
  obtain ⟨hw, hm⟩ := aggnCanonCoset_spec hd gs r
  rw [aggnLeastPerm_eq hm, encPerm_decPerm hw]

end Algo
