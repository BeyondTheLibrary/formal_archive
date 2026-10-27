/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the kernel of an action given by the images of the generators
(§2.2.3, Proposition 2.2.6 (a)).
-/
import Workspace.Algo.ChainTransversal

/-!
# The kernel of an action given on the generators (Prop. 2.2.6 (a))

> **Proposition 2.2.6.** Let `G ≤ S(Ω)` be given by a list of generators and let
> `ϕ : G → S(Γ)` be a homomorphism given by the images of the generators.  Then
> **(a)** generators of `ker ϕ` can be found in polynomial time.

`Workspace/Algo/ChainTransversal.lean` does this for the restriction to a **window** `Δ ⊆ Ω`,
where the kernel is the pointwise stabilizer `G_{(Δ)}`.  A general action is not of that
shape: Theorem 11.1.9 descends to `N = ker(G → S(ℬ))`, whose elements fix the blocks
*setwise* and move the points of `Ω` freely.

This file reduces the general case to the window case, which is what Luks's algorithm does:
run the group on the **disjoint union** `Ω ⊔ Γ`.  A generator `g` is extended to the
permutation `g ⊔ ϕ(g)` of `Ω ⊔ Γ`, the extended group `E` acts on `Γ` as `ϕ` does, and
`ker ϕ` is the pointwise stabilizer of `Γ` inside `E`, read back on `Ω`.  So
`Algo.rawKerGens` and `Algo.rawCosetRepBin` apply verbatim, and Proposition 2.2.6 (a) for the
general action falls out of `Algo.cover_winCosetRep`.

## The two domains

`Ω` is `Fin n`, `Γ` is `Fin m`, and `Ω ⊔ Γ` is `Fin (n + m)` with `Ω` first.  A point of `Γ`
with the label `j` is therefore the point `n + j` of the big domain, and the window whose
pointwise stabilizer is wanted is `Algo.extWin n m = [n, …, n + m − 1]`.

## The homomorphism is a hypothesis, not a computation

A list of images of the generators does **not** in general define a homomorphism, and no
routine can be asked to check that it does (the check is at least as hard as membership
testing).  So `ϕ` is a hypothesis of every specification here, exactly as invariance of the
window is a hypothesis in `Workspace/Algo/Restrict.lean`.  The routines themselves are total.

## Main definitions

* `Algo.extHom`, `Algo.extPerm` — the permutation of `Ω ⊔ Γ` built from a pair;
* `Algo.rawExtPerm`, `Algo.rawExtGens` — the routine, and `Algo.extWin` the window;
* `Algo.rowsBefore`, `Algo.rawProjPerm`, `Algo.rawProjGens` — the read-back to `Ω`;
* `Algo.graphHom` — `g ↦ g ⊔ ϕ(g)`, whose range is the extended group;
* `Algo.actKerGens`, `Algo.actCosetRep`, `Algo.actCosetIndex` — the three routines of
  Proposition 2.2.6 (a) for a general action.

## Main results

* `Algo.decGroup_actKerGens` — **Prop. 2.2.6 (a)**: the routine returns generators of
  `ker ϕ`;
* `Algo.cover_actCosetRep` — the covering half: `G` is the union of the `|G : ker ϕ|` left
  cosets of `ker ϕ` with the computed representatives.

No axiom and no `sorry`.
-/

namespace Algo

open RAM RAM.Targets Equiv Equiv.Perm
open scoped Pointwise

variable {n m : ℕ}

/-! ## The permutation of the disjoint union -/

/-- **The permutation of `Ω ⊔ Γ = Fin (n + m)` built from a permutation of each part.** -/
def extHom (n m : ℕ) : Perm (Fin n) × Perm (Fin m) →* Perm (Fin (n + m)) :=
  (finSumFinEquiv.permCongrHom :
      Perm (Fin n ⊕ Fin m) ≃* Perm (Fin (n + m))).toMonoidHom.comp
    (Equiv.Perm.sumCongrHom (Fin n) (Fin m))

/-- `a ⊔ b`, the permutation of `Fin (n + m)` that acts as `a` on the first `n` points and as
`b` on the last `m`. -/
def extPerm (n m : ℕ) (a : Perm (Fin n)) (b : Perm (Fin m)) : Perm (Fin (n + m)) :=
  extHom n m (a, b)

theorem extPerm_apply (a : Perm (Fin n)) (b : Perm (Fin m)) (x : Fin (n + m)) :
    extPerm n m a b x = finSumFinEquiv (Sum.map a b (finSumFinEquiv.symm x)) := rfl

@[simp] theorem extPerm_castAdd (a : Perm (Fin n)) (b : Perm (Fin m)) (i : Fin n) :
    extPerm n m a b (Fin.castAdd m i) = Fin.castAdd m (a i) := by
  rw [extPerm_apply, finSumFinEquiv_symm_apply_castAdd]
  simp [finSumFinEquiv_apply_left]

@[simp] theorem extPerm_natAdd (a : Perm (Fin n)) (b : Perm (Fin m)) (j : Fin m) :
    extPerm n m a b (Fin.natAdd n j) = Fin.natAdd n (b j) := by
  rw [extPerm_apply, finSumFinEquiv_symm_apply_natAdd]
  simp [finSumFinEquiv_apply_right]

theorem extPerm_mul (a a' : Perm (Fin n)) (b b' : Perm (Fin m)) :
    extPerm n m (a * a') (b * b') = extPerm n m a b * extPerm n m a' b' := by
  rw [extPerm, extPerm, extPerm, ← map_mul]
  rfl

@[simp] theorem extPerm_one : extPerm n m 1 1 = 1 := by
  rw [extPerm, show ((1 : Perm (Fin n)), (1 : Perm (Fin m))) = 1 from rfl, map_one]

theorem extHom_injective : Function.Injective (extHom n m) :=
  ((finSumFinEquiv.permCongrHom :
      Perm (Fin n ⊕ Fin m) ≃* Perm (Fin (n + m))).injective).comp
    Equiv.Perm.sumCongrHom_injective

theorem extPerm_injective {a a' : Perm (Fin n)} {b b' : Perm (Fin m)}
    (h : extPerm n m a b = extPerm n m a' b') : a = a' ∧ b = b' :=
  Prod.mk.injEq .. ▸ (Prod.ext_iff.1 (extHom_injective h))

/-- **The value of `a ⊔ b` at a point of `Ω`**, read as a natural. -/
theorem extPerm_val_lt (a : Perm (Fin n)) (b : Perm (Fin m)) {i : ℕ} (hi : i < n)
    (hi' : i < n + m) :
    ((extPerm n m a b ⟨i, hi'⟩ : Fin (n + m)) : ℕ) = (a ⟨i, hi⟩ : Fin n) := by
  have hx : (⟨i, hi'⟩ : Fin (n + m)) = Fin.castAdd m ⟨i, hi⟩ := rfl
  rw [hx, extPerm_castAdd]
  rfl

/-- **The value of `a ⊔ b` at a point of `Γ`**, read as a natural. -/
theorem extPerm_val_ge (a : Perm (Fin n)) (b : Perm (Fin m)) {j : ℕ} (hj : j < m)
    (hj' : n + j < n + m) :
    ((extPerm n m a b ⟨n + j, hj'⟩ : Fin (n + m)) : ℕ) = n + (b ⟨j, hj⟩ : Fin m) := by
  have hx : (⟨n + j, hj'⟩ : Fin (n + m)) = Fin.natAdd n ⟨j, hj⟩ := rfl
  rw [hx, extPerm_natAdd]
  rfl

/-! ## The routine -/

/-- **One generator extended to `Ω ⊔ Γ`**: its table on `Ω`, then its table on `Γ` shifted by
the size of `Ω`. -/
def rawExtPerm (p : RawPerm × RawPerm) : RawPerm := p.1 ++ p.2.map (fun u => u + p.1.length)

/-- **A list of generators extended to `Ω ⊔ Γ`**, one image per generator. -/
def rawExtGens (p : RawGens × RawGens) : RawGens := (p.1.zip p.2).map rawExtPerm

@[simp] theorem length_rawExtPerm (g h : RawPerm) :
    (rawExtPerm (g, h)).length = g.length + h.length := by simp [rawExtPerm]

/-- **The routine computes `a ⊔ b`.** -/
theorem rawExtPerm_spec (a : Perm (Fin n)) (b : Perm (Fin m)) :
    rawExtPerm (encPerm n a, encPerm m b) = encPerm (n + m) (extPerm n m a b) := by
  have hA : (encPerm n a).length = n := length_encPerm n a
  show encPerm n a ++ (encPerm m b).map (fun u => u + (encPerm n a).length)
      = encPerm (n + m) (extPerm n m a b)
  rw [hA, show encPerm (n + m) (extPerm n m a b)
      = List.ofFn (fun k : Fin (n + m) => ((extPerm n m a b k : Fin (n + m)) : ℕ)) from rfl,
    List.ofFn_add]
  congr 1
  · show List.ofFn (fun i : Fin n => ((a i : Fin n) : ℕ))
        = List.ofFn (fun i : Fin n =>
            ((extPerm n m a b (i.castLE (Nat.le_add_right n m)) : Fin (n + m)) : ℕ))
    refine congrArg List.ofFn (funext (fun i => ?_))
    rw [show i.castLE (Nat.le_add_right n m) = Fin.castAdd m i from rfl, extPerm_castAdd]
    rfl
  · show (List.ofFn (fun j : Fin m => ((b j : Fin m) : ℕ))).map (fun u => u + n)
        = List.ofFn (fun j : Fin m =>
            ((extPerm n m a b (j.natAdd n) : Fin (n + m)) : ℕ))
    rw [List.map_ofFn]
    refine congrArg List.ofFn (funext (fun j => ?_))
    rw [Function.comp_apply, extPerm_natAdd]
    show ((b j : Fin m) : ℕ) + n = n + ((b j : Fin m) : ℕ)
    omega

/-- **The routine extends a whole generating list.** -/
theorem rawExtGens_spec (gens : List (Perm (Fin n))) (imgs : List (Perm (Fin m)))
    (hlen : gens.length = imgs.length) :
    rawExtGens (gens.map (encPerm n), imgs.map (encPerm m))
      = ((gens.zip imgs).map (fun p => extPerm n m p.1 p.2)).map (encPerm (n + m)) := by
  rw [rawExtGens, List.zip_map, List.map_map, List.map_map]
  refine List.map_congr_left (fun p _ => ?_)
  exact rawExtPerm_spec p.1 p.2

/-- The extended permutations are well formed for the degree `n + m`. -/
theorem wf_rawExtGens (gens : List (Perm (Fin n))) (imgs : List (Perm (Fin m)))
    (hlen : gens.length = imgs.length) :
    RawGens.WF (n + m) (rawExtGens (gens.map (encPerm n), imgs.map (encPerm m))) := by
  rw [rawExtGens_spec gens imgs hlen]
  intro g hg
  obtain ⟨σ, -, rfl⟩ := List.mem_map.1 hg
  exact wf_encPerm _ _

theorem polyFun_rawExtPerm : PolyFun rawExtPerm := by
  have hf : PolyFun (fun z : ℕ × ℕ => z.2 + z.1) :=
    (polyFun_snd.pair polyFun_fst).comp polyFun_add
  have hin : PolyFun (fun p : RawPerm × RawPerm => ((p.1.length, p.2) : ℕ × List ℕ)) :=
    (polyFun_fst.comp polyFun_length).pair polyFun_snd
  have hshift : PolyFun (fun p : RawPerm × RawPerm =>
      p.2.map (fun u => u + p.1.length)) :=
    (hin.comp (PolyFun.mapParam hf)).of_eq (fun _ => rfl)
  exact (polyFun_fst.pair hshift).comp polyFun_append

theorem polyFun_rawExtGens : PolyFun rawExtGens :=
  (polyFun_zip.comp (PolyFun.map polyFun_rawExtPerm)).of_eq (fun _ => rfl)

/-! ## The window `Γ` inside `Ω ⊔ Γ`, and the read-back to `Ω` -/

/-- **The points of `Γ` inside `Ω ⊔ Γ`**: `[n, …, n + m − 1]`. -/
def extWin (n m : ℕ) : List ℕ := (List.range m).map (fun j => j + n)

@[simp] theorem length_extWin (n m : ℕ) : (extWin n m).length = m := by simp [extWin]

theorem nodup_extWin (n m : ℕ) : (extWin n m).Nodup := by
  rw [extWin]
  exact (List.nodup_range).map (fun a b h => by omega)

theorem lt_extWin {u : ℕ} (h : u ∈ extWin n m) : u < n + m := by
  rw [extWin] at h
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 h
  have := List.mem_range.1 hj
  omega

theorem mem_extWin {u : ℕ} : u ∈ extWin n m ↔ n ≤ u ∧ u < n + m := by
  rw [extWin]
  constructor
  · intro h
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 h
    have := List.mem_range.1 hj
    omega
  · rintro ⟨h1, h2⟩
    exact List.mem_map.2 ⟨u - n, List.mem_range.2 (by omega), by omega⟩

/-- **The entries of a list before the position `k`.**  Extensionally `p.1.take p.2`, but
written as a `filter` over `List.zipIdx`, which is a `RAM.PolyFun` (`Algo.rowsFrom` does the
same for `List.drop`). -/
def rowsBefore {α : Type*} (p : List α × ℕ) : List α :=
  (p.1.zipIdx.filter (fun q => decide (q.2 < p.2))).map Prod.fst

theorem rowsBefore_aux {α : Type*} (l : List α) (k s : ℕ) :
    ((l.zipIdx s).filter (fun q => decide (q.2 < k))).map Prod.fst = l.take (k - s) := by
  induction l generalizing s with
  | nil => simp
  | cons a t ih =>
      rw [List.zipIdx_cons, List.filter_cons]
      by_cases hs : s < k
      · rw [if_pos (by simpa using hs), List.map_cons, ih (s + 1)]
        have h1 : k - s = (k - (s + 1)) + 1 := by omega
        rw [h1, List.take_succ_cons]
      · rw [if_neg (by simpa using hs), ih (s + 1)]
        have h1 : k - (s + 1) = 0 := by omega
        have h2 : k - s = 0 := by omega
        rw [h1, h2, List.take_zero, List.take_zero]

theorem rowsBefore_eq_take {α : Type*} (l : List α) (k : ℕ) :
    rowsBefore (l, k) = l.take k := by
  have := rowsBefore_aux l k 0
  rw [rowsBefore]
  simpa using this

theorem polyFun_rowsBefore {α : Type*} [Enc α] : PolyFun (rowsBefore (α := α)) := by
  have hq : PolyFun (fun z : ℕ × (α × ℕ) => decide (z.2.2 < z.1)) := by
    have h1 : PolyFun (fun z : ℕ × (α × ℕ) => (z.2.2 + 1, z.1)) :=
      (((polyFun_snd.comp polyFun_snd).pair (polyFun_const 1)).comp polyFun_add).pair polyFun_fst
    exact (h1.comp polyFun_le).of_eq (fun _ => rfl)
  have hz : PolyFun (fun p : List α × ℕ => ((p.2, p.1.zipIdx) : ℕ × List (α × ℕ))) :=
    polyFun_snd.pair (polyFun_fst.comp polyFun_zipIdx)
  exact ((hz.comp (PolyFun.filterParam hq)).comp
    (PolyFun.map (polyFun_fst (α := α) (β := ℕ)))).of_eq (fun _ => rfl)

/-- **One permutation of `Ω ⊔ Γ` read back on `Ω`**: its table on the first `n` points. -/
def rawProjPerm (p : RawPerm × ℕ) : RawPerm := rowsBefore (p.1, p.2)

/-- **A generating list of `Ω ⊔ Γ` read back on `Ω`.** -/
def rawProjGens (p : RawGens × ℕ) : RawGens := p.1.map (fun g => rawProjPerm (g, p.2))

/-- **The read-back undoes the extension.** -/
theorem rawProjPerm_spec (a : Perm (Fin n)) (b : Perm (Fin m)) :
    rawProjPerm (encPerm (n + m) (extPerm n m a b), n) = encPerm n a := by
  rw [rawProjPerm, ← rawExtPerm_spec, rawExtPerm, rowsBefore_eq_take]
  simp

theorem polyFun_rawProjPerm : PolyFun rawProjPerm := polyFun_rowsBefore

theorem polyFun_rawProjGens : PolyFun rawProjGens := by
  have hf : PolyFun (fun z : ℕ × RawPerm => rawProjPerm (z.2, z.1)) :=
    (polyFun_snd.pair polyFun_fst).comp polyFun_rawProjPerm
  have hin : PolyFun (fun p : RawGens × ℕ => ((p.2, p.1) : ℕ × RawGens)) :=
    polyFun_snd.pair polyFun_fst
  exact (hin.comp (PolyFun.mapParam hf)).of_eq (fun _ => rfl)

/-- **The read-back of one permutation of `Ω ⊔ Γ`, as a permutation of `Ω`.**  On a
permutation of the shape `a ⊔ b` it is `a`; on anything else it is junk. -/
noncomputable def projOf (n m : ℕ) (σ : Perm (Fin (n + m))) : Perm (Fin n) :=
  decPerm n (rawProjPerm (encPerm (n + m) σ, n))

@[simp] theorem projOf_extPerm (a : Perm (Fin n)) (b : Perm (Fin m)) :
    projOf n m (extPerm n m a b) = a := by
  rw [projOf, rawProjPerm_spec, decPerm_encPerm]

/-! ## The action given by the images of the generators -/

variable {gens : List (Perm (Fin n))} {imgs : List (Perm (Fin m))}

/-- **The data of Proposition 2.2.6**: `imgs` lists the images of the generators of `G` under
the homomorphism `ϕ : G → S(Γ)`.  That the assignment extends to a homomorphism at all is a
*hypothesis*: no routine can check it. -/
def ImgsOf (gens : List (Perm (Fin n))) (imgs : List (Perm (Fin m)))
    (ϕ : genGroup gens →* Perm (Fin m)) : Prop :=
  gens.length = imgs.length ∧
    ∀ (i : ℕ) (hi : i < gens.length) (hi' : i < imgs.length),
      imgs[i] = ϕ ⟨gens[i], Subgroup.subset_closure (List.getElem_mem hi)⟩

/-- **The extended generators**: `g ⊔ ϕ(g)`, one per generator of `G`. -/
def extGensOf (n m : ℕ) (gens : List (Perm (Fin n))) (imgs : List (Perm (Fin m))) :
    List (Perm (Fin (n + m))) :=
  (gens.zip imgs).map (fun p => extPerm n m p.1 p.2)

theorem mem_extGensOf {ϕ : genGroup gens →* Perm (Fin m)} (hI : ImgsOf gens imgs ϕ)
    {y : Perm (Fin (n + m))} :
    y ∈ extGensOf n m gens imgs ↔
      ∃ (g : Perm (Fin n)) (hg : g ∈ gens),
        y = extPerm n m g (ϕ ⟨g, Subgroup.subset_closure hg⟩) := by
  obtain ⟨hlen, himg⟩ := hI
  constructor
  · intro hy
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hy
    obtain ⟨i, hi, hpi⟩ := List.getElem_of_mem hp
    rw [List.length_zip, ← hlen, min_self] at hi
    have hi' : i < imgs.length := by omega
    have hz : (gens.zip imgs)[i]'(by rw [List.length_zip, ← hlen, min_self]; exact hi)
        = (gens[i], imgs[i]) := List.getElem_zip
    have hp2 : p = (gens[i], imgs[i]) := by rw [← hpi]; exact hz
    subst hp2
    exact ⟨gens[i], List.getElem_mem hi, by rw [himg i hi hi']⟩
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
    have hi' : i < imgs.length := by omega
    refine List.mem_map.2 ⟨(gens[i], imgs[i]), ?_, ?_⟩
    · have hz : (gens.zip imgs)[i]'(by rw [List.length_zip, ← hlen, min_self]; exact hi)
          = (gens[i], imgs[i]) := List.getElem_zip
      rw [← hz]
      exact List.getElem_mem _
    · rw [himg i hi hi']

/-! ## The graph of the action -/

/-- **The graph of `ϕ`**: `g ↦ g ⊔ ϕ(g)`, an injective homomorphism `G → S(Ω ⊔ Γ)`. -/
def graphHom (n m : ℕ) (gens : List (Perm (Fin n))) (ϕ : genGroup gens →* Perm (Fin m)) :
    genGroup gens →* Perm (Fin (n + m)) :=
  (extHom n m).comp (((genGroup gens).subtype).prod ϕ)

theorem graphHom_apply (ϕ : genGroup gens →* Perm (Fin m)) (g : genGroup gens) :
    graphHom n m gens ϕ g = extPerm n m (g : Perm (Fin n)) (ϕ g) := rfl

/-- **The extended group is the graph of the action.** -/
theorem range_graphHom {ϕ : genGroup gens →* Perm (Fin m)} (hI : ImgsOf gens imgs ϕ) :
    (graphHom n m gens ϕ).range = genGroup (extGensOf n m gens imgs) := by
  have hrange := range_eq_closure_gens (n := n) (S := {g : Perm (Fin n) | g ∈ gens})
    (graphHom n m gens ϕ)
  refine Eq.trans hrange ?_
  rw [genGroup]
  congr 1
  ext y
  constructor
  · rintro ⟨g, hg, hgens, rfl⟩
    exact (mem_extGensOf hI).2 ⟨g, hgens, rfl⟩
  · intro hy
    obtain ⟨g, hg, rfl⟩ := (mem_extGensOf hI).1 hy
    exact ⟨g, Subgroup.subset_closure hg, hg, rfl⟩

/-! ## The kernel -/

/-- **The kernel of the action**, as a subgroup of `S(Ω)`: `ker(G → S(Γ))`. -/
def actKer (gens : List (Perm (Fin n))) (ϕ : genGroup gens →* Perm (Fin m)) :
    Subgroup (Perm (Fin n)) := ϕ.ker.map (genGroup gens).subtype

theorem mem_actKer {ϕ : genGroup gens →* Perm (Fin m)} {a : Perm (Fin n)} :
    a ∈ actKer gens ϕ ↔ ∃ h : a ∈ genGroup gens, ϕ ⟨a, h⟩ = 1 := by
  constructor
  · rintro ⟨⟨g, hg⟩, hker, rfl⟩
    exact ⟨hg, hker⟩
  · rintro ⟨h, hker⟩
    exact ⟨⟨a, h⟩, hker, rfl⟩

/-- **The points of `Γ` inside `Ω ⊔ Γ`**, as a set. -/
def extWinSet (n m : ℕ) : Set (Fin (n + m)) := {x : Fin (n + m) | (x : ℕ) ∈ extWin n m}

theorem mem_extWinSet {x : Fin (n + m)} : x ∈ extWinSet n m ↔ ∃ j : Fin m, x = Fin.natAdd n j := by
  rw [extWinSet, Set.mem_setOf_eq, mem_extWin]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨(x : ℕ) - n, by omega⟩, ?_⟩
    apply Fin.ext
    show (x : ℕ) = n + ((x : ℕ) - n)
    omega
  · rintro ⟨j, rfl⟩
    refine ⟨?_, (Fin.natAdd n j).isLt⟩
    show n ≤ ((Fin.natAdd n j : Fin (n + m)) : ℕ)
    simp [Fin.natAdd]

theorem extPerm_inv (a : Perm (Fin n)) (b : Perm (Fin m)) :
    (extPerm n m a b)⁻¹ = extPerm n m a⁻¹ b⁻¹ := by
  rw [extPerm, extPerm, ← map_inv]
  rfl

/-- **The pointwise stabilizer of `Γ` in the extended group is the graph of the kernel.**
Paper: Proposition 2.2.6 (a), `ker ϕ = E_{(Γ)}` read on `Ω`. -/
theorem mem_pointwiseStabilizer_ext {ϕ : genGroup gens →* Perm (Fin m)}
    (hI : ImgsOf gens imgs ϕ) {σ : Perm (Fin (n + m))} :
    σ ∈ Babai.pointwiseStabilizer (genGroup (extGensOf n m gens imgs)) (extWinSet n m)
      ↔ ∃ a, a ∈ actKer gens ϕ ∧ σ = extPerm n m a 1 := by
  rw [Babai.mem_pointwiseStabilizer, ← range_graphHom hI]
  constructor
  · rintro ⟨⟨g, rfl⟩, hfix⟩
    refine ⟨(g : Perm (Fin n)), ?_, ?_⟩
    · refine mem_actKer.2 ⟨g.2, ?_⟩
      apply Equiv.ext
      intro j
      have h := hfix (Fin.natAdd n j) (mem_extWinSet.2 ⟨j, rfl⟩)
      rw [graphHom_apply, extPerm_natAdd] at h
      have : (ϕ g) j = j := by
        have := congrArg (fun x : Fin (n + m) => (x : ℕ)) h
        simp only [Fin.natAdd] at this
        exact Fin.ext (by omega)
      rw [show (⟨(g : Perm (Fin n)), g.2⟩ : genGroup gens) = g from rfl]
      simpa using this
    · rw [graphHom_apply]
      congr 1
      apply Equiv.ext
      intro j
      have h := hfix (Fin.natAdd n j) (mem_extWinSet.2 ⟨j, rfl⟩)
      rw [graphHom_apply, extPerm_natAdd] at h
      have := congrArg (fun x : Fin (n + m) => (x : ℕ)) h
      simp only [Fin.natAdd] at this
      exact Fin.ext (by simpa using (by omega : ((ϕ g) j : ℕ) = (j : ℕ)))
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨hmem, hker⟩ := mem_actKer.1 ha
    refine ⟨⟨⟨a, hmem⟩, ?_⟩, ?_⟩
    · rw [graphHom_apply, hker]
    · intro x hx
      obtain ⟨j, rfl⟩ := mem_extWinSet.1 hx
      rw [extPerm_natAdd]
      simp

theorem mem_smul_set_group' {Γ : Type*} [Group Γ] {τ x : Γ} {S : Set Γ} :
    x ∈ τ • S ↔ τ⁻¹ * x ∈ S := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa [smul_eq_mul] using hu
  · intro h
    exact ⟨τ⁻¹ * x, h, by simp [smul_eq_mul]⟩

theorem actKer_le (ϕ : genGroup gens →* Perm (Fin m)) : actKer gens ϕ ≤ genGroup gens := by
  rintro a ha
  exact (mem_actKer.1 ha).1

/-- **The extended group is exactly the graph of `ϕ`.** -/
theorem mem_ext_group_iff {ϕ : genGroup gens →* Perm (Fin m)} (hI : ImgsOf gens imgs ϕ)
    {σ : Perm (Fin (n + m))} :
    σ ∈ genGroup (extGensOf n m gens imgs) ↔
      ∃ (a : Perm (Fin n)) (h : a ∈ genGroup gens), σ = extPerm n m a (ϕ ⟨a, h⟩) := by
  rw [← range_graphHom hI]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨(g : Perm (Fin n)), g.2, rfl⟩
  · rintro ⟨a, h, rfl⟩
    exact ⟨⟨a, h⟩, rfl⟩

/-! ## Proposition 2.2.6 (a) for a general action -/

/-- **Proposition 2.2.6 (a)** (§2.2.3), for an action given by the images of the generators:
generators of the pointwise stabilizer of `Γ` in the extended group, read back on `Ω`,
generate `ker ϕ`. -/
theorem genGroup_map_projOf {ϕ : genGroup gens →* Perm (Fin m)} (hI : ImgsOf gens imgs ϕ)
    (L : List (Perm (Fin (n + m))))
    (hL : genGroup L
      = Babai.pointwiseStabilizer (genGroup (extGensOf n m gens imgs)) (extWinSet n m)) :
    genGroup (L.map (projOf n m)) = actKer gens ϕ := by
  have hgen : ∀ τ ∈ L, ∃ a, a ∈ actKer gens ϕ ∧ τ = extPerm n m a 1 := by
    intro τ hτ
    have hmem : τ ∈ genGroup L := Subgroup.subset_closure hτ
    rw [hL] at hmem
    exact (mem_pointwiseStabilizer_ext hI).1 hmem
  apply le_antisymm
  · rw [genGroup, Subgroup.closure_le]
    rintro y hy
    obtain ⟨τ, hτ, rfl⟩ := List.mem_map.1 hy
    obtain ⟨a, ha, rfl⟩ := hgen τ hτ
    rw [SetLike.mem_coe, projOf_extPerm]
    exact ha
  · have key : ∀ σ ∈ genGroup L,
        ∃ c, σ = extPerm n m c 1 ∧ c ∈ genGroup (L.map (projOf n m)) := by
      intro σ hσ
      rw [genGroup] at hσ
      induction hσ using Subgroup.closure_induction with
      | mem x hx =>
          obtain ⟨c, hc, hxc⟩ := hgen x hx
          refine ⟨c, hxc, Subgroup.subset_closure ?_⟩
          exact List.mem_map.2 ⟨x, hx, by rw [hxc, projOf_extPerm]⟩
      | one => exact ⟨1, by rw [extPerm_one], Subgroup.one_mem _⟩
      | mul x y hx hy ihx ihy =>
          obtain ⟨c, hxc, hc⟩ := ihx
          obtain ⟨d, hyd, hd⟩ := ihy
          exact ⟨c * d, by rw [hxc, hyd, ← extPerm_mul, mul_one], Subgroup.mul_mem _ hc hd⟩
      | inv x hx ihx =>
          obtain ⟨c, hxc, hc⟩ := ihx
          exact ⟨c⁻¹, by rw [hxc, extPerm_inv, inv_one], Subgroup.inv_mem _ hc⟩
    intro a ha
    have hext : extPerm n m a 1 ∈ genGroup L := by
      rw [hL]
      exact (mem_pointwiseStabilizer_ext hI).2 ⟨a, ha, rfl⟩
    obtain ⟨c, hc, hcmem⟩ := key _ hext
    rw [(extPerm_injective hc).1]
    exact hcmem

/-- **Proposition 2.2.6 (a), the covering half**, for a general action: `G` is the union of
the left cosets of `ker ϕ` with the representatives read back from the extended group. -/
theorem cover_projOf {ϕ : genGroup gens →* Perm (Fin m)} (hI : ImgsOf gens imgs ϕ)
    (reps : ℕ → Perm (Fin (n + m))) (idx : ℕ)
    (hcov : (genGroup (extGensOf n m gens imgs) : Set (Perm (Fin (n + m))))
      = ⋃ j ∈ List.range idx, reps j
          • (Babai.pointwiseStabilizer (genGroup (extGensOf n m gens imgs))
              (extWinSet n m) : Set (Perm (Fin (n + m))))) :
    (genGroup gens : Set (Perm (Fin n)))
      = ⋃ j ∈ List.range idx,
          projOf n m (reps j) • (actKer gens ϕ : Set (Perm (Fin n))) := by
  have hrepE : ∀ j ∈ List.range idx, reps j ∈ genGroup (extGensOf n m gens imgs) := by
    intro j hj
    have h1 : reps j ∈ ⋃ j' ∈ List.range idx, reps j'
        • (Babai.pointwiseStabilizer (genGroup (extGensOf n m gens imgs))
            (extWinSet n m) : Set (Perm (Fin (n + m)))) := by
      simp only [Set.mem_iUnion, exists_prop]
      refine ⟨j, hj, mem_smul_set_group'.2 ?_⟩
      rw [inv_mul_cancel]
      exact Subgroup.one_mem _
    rw [← hcov] at h1
    exact h1
  ext a
  simp only [SetLike.mem_coe, Set.mem_iUnion, exists_prop]
  constructor
  · intro ha
    have hset : extPerm n m a (ϕ ⟨a, ha⟩)
        ∈ (genGroup (extGensOf n m gens imgs) : Set (Perm (Fin (n + m)))) :=
      (mem_ext_group_iff hI).2 ⟨a, ha, rfl⟩
    rw [hcov] at hset
    simp only [Set.mem_iUnion, exists_prop] at hset
    obtain ⟨j, hj, hmem⟩ := hset
    obtain ⟨c, hc, hrepeq⟩ := (mem_ext_group_iff hI).1 (hrepE j hj)
    rw [mem_smul_set_group'] at hmem
    have hprod : (reps j)⁻¹ * extPerm n m a (ϕ ⟨a, ha⟩)
        = extPerm n m (c⁻¹ * a) ((ϕ ⟨c, hc⟩)⁻¹ * ϕ ⟨a, ha⟩) := by
      rw [hrepeq, extPerm_inv, ← extPerm_mul]
    rw [hprod] at hmem
    obtain ⟨k, hk, hkeq⟩ := (mem_pointwiseStabilizer_ext hI).1 hmem
    have hck : c⁻¹ * a = k := (extPerm_injective hkeq).1
    refine ⟨j, hj, ?_⟩
    rw [hrepeq, projOf_extPerm, mem_smul_set_group']
    show c⁻¹ * a ∈ (actKer gens ϕ : Set (Perm (Fin n)))
    rw [hck]
    exact hk
  · rintro ⟨j, hj, hmem⟩
    obtain ⟨c, hc, hrepeq⟩ := (mem_ext_group_iff hI).1 (hrepE j hj)
    rw [hrepeq, projOf_extPerm, mem_smul_set_group'] at hmem
    have h1 : c⁻¹ * a ∈ genGroup gens := actKer_le ϕ hmem
    have h2 : a = c * (c⁻¹ * a) := by group
    rw [h2]
    exact Subgroup.mul_mem _ hc h1

/-! ## The three routines of Proposition 2.2.6 (a)

The group on `Ω` arrives as a domain witness `dom` of length `n` together with its generators;
the second domain `Γ` arrives as a witness `gdom` of length `m` together with the images of
the generators.  The domain witness of `Ω ⊔ Γ` is the concatenation, and the window is
`[n, …, n + m − 1]`, read off `gdom` so that `m` never has to be a machine natural. -/

/-- The domain witness of `Ω ⊔ Γ`. -/
def rawExtDom (p : List ℕ × List ℕ) : List ℕ := p.1 ++ p.2

/-- The window `Γ` inside `Ω ⊔ Γ`, computed from the two domain witnesses. -/
def rawExtWin (p : List ℕ × List ℕ) : List ℕ := p.2.zipIdx.map (fun q => q.2 + p.1.length)

theorem rawExtWin_eq (dom gdom : List ℕ) (hd : dom.length = n) (hg : gdom.length = m) :
    rawExtWin (dom, gdom) = extWin n m := by
  have h1 : gdom.zipIdx.map (fun q : ℕ × ℕ => q.2 + dom.length)
      = (gdom.zipIdx.map Prod.snd).map (fun u => u + dom.length) := by
    rw [List.map_map]
    rfl
  show gdom.zipIdx.map (fun q : ℕ × ℕ => q.2 + dom.length) = (List.range m).map (fun j => j + n)
  rw [h1, List.zipIdx_map_snd, hd, hg, ← List.range_eq_range']

/-- **Generators of `ker ϕ`** (Prop. 2.2.6 (a)).  `p.1 = (dom, gens)` is the group on `Ω`,
`p.2 = (gdom, imgs)` is the second domain and the images of the generators. -/
def actKerGens (p : (List ℕ × RawGens) × (List ℕ × RawGens)) : RawGens :=
  rawProjGens (rawKerGens ((rawExtDom (p.1.1, p.2.1), rawExtGens (p.1.2, p.2.2)),
    rawExtWin (p.1.1, p.2.1)), p.1.1.length)

/-- **The `j`-th left coset representative of `ker ϕ` in `G`**, read off the stabilizer chain
of the extended group; `j` is a machine natural, in binary. -/
def actCosetRep (p : ((List ℕ × RawGens) × (List ℕ × RawGens)) × ℕ) : RawPerm :=
  rawProjPerm (rawCosetRepBin ((rawExtDom (p.1.1.1, p.1.2.1), rawExtGens (p.1.1.2, p.1.2.2)),
    (rawExtWin (p.1.1.1, p.1.2.1), p.2)), p.1.1.1.length)

/-- **The number of cosets**, `|G : ker ϕ|`. -/
noncomputable def actCosetIndex (n m : ℕ) (dom gdom : List ℕ) (gens : List (Perm (Fin n)))
    (imgs : List (Perm (Fin m))) : ℕ :=
  winCosetIndex (n + m) (dom ++ gdom) (extWin n m) (extGensOf n m gens imgs)

section Routines

variable {dom gdom : List ℕ} {ϕ : genGroup gens →* Perm (Fin m)}

/-- **Proposition 2.2.6 (a)** (§2.2.3): the routine returns a generating list of
`ker(G → S(Γ))`. -/
theorem decGroup_actKerGens (hd : dom.length = n) (hg : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) :
    decGroup n (actKerGens ((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))))
      = actKer gens ϕ := by
  have hEDlen : (dom ++ gdom).length = n + m := by
    rw [List.length_append, hd, hg]
  have hEG : rawExtGens (gens.map (encPerm n), imgs.map (encPerm m))
      = (extGensOf n m gens imgs).map (encPerm (n + m)) := rawExtGens_spec gens imgs hI.1
  have hEW : rawExtWin (dom, gdom) = extWin n m := rawExtWin_eq dom gdom hd hg
  set S := rawKerGens ((dom ++ gdom, (extGensOf n m gens imgs).map (encPerm (n + m))),
    extWin n m) with hS
  have hSwf : RawGens.WF (n + m) S :=
    wf_rawKerGens hEDlen (nodup_extWin n m) (fun x hx => lt_extWin hx) _
  have hSgrp : decGroup (n + m) S
      = Babai.pointwiseStabilizer (genGroup (extGensOf n m gens imgs)) (extWinSet n m) :=
    decGroup_rawKerGens hEDlen (nodup_extWin n m) (fun x hx => lt_extWin hx) _
  have hroutine : actKerGens ((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m)))
      = rawProjGens (S, n) := by
    show rawProjGens (rawKerGens ((rawExtDom (dom, gdom),
      rawExtGens (gens.map (encPerm n), imgs.map (encPerm m))), rawExtWin (dom, gdom)),
      dom.length) = rawProjGens (S, n)
    rw [show rawExtDom (dom, gdom) = dom ++ gdom from rfl, hEG, hEW, hd, hS]
  set T := S.map (decPerm (n + m)) with hT
  have hSenc : S = T.map (encPerm (n + m)) := (map_encPerm_decPerm' hSwf).symm
  have hdec : (rawProjGens (S, n)).map (decPerm n) = T.map (projOf n m) := by
    have h1 : rawProjGens (S, n)
        = (T.map (encPerm (n + m))).map (fun g => rawProjPerm (g, n)) := by
      rw [← hSenc]
      rfl
    rw [h1, List.map_map, List.map_map]
    exact List.map_congr_left (fun τ _ => rfl)
  rw [hroutine, decGroup, hdec]
  refine genGroup_map_projOf hI T ?_
  rw [← hSgrp, decGroup, ← hT]

/-- The `j`-th representative the routine computes, decoded. -/
theorem decPerm_actCosetRep (hd : dom.length = n) (hg : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (j : ℕ) :
    decPerm n (actCosetRep (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), j))
      = projOf n m (winCosetRep (n + m) (dom ++ gdom) (extWin n m)
          (extGensOf n m gens imgs) j) := by
  have hEDlen : (dom ++ gdom).length = n + m := by
    rw [List.length_append, hd, hg]
  have hEG : rawExtGens (gens.map (encPerm n), imgs.map (encPerm m))
      = (extGensOf n m gens imgs).map (encPerm (n + m)) := rawExtGens_spec gens imgs hI.1
  have hEW : rawExtWin (dom, gdom) = extWin n m := rawExtWin_eq dom gdom hd hg
  show decPerm n (rawProjPerm (rawCosetRepBin ((rawExtDom (dom, gdom),
    rawExtGens (gens.map (encPerm n), imgs.map (encPerm m))),
    (rawExtWin (dom, gdom), j)), dom.length)) = _
  rw [show rawExtDom (dom, gdom) = dom ++ gdom from rfl, hEG, hEW, hd,
    rawCosetRepBin_spec hEDlen (nodup_extWin n m) (fun x hx => lt_extWin hx) _ j]
  rfl

/-- **Proposition 2.2.6 (a), the covering half**, as the routines compute it: `G` is the union
of the `|G : ker ϕ|` left cosets of `ker ϕ` with the computed representatives. -/
theorem cover_actCosetRep (hd : dom.length = n) (hg : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) :
    (genGroup gens : Set (Perm (Fin n)))
      = ⋃ j ∈ List.range (actCosetIndex n m dom gdom gens imgs),
          decPerm n (actCosetRep (((dom, gens.map (encPerm n)),
              (gdom, imgs.map (encPerm m))), j))
            • (actKer gens ϕ : Set (Perm (Fin n))) := by
  have hEDlen : (dom ++ gdom).length = n + m := by
    rw [List.length_append, hd, hg]
  have hcov := cover_winCosetRep (n := n + m) (dom := dom ++ gdom) (Δ := extWin n m)
    hEDlen (nodup_extWin n m) (fun x hx => lt_extWin hx) (extGensOf n m gens imgs)
  have hproj := cover_projOf hI
    (fun j => winCosetRep (n + m) (dom ++ gdom) (extWin n m) (extGensOf n m gens imgs) j)
    (actCosetIndex n m dom gdom gens imgs) hcov
  rw [hproj]
  refine Set.iUnion_congr (fun j => ?_)
  refine Set.iUnion_congr_Prop Iff.rfl (fun _ => ?_)
  rw [decPerm_actCosetRep hd hg hI j]

end Routines

/-! ## The running times -/

theorem polyFun_rawExtDom : PolyFun rawExtDom := polyFun_append

theorem polyFun_rawExtWin : PolyFun rawExtWin := by
  have hf : PolyFun (fun z : ℕ × (ℕ × ℕ) => z.2.2 + z.1) :=
    ((polyFun_snd.comp polyFun_snd).pair polyFun_fst).comp polyFun_add
  have hin : PolyFun (fun p : List ℕ × List ℕ =>
      ((p.1.length, p.2.zipIdx) : ℕ × List (ℕ × ℕ))) :=
    (polyFun_fst.comp polyFun_length).pair (polyFun_snd.comp polyFun_zipIdx)
  exact (hin.comp (PolyFun.mapParam hf)).of_eq (fun _ => rfl)

theorem polyFun_actKerGens : PolyFun actKerGens := by
  have hdom : PolyFun (fun p : (List ℕ × RawGens) × (List ℕ × RawGens) =>
      ((p.1.1, p.2.1) : List ℕ × List ℕ)) :=
    (polyFun_fst.comp polyFun_fst).pair (polyFun_snd.comp polyFun_fst)
  have hgens : PolyFun (fun p : (List ℕ × RawGens) × (List ℕ × RawGens) =>
      ((p.1.2, p.2.2) : RawGens × RawGens)) :=
    (polyFun_fst.comp polyFun_snd).pair (polyFun_snd.comp polyFun_snd)
  have hker : PolyFun (fun p : (List ℕ × RawGens) × (List ℕ × RawGens) =>
      rawKerGens ((rawExtDom (p.1.1, p.2.1), rawExtGens (p.1.2, p.2.2)),
        rawExtWin (p.1.1, p.2.1))) :=
    (((hdom.comp polyFun_rawExtDom).pair (hgens.comp polyFun_rawExtGens)).pair
      (hdom.comp polyFun_rawExtWin)).comp polyFun_rawKerGens
  have hn : PolyFun (fun p : (List ℕ × RawGens) × (List ℕ × RawGens) => p.1.1.length) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_length
  exact ((hker.pair hn).comp polyFun_rawProjGens).of_eq (fun _ => rfl)

theorem polyFun_actCosetRep : PolyFun actCosetRep := by
  have hdom : PolyFun (fun p : ((List ℕ × RawGens) × (List ℕ × RawGens)) × ℕ =>
      ((p.1.1.1, p.1.2.1) : List ℕ × List ℕ)) :=
    (((polyFun_fst.comp polyFun_fst).comp polyFun_fst).pair
      ((polyFun_fst.comp polyFun_snd).comp polyFun_fst))
  have hgens : PolyFun (fun p : ((List ℕ × RawGens) × (List ℕ × RawGens)) × ℕ =>
      ((p.1.1.2, p.1.2.2) : RawGens × RawGens)) :=
    (((polyFun_fst.comp polyFun_fst).comp polyFun_snd).pair
      ((polyFun_fst.comp polyFun_snd).comp polyFun_snd))
  have hrep : PolyFun (fun p : ((List ℕ × RawGens) × (List ℕ × RawGens)) × ℕ =>
      rawCosetRepBin ((rawExtDom (p.1.1.1, p.1.2.1), rawExtGens (p.1.1.2, p.1.2.2)),
        (rawExtWin (p.1.1.1, p.1.2.1), p.2))) :=
    (((hdom.comp polyFun_rawExtDom).pair (hgens.comp polyFun_rawExtGens)).pair
      ((hdom.comp polyFun_rawExtWin).pair polyFun_snd)).comp polyFun_rawCosetRepBin
  have hn : PolyFun (fun p : ((List ℕ × RawGens) × (List ℕ × RawGens)) × ℕ =>
      p.1.1.1.length) :=
    ((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_length
  exact ((hrep.pair hn).comp polyFun_rawProjPerm).of_eq (fun _ => rfl)

/-! ## The number of cosets is `|G : ker ϕ| = |G^ϕ|` (risk R-A7-3)

`Algo.cover_actCosetRep` says that the `Algo.actCosetIndex` representatives cover `G`, so the
number is at least the true index.  With `Algo.winCosetIndex_mul_card` it is exactly the
index, and by the first isomorphism theorem the index is `|G^ϕ|`, the order of the image —
which for the action on a block system is Theorem 11.1.9's `|Ḡ|`. -/

section Index

variable {gens : List (Perm (Fin n))} {imgs : List (Perm (Fin m))} {dom gdom : List ℕ}

/-- The graph `g ↦ g ⊔ ϕ(g)` is injective: the first component is `g` itself. -/
theorem graphHom_injective (ϕ : genGroup gens →* Perm (Fin m)) :
    Function.Injective (graphHom n m gens ϕ) := by
  intro g g' h
  rw [graphHom_apply, graphHom_apply] at h
  exact Subtype.ext (extPerm_injective h).1

/-- The pointwise stabilizer of `Γ` in the extended group has the same order as `ker ϕ` read
on `Ω`: it is the graph of it (`Algo.mem_pointwiseStabilizer_ext`). -/
theorem card_pointwiseStabilizer_ext {ϕ : genGroup gens →* Perm (Fin m)}
    (hI : ImgsOf gens imgs ϕ) :
    Nat.card (Babai.pointwiseStabilizer (genGroup (extGensOf n m gens imgs)) (extWinSet n m))
      = Nat.card (actKer gens ϕ) := by
  refine (Nat.card_congr (Equiv.ofBijective
    (fun a : actKer gens ϕ => (⟨extPerm n m (a : Perm (Fin n)) 1,
      (mem_pointwiseStabilizer_ext hI).2 ⟨(a : Perm (Fin n)), a.2, rfl⟩⟩ :
      Babai.pointwiseStabilizer (genGroup (extGensOf n m gens imgs)) (extWinSet n m)))
    ⟨?_, ?_⟩)).symm
  · intro a a' h
    exact Subtype.ext (extPerm_injective (congrArg Subtype.val h)).1
  · rintro ⟨σ, hσ⟩
    obtain ⟨a, ha, rfl⟩ := (mem_pointwiseStabilizer_ext hI).1 hσ
    exact ⟨⟨a, ha⟩, rfl⟩

/-- **R-A7-3**, the multiplicative form: the computed number of cosets times the order of
`ker ϕ` is `|G|`. -/
theorem actCosetIndex_mul_card (hd : dom.length = n) (hg : gdom.length = m)
    {ϕ : genGroup gens →* Perm (Fin m)} (hI : ImgsOf gens imgs ϕ) :
    actCosetIndex n m dom gdom gens imgs * Nat.card (actKer gens ϕ)
      = Nat.card (genGroup gens) := by
  have hED : (dom ++ gdom).length = n + m := by rw [List.length_append, hd, hg]
  have h := winCosetIndex_mul_card (n := n + m) (dom := dom ++ gdom) (Δ := extWin n m)
    hED (nodup_extWin n m) (fun x hx => lt_extWin hx) (extGensOf n m gens imgs)
  rw [show {x : Fin (n + m) | (x : ℕ) ∈ extWin n m} = extWinSet n m from rfl,
    card_pointwiseStabilizer_ext hI] at h
  rw [actCosetIndex, h, ← range_graphHom hI]
  exact (Nat.card_congr (MonoidHom.ofInjective (graphHom_injective ϕ)).toEquiv).symm

/-- **R-A7-3, closed for `Algo.actCosetIndex`**: the number of coset representatives the
routine produces is `|G : ker ϕ| = |G^ϕ|`, the order of the image of `ϕ`.  Paper: the `|Ḡ|`
of Theorem 11.1.9 and the `|G : H|` of Proposition 11.1.6. -/
theorem actCosetIndex_eq_card_range (hd : dom.length = n) (hg : gdom.length = m)
    {ϕ : genGroup gens →* Perm (Fin m)} (hI : ImgsOf gens imgs ϕ) :
    actCosetIndex n m dom gdom gens imgs = Nat.card ϕ.range := by
  have hker : Nat.card (actKer gens ϕ) = Nat.card ϕ.ker :=
    (Nat.card_congr (Subgroup.equivMapOfInjective ϕ.ker (genGroup gens).subtype
      (Subgroup.subtype_injective _)).toEquiv).symm
  have hG : Nat.card (genGroup gens) = Nat.card ϕ.range * Nat.card ϕ.ker := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ϕ).toEquiv]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup ϕ.ker
  have h := actCosetIndex_mul_card hd hg hI
  rw [hker, hG] at h
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h

end Index

end Algo
