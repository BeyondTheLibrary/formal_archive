import Workspace.Algo.AggNodeCosetImage
import Workspace.Algo.AggNodeRestrictedMem

/-! # The local-guide tuple relation from a stored coset

For tuples `u,v`, their ordered transporter `b` satisfies `b u = v`.
A stored coset `r H` contains a map with this action precisely when the
restriction of `r⁻¹ b` belongs to the restriction of `H` to the source
set. This is one polynomial group-membership test.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv

abbrev AggnCosetTupleContext := List ℕ × (List ℕ × List ℕ)
abbrev AggnCosetTupleSomeInput := AggnCosetTupleContext × (RawGens × RawPerm)

def aggnCosetTupleCandidate (p : AggnCosetTupleSomeInput) : RawPerm :=
  rawMul (rawInv p.2.2,aggnTransportBase p.1)

def aggnCosetTupleSome (p : AggnCosetTupleSomeInput) : Bool :=
  aggnRestrictedMem ((p.1.1,p.2.1),(p.1.2.1,aggnCosetTupleCandidate p))

def aggnCosetTuple (p : AggnCosetTupleContext × RawCoset) : Bool :=
  (top2NormC p.1.1 p.2).any fun q => aggnCosetTupleSome (p.1,q)

theorem aggnPolyFun_cosetTupleCandidate : PolyFun aggnCosetTupleCandidate :=
  (((polyFun_snd.comp polyFun_snd).comp polyFun_rawInv).pair
    (polyFun_fst.comp aggnPolyFun_transportBase)).comp polyFun_rawMul

theorem aggnPolyFun_cosetTupleSome : PolyFun aggnCosetTupleSome :=
  ((((polyFun_fst.comp polyFun_fst).pair (polyFun_snd.comp polyFun_fst)).pair
    (((polyFun_fst.comp polyFun_snd).comp polyFun_fst).pair
      aggnPolyFun_cosetTupleCandidate)).comp aggnPolyFun_restrictedMem)

theorem aggnPolyFun_cosetTuple : PolyFun aggnCosetTuple := by
  have hn : PolyFun (fun p : AggnCosetTupleContext × RawCoset => top2NormC p.1.1 p.2) :=
    ((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp polyFun_top2NormC
  exact ((hn.pair polyFun_fst).comp
    (PolyFun.optionElim (polyFun_const false)
      ((polyFun_snd.pair polyFun_fst).comp aggnPolyFun_cosetTupleSome))).of_eq
        (fun p => by unfold aggnCosetTuple; cases top2NormC p.1.1 p.2 <;> rfl)

theorem aggnCosetTupleSome_spec {m : ℕ} {dom u v : List ℕ} {gs : RawGens} {r : RawPerm}
    (hd : dom.length = m) (hu : u.Nodup) (hv : v.Nodup)
    (hult : ∀ a ∈ u,a < m) (hvlt : ∀ a ∈ v,a < m) (hlen : u.length = v.length)
    (hw : RawGens.WF m gs) (hr : RawPerm.WF m r)
    (hmap : ∀ π ∈ decCoset m (some (gs,r)),π '' winSet m u = winSet m v) :
    aggnCosetTupleSome ((dom,u,v),(gs,r)) = true ↔
      ∃ π ∈ decCoset m (some (gs,r)),∀ i : Fin u.length,
        π (winPt m u hult i).val = (winPt m v hvlt (i.cast hlen)).val := by
  let b := aggnTransportBase (dom,u,v)
  let d := aggnCosetTupleCandidate ((dom,u,v),(gs,r))
  have hb := aggnTransportBase_spec hd hu hv hult hvlt hlen
  have hdw : RawPerm.WF m d := wf_rawMul (wf_rawInv hr) hb.1
  have hde : decPerm m d = (decPerm m r)⁻¹ * decPerm m b := by
    rw [show d = rawMul (rawInv r,b) from rfl,rawMul_of_wf (wf_rawInv hr) hb.1,
      decPerm_encPerm,rawInv_of_wf hr,decPerm_encPerm]
  have hrmap : (decPerm m r) '' winSet m u = winSet m v :=
    hmap _ ⟨1,(decGroup m gs).one_mem,by simp⟩
  have hinv : IsInvariant (decGroup m gs) (winSet m u) := by
    intro h hh
    apply (decPerm m r).injective.image_injective
    rw [← perm_mul_image,hmap _ ⟨h,hh,rfl⟩,hrmap]
  have hdmap : (decPerm m d) '' winSet m u = winSet m u := by
    rw [hde,perm_mul_image,hb.2,← hrmap,Set.image_image]
    simp
  rw [aggnCosetTupleSome,aggnRestrictedMem_spec hu hult hw hdw hinv hdmap]
  constructor
  · rintro ⟨h,hh,heq⟩
    refine ⟨decPerm m r * h,⟨h,hh,rfl⟩,?_⟩
    intro i
    rw [Perm.mul_apply,heq _ (winPt m u hult i).property,hde,Perm.mul_apply]
    simp only [Perm.inv_def,Equiv.apply_symm_apply]
    exact aggnTransportBase_apply hd hu hv hult hvlt hlen i
  · rintro ⟨π,⟨h,hh,rfl⟩,heq⟩
    refine ⟨h,hh,?_⟩
    intro a ha
    obtain ⟨i,hi⟩ := (winPt_bijective u hu hult).surjective ⟨a,ha⟩
    have hai : (winPt m u hult i).val = a := congrArg Subtype.val hi
    rw [← hai,hde,Perm.mul_apply]
    apply (decPerm m r).injective
    simpa only [b,Perm.inv_def,Equiv.apply_symm_apply,Perm.mul_apply,
      aggnTransportBase_apply hd hu hv hult hvlt hlen] using heq i

/-- The tuple test accepts every raw encoding of the stored comparison answer. -/
theorem aggnCosetTuple_spec {m : ℕ} {dom u v : List ℕ} {q : RawCoset}
    (hd : dom.length = m) (hu : u.Nodup) (hv : v.Nodup)
    (hult : ∀ a ∈ u,a < m) (hvlt : ∀ a ∈ v,a < m) (hlen : u.length = v.length)
    (hmap : ∀ π ∈ decCoset m q,π '' winSet m u = winSet m v) :
    aggnCosetTuple ((dom,u,v),q) = true ↔
      ∃ π ∈ decCoset m q,∀ i : Fin u.length,
        π (winPt m u hult i).val = (winPt m v hvlt (i.cast hlen)).val := by
  have he := decCoset_top2NormC hd q
  cases hn : top2NormC dom q with
  | none =>
    have hq : decCoset m q = ∅ := by rw [← he,hn]; rfl
    simp [aggnCosetTuple,hn,hq]
  | some p =>
    obtain ⟨hw,_,hr⟩ := rawRightTranslate_wf hd (rawOne dom) q hn
    have hm : ∀ π ∈ decCoset m (some p),π '' winSet m u = winSet m v := by
      rw [← hn,he]
      exact hmap
    have h := aggnCosetTupleSome_spec hd hu hv hult hvlt hlen hw hr hm
    simpa only [aggnCosetTuple,hn,Option.any_some,← he] using h

end Algo
