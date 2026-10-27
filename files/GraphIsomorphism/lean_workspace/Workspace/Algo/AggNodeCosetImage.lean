import Workspace.Algo.AggNodeAggregateCase2b
import Workspace.Algo.AggNodeCompareLookup
import Workspace.Algo.TopWindowRound

/-! # Images of the stored comparison cosets

Local guides use the induced bijections on the giant domain. Map the
generators and representative through the existing action routine.
Normalize first so the result is correct for every raw encoding of a
comparison answer, without a well-formedness promise about that answer.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Classical

def aggnCosetImageSome (p : RawAction × (RawGens × RawPerm)) : RawGens × RawPerm :=
  (aggImage (p.1,p.2.1),normPerm (p.1.2.1,rawImgOf (p.1,p.2.2)))

def aggnCosetImage (p : RawAction × RawCoset) : RawCoset :=
  (top2NormC p.1.1.1 p.2).map fun q => aggnCosetImageSome (p.1,q)

theorem aggnPolyFun_cosetImageSome : PolyFun aggnCosetImageSome := by
  have hh : PolyFun (fun p : RawAction × (RawGens × RawPerm) => aggImage (p.1,p.2.1)) :=
    (polyFun_fst.pair (polyFun_snd.comp polyFun_fst)).comp aggPolyFun_image
  have hr : PolyFun (fun p : RawAction × (RawGens × RawPerm) => rawImgOf (p.1,p.2.2)) :=
    (polyFun_fst.pair (polyFun_snd.comp polyFun_snd)).comp polyFun_rawImgOf
  have hm : PolyFun (fun p : RawAction × (RawGens × RawPerm) => p.1.2.1) :=
    (polyFun_fst.comp polyFun_snd).comp polyFun_fst
  exact hh.pair ((hm.pair hr).comp polyFun_normPerm)

theorem aggnPolyFun_cosetImage : PolyFun aggnCosetImage := by
  have hq : PolyFun (fun p : RawAction × RawCoset => top2NormC p.1.1.1 p.2) :=
    ((((polyFun_fst.comp polyFun_fst).comp polyFun_fst).pair polyFun_snd).comp polyFun_top2NormC)
  have hs : PolyFun (fun z : (RawGens × RawPerm) × RawAction => some (aggnCosetImageSome (z.2,z.1))) :=
    ((polyFun_snd.pair polyFun_fst).comp aggnPolyFun_cosetImageSome).comp polyFun_some
  exact ((hq.pair polyFun_fst).comp (PolyFun.optionElim (polyFun_const none) hs)).of_eq
    (fun p => by unfold aggnCosetImage; cases top2NormC p.1.1.1 p.2 <;> rfl)

theorem aggnImage_spec {n m : ℕ} {A : RawAction} {gs : RawGens}
    {ϕ : decGroup n A.1.2 →* Perm (Fin m)} (hA : RawAction.WF n m A ϕ)
    (hw : RawGens.WF n gs) (hle : decGroup n gs ≤ decGroup n A.1.2) :
    decGroup m (aggImage (A,gs)) = imgPhi ϕ hle := by
  have h := aggImage_spec hA.1 hA.2.1 hA.2.2.2.2 hw hle
  simpa only [map_encPerm_decPerm hA.2.2.1,map_encPerm_decPerm hA.2.2.2.1] using h

theorem aggnCosetImageSome_spec {n m : ℕ} {A : RawAction} {gs : RawGens} {r : RawPerm}
    {ϕ : decGroup n A.1.2 →* Perm (Fin m)} (hA : RawAction.WF n m A ϕ)
    (hw : RawGens.WF n gs) (hr : RawPerm.WF n r)
    (hsub : decCoset n (some (gs,r)) ⊆ (decGroup n A.1.2 : Set (Perm (Fin n)))) :
    decCoset m (some (aggnCosetImageSome (A,(gs,r)))) =
      {π | ∃ σ : decGroup n A.1.2,σ.val ∈ decCoset n (some (gs,r)) ∧ ϕ σ = π} := by
  have hrG : decPerm n r ∈ decGroup n A.1.2 := hsub ⟨1,(decGroup n gs).one_mem,by simp⟩
  have hle : decGroup n gs ≤ decGroup n A.1.2 := by
    intro g hg
    have hh := (decGroup n A.1.2).mul_mem ((decGroup n A.1.2).inv_mem hrG) (hsub ⟨g,hg,rfl⟩)
    simpa using hh
  have hi := aggnRawImgOf_spec hA hr hrG
  have hH := aggnImage_spec hA hw hle
  unfold aggnCosetImageSome
  change {π | ∃ h ∈ decGroup m (aggImage (A,gs)),π = decPerm m (normPerm (A.2.1,rawImgOf (A,r))) * h} = _
  rw [decPerm_normPerm hA.2.1,hi,decPerm_encPerm,hH]
  ext π
  constructor
  · rintro ⟨h,⟨g,rfl⟩,rfl⟩
    refine ⟨⟨decPerm n r * g.val,(decGroup n A.1.2).mul_mem hrG (hle g.property)⟩,
      ⟨g.val,g.property,rfl⟩,?_⟩
    exact ϕ.map_mul ⟨decPerm n r,hrG⟩ ⟨g.val,hle g.property⟩
  · rintro ⟨σ,⟨g,hg,he⟩,rfl⟩
    refine ⟨ϕ ⟨g,hle hg⟩,⟨⟨g,hg⟩,rfl⟩,?_⟩
    have he' : σ = (⟨decPerm n r,hrG⟩ : decGroup n A.1.2) * ⟨g,hle hg⟩ := Subtype.ext he
    rw [he',map_mul]

/-- Exact induced coset for any correct raw answer encoding. -/
theorem aggnCosetImage_spec {n m : ℕ} {A : RawAction} {q : RawCoset}
    {ϕ : decGroup n A.1.2 →* Perm (Fin m)} (hA : RawAction.WF n m A ϕ)
    (hsub : decCoset n q ⊆ (decGroup n A.1.2 : Set (Perm (Fin n)))) :
    decCoset m (aggnCosetImage (A,q)) =
      {π | ∃ σ : decGroup n A.1.2,σ.val ∈ decCoset n q ∧ ϕ σ = π} := by
  have he := decCoset_top2NormC hA.1 q
  cases hn : top2NormC A.1.1 q with
  | none =>
    have hq : decCoset n q = ∅ := by rw [← he,hn]; rfl
    rw [aggnCosetImage,hn]
    change ∅ = _
    simp [hq]
  | some p =>
    obtain ⟨hw,_,hr⟩ := rawRightTranslate_wf hA.1 (rawOne A.1.1) q hn
    have hsub' : decCoset n (some p) ⊆ (decGroup n A.1.2 : Set (Perm (Fin n))) := by
      rw [← hn,he]
      exact hsub
    have h := aggnCosetImageSome_spec hA hw hr hsub'
    rw [aggnCosetImage,hn,Option.map_some,h,← he,hn]

end Algo
