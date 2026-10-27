import Workspace.Cited.CameronRecognition

/-!
# The cited routine for Cameron groups, as used by Reduce-to-Johnson

`Babai.cameronStructure_polyTime` (`Workspace/Cited/CameronRecognition.lean`) is the cited
sentence of Sec. 11.2: the structure of a Cameron group can be found in polynomial time
[BaLS].  This file does three things.

* `Algo.CameronStructureSpec` names the specification part of the axiom, and
  `Algo.cameronStructureSpec_exists` shows that a function with this specification exists
  with no axiom.  So the axiom adds only the running time.
* `Algo.cameronStructureSpec_isCameronGroup` reads the output as Def. 11.2.2.
* `Algo.exists_polyFun_cameronSpec` gives the hypothesis `(cameron, hpoly, hspec)` that the
  theorems of `Workspace/Algo/CameronDescent.lean` take: the input of step 6 of Procedure
  Reduce-to-Johnson is a large primitive group, which is a Cameron group by the cited
  Theorem 11.2.3.
-/

namespace Algo

open RAM

/-- The specification part of `Babai.cameronStructure_polyTime`: on generators of a
Cameron group the function returns a Cameron structure of that group (Def. 11.2.2).
Nothing is asked on other inputs. -/
def CameronStructureSpec (cameron : RawGens × List ℕ → Option RawCameron) : Prop :=
  ∀ (n : ℕ) (gs : RawGens) (dom : List ℕ), dom.length = n → RawGens.WF n gs →
    (∃ s t k : ℕ, Babai.IsCameronGroup (decGroup n gs) s t k) →
    ∃ (c : RawCameron) (h : c.WF n), cameron (gs, dom) = some c ∧
      (∃ R : Fin c.s → Subgroup (decGroup n gs),
        Babai.IsSocleFactorization (decGroup n gs) R c.k) ∧
      Babai.basePower (Babai.JohnsonA c.k c.t) c.s ≤
        (decGroup n gs).map (Equiv.permCongrHom (decCameron c h)).toMonoidHom ∧
      (decGroup n gs).map (Equiv.permCongrHom (decCameron c h)).toMonoidHom ≤
        Babai.wreathProduct (Babai.JohnsonS c.k c.t) c.s

/-- The axiom, with its specification named. -/
theorem cameronStructure_polyTime :
    ∃ cameron : RawGens × List ℕ → Option RawCameron,
      PolyFun cameron ∧ CameronStructureSpec cameron :=
  Babai.cameronStructure_polyTime

/-- **The specification alone adds nothing.**  By Def. 11.2.2 and choice there is a
function with the specification of the axiom; no time bound is claimed for it.  So the
only content of `Babai.cameronStructure_polyTime` is the running time. -/
theorem cameronStructureSpec_exists :
    ∃ cameron : RawGens × List ℕ → Option RawCameron, CameronStructureSpec cameron := by
  classical
  let P (q : RawGens × List ℕ) (c : RawCameron) : Prop :=
    ∃ h : c.WF q.2.length,
      (∃ R : Fin c.s → Subgroup (decGroup q.2.length q.1),
        Babai.IsSocleFactorization (decGroup q.2.length q.1) R c.k) ∧
      Babai.basePower (Babai.JohnsonA c.k c.t) c.s ≤
        (decGroup q.2.length q.1).map (Equiv.permCongrHom (decCameron c h)).toMonoidHom ∧
      (decGroup q.2.length q.1).map (Equiv.permCongrHom (decCameron c h)).toMonoidHom ≤
        Babai.wreathProduct (Babai.JohnsonS c.k c.t) c.s
  let f (q : RawGens × List ℕ) : Option RawCameron :=
    if h : ∃ c, P q c then some h.choose else none
  refine ⟨f, ?_⟩
  intro n gs dom hd hw hcam
  subst n
  have hex : ∃ c, P (gs, dom) c := by
    obtain ⟨s, t, k, hs, ht, hm, hk, _, hR, e, hlo, hhi⟩ := hcam
    let c := camEncode e
    have h : c.WF dom.length := camEncode_wf e hs ht hm hk
    refine ⟨c, h, hR, ?_, ?_⟩
    · simpa only [c, camDecode_encode] using hlo
    · simpa only [c, camDecode_encode] using hhi
  obtain ⟨h, hR, hlo, hhi⟩ := hex.choose_spec
  exact ⟨hex.choose, h, dif_pos hex, hR, hlo, hhi⟩

/-- The output is a Cameron structure in the sense of Def. 11.2.2, with the returned
bijection as the identification. -/
theorem cameronStructureSpec_isCameronGroup
    {cameron : RawGens × List ℕ → Option RawCameron} (hspec : CameronStructureSpec cameron)
    {n : ℕ} {gs : RawGens} {dom : List ℕ} (hd : dom.length = n) (hw : RawGens.WF n gs)
    (hcam : ∃ s t k : ℕ, Babai.IsCameronGroup (decGroup n gs) s t k) :
    ∃ (c : RawCameron) (_ : c.WF n), cameron (gs, dom) = some c ∧
      Babai.IsCameronGroup (decGroup n gs) c.s c.t c.k := by
  obtain ⟨c, h, heq, hR, hlo, hhi⟩ := hspec n gs dom hd hw hcam
  exact ⟨c, h, heq, h.s_pos, h.t_pos, h.k_max, h.k_gt,
    by simpa using h.card, hR, decCameron c h, hlo, hhi⟩

/-- The specification of the axiom gives the hypothesis of the descent theorems: a
primitive group of degree `n ≥ 25` and order at least `n^{1 + log₂ n}` is a Cameron group
by the cited Theorem 11.2.3. -/
theorem cameronSpec_of_structureSpec
    {cameron : RawGens × List ℕ → Option RawCameron} (hspec : CameronStructureSpec cameron) :
    CameronSpec cameron := by
  intro n gs dom hd hw hn hp hb
  exact hspec n gs dom hd hw
    (Babai.Theorem_11_2_3 (decGroup n gs) (by simpa using hn) hp (by simpa using hb))

/-- **The hypothesis `(cameron, hpoly, hspec)` of `Workspace/Algo/CameronDescent.lean` is
discharged** by the cited routine. -/
theorem exists_polyFun_cameronSpec :
    ∃ cameron : RawGens × List ℕ → Option RawCameron, PolyFun cameron ∧ CameronSpec cameron := by
  obtain ⟨cameron, hpoly, hspec⟩ := cameronStructure_polyTime
  exact ⟨cameron, hpoly, cameronSpec_of_structureSpec hspec⟩

end Algo

#print axioms Algo.cameronStructureSpec_exists
#print axioms Algo.exists_polyFun_cameronSpec
