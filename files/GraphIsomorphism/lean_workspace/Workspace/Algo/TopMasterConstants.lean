import Workspace.Algo.TopMasterCameronAdmission

/-! # The admission constants of the master carrier
The master carrier admits a child only if its encoding is at most `masterInputCap a b n`.
Every child the carrier makes is a checked window call (`Algo.masterCheckedCall`), which is
admitted for every `a b` (`Algo.masterCheckedCall_admitted`), except the children of the
Cameron descent of line 1, step 6, whose encodings are bounded by
`Algo.masterCameronChildBound n`. So one pair `a b` above that bound serves every line.
-/
namespace Algo

/-- The admission constants: a pair with `masterCameronChildBound n ≤ masterInputCap a b n`
for all `n` (`Algo.exists_masterCameronChild_cap`). -/
noncomputable def masterCapA : ℕ := exists_masterCameronChild_cap.choose
noncomputable def masterCapB : ℕ := exists_masterCameronChild_cap.choose_spec.choose

theorem masterCap_spec (n : ℕ) :
    masterCameronChildBound n ≤ masterInputCap masterCapA masterCapB n :=
  exists_masterCameronChild_cap.choose_spec.choose_spec n

end Algo
