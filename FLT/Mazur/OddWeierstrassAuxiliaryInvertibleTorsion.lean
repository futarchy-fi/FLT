/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GroupTorsionUnramifiedBaseChange
public import FLT.Mazur.GroupTorsionUnramifiedTransport
public import FLT.Mazur.OddWeierstrassAuxiliarySchemeGroupComparison
public import FLT.Mazur.WeierstrassTorsionFormallyUnramified

/-!
# Invertible torsion in the actual auxiliary group family

The level only needs to be a unit on the original test scheme. The evaluated
coefficient model, arbitrary base change, and the original group comparison
transport formal unramifiedness to its full torsion equalizer.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Obj
namespace FLT.Mazur.OddWeierstrassParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {T : Scheme} (f : T ⟶ levelThree.left)

/-- Full torsion of the actual auxiliary family is unramified at every invertible level. -/
theorem auxiliarySchemeTorsion_formallyUnramified (n : ℕ) (hn : IsUnit (n : Γ(T, ⊤))) :
    FormallyUnramified (GroupTorsionScheme.scheme (auxiliarySchemeGroup f).X n).hom := by
  have h : FormallyUnramified
      (GroupTorsionScheme.scheme (auxiliaryPullbackGroup f.appTop.hom).X n).hom :=
    WeierstrassIntegralChart.integralTorsion_formallyUnramified
      (auxiliaryPullbackEquation f.appTop.hom)
      (auxiliaryPullbackEquation_discriminant f.appTop.hom) n hn
  let _ : FormallyUnramified (GroupTorsionScheme.scheme
      ((Over.pullback T.toSpecΓ).mapCommGrp.obj (auxiliaryPullbackGroup f.appTop.hom)).X n).hom :=
    GroupTorsionScheme.baseChange_formallyUnramified T.toSpecΓ
      (auxiliaryPullbackGroup f.appTop.hom).X n
  exact GroupTorsionScheme.transport_formallyUnramified _ _
    (auxiliarySchemeCoefficientGroupIso f) n

end FLT.Mazur.OddWeierstrassParameter
