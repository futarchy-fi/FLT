/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicRestrictedLocalization
public import FLT.Mazur.CyclicCharacteristicResidualPrincipalBasis
public import FLT.Mazur.LocallyRingedPrincipalAffineness

/-!
# The original affine residual comparison is an isomorphism

The original homeomorphism and the actual principal restrictions identify the
canonical locally ringed map. Transport through the section coordinates retains
the previously constructed residual comparison and its sheaf pullback.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (i : InvariantAffineIndex n)

/-- The canonical spectrum map has the topology of the original residual comparison. -/
theorem affineOpenSpace_toΓSpecBase_isHomeomorph :
    IsHomeomorph (invariantOpenSpace n (affineOrbitOpen n i)).toΓSpecBase := by
  let f := (invariantOpenSpace n (affineOrbitOpen n i)).toΓSpec
  let g := Spec.locallyRingedSpaceMap
    (invariantOpenSectionsIso n (affineOrbitOpen n i)).inv
  let h := (affineResidualComparisonIso n i).inv.toLRSHom
  have hg : IsIso g :=
    Spec.toLocallyRingedSpace.map_isIso
      (invariantOpenSectionsIso n (affineOrbitOpen n i)).inv.op
  have hh : IsIso h := inferInstance
  have hgb : IsIso g.base := LocallyRingedSpace.forgetToTop.map_isIso g
  have hhb : IsIso h.base := LocallyRingedSpace.forgetToTop.map_isIso h
  have hc : IsIso ((f.base ≫ g.base) ≫ h.base) :=
    (TopCat.isIso_iff_isHomeomorph _).mpr
      (affineResidualRingedComparison_base_isHomeomorph n i)
  have hfg : IsIso (f.base ≫ g.base) := IsIso.of_isIso_comp_right _ h.base
  have hf : IsIso f.base := IsIso.of_isIso_comp_right _ g.base
  exact (TopCat.isIso_iff_isHomeomorph f.base).mp hf

/-- The canonical map of the actual orbit open is a locally ringed isomorphism. -/
instance affineOpenSpace_toΓSpec_isIso :
    IsIso (invariantOpenSpace n (affineOrbitOpen n i)).toΓSpec :=
  LocallyRingedPrincipalComparison.isIso_toΓSpec _
    (affineOpenSpace_toΓSpecBase_isHomeomorph n i)
    (invariantOpenSpace_principal_isLocalization n (affineOrbitOpen n i))

/-- The original invariant affine comparison is an isomorphism. -/
instance affineInvariantComparison_isIso :
    IsIso (invariantAffineComparison n (affineOrbitOpen n i)) := by
  unfold invariantAffineComparison
  have : IsIso (Spec.locallyRingedSpaceMap
      (invariantOpenSectionsIso n (affineOrbitOpen n i)).inv) :=
    Spec.toLocallyRingedSpace.map_isIso
      (invariantOpenSectionsIso n (affineOrbitOpen n i)).inv.op
  infer_instance

/-- The original full residual comparison, including its sheaf map, is an isomorphism. -/
instance affineResidualRingedComparison_isIso :
    IsIso (affineResidualRingedComparison n i) := by
  unfold affineResidualRingedComparison
  infer_instance

/-- The original quotient open is isomorphic to the spectrum of its full residual functions. -/
def affineResidualRingedIso : invariantOpenSpace n (affineOrbitOpen n i) ≅
    (affineResidualSpectrum n i).toLocallyRingedSpace :=
  asIso (affineResidualRingedComparison n i)

/-- Its base map is exactly the original orbit-to-residual-spectrum map. -/
theorem affineResidualRingedIso_base (z : affineOrbitOpen n i) :
    (affineResidualRingedIso n i).hom.base z = orbitToResidualSpectrum n i z :=
  affineResidualRingedComparison_base n i z

end FLT.Mazur.CyclicCharacteristicOrbit
