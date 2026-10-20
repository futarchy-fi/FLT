/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArithmeticOneGonGeneralizedCurve
public import FLT.Mazur.OneGonSmoothingRelativeGroupSpecialization

/-!
# The arithmetic zero-parameter one-gon has the original torus group

The split-nodal group comparison works over any coefficient ring. Inversion
corrects its coordinate to the one used in the original pinching presentation.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj GrpObj

namespace FLT.Mazur.ArithmeticOneGonTorus

open OneGonSmoothing ArithmeticOneGonGeneralizedCurve WeierstrassIntegralChart

variable (R : Type) [CommRing R]

/-- The original arithmetic cubic at parameter zero. -/
def boundaryCurve : GeneralizedEllipticCurve (Spec (.of R)) :=
  curve (0 : R) (by simp)

/-- Inversion preserves the multiplicative group law over every coefficient ring. -/
theorem inversion_isMonHom : IsMonHom ι[MultiplicativeGroupScheme.gm R] := by
  constructor
  · have hi : (1 : 𝟙_ (Over (Spec (.of R))) ⟶ MultiplicativeGroupScheme.gm R) ≫
        ι[MultiplicativeGroupScheme.gm R] = 1 := by
      change (1 : 𝟙_ (Over (Spec (.of R))) ⟶ MultiplicativeGroupScheme.gm R)⁻¹ = 1
      exact inv_one
    simpa only [CategoryTheory.Hom.one_def,
      CartesianMonoidalCategory.toUnit_unique
        (CartesianMonoidalCategory.toUnit (𝟙_ (Over (Spec (.of R))))) (𝟙 _),
      Category.id_comp] using hi
  · rw [GrpObj.mul_inv_rev, IsCommMonObj.mul_comm]

/-- Inversion bundled on the arithmetic torus. -/
def inversion : CommGrp.mk (MultiplicativeGroupScheme.gm R) ≅
    CommGrp.mk (MultiplicativeGroupScheme.gm R) := by
  let _ := inversion_isMonHom R
  exact CommGrp.mkIso' (asIso ι[MultiplicativeGroupScheme.gm R])

/-- The torus group with the corrected original pinching coordinate. -/
def groupIso : CommGrp.mk (MultiplicativeGroupScheme.gm R) ≅ relativeGroup (0 : R) :=
  inversion R ≪≫ (zeroRelativeGroupTorusIso (R := R)).symm

/-- The arithmetic torus presentation of the actual generalized curve. -/
def torusIso : MultiplicativeGroupScheme.gm R ≅ (boundaryCurve R).group :=
  (CommGrp.forget (Over (Spec (.of R)))).mapIso (groupIso R)

instance torusIso_isMonHom : IsMonHom (torusIso R).hom :=
  inferInstanceAs (IsMonHom (groupIso R).hom.hom.hom.hom)

/-- The torus presentation retains inversion and the original Laurent parametrization. -/
theorem torusIso_hom :
    (torusIso R).hom = ι[MultiplicativeGroupScheme.gm R] ≫
      (splitNodalRelativeSmoothOverIso (-1 : Rˣ)).hom := by
  change ι[MultiplicativeGroupScheme.gm R] ≫
    (integralSmoothSplitNodalTorusIso (-1 : Rˣ)).inv.hom.hom.hom = _
  congr 1

/-- The full-curve embedding retains the original arithmetic smooth-open inclusion. -/
theorem torusIso_inclusion :
    (torusIso R).hom ≫ (boundaryCurve R).inclusion =
      ι[MultiplicativeGroupScheme.gm R] ≫
        (splitNodalRelativeSmoothOverIso (-1 : Rˣ)).hom ≫
          relativeGroupInclusion (0 : R) := by
  rw [torusIso_hom]
  change (_ ≫ _) ≫ (curve (0 : R) _).inclusion = _
  rw [curve_inclusion, Category.assoc]

end FLT.Mazur.ArithmeticOneGonTorus
