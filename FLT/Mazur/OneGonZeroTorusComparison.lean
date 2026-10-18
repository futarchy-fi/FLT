/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingZeroFiber
public import FLT.Mazur.OneGonSmoothingRelativeGroupSpecialization

/-!
# The original one-gon torus coordinate in the smooth cubic group

The pinching uses the inverse of the split nodal tangent coordinate. This
comparison retains the actual open immersion and corrects the group coordinate
by inversion before comparing the whole closed curves.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj GrpObj
open scoped LaurentPolynomial
namespace FLT.Mazur.OneGonSmoothing
open WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R]

/-- The original infinity coordinates are the inverted split-nodal coordinates. -/
theorem zeroInfinityToTorus_eq_invert :
    zeroInfinityToTorus (R := R) = LaurentPolynomial.invert.toAlgHom.comp
      (splitNodalChartToLaurent (-1 : Rˣ)) := by
  apply hom_ext
  intro i
  change zeroInfinityToTorus (coord (equation (0 : R)) 1 i) =
    LaurentPolynomial.invert
      (splitNodalChartToLaurent (-1 : Rˣ) (coord (splitNodalEquation (-1 : Rˣ)) 1 i))
  rw [splitNodalChartToLaurent_coord]
  fin_cases i
  · simp [splitNodalLaurentX]
  · simp
  · simp [splitNodalLaurentZ, splitNodalLaurentX]

variable (K : Type) [Field K]

/-- Scheme inversion is the Laurent-coordinate inversion on the original torus. -/
theorem torus_inversion_left :
    ι[MultiplicativeGroupScheme.gm K].left = (ProjectiveLine.inversion K).hom := by
  change Spec.map (CommRingCat.ofHom (HopfAlgebra.antipodeAlgHom K K[T;T⁻¹]).toRingHom) = _
  rw [ProjectiveLine.inversion_hom]
  congr 1
  apply congrArg CommRingCat.ofHom
  change (HopfAlgebra.antipodeAlgHom K K[T;T⁻¹]).toRingHom =
    (LaurentPolynomial.invert (R := K)).toAlgHom.toRingHom
  apply congrArg (fun f : K[T;T⁻¹] →ₐ[K] K[T;T⁻¹] => f.toRingHom)
  apply LaurentUnitPoints.hom_ext <;>
    change HopfAlgebra.antipode K _ = _ <;>
    simp [LaurentPolynomial.antipode_T]

/-- The original infinity chart differs from the smooth-group chart by inversion. -/
theorem zeroTorusChartIso_eq :
    (zeroTorusChartIso K).hom =
      ι[MultiplicativeGroupScheme.gm K].left ≫ (splitNodalTorusIso (-1 : Kˣ)).hom := by
  rw [torus_inversion_left, ProjectiveLine.inversion_hom]
  change Spec.map (CommRingCat.ofHom (zeroInfinityToTorus (R := K)).toRingHom) =
    Spec.map _ ≫ Spec.map
      (CommRingCat.ofHom (splitNodalChartToLaurent (-1 : Kˣ)).toRingHom)
  rw [← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom))
    (zeroInfinityToTorus_eq_invert (R := K))

/-- The smooth group comparison retains the actual original torus embedding. -/
@[reassoc] theorem zeroTorusInclusion_eq :
    zeroTorusInclusion K = ι[MultiplicativeGroupScheme.gm K].left ≫
      (splitNodalRelativeSmoothOverIso (-1 : Kˣ)).hom.left ≫
        (relativeGroupInclusion (0 : K)).left := by
  rw [zeroTorusInclusion, zeroTorusChartIso_eq, Category.assoc]
  exact congrArg (ι[MultiplicativeGroupScheme.gm K].left ≫ ·)
    (splitNodalTorusToSmooth_inclusion (-1 : Kˣ)).symm

/-- The whole pinching comparison agrees with the corrected smooth-group coordinate. -/
@[reassoc] theorem torus_zeroFiberIso_group :
    OneGonGluing.torus K ≫ (zeroFiberIso K).hom =
      ι[MultiplicativeGroupScheme.gm K].left ≫
        (splitNodalRelativeSmoothOverIso (-1 : Kˣ)).hom.left ≫
          (relativeGroupInclusion (0 : K)).left := by
  rw [torus_zeroFiberIso, zeroTorusInclusion_eq]

end FLT.Mazur.OneGonSmoothing
