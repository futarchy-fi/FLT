/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXConicPunctureInclusion
public import FLT.Mazur.WeierstrassModificationXConicParameterSections
public import FLT.Mazur.ProjectiveLineEndpoints

/-!
# The full affine parameter, with its original puncture and origin

A vanishing divided constant makes the entire parameter open an affine line.
The identification preserves the original coordinate, puncture and marking.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped Polynomial LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
open WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type*} [Field K] (c : K) (hc : c = 0)

/-- The full parameter algebra, without replacing its original divided constant. -/
def conicZeroAffineEquiv : ConicParameterOpen c ≃ₐ[K] K[X] := by
  subst c
  exact conicZeroParameterEquiv K

/-- The identification preserves every polynomial in the parameter. -/
theorem conicZeroAffineEquiv_base (p : K[X]) :
    conicZeroAffineEquiv c hc (algebraMap K[X] (ConicParameterOpen c) p) = p := by
  subst c
  exact conicZeroParameterEquiv_base K p

/-- The original full affine parameter as a scheme isomorphism. -/
def conicZeroAffineIso : ProjectiveLine.chart K ≅ Spec (.of (ConicParameterOpen c)) :=
  Scheme.Spec.mapIso (conicZeroAffineEquiv c hc).toRingEquiv.toCommRingCatIso.op

/-- The standard puncture is the original conic puncture in these full coordinates. -/
@[reassoc] theorem conicZeroAffineIso_puncture :
    ProjectiveLine.overlapLeft K ≫ (conicZeroAffineIso c hc).hom =
      Spec.map (CommRingCat.ofHom (conicZeroPuncture c hc).toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  change (Polynomial.toLaurentAlg.comp (conicZeroAffineEquiv c hc).toAlgHom).toRingHom = _
  congr 1
  apply IsLocalization.algHom_ext (Submonoid.powers (conicParameterPolynomial c))
  apply AlgHom.ext
  intro p
  change Polynomial.toLaurent (conicZeroAffineEquiv c hc (algebraMap _ _ p)) = _
  rw [conicZeroAffineEquiv_base]
  exact (conicZeroPuncture_base c hc p).symm

/-- The affine origin is exactly the original conic parameter marking. -/
@[reassoc] theorem conicZeroAffineIso_origin :
    ProjectiveLine.chartZero K ≫ (conicZeroAffineIso c hc).hom =
      Spec.map (CommRingCat.ofHom (conicParameterOrigin c).toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  change ((Polynomial.aeval (0 : K)).comp (conicZeroAffineEquiv c hc).toAlgHom).toRingHom = _
  congr 1
  apply IsLocalization.algHom_ext (Submonoid.powers (conicParameterPolynomial c))
  apply AlgHom.ext
  intro p
  change Polynomial.eval 0 (conicZeroAffineEquiv c hc (algebraMap _ _ p)) = _
  rw [conicZeroAffineEquiv_base]
  exact (conicParameterOrigin_base c p).symm

/-- The complete parameter identification is over the original coefficient field. -/
@[reassoc] theorem conicZeroAffineIso_structure :
    (conicZeroAffineIso c hc).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (ConicParameterOpen c))) =
        ProjectiveLine.chartToBase K := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (conicZeroAffineEquiv c hc).commutes

end FLT.Mazur.WeierstrassModificationX
