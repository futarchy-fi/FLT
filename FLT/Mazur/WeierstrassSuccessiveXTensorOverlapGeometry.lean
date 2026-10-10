/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXTensorOverlap

/-!
# The cartesian square of the actual tensor overlap

The tensor principal opens retain the original integral overlap morphism,
its coefficient structure, and its entire preceding-chart contraction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
  (S : Type u) [CommRing S] [Algebra R S]

/-- The tensor incidence open projects to its original integral principal open. -/
def tensorXOpenProjection : Spec (.of (TensorXOpen W s π b3 b4 b6 S)) ⟶
    Spec (.of (XOpen W s π b3 b4 b6)) :=
  Spec.map (CommRingCat.ofHom (tensorXOpenCoefficient W s π b3 b4 b6 S).toRingHom)

/-- The tensor divided open projects to its original integral principal open. -/
def tensorDividedOpenProjection : Spec (.of (TensorDividedOpen W s π b3 b4 b6 S)) ⟶
    Spec (.of (DividedOpen W s π b3 b4 b6)) :=
  Spec.map (CommRingCat.ofHom (tensorDividedOpenCoefficient W s π b3 b4 b6 S).toRingHom)

/-- The actual base-changed overlap isomorphism between the tensor principal opens. -/
def tensorOverlapIso : Spec (.of (TensorXOpen W s π b3 b4 b6 S)) ≅
    Spec (.of (TensorDividedOpen W s π b3 b4 b6 S)) :=
  Scheme.Spec.mapIso (tensorOverlapEquiv W s π b3 b4 b6 S).toRingEquiv.toCommRingCatIso.op

/-- The original integral overlap morphism is retained by the full tensor transition. -/
@[reassoc] theorem tensorOverlapIso_square :
    (tensorOverlapIso W s π b3 b4 b6 S).hom ≫ tensorDividedOpenProjection W s π b3 b4 b6 S =
      tensorXOpenProjection W s π b3 b4 b6 S ≫ (overlapIso W s π b3 b4 b6).hom := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext z
  exact tensorOverlapEquiv_coefficient W s π b3 b4 b6 S z

/-- The displayed square is cartesian, retaining the actual integral overlap morphism. -/
theorem tensorOverlapIso_isPullback :
    IsPullback (tensorOverlapIso W s π b3 b4 b6 S).hom
      (tensorXOpenProjection W s π b3 b4 b6 S)
      (tensorDividedOpenProjection W s π b3 b4 b6 S) (overlapIso W s π b3 b4 b6).hom :=
  IsPullback.of_horiz_isIso ⟨tensorOverlapIso_square W s π b3 b4 b6 S⟩

/-- Both original preceding-chart contractions agree on the entire tensor overlap. -/
@[reassoc] theorem tensorOverlapIso_toPrevious :
    (tensorOverlapIso W s π b3 b4 b6 S).hom ≫
      tensorDividedOpenProjection W s π b3 b4 b6 S ≫ dividedOpenInclusion W s π b3 b4 b6 ≫
        dividedToPrevious W s π b3 b4 b6 =
      tensorXOpenProjection W s π b3 b4 b6 S ≫ xOpenInclusion W s π b3 b4 b6 ≫
        toDivided W s π b3 b4 b6 := by
  rw [tensorOverlapIso_square_assoc, overlapIso_toPrevious]

/-- The tensor transition preserves the new coefficient field or ring structure. -/
@[reassoc] theorem tensorOverlapIso_structure :
    (tensorOverlapIso W s π b3 b4 b6 S).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap S (TensorDividedOpen W s π b3 b4 b6 S))) =
        Spec.map (CommRingCat.ofHom (algebraMap S (TensorXOpen W s π b3 b4 b6 S))) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (tensorOverlapEquiv W s π b3 b4 b6 S).commutes

end FLT.Mazur.WeierstrassSuccessiveX
