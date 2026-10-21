/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonCommonCoefficientCurve
public import FLT.Mazur.OneGonSmoothCoefficientGroup

/-!
# Smooth groups from independent coefficient bases

Equality of the two smoothing parameters in a common ring identifies the
actual base-changed smooth groups. This is a bundled group isomorphism, so
it retains multiplication, identity, and inverse on singular fibers as well.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.OneGonSmoothing
open WeierstrassIntegralChart WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A C] [Algebra B C] (a : A) (b : B)

/-- Independent initial smooth groups identify over the common coefficient ring. -/
irreducible_def commonCoefficientGroupIso (h : algebraMap A C a = algebraMap B C b) :
    originalSmoothBaseChangeGroup C (equation a) ≅
      originalSmoothBaseChangeGroup C (equation b) :=
  (smoothCoefficientGroupIso a).symm ≪≫ smoothEquationGroupIso (congrArg equation h) ≪≫
    smoothCoefficientGroupIso b

/-- Recovery agrees with equality transport on the actual intrinsic smooth group. -/
@[reassoc] theorem commonCoefficientGroupIso_recovery
    (h : algebraMap A C a = algebraMap B C b) :
    (smoothCoefficientGroupIso a).hom ≫ (commonCoefficientGroupIso a b h).hom =
      (smoothEquationGroupIso (congrArg equation h)).hom ≫
        (smoothCoefficientGroupIso b).hom := by
  rw [commonCoefficientGroupIso_def]
  exact iso_common_recovery _ _ _

/-- The underlying relative scheme comparison retains the common base. -/
def commonCoefficientSmoothIso (h : algebraMap A C a = algebraMap B C b) :
    (originalSmoothBaseChangeGroup C (equation a)).X ≅
      (originalSmoothBaseChangeGroup C (equation b)).X :=
  (CommGrp.forget (Over (Spec (.of C)))).mapIso (commonCoefficientGroupIso a b h)

instance commonCoefficientSmoothIso_isMonHom
    (h : algebraMap A C a = algebraMap B C b) :
    IsMonHom (commonCoefficientSmoothIso a b h).hom := by
  change IsMonHom (commonCoefficientGroupIso a b h).hom.hom.hom.hom
  infer_instance

/-- The inverse also preserves the group laws, without any smoothness of the whole cubic. -/
instance commonCoefficientSmoothIso_inv_isMonHom
    (h : algebraMap A C a = algebraMap B C b) :
    IsMonHom (commonCoefficientSmoothIso a b h).inv := by
  change IsMonHom (commonCoefficientGroupIso a b h).inv.hom.hom.hom
  infer_instance

/-- The scheme comparison retains the full geometric recovery map. -/
@[reassoc] theorem commonCoefficientSmoothIso_recovery
    (h : algebraMap A C a = algebraMap B C b) :
    (smoothCoefficientGroupOverIso a).hom ≫ (commonCoefficientSmoothIso a b h).hom =
      ((CommGrp.forget (Over (Spec (.of C)))).mapIso
        (smoothEquationGroupIso (congrArg equation h))).hom ≫
          (smoothCoefficientGroupOverIso b).hom := by
  exact congrArg (fun f => (CommGrp.forget (Over (Spec (.of C)))).map f)
    (commonCoefficientGroupIso_recovery a b h)

end FLT.Mazur.OneGonSmoothing
