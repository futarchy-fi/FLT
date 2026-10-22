/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveIntegralMarkingAmple
public import FLT.Mazur.GeneralizedCurveMarkingCoordinateRing
public import FLT.Mazur.AmpleDivisorComplementAffine

/-!
# The original affine cubic complement for integral geometric fibers

The actual marking line is ample without assuming the whole curve smooth.
Consequently its complement is affine and the constructed coordinate morphism
is an isomorphism, retaining the original base map. Higher polygons are excluded
by the explicit geometric integrality hypothesis in this specialization.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory Scheme.Modules
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle Scheme.Modules.pullback

variable {S : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (E : GeneralizedEllipticCurve S) [GeometricallyIntegral E.curve.hom]
  (s : 𝟙_ (Over S) ⟶ E.group)

local notation "t" => s ≫ E.inclusion
local notation "hI" => And.left (smoothMarking_relativeCartier E s)
local notation "U" => Scheme.Opens.toScheme (X := Over.left (curve E))
  (TopologicalSpace.Closeds.compl
    (Scheme.IdealSheafData.support (Scheme.Hom.ker (Over.Hom.left (t)))))

/-- The actual marking complement is affine for families with integral geometric fibers. -/
theorem smoothMarkingComplement_isAffine : IsAffineOpen (t).left.ker.support.compl := by
  let _ : IsProper E.curve.hom := E.family.family.1
  exact isAffineOpen_divisorComplement (E.curve.hom ≫ S.isoSpec.hom) (hI)
    (E.smoothMarkingLine_ample s)

variable (e : (pullback (s ≫ E.inclusion).left).obj
  (divisorLineBundle (s ≫ E.inclusion).left.ker
    (smoothMarking_relativeCartier E s).1) ≅ structureModule S)

local notation "W" => smoothMarkingWeierstrassCurve E s e

/-- The constructed original coordinate morphism is an affine scheme isomorphism. -/
theorem smoothMarkingToAffineCubic_isIso : IsIso (smoothMarkingToAffineCubic E s e) := by
  let _ : IsAffine U := E.smoothMarkingComplement_isAffine s
  let _ : IsIso (CommRingCat.ofHom (smoothMarkingCoordinateEvaluation E s e)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (smoothMarkingCoordinateRingEquiv E s e).bijective
  unfold smoothMarkingToAffineCubic
  infer_instance

/-- The original complement identified with its constructed relative Weierstrass cubic. -/
def smoothMarkingAffineIso : U ≅ Spec (.of (W).toAffine.CoordinateRing) := by
  let _ := smoothMarkingToAffineCubic_isIso E s e
  exact asIso (smoothMarkingToAffineCubic E s e)

/-- The affine scheme comparison preserves the actual structure morphism. -/
theorem smoothMarkingAffineIso_over :
    (smoothMarkingAffineIso E s e).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) (W).toAffine.CoordinateRing)) =
        (Scheme.Opens.ι (X := E.curve.left) (t).left.ker.support.compl) ≫
          E.curve.hom ≫ S.toSpecΓ :=
  smoothMarkingToAffineCubic_over E s e

end FLT.Mazur.GeneralizedEllipticCurve
