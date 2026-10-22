/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingFrameCocycle

/-!
# Arbitrary pullbacks retain the original framed cubic transitions

The actual maps over the coefficient spectrum and their exact cocycle may
be pulled back along any scheme morphism. This includes nonflat and nilpotent
base changes; it does not identify independently chosen new pole splittings.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle Scheme.Modules.pullback
  smoothMarkingWeierstrassCurve
variable {S : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (E : GeneralizedEllipticCurve S) (s : 𝟙_ (Over S) ⟶ E.group)
  (e f g : (pullback (s ≫ E.inclusion).left).obj
    (divisorLineBundle (s ≫ E.inclusion).left.ker
      (smoothMarking_relativeCartier E s).1) ≅ structureModule S)

/-- The original cubic morphism as a morphism over its actual coefficient spectrum. -/
def smoothMarkingCubicOverMap :
    Over.mk (E.curve.hom ≫ S.toSpecΓ) ⟶
      Over.mk (integralCurveStructure (smoothMarkingWeierstrassCurve E s e)) :=
  Over.homMk (smoothMarkingToIntegralCubic E s e) (smoothMarkingToIntegralCubic_over E s e)

/-- The complete frame transition retains its coefficient base as an actual over isomorphism. -/
def smoothMarkingFrameCubicOverIso :
    Over.mk (integralCurveStructure (smoothMarkingWeierstrassCurve E s e)) ≅
      Over.mk (integralCurveStructure (smoothMarkingWeierstrassCurve E s f)) :=
  Over.isoMk (smoothMarkingFrameCubicIso E s e f) (smoothMarkingFrameCubicIso_over E s e f)

/-- The original cubic morphisms commute with the transition as morphisms over the base. -/
theorem smoothMarkingCubicOverMap_frameChange :
    smoothMarkingCubicOverMap E s e ≫ (smoothMarkingFrameCubicOverIso E s e f).hom =
      smoothMarkingCubicOverMap E s f := by
  ext1
  exact smoothMarkingToIntegralCubic_frameChange E s e f

/-- The same-base complete cubic cocycle retains its over-category structure. -/
theorem smoothMarkingFrameCubicOverIso_cocycle :
    smoothMarkingFrameCubicOverIso E s e f ≪≫ smoothMarkingFrameCubicOverIso E s f g =
      smoothMarkingFrameCubicOverIso E s e g := by
  apply Iso.ext
  ext1
  exact congrArg Iso.hom (smoothMarkingFrameCubicIso_cocycle E s e f g)

variable {T : Scheme} (a : T ⟶ Spec (.of Γ(S, ⊤)))

/-- Every actual coefficient-base change retains the original compatible cubic maps. -/
theorem smoothMarkingCubicOverMap_pullback_frameChange :
    (Over.pullback a).map (smoothMarkingCubicOverMap E s e) ≫
      ((Over.pullback a).mapIso (smoothMarkingFrameCubicOverIso E s e f)).hom =
        (Over.pullback a).map (smoothMarkingCubicOverMap E s f) := by
  rw [Functor.mapIso_hom, ← Functor.map_comp, smoothMarkingCubicOverMap_frameChange]

/-- The original triple-frame cocycle remains exact after arbitrary, possibly nonflat pullback. -/
theorem smoothMarkingFrameCubicOverIso_pullback_cocycle :
    (Over.pullback a).mapIso (smoothMarkingFrameCubicOverIso E s e f) ≪≫
      (Over.pullback a).mapIso (smoothMarkingFrameCubicOverIso E s f g) =
        (Over.pullback a).mapIso (smoothMarkingFrameCubicOverIso E s e g) := by
  rw [← Functor.mapIso_trans, smoothMarkingFrameCubicOverIso_cocycle]

end FLT.Mazur.GeneralizedEllipticCurve
