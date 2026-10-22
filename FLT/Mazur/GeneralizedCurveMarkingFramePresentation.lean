/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingFramePullback
public import FLT.Mazur.GeneralizedCurveMarkingProjectiveIso

/-!
# The explicit frame transitions compare the original full presentations

For integral geometric fibers the coordinate transition is exactly the
comparison through the original curve. Thus the constructed pointed cubic
presentations and their arbitrary pullbacks agree by the explicit frame law.
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
  (E : GeneralizedEllipticCurve S) [GeometricallyIntegral E.curve.hom]
  (s : 𝟙_ (Over S) ⟶ E.group)
  (e f : (pullback (s ≫ E.inclusion).left).obj
    (divisorLineBundle (s ≫ E.inclusion).left.ker
      (smoothMarking_relativeCartier E s).1) ≅ structureModule S)

/-- The original full presentation changes by the explicitly constructed projective transition. -/
theorem smoothMarkingIntegralCubicIso_frameChange :
    smoothMarkingIntegralCubicIso E s e ≪≫ smoothMarkingFrameCubicIso E s e f =
      smoothMarkingIntegralCubicIso E s f := by
  apply Iso.ext
  exact smoothMarkingToIntegralCubic_frameChange E s e f

/-- The explicit admissible transition equals comparison through the entire original curve. -/
theorem smoothMarkingFrameCubicIso_eq_comparison :
    smoothMarkingFrameCubicIso E s e f =
      (smoothMarkingIntegralCubicIso E s e).symm ≪≫ smoothMarkingIntegralCubicIso E s f := by
  rw [← smoothMarkingIntegralCubicIso_frameChange E s e f]
  simp only [Iso.symm_self_id_assoc]

/-- The original full presentation is an isomorphism over its actual coefficient spectrum. -/
theorem smoothMarkingCubicOverMap_isIso : IsIso (smoothMarkingCubicOverMap E s e) := by
  let Q : Over.mk (E.curve.hom ≫ S.toSpecΓ) ≅
      Over.mk (integralCurveStructure (smoothMarkingWeierstrassCurve E s e)) :=
    Over.isoMk (smoothMarkingIntegralCubicIso E s e) (smoothMarkingIntegralCubicIso_over E s e)
  change IsIso Q.hom
  infer_instance

/-- Every scheme-theoretic base change retains that full original presentation. -/
theorem smoothMarkingCubicOverMap_pullback_isIso {T : Scheme}
    (a : T ⟶ Spec (.of Γ(S, ⊤))) :
    IsIso ((Over.pullback a).map (smoothMarkingCubicOverMap E s e)) := by
  let _ := smoothMarkingCubicOverMap_isIso E s e
  infer_instance

end FLT.Mazur.GeneralizedEllipticCurve
