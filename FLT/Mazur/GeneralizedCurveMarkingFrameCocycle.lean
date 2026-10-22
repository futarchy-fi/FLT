/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingFrameCubicChange
public import FLT.Mazur.WeierstrassVariableChangeProjectiveComposition
public import FLT.Mazur.WeierstrassVariableChangeIdentity

/-!
# Coherent transitions between the original framed cubic presentations

The constructed admissible changes and complete pointed cubic isomorphisms
satisfy identity, composition, and inversion. The equalities concern the
actual maps, including the contracted components of higher polygons.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory WeierstrassCurve
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve ModuleLineBundleTensorPullback WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
  Scheme.Modules.pullback sectionPoleMultiplicativeCoordinates relativePoleFunction
  smoothMarkingWeierstrassCurve
variable {S : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (E : GeneralizedEllipticCurve S) (s : 𝟙_ (Over S) ⟶ E.group)
  (e f g : (pullback (s ≫ E.inclusion).left).obj
    (divisorLineBundle (s ≫ E.inclusion).left.ker
      (smoothMarking_relativeCartier E s).1) ≅ structureModule S)

omit [IsAffine S] [IsNoetherianRing Γ(S, ⊤)] in
/-- The constructed admissible frame change is the identity when both frames coincide. -/
theorem smoothMarkingFrameChange_self : smoothMarkingFrameChange E s e e = 1 := by
  apply VariableChange.ext
  · exact frameComparisonUnit_self e ⊤
  · rfl
  · rfl
  · rfl

omit [IsAffine S] [IsNoetherianRing Γ(S, ⊤)] in
/-- Three actual frames give the exact admissible-change cocycle. -/
theorem smoothMarkingFrameChange_cocycle :
    smoothMarkingFrameChange E s e f * smoothMarkingFrameChange E s f g =
      smoothMarkingFrameChange E s e g := by
  apply VariableChange.ext
  · exact smoothMarkingFrameUnit_cocycle E s e f g
  · simp [smoothMarkingFrameChange, VariableChange.mul_def]
  · simp [smoothMarkingFrameChange, VariableChange.mul_def]
  · simp [smoothMarkingFrameChange, VariableChange.mul_def]

/-- The complete pointed cubic transition is identity for a repeated frame. -/
theorem smoothMarkingFrameCubicIso_self :
    smoothMarkingFrameCubicIso E s e e = Iso.refl _ := by
  simp only [smoothMarkingFrameCubicIso, smoothMarkingFrameChange_self,
    integralVariableChangeIso_one]

/-- The complete projective transitions compose according to the original frame cocycle. -/
theorem smoothMarkingFrameCubicIso_cocycle :
    smoothMarkingFrameCubicIso E s e f ≪≫ smoothMarkingFrameCubicIso E s f g =
      smoothMarkingFrameCubicIso E s e g := by
  apply Iso.ext
  change integralVariableChangeTo _ _ _ _ ≫ integralVariableChangeTo _ _ _ _ = _
  rw [integralVariableChangeTo_comp _ _ _ _ _ _ _
    (by rw [smoothMarkingFrameChange_cocycle]; exact smoothMarkingFrameChange_equation E s e g)]
  congr 1
  exact smoothMarkingFrameChange_cocycle E s e f g

/-- Reversing the actual two frames inverts their entire pointed cubic isomorphism. -/
theorem smoothMarkingFrameCubicIso_reverse :
    smoothMarkingFrameCubicIso E s f e = (smoothMarkingFrameCubicIso E s e f).symm := by
  apply Iso.ext
  apply (cancel_epi (smoothMarkingFrameCubicIso E s e f).hom).mp
  have h := congrArg Iso.hom (smoothMarkingFrameCubicIso_cocycle E s e f e)
  rw [smoothMarkingFrameCubicIso_self] at h
  exact h.trans (smoothMarkingFrameCubicIso E s e f).hom_inv_id.symm

end FLT.Mazur.GeneralizedEllipticCurve
