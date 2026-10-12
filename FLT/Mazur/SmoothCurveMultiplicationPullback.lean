/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothCyclicDivisorEquations

/-!
# Full smooth-curve multiplication under a cartesian comparison

The full DR comparison and the original smooth inclusions identify the group
law on the source with the monoidal pullback of the original curve group law.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} (E : GeneralizedEllipticCurve S)
  (F : GeneralizedEllipticCurve T) [Smooth E.curve.hom] [Smooth F.curve.hom]
  (k : T ⟶ S) (e : F ≅ E.baseChange k)
attribute [local instance] smoothCurveCommGrpObj

omit [Smooth E.curve.hom] in
/-- The full curve comparison is determined by its group comparison and original inclusions. -/
theorem smoothCurvePullbackHom_eq :
    e.hom.curve = inv F.inclusion ≫ e.hom.group ≫ (Over.pullback k).map E.inclusion := by
  apply (cancel_epi F.inclusion).mp
  rw [IsIso.hom_inv_id_assoc, e.hom.inclusion, baseChange_inclusion]
  rfl

/-- The same curve map is a homomorphism to the pulled-back original curve group. -/
instance smoothCurvePullbackHom_isMonHom :
    IsMonHom (show F.curve ⟶ (Over.pullback k).obj E.curve from e.hom.curve) := by
  rw [smoothCurvePullbackHom_eq E F k e]
  change IsMonHom (inv F.inclusion ≫ e.hom.group ≫ (Over.pullback k).map E.inclusion)
  let _ : IsMonHom (inv F.inclusion) :=
    inferInstanceAs (IsMonHom (asIso F.inclusion).inv)
  infer_instance

/-- Multiplication on the entire source curve is the original pulled-back multiplication. -/
theorem smoothCurvePullbackHom_mul :
    μ[F.curve] ≫ e.hom.curve = (e.hom.curve ⊗ₘ e.hom.curve) ≫
      Functor.LaxMonoidal.μ (Over.pullback k) E.curve E.curve ≫
        (Over.pullback k).map μ[E.curve] :=
  IsMonHom.mul_hom (show F.curve ⟶ (Over.pullback k).obj E.curve from e.hom.curve)

end FLT.Mazur.GeneralizedEllipticCurve
