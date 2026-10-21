/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonCommonCoefficientInclusion

/-!
# Coherence of independent one-gon comparisons

Three independent parameter models give the same whole-curve and smooth-group
comparison by direct or successive comparison over a common coefficient ring.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OneGonSmoothing
open WeierstrassIntegralChart WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Sealed whole-curve parameter transport composes along equality of parameters. -/
theorem parameterCurveIso_trans {R : Type} [CommRing R] {r s t : R}
    (h : r = s) (k : s = t) :
    (parameterCurveIso h).hom ≫ (parameterCurveIso k).hom =
      (parameterCurveIso (h.trans k)).hom := by
  subst s t
  rw [parameterCurveIso_def]
  simp

/-- Sealed intrinsic group transport composes without changing the group structure. -/
theorem smoothEquationGroupIso_trans {R : Type} [CommRing R]
    {U V W : WeierstrassCurve R} (h : U = V) (k : V = W) :
    (smoothEquationGroupIso h).hom ≫ (smoothEquationGroupIso k).hom =
      (smoothEquationGroupIso (h.trans k)).hom := by
  subst V W
  rw [smoothEquationGroupIso_def]
  simp

variable {A B C D : Type} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  [Algebra A C] [Algebra B C] [Algebra D C] (a : A) (b : B) (d : D)
  (h : algebraMap A C a = algebraMap B C b)
  (k : algebraMap B C b = algebraMap D C d)

/-- Independent whole-curve comparisons satisfy the cocycle equation. -/
@[reassoc] theorem commonCoefficientCurveIso_trans :
    (commonCoefficientCurveIso a b h).hom ≫ (commonCoefficientCurveIso b d k).hom =
      (commonCoefficientCurveIso a d (h.trans k)).hom := by
  apply (cancel_epi (coefficientCurveOverIso a).hom).mp
  rw [← Category.assoc, commonCoefficientCurveIso_recovery, Category.assoc,
    commonCoefficientCurveIso_recovery, ← Category.assoc, parameterCurveIso_trans,
    commonCoefficientCurveIso_recovery]

/-- The cocycle equation holds in the category of bundled commutative group objects. -/
@[reassoc] theorem commonCoefficientGroupIso_trans :
    (commonCoefficientGroupIso a b h).hom ≫ (commonCoefficientGroupIso b d k).hom =
      (commonCoefficientGroupIso a d (h.trans k)).hom := by
  apply (cancel_epi (smoothCoefficientGroupIso a).hom).mp
  rw [← Category.assoc, commonCoefficientGroupIso_recovery, Category.assoc,
    commonCoefficientGroupIso_recovery, ← Category.assoc, smoothEquationGroupIso_trans,
    commonCoefficientGroupIso_recovery]

/-- Forgetting the group laws retains the same coherent geometric comparison. -/
@[reassoc] theorem commonCoefficientSmoothIso_trans :
    (commonCoefficientSmoothIso a b h).hom ≫ (commonCoefficientSmoothIso b d k).hom =
      (commonCoefficientSmoothIso a d (h.trans k)).hom := by
  exact congrArg (fun f => (CommGrp.forget (Over (Spec (.of C)))).map f)
    (commonCoefficientGroupIso_trans a b d h k)

end FLT.Mazur.OneGonSmoothing
