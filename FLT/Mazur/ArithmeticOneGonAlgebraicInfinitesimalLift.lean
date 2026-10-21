/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArithmeticOneGonAlgebraicFamily
public import FLT.Mazur.ArithmeticOneGonParameterLifting
public import FLT.Mazur.GeneralizedCurveBaseChangeCompEq

/-!
# Full arithmetic families across nilpotent thickenings

The lifted parameter gives an actual generalized curve over the thickening.
Its reduction recovers the original family as a full generalized curve, with
its smooth group and whole-curve action. This is lifting inside this explicit
family, not a versality theorem for deformations of all generalized curves.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.ArithmeticOneGonParameter
open GeneralizedEllipticCurve ArithmeticOneGonGeneralizedCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (I : Ideal R) (hI : IsNilpotent I)
  (f : ParameterRing →+* R ⧸ I)

include hI in
/-- An original parameter test lifts to a full arithmetic family with its exact reduction. -/
theorem exists_nilpotent_curve_lift :
    ∃ (t : R) (ht : IsUnit (1 + 432 * t)),
      Nonempty ((curve t ht).baseChange (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ≅
        universalCurve.baseChange (Spec.map (CommRingCat.ofHom f))) := by
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (f parameter)
  let hu := lifted_factor_isUnit I hI f t ht
  have hf : (Ideal.Quotient.mk I).comp (specialize t hu) = f := by
    apply hom_ext
    change Ideal.Quotient.mk I (specialize t hu parameter) = f parameter
    rw [specialize_parameter, ht]
  have hw : Spec.map (CommRingCat.ofHom f) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ parameterMap t hu := by
    rw [parameterMap, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext hf.symm)
  refine ⟨t, hu, ⟨?_⟩⟩
  exact (baseChangeFunctor (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).mapIso
    (specializationIso t hu) ≪≫
      (universalCurve.baseChangeCompEqIso (parameterMap t hu)
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
        (Spec.map (CommRingCat.ofHom f)) hw).symm

end FLT.Mazur.ArithmeticOneGonParameter
