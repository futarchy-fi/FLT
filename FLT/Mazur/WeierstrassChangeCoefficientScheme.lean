/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassChangeCoefficientTensor
public import FLT.Mazur.WeierstrassChangeComparisonScheme
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Coefficient base change of the actual full comparison scheme

The constructed affine comparison scheme is the geometric pullback of the
original scheme under every coefficient homomorphism, without flatness.
The isomorphism retains its original coefficient-base projection.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry WeierstrassCurve
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassChangeParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
  (W V : WeierstrassCurve R)
local notation "W'" => W.map (algebraMap R A)
local notation "V'" => V.map (algebraMap R A)

/-- The equation comparison scheme commutes with arbitrary coefficient base change. -/
def comparisonCoefficientBaseChangeIso : comparisonScheme W' V' ≅
    pullback (Spec.algebraMap R A) (comparisonStructure W V) :=
  Scheme.Spec.mapIso (coefficientTensorEquiv (A := A) W V).toRingEquiv.toCommRingCatIso.op ≪≫
    (pullbackSpecIso R A (EquationRing W V)).symm

/-- The geometric base-change comparison retains exactly the new coefficient-base map. -/
@[reassoc] theorem comparisonCoefficientBaseChangeIso_structure :
    (comparisonCoefficientBaseChangeIso (A := A) W V).hom ≫ pullback.fst _ _ =
      comparisonStructure W' V' := by
  change (Scheme.Spec.mapIso
    (coefficientTensorEquiv (A := A) W V).toRingEquiv.toCommRingCatIso.op).hom ≫
      (pullbackSpecIso R A (EquationRing W V)).inv ≫ pullback.fst _ _ = _
  rw [pullbackSpecIso_inv_fst']
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (coefficientTensorForward (A := A) W V).comp_algebraMap

end FLT.Mazur.WeierstrassChangeParameter
