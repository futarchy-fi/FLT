/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.DenseClosedRestriction
public import FLT.Mazur.WeierstrassGenericKernelClosure
public import FLT.Mazur.WeierstrassCoefficientNegation
public import FLT.Mazur.WeierstrassGlobalNegationInvolution

/-!
# Negation on the original generic kernel's integral closure

Generic stability under negation forces stability of the same schematic closure.
The resulting automorphism is defined on the whole closure, even at singular points.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
  (W : WeierstrassCurve R) {H : Scheme}
  (i : H ⟶ integralCurve (W.map (algebraMap R K))) [IsClosedImmersion i]
  (n : H ⟶ H) (hn : n ≫ i = i ≫ integralCurveNegation (W.map (algebraMap R K)))

include hn in
omit [IsClosedImmersion i] in
/-- The original generic inverse preserves the dense factorization in the integral cubic. -/
theorem genericKernelToClosure_negation_square :
    genericKernelToClosure W i ≫
      (genericKernelClosureInclusion W i ≫ integralCurveNegation W) =
        (n ≫ genericKernelToClosure W i) ≫ genericKernelClosureInclusion W i := by
  simp only [Category.assoc, genericKernelToClosure_inclusion,
    genericKernelToClosure_inclusion_assoc]
  rw [← integralCoefficientMorphism_negation, ← Category.assoc, ← hn, Category.assoc]

/-- Restrict the original cubic inverse to the actual schematic closure. -/
def genericClosureNegation : genericKernelClosure W i ⟶ genericKernelClosure W i :=
  DenseClosedRestriction.lift (genericKernelToClosure W i) (genericKernelClosureInclusion W i)
    (genericKernelClosureInclusion W i ≫ integralCurveNegation W)
    (n ≫ genericKernelToClosure W i) (genericKernelToClosure_negation_square W i n hn)

/-- The constructed inverse is precisely the original ambient negation. -/
@[reassoc] theorem genericClosureNegation_inclusion :
    genericClosureNegation W i n hn ≫ genericKernelClosureInclusion W i =
      genericKernelClosureInclusion W i ≫ integralCurveNegation W :=
  DenseClosedRestriction.lift_inclusion _ _ _ _ _

/-- The inverse retains the exact original generic operation. -/
@[reassoc] theorem genericKernelToClosure_negation :
    genericKernelToClosure W i ≫ genericClosureNegation W i n hn =
      n ≫ genericKernelToClosure W i := DenseClosedRestriction.dense_lift _ _ _ _ _

/-- Negation is over the original integral base. -/
@[reassoc] theorem genericClosureNegation_structure :
    genericClosureNegation W i n hn ≫ genericKernelClosureStructure W i =
      genericKernelClosureStructure W i := by
  rw [genericKernelClosureStructure, genericClosureNegation_inclusion_assoc,
    integralCurveNegation_structure]

/-- The restricted inverse is involutive on the entire closure. -/
@[reassoc] theorem genericClosureNegation_comp :
    genericClosureNegation W i n hn ≫ genericClosureNegation W i n hn = 𝟙 _ := by
  apply (cancel_mono (genericKernelClosureInclusion W i)).mp
  simp only [Category.assoc, genericClosureNegation_inclusion,
    genericClosureNegation_inclusion_assoc, integralCurveNegation_comp,
    Category.comp_id, Category.id_comp]

/-- The same closure carries an actual automorphism extending its generic inverse. -/
def genericClosureNegationIso : genericKernelClosure W i ≅ genericKernelClosure W i where
  hom := genericClosureNegation W i n hn
  inv := genericClosureNegation W i n hn
  hom_inv_id := genericClosureNegation_comp W i n hn
  inv_hom_id := genericClosureNegation_comp W i n hn

end FLT.Mazur.WeierstrassIntegralChart
