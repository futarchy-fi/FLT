/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityFieldSmooth
public import FLT.Mazur.WeierstrassProjectiveSmoothResidues

/-!
# The original infinity law on all smooth inputs

The regular infinity neighborhood restricts to a morphism between the actual
smooth input open and the relative smooth curve in every reduction type.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The original left input of the original infinity addition chart. -/
def infinityInputLeft : Coordinate W 1 →ₐ[R] InfinityAdditionOpen W :=
  (infinityAdditionRestriction W).comp (chartProductLeft W 1 1)

/-- The original right input of the original infinity addition chart. -/
def infinityInputRight : Coordinate W 1 →ₐ[R] InfinityAdditionOpen W :=
  (infinityAdditionRestriction W).comp (chartProductRight W 1 1)

/-- The actual smooth-input open in the original infinity output domain. -/
def infinitySmoothInputOpen : (Spec (.of (InfinityAdditionOpen W))).Opens :=
  (Spec.map (CommRingCat.ofHom (infinityInputLeft W).toRingHom) ≫
      integralCurveChart W 1) ⁻¹ᵁ integralSmoothOpen W ⊓
    (Spec.map (CommRingCat.ofHom (infinityInputRight W).toRingHom) ≫
      integralCurveChart W 1) ⁻¹ᵁ integralSmoothOpen W

/-- The original infinity chart sends all actual smooth inputs into the relative smooth locus. -/
theorem infinitySmoothInputOpen_output (p : Spec (.of (InfinityAdditionOpen W)))
    (hp : p ∈ infinitySmoothInputOpen W) :
    (Spec.map (CommRingCat.ofHom (infinityAdditionChart W).toRingHom) ≫
      integralCurveChart W 1) p ∈ integralSmoothOpen W := by
  apply chartAlgebra_smooth_at_of_residue W 1 (infinityAdditionChart W) p
  exact infinityFieldPoint_nonsingular W
    (IsScalarTower.toAlgHom R (InfinityAdditionOpen W) p.asIdeal.ResidueField)
    (chartAlgebra_residue_nonsingular_at W 1 (infinityInputLeft W) p hp.1)
    (chartAlgebra_residue_nonsingular_at W 1 (infinityInputRight W) p hp.2)

/-- The original infinity addition morphism restricted to its full smooth-input open. -/
def infinitySmoothChart :
    (infinitySmoothInputOpen W).toScheme ⟶ (integralSmoothOpen W).toScheme :=
  IsOpenImmersion.lift (integralSmoothOpen W).ι
    ((infinitySmoothInputOpen W).ι ≫
      Spec.map (CommRingCat.ofHom (infinityAdditionChart W).toRingHom) ≫
        integralCurveChart W 1) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨p, rfl⟩
      exact infinitySmoothInputOpen_output W p.val p.property)

/-- Restricting the infinity output retains the entire original scheme morphism. -/
@[reassoc] theorem infinitySmoothChart_inclusion :
    infinitySmoothChart W ≫ (integralSmoothOpen W).ι =
      (infinitySmoothInputOpen W).ι ≫
        Spec.map (CommRingCat.ofHom (infinityAdditionChart W).toRingHom) ≫
          integralCurveChart W 1 :=
  IsOpenImmersion.lift_fac _ _ _

/-- The restricted infinity addition is over the original coefficient spectrum. -/
theorem infinitySmoothChart_structure :
    infinitySmoothChart W ≫ integralSmoothStructure W =
      (infinitySmoothInputOpen W).ι ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (InfinityAdditionOpen W))) := by
  rw [integralSmoothStructure, infinitySmoothChart_inclusion_assoc,
    integralCurveChart_structure]
  rw [chartStructure, specAlgHom_structure (infinityAdditionChart W)]

end FLT.Mazur.WeierstrassIntegralChart
