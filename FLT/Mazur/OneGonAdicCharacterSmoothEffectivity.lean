/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicSmoothProjection
public import FLT.Mazur.FiniteCharacterAdicJacobson
public import FLT.Mazur.JacobsonReductionOpenDetection
public import FLT.Mazur.DiagonalizableCoefficientReduction

/-!
# The effective original character map factors through the smooth group

The initial character reduction has Jacobson kernel, so its smooth image
forces the whole effective map into the original smooth open. The resulting
relative morphism retains every constructed finite-stage map.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.OneGonAdicCharacterTower

open OneGonSmoothing WeierstrassIntegralChart CharacterSchemeBaseChange

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R G : Type} [CommRing R] [AddCommGroup G] [Finite G]
  (I : Ideal R) [IsAdicComplete I R] (t : R) (ht : t ∈ I)
  (g : stageSource I G 0 ⟶ stageGroup I t 0)

/-- The entire effective original character map lands in the full original smooth open. -/
theorem effectiveAffine_range_smooth :
    Set.range (effectiveAffine I t ht g ≫ integralCurveChart (equation t) 1) ⊆
      integralSmoothOpen (equation t) := by
  apply JacobsonReductionOpenDetection.range_subset
    (FiniteCharacterAdicElements.reduction (G := G) I 0)
    (DiagonalizableCobar.coefficientReduction_surjective R G (I ^ (0 + 1)))
    (FiniteCharacterAdicElements.reduction_zero_ker_le_jacobson I)
  rw [← Category.assoc, effectiveAffine_reduction]
  exact towerAffine_range_smooth I t ht g 0

/-- The actual effective map into the original smooth group, before proving its group laws. -/
def effectiveSmooth : Spec (.of (AddMonoidAlgebra R G)) ⟶
    (integralSmoothOpen (equation t)).toScheme :=
  IsOpenImmersion.lift (integralSmoothOpen (equation t)).ι
    (effectiveAffine I t ht g ≫ integralCurveChart (equation t) 1)
    (by rw [Scheme.Opens.range_ι]; exact effectiveAffine_range_smooth I t ht g)

/-- Smooth factorization retains the full original map into the original cubic. -/
@[reassoc] theorem effectiveSmooth_inclusion :
    effectiveSmooth I t ht g ≫ (integralSmoothOpen (equation t)).ι =
      effectiveAffine I t ht g ≫ integralCurveChart (equation t) 1 :=
  IsOpenImmersion.lift_fac _ _ _

/-- The smooth factor is a morphism over the original complete coefficient base. -/
@[reassoc] theorem effectiveSmooth_structure :
    effectiveSmooth I t ht g ≫ integralSmoothStructure (equation t) =
      (model R G).hom := by
  rw [integralSmoothStructure, effectiveSmooth_inclusion_assoc,
    integralCurveChart_structure, effectiveAffine_structure]

/-- The effective original smooth map, bundled over its original base. -/
def effectiveSmoothOver : model R G ⟶ (integralSmoothGroup (equation t)).X :=
  Over.homMk (effectiveSmooth I t ht g) (effectiveSmooth_structure I t ht g)

/-- Every finite reduction recovers the constructed original smooth-group map exactly. -/
@[reassoc] theorem effectiveSmooth_reduction (m : ℕ) :
    Spec.map (CommRingCat.ofHom (FiniteCharacterAdicElements.reduction (G := G) I m)) ≫
      effectiveSmooth I t ht g =
        (tower I t ht g m).hom.hom.hom.left ≫ smoothProjection I t m := by
  apply (cancel_mono (integralSmoothOpen (equation t)).ι).mp
  rw [Category.assoc, effectiveSmooth_inclusion, ← Category.assoc,
    effectiveAffine_reduction, towerAffine_inclusion, Category.assoc]

end FLT.Mazur.OneGonAdicCharacterTower
