/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicFiniteSubgroup
public import FLT.Mazur.OneGonSmoothingCoefficientChange

/-!
# Cartesian original character sources at finite adic orders

The actual coefficient reduction is the character-scheme base change, with
its original projection retained. The finite tower map into the full cubic
commutes with the effective complete-base embedding on every function.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.OneGonAdicCharacterTower

open OneGonSmoothing WeierstrassIntegralChart CharacterSchemeBaseChange

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R G : Type} [CommRing R] [AddCommGroup G] (I : Ideal R) (t : R)

/-- The full character coefficient reduction is a Cartesian base-change projection. -/
theorem characterReduction_isPullback (m : ℕ) :
    IsPullback (Spec.map (CommRingCat.ofHom
      (FiniteCharacterAdicElements.reduction (G := G) I m)))
      (model (StageRing I m) G).hom (model R G).hom
      (baseMap R (StageRing I m)) := by
  apply IsPullback.of_iso_pullback _
    (schemeIso R (StageRing I m) G ≪≫ pullbackSymmetry _ _)
  · change (schemeIso R (StageRing I m) G).hom ≫ (pullbackSymmetry _ _).hom ≫ _ = _
    rw [pullbackSymmetry_hom_comp_fst, schemeIso_snd]
    rfl
  · change (schemeIso R (StageRing I m) G).hom ≫ (pullbackSymmetry _ _).hom ≫ _ = _
    rw [pullbackSymmetry_hom_comp_snd, schemeIso_fst]
  · constructor
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    simp [FiniteCharacterAdicElements.reduction]

variable (ht : t ∈ I) (g : stageSource I G 0 ⟶ stageGroup I t 0)

/-- Each tower subgroup map into its entire original finite-order cubic. -/
def stageCurveMap (m : ℕ) : (model (StageRing I m) G).left ⟶
    (family (parameter I t m)).left :=
  (tower I t ht g m).hom.hom.hom.left ≫ (integralSmoothOpen (equation (parameter I t m))).ι

/-- The smooth projection retains the whole original finite cubic coefficient morphism. -/
@[reassoc] theorem smoothProjection_curve (m : ℕ) :
    smoothProjection I t m ≫ (integralSmoothOpen (equation t)).ι =
      (integralSmoothOpen (equation (parameter I t m))).ι ≫
        coefficientMorphism (S := StageRing I m) t := by
  rw [smoothProjection, Category.assoc,
    WeierstrassDividedDepth.originalSmoothCoefficientMap_inclusion,
    equationTransport_smoothInclusion_assoc
      (equation_map t (algebraMap R (StageRing I m))).symm]
  rfl

variable [Finite G] [IsAdicComplete I R]

/-- Every full finite-stage curve embedding is the reduction of the effective original map. -/
theorem stageCurveMap_reduction (m : ℕ) :
    Spec.map (CommRingCat.ofHom (FiniteCharacterAdicElements.reduction (G := G) I m)) ≫
        (effectiveSmooth I t ht g ≫ (integralSmoothOpen (equation t)).ι) =
      stageCurveMap I t ht g m ≫ coefficientMorphism (S := StageRing I m) t := by
  rw [← Category.assoc, effectiveSmooth_reduction, Category.assoc, smoothProjection_curve]
  exact (Category.assoc _ _ _).symm

end FLT.Mazur.OneGonAdicCharacterTower
