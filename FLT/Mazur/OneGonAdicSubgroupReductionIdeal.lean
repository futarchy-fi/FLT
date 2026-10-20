/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicReductionCartesian
public import FLT.Mazur.OneGonAdicCanonicalSubgroup

/-!
# Full subgroup ideals at every finite adic reduction

Every constructed tower embedding is the Cartesian pullback of the original
complete-base subgroup embedding. Its full defining ideal is consequently
the actual ideal-sheaf pullback, including every infinitesimal multiplicity.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.OneGonAdicCharacterTower

open OneGonSmoothing WeierstrassIntegralChart CharacterSchemeBaseChange

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n]
  (g : stageSource I (ZMod n) 0 ⟶ stageGroup I t 0)
  [IsClosedImmersion g.hom.hom.hom.left]

omit [IsAdicComplete I R] [NeZero n] [IsClosedImmersion g.hom.hom.hom.left] in
/-- Each original finite-stage whole-curve embedding retains its quotient coefficient base. -/
@[reassoc] theorem stageCurveMap_structure (m : ℕ) :
    stageCurveMap I t ht g m ≫ (family (parameter I t m)).hom =
      (model (StageRing I m) (ZMod n)).hom := by
  change ((tower I t ht g m).hom.hom.hom.left ≫
    (integralSmoothOpen (equation (parameter I t m))).ι) ≫ _ = _
  rw [Category.assoc]
  exact (tower I t ht g m).hom.hom.hom.w

/-- The original tower embedding is the actual whole-curve pullback of the effective subgroup. -/
theorem stageCurveMap_isPullback (m : ℕ) :
    IsPullback (Spec.map (CommRingCat.ofHom
      (FiniteCharacterAdicElements.reduction (G := ZMod n) I m)))
      (stageCurveMap I t ht g m) (effectiveFiniteSubgroup I t ht n g).curveMap.left
      (coefficientMorphism (S := StageRing I m) t) := by
  have h : IsPullback (Spec.map (CommRingCat.ofHom
      (FiniteCharacterAdicElements.reduction (G := ZMod n) I m)))
      (stageCurveMap I t ht g m ≫ (family (parameter I t m)).hom)
      ((effectiveFiniteSubgroup I t ht n g).curveMap.left ≫ (family t).hom)
      (baseMap R (StageRing I m)) := by
    rw [stageCurveMap_structure]
    change IsPullback _ _
      ((effectiveFiniteSubgroup I t ht n g).curveMap.left ≫
        (ArithmeticOneGonGeneralizedCurve.curve t
          (complementaryFactor_isUnit I t ht)).curve.hom) _
    rw [Over.w]
    exact characterReduction_isPullback I m
  apply h.of_bot _ (coefficient_isPullback t)
  rw [effectiveFiniteSubgroup_curveMap]
  exact stageCurveMap_reduction I t ht g m

/-- The actual finite-stage embedding is closed in the whole finite-stage cubic. -/
theorem stageCurveMap_isClosedImmersion (m : ℕ) :
    IsClosedImmersion (stageCurveMap I t ht g m) :=
  MorphismProperty.of_isPullback (stageCurveMap_isPullback I t ht n g m) inferInstance

/-- The full tower ideal is the full original subgroup ideal pulled back to the finite cubic. -/
theorem stageCurveMap_ker (m : ℕ) :
    (stageCurveMap I t ht g m).ker =
      (effectiveFiniteSubgroup I t ht n g).ideal.comap
        (coefficientMorphism (S := StageRing I m) t) := by
  let h := (stageCurveMap_isPullback I t ht n g m).flip
  rw [← h.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]
  exact Scheme.IdealSheafData.ker_fst_of_isClosedImmersion _ _

/-- Every full finite reduction of the canonical subgroup retains its constructed tower ideal. -/
theorem canonicalFiniteSubgroup_reduction_ideal (m : ℕ) :
    (canonicalFiniteSubgroup I t ht n).ideal.comap
        (coefficientMorphism (S := StageRing I m) t) =
      (stageCurveMap I t ht (initialRootsHom n I t ht) m).ker :=
  (stageCurveMap_ker I t ht n (initialRootsHom n I t ht) m).symm

end FLT.Mazur.OneGonAdicCharacterTower
