/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicInitialCoefficientNaturality
public import FLT.Mazur.OneGonAdicCharacterCoefficientEffectivity
public import FLT.Mazur.OneGonAdicCanonicalSubgroup
public import FLT.Mazur.OneGonSmoothCoefficientProjection

/-!
# Canonical complete-base roots retain the full coefficient-change ideal

Naturality includes the original initial roots, the effective group map, and
the full whole-curve closed embedding. The resulting Cartesian square preserves
the entire subgroup ideal, including its nonreduced scheme structure.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.OneGonAdicCharacterTower
open OneGonSmoothing WeierstrassIntegralChart CharacterSchemeBaseChange
open CharacterAlgebraScalarExtension
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
  (I : Ideal R) (J : Ideal S) [IsAdicComplete I R] [IsAdicComplete J S]
  (hf : I ≤ J.comap (algebraMap R S)) (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n]

/-- Independent effectivity retains the actual initial roots under coefficient change. -/
theorem canonicalCharacterHom_coefficient :
    characterCoefficientHom _ _ (algebraMap R S) (equation_map t (algebraMap R S)).symm
      (effectiveCharacterHom I t ht (initialRootsHom n I t ht)) =
        effectiveCharacterHom J (algebraMap R S t) (hf ht)
          (initialRootsHom n J (algebraMap R S t) (hf ht)) := by
  have h := effectiveCoefficientHom_eq I J (algebraMap R S) hf t ht (initialRootsHom n I t ht)
  rw [coefficientTower_initialRoots] at h
  exact h

/-- The actual canonical smooth embeddings form the original coefficient square. -/
@[reassoc] theorem canonicalSmooth_coefficient :
    effectiveSmooth J (algebraMap R S t) (hf ht)
      (initialRootsHom n J (algebraMap R S t) (hf ht)) ≫ smoothCoefficientProjection t =
        Spec.map (CommRingCat.ofHom (coeff R S (ZMod n)).toRingHom) ≫
          effectiveSmooth I t ht (initialRootsHom n I t ht) := by
  have h := effectiveSmooth_coefficient_naturality I J (algebraMap R S) hf t ht
    (initialRootsHom n I t ht)
  rw [coefficientTower_initialRoots] at h
  exact h

/-- The full original canonical curve embeddings commute with coefficient change. -/
@[reassoc] theorem canonicalCurveMap_coefficient :
    (canonicalFiniteSubgroup J (algebraMap R S t) (hf ht) n).curveMap.left ≫
      coefficientMorphism t =
        Spec.map (CommRingCat.ofHom (coeff R S (ZMod n)).toRingHom) ≫
          (canonicalFiniteSubgroup I t ht n).curveMap.left := by
  change (effectiveFiniteSubgroup J _ _ n _).curveMap.left ≫ _ =
    _ ≫ (effectiveFiniteSubgroup I _ _ n _).curveMap.left
  rw [effectiveFiniteSubgroup_curveMap, effectiveFiniteSubgroup_curveMap,
    Category.assoc, ← smoothCoefficientProjection_inclusion,
    ← Category.assoc, canonicalSmooth_coefficient, Category.assoc]

/-- The full canonical embedding over the new complete pair is the original pullback. -/
theorem canonicalCurveMap_coefficient_isPullback :
    IsPullback (Spec.map (CommRingCat.ofHom (coeff R S (ZMod n)).toRingHom))
      (canonicalFiniteSubgroup J (algebraMap R S t) (hf ht) n).curveMap.left
      (canonicalFiniteSubgroup I t ht n).curveMap.left (coefficientMorphism t) := by
  have hc : IsPullback (Spec.map (CommRingCat.ofHom (coeff R S (ZMod n)).toRingHom))
      (model S (ZMod n)).hom (model R (ZMod n)).hom (baseMap R S) := by
    apply IsPullback.of_iso_pullback _
      (schemeIso R S (ZMod n) ≪≫ pullbackSymmetry _ _)
    · rw [Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_fst, schemeIso_snd]
    · rw [Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_snd, schemeIso_fst]
    · exact ⟨characterCoefficient_structure (G := ZMod n) (algebraMap R S)⟩
  have hR : (canonicalFiniteSubgroup I t ht n).curveMap.left ≫ (family t).hom =
      (model R (ZMod n)).hom := (canonicalFiniteSubgroup I t ht n).curveMap.w
  have hS : (canonicalFiniteSubgroup J (algebraMap R S t) (hf ht) n).curveMap.left ≫
      (family (algebraMap R S t)).hom = (model S (ZMod n)).hom :=
    (canonicalFiniteSubgroup J (algebraMap R S t) (hf ht) n).curveMap.w
  rw [← hR, ← hS] at hc
  exact hc.of_bot (canonicalCurveMap_coefficient I J hf t ht n).symm
    (coefficient_isPullback t)

/-- Arbitrary complete coefficient change retains the entire canonical subgroup ideal. -/
theorem canonicalFiniteSubgroup_coefficient_ideal :
    (canonicalFiniteSubgroup J (algebraMap R S t) (hf ht) n).ideal =
      (canonicalFiniteSubgroup I t ht n).ideal.comap (coefficientMorphism t) := by
  change (canonicalFiniteSubgroup J (algebraMap R S t) (hf ht) n).curveMap.left.ker = _
  let h := (canonicalCurveMap_coefficient_isPullback I J hf t ht n).flip
  rw [← h.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]
  exact Scheme.IdealSheafData.ker_fst_of_isClosedImmersion _ _

end FLT.Mazur.OneGonAdicCharacterTower
