/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicIndependentEmbedding
public import FLT.Mazur.OneGonSmoothCoefficientProjection
public import FLT.Mazur.CoefficientFactorizationDescent

/-!
# Recovering smooth factors for independent supports

The actual complete-base character scheme is identified with the recovery of
the fixed finite coefficient source. Its smooth factor maps to the original
finite coefficient smooth model, with the original whole-cubic composite.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.OneGonAdicIndependentModel

open OneGonAdicCharacterTower OneGonSmoothing WeierstrassIntegralChart
open CharacterSchemeBaseChange Approximation

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n] (s : Set R)

/-- The actual character coefficient projection to the selected algebraic source. -/
def sourceProjection : (model R (ZMod n)).left ⟶
    (carrier I t ht n s).left :=
  Spec.map (CommRingCat.ofHom (CharacterAlgebraScalarExtension.coeff
    (base I t ht n s) R (ZMod n)).toRingHom)

/-- The complete character scheme is the recovery of the fixed finite coefficient source. -/
def sourceRecovery : (model R (ZMod n)).left ≅
    (coefficientModelCone (base I t ht n s) (carrier I t ht n s).hom).pt :=
  (coefficientMap_isPullback (base I t ht n s) R (ZMod n)).isoPullback

/-- Recovery retains exactly the chosen character coefficient projection. -/
@[reassoc] theorem sourceRecovery_fst :
    (sourceRecovery I t ht n s).inv ≫ sourceProjection I t ht n s =
      pullback.fst (carrier I t ht n s).hom
        (Spec.map (CommRingCat.ofHom (base I t ht n s).val.toRingHom)) :=
  (coefficientMap_isPullback (base I t ht n s) R (ZMod n)).isoPullback_inv_fst

/-- The original canonical smooth factor, viewed on the recovered model source. -/
def recoveredSmoothFactor :
    (coefficientModelCone (base I t ht n s) (carrier I t ht n s).hom).pt ⟶
      (integralSmoothOpen (equation (parameter I t ht n s))).toScheme :=
  (sourceRecovery I t ht n s).inv ≫
    effectiveSmooth I t ht (initialRootsHom n I t ht) ≫
      smoothCoefficientProjection (S := R) (parameter I t ht n s)

/-- The recovered smooth factor has the exact initial algebraic embedding as composite. -/
@[reassoc] theorem recoveredSmoothFactor_inclusion :
    recoveredSmoothFactor I t ht n s ≫
      (integralSmoothOpen (equation (parameter I t ht n s))).ι =
        pullback.fst (carrier I t ht n s).hom
          (Spec.map (CommRingCat.ofHom (base I t ht n s).val.toRingHom)) ≫
            embedding I t ht n s := by
  rw [recoveredSmoothFactor, Category.assoc, Category.assoc,
    smoothCoefficientProjection_inclusion]
  have he := effectiveSmooth_inclusion_assoc I t ht (initialRootsHom n I t ht)
    (coefficientMorphism (S := R) (parameter I t ht n s))
  erw [he]
  have h := (embedding_isPullback I t ht n s).w
  rw [OneGonAdicCharacterTower.canonical_curveMap_coordinates] at h
  change sourceProjection I t ht n s ≫ embedding I t ht n s =
    (effectiveAffine I t ht (initialRootsHom n I t ht) ≫
      integralCurveChart (equation t) 1) ≫
        coefficientMorphism (S := R) (parameter I t ht n s) at h
  rw [Category.assoc] at h
  erw [← h]
  rw [← Category.assoc, sourceRecovery_fst]

/-- The recovered factor is over the initial finite coefficient spectrum. -/
@[reassoc] theorem recoveredSmoothFactor_structure :
    recoveredSmoothFactor I t ht n s ≫
      integralSmoothStructure (equation (parameter I t ht n s)) =
        pullback.fst (carrier I t ht n s).hom
          (Spec.map (CommRingCat.ofHom (base I t ht n s).val.toRingHom)) ≫
            (carrier I t ht n s).hom := by
  change _ ≫ (integralSmoothOpen _).ι ≫ _ = _
  rw [recoveredSmoothFactor_inclusion_assoc]
  exact congrArg (fun f => pullback.fst (carrier I t ht n s).hom
    (Spec.map (CommRingCat.ofHom (base I t ht n s).val.toRingHom)) ≫ f)
      (embedding_structure I t ht n s)

end FLT.Mazur.OneGonAdicIndependentModel
