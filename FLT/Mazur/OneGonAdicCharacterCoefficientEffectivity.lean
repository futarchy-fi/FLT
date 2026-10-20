/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicCharacterCoefficientTower
public import FLT.Mazur.OneGonAdicCharacterEffectivityUnique

/-!
# Effective smooth character homomorphisms commute with coefficient change

Every finite reduction of the changed complete homomorphism is the independently
constructed new tower. Effective uniqueness therefore gives the comparison over
arbitrary complete coefficient pairs, without flatness or injectivity assumptions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OneGonAdicCharacterTower
open OneGonSmoothing WeierstrassIntegralChart CharacterSchemeBaseChange
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S G : Type} [CommRing R] [CommRing S] [AddCommGroup G] [Finite G]
  (I : Ideal R) (J : Ideal S) [IsAdicComplete I R] [IsAdicComplete J S]
  (f : R →+* S) (hf : I ≤ J.comap f) (t : R) (ht : t ∈ I)
  (g : stageSource I G 0 ⟶ stageGroup I t 0)

/-- The actual coefficient change of the effective original group homomorphism. -/
def effectiveCoefficientHom : CommGrp.mk (model S G) ⟶ integralSmoothGroup (equation (f t)) :=
  characterCoefficientHom _ _ f (equation_map t f).symm (effectiveCharacterHom I t ht g)

attribute [local irreducible] tower coefficientTower

omit [IsAdicComplete J S] in
/-- Every finite reduction of the changed effective map is the new original tower. -/
theorem effectiveCoefficientHom_reduction (m : ℕ) :
    Spec.map (CommRingCat.ofHom (FiniteCharacterAdicElements.reduction (G := G) J m)) ≫
      (effectiveCoefficientHom I f t ht g).hom.hom.hom.left =
        (tower J (f t) (hf ht) (coefficientTower I J f hf t ht g 0) m).hom.hom.hom.left ≫
          smoothProjection J (f t) m := by
  apply smoothCoefficientMapTo_ext (equation t) _ f (equation_map t f).symm
  · rw [Category.assoc]
    change _ ≫ (characterCoefficientHom _ _ f _ _).hom.hom.hom.left ≫ _ = _
    rw [characterCoefficientHom_projection,
      stageCharacterCoefficient_spec_reduction_assoc I J f hf m,
      effectiveCharacterHom_reduction I t ht g m, Category.assoc,
      stageSmoothCoefficient_projection I J f hf t m,
      tower_coefficient_naturality_assoc I J f hf t ht g m]
  · let c := Spec.map (CommRingCat.ofHom
      (FiniteCharacterAdicElements.reduction (G := G) J m))
    let d := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J ^ (m + 1))))
    let a := (effectiveCoefficientHom I f t ht g).hom.hom.hom
    let b := (tower J (f t) (hf ht) (coefficientTower I J f hf t ht g 0) m).hom.hom.hom
    calc
      (c ≫ a.left) ≫ (integralSmoothGroup (equation (f t))).X.hom =
          c ≫ (model S G).hom :=
        (Category.assoc _ _ _).trans (congrArg (c ≫ ·) a.w)
      _ = (stageSource J G m).X.hom ≫ d :=
        characterCoefficient_structure (G := G) (Ideal.Quotient.mk (J ^ (m + 1)))
      _ = (b.left ≫ (stageGroup J (f t) m).X.hom) ≫ d :=
        congrArg (· ≫ d) b.w.symm
      _ = b.left ≫ (stageGroup J (f t) m).X.hom ≫ d := Category.assoc _ _ _
      _ = b.left ≫ smoothProjection J (f t) m ≫ integralSmoothStructure (equation (f t)) :=
        congrArg (b.left ≫ ·) (smoothProjection_structure J (f t) m).symm
      _ = (b.left ≫ smoothProjection J (f t) m) ≫ integralSmoothStructure (equation (f t)) :=
        (Category.assoc _ _ _).symm

/-- Coefficient change agrees with independent effectivity over the new complete pair. -/
theorem effectiveCoefficientHom_eq :
    effectiveCoefficientHom I f t ht g =
      effectiveCharacterHom J (f t) (hf ht) (coefficientTower I J f hf t ht g 0) :=
  effectiveCharacterHom_unique J (f t) (hf ht) _ _
    (effectiveCoefficientHom_reduction I J f hf t ht g)

/-- The actual original effective smooth maps satisfy the full coefficient square. -/
@[reassoc] theorem effectiveSmooth_coefficient_naturality :
    effectiveSmooth J (f t) (hf ht) (coefficientTower I J f hf t ht g 0) ≫
      smoothCoefficientMapTo (equation t) (equation (f t)) f (equation_map t f).symm =
        Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom G f)) ≫
          effectiveSmooth I t ht g := by
  have h := characterCoefficientHom_projection (equation t) (equation (f t)) f
    (equation_map t f).symm (effectiveCharacterHom I t ht g)
  change (effectiveCoefficientHom I f t ht g).hom.hom.hom.left ≫ _ = _ at h
  rw [effectiveCoefficientHom_eq I J f hf t ht g] at h
  exact h

end FLT.Mazur.OneGonAdicCharacterTower
