/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicCharacterCoefficientSquares
public import FLT.Mazur.OneGonAdicSmoothCoefficientSquares
public import FLT.Mazur.WeierstrassCharacterCoefficientHom
public import FLT.Mazur.OneGonAdicCharacterTower

/-!
# Naturality of the actual finite character tower

The coefficient-changed original homomorphisms form a compatible tower.
Uniqueness of the square-zero lift identifies every stage with the tower
constructed independently over the new coefficient pair.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OneGonAdicCharacterTower
open OneGonSmoothing WeierstrassIntegralChart AdicFormallySmoothStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S G : Type} [CommRing R] [CommRing S] [AddCommGroup G]
  (I : Ideal R) (J : Ideal S) (f : R →+* S) (hf : I ≤ J.comap f)
  (t : R) (ht : t ∈ I) (g : stageSource I G 0 ⟶ stageGroup I t 0)

/-- Change the coefficients of each actual original homomorphism. -/
def coefficientTower (m : ℕ) : stageSource J G m ⟶ stageGroup J (f t) m :=
  characterCoefficientHom _ _ (stageCoefficient I J f hf m)
    (stageCoefficient_equation I J f hf t m) (tower I t ht g m)

/-- The changed tower retains the original map at every finite order. -/
@[reassoc] theorem coefficientTower_projection (m : ℕ) :
    (coefficientTower I J f hf t ht g m).hom.hom.hom.left ≫
      stageSmoothCoefficient I J f hf t m =
        Spec.map (CommRingCat.ofHom (stageCharacterCoefficient I J f hf m)) ≫
          (tower I t ht g m).hom.hom.hom.left :=
  characterCoefficientHom_projection _ _ _ _ _

attribute [local irreducible] tower coefficientTower

/-- The changed original homomorphisms satisfy the genuine adjacent reduction squares. -/
theorem coefficientTower_reduction (m : ℕ) :
    Spec.map (CommRingCat.ofHom (characterRestriction J G m)) ≫
      (coefficientTower I J f hf t ht g (m + 1)).hom.hom.hom.left =
        (coefficientTower I J f hf t ht g m).hom.hom.hom.left ≫
          smoothRestriction J (f t) m := by
  apply smoothCoefficientMapTo_ext _ _ (stageCoefficient I J f hf (m + 1))
    (stageCoefficient_equation I J f hf t (m + 1))
  · change (_ ≫ _) ≫ stageSmoothCoefficient I J f hf t (m + 1) =
      (_ ≫ _) ≫ stageSmoothCoefficient I J f hf t (m + 1)
    rw [Category.assoc, coefficientTower_projection I J f hf t ht g (m + 1),
      ← stageCharacterCoefficient_spec_restriction_assoc I J f hf m,
      tower_reduction I t ht g m, Category.assoc,
      stageSmoothCoefficient_restriction I J f hf t m,
      coefficientTower_projection_assoc I J f hf t ht g m]
  · let c := Spec.map (CommRingCat.ofHom (characterRestriction J G m))
    let d := Spec.map (CommRingCat.ofHom (restriction J m).toRingHom)
    let a := (coefficientTower I J f hf t ht g (m + 1)).hom.hom.hom
    let b := (coefficientTower I J f hf t ht g m).hom.hom.hom
    calc
      (c ≫ a.left) ≫ (stageGroup J (f t) (m + 1)).X.hom =
          c ≫ (stageSource J G (m + 1)).X.hom :=
        (Category.assoc _ _ _).trans (congrArg (c ≫ ·) a.w)
      _ = (stageSource J G m).X.hom ≫ d :=
        characterCoefficient_structure (G := G) (restriction J m).toRingHom
      _ = (b.left ≫ (stageGroup J (f t) m).X.hom) ≫ d :=
        congrArg (· ≫ d) b.w.symm
      _ = b.left ≫ (stageGroup J (f t) m).X.hom ≫ d := Category.assoc _ _ _
      _ = b.left ≫ smoothRestriction J (f t) m ≫ (stageGroup J (f t) (m + 1)).X.hom :=
        congrArg (b.left ≫ ·) (smoothRestriction_structure J (f t) m).symm
      _ = (b.left ≫ smoothRestriction J (f t) m) ≫
          (stageGroup J (f t) (m + 1)).X.hom := (Category.assoc _ _ _).symm

/-- Independent construction over the new pair agrees at every finite order. -/
theorem coefficientTower_eq :
    coefficientTower I J f hf t ht g =
      tower J (f t) (hf ht) (coefficientTower I J f hf t ht g 0) :=
  tower_unique J (f t) (hf ht) _ _ rfl (coefficientTower_reduction I J f hf t ht g)

/-- The naturality square retains both independently constructed finite homomorphisms. -/
@[reassoc] theorem tower_coefficient_naturality (m : ℕ) :
    (tower J (f t) (hf ht) (coefficientTower I J f hf t ht g 0) m).hom.hom.hom.left ≫
      stageSmoothCoefficient I J f hf t m =
        Spec.map (CommRingCat.ofHom (stageCharacterCoefficient I J f hf m)) ≫
          (tower I t ht g m).hom.hom.hom.left := by
  rw [← coefficientTower_eq]
  exact coefficientTower_projection I J f hf t ht g m

end FLT.Mazur.OneGonAdicCharacterTower
