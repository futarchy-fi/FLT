/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticCoefficientModificationSections
public import FLT.Mazur.WeierstrassCoefficientShearSmoothOrbitDescent
public import FLT.Mazur.WeierstrassDividedPositiveSplitSmoothSpecialization

/-!
# The original arithmetic sections lie in the complete smooth identity chart

The intrinsic coefficient smooth point is constructed from the original
integral section by the proved cartesian square. Its image is exactly the
arithmetic point in the complete model, including in the strict split fiber.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (S : Type u) [CommRing S] [Algebra A S]
local notation "qS" => Spec.map (CommRingCat.ofHom (algebraMap A S))
local notation "H" => originalSmoothCoefficientMap_isPullback S W

/-- The actual coefficient restriction of the original smooth integral section. -/
def e0SmoothCoefficientSection (P : ellipticE0 A W) :
    Spec (.of S) ⟶ (integralSmoothOpen (W.map (algebraMap A S))).toScheme :=
  (H).lift (qS ≫ (e0SmoothSectionEquiv A W P).left) (𝟙 _)
    (by
      have h : (e0SmoothSectionEquiv A W P).left ≫ integralSmoothStructure W =
          𝟙 (Spec (.of A)) := (e0SmoothSectionEquiv A W P).w
      rw [Category.assoc, h, Category.comp_id, Category.id_comp])

/-- The intrinsic coefficient point projects to the original integral section. -/
@[reassoc] theorem e0SmoothCoefficientSection_projection (P : ellipticE0 A W) :
    e0SmoothCoefficientSection A W S P ≫ originalSmoothCoefficientMap S W =
      qS ≫ (e0SmoothSectionEquiv A W P).left :=
  (H).lift_fst _ _ _

/-- This point is a section over the actual coefficient spectrum. -/
@[reassoc] theorem e0SmoothCoefficientSection_structure (P : ellipticE0 A W) :
    e0SmoothCoefficientSection A W S P ≫
      integralSmoothStructure (W.map (algebraMap A S)) = 𝟙 _ :=
  (H).lift_snd _ _ _

variable {W} {π : A} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (r : S) (j : ℕ) (hj : j ≤ n)

/-- The complete original smooth orbit contains the actual arithmetic coefficient section. -/
@[reassoc] theorem e0SmoothCoefficientSection_embedding (P : ellipticE0 A W) :
    e0SmoothCoefficientSection A W S P ≫ coefficientShearSmoothEmbedding hπ data S r j hj =
      e0CoefficientSection A hπ data S r j hj P := by
  apply (coefficientShearGlued_isPullback hπ data S r j hj).hom_ext
  · rw [Category.assoc, coefficientShearSmoothEmbedding_structure,
      e0SmoothCoefficientSection_structure, e0CoefficientSection_structure]
  · rw [Category.assoc, coefficientShearSmoothEmbedding_projection,
      e0SmoothCoefficientSection_projection_assoc, e0CoefficientSection_projection]
    rfl

omit S [CommRing S] [Algebra A S] r j hj in
/-- The strict split identity chart is the specialization of the original arithmetic section. -/
@[reassoc] theorem e0SmoothCoefficientSection_positiveSplit {depth : ℕ}
    (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
    (hk : 2 * (start + s + 1) ≤ depth) (P : ellipticE0 A W) :
    e0SmoothCoefficientSection A W (ResidueField A) P ≫
        positiveSplitOriginalSmoothMap hπ data D s hs hk =
      e0FiniteClosedPoint A hπ data (s + 1) hs P := by
  apply (IsPullback.of_hasPullback
    (Spec.map (CommRingCat.ofHom (algebraMap A (ResidueField A))))
    (finiteGlobalStructure hπ data (s + 1) hs)).hom_ext
  · rw [Category.assoc, positiveSplitOriginalSmoothMap_structure,
      e0SmoothCoefficientSection_structure]
    exact (e0FiniteClosedPoint_structure A hπ data (s + 1) hs P).symm
  · rw [Category.assoc, positiveSplitOriginalSmoothMap_specialization,
      e0SmoothCoefficientSection_projection_assoc]
    exact (Category.assoc _ _ _).trans
      (e0FiniteClosedPoint_projection A hπ data (s + 1) hs P).symm

end FLT.Mazur.WeierstrassDividedDepth
