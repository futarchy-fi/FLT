/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NeronPolygonScaling
public import FLT.Mazur.PolygonAtlasSmoothLocus
public import FLT.Mazur.PolygonScaledReciprocal

/-!
# Independent component coordinates on a complete pinched polygon

An arbitrary unit on each projective component fixes both endpoint sections.
The original pinching pushout therefore descends these scalings to an isomorphism
of the entire polygon, fixing every node and preserving the coefficient map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.PolygonPinching

variable (K : Type u) [Field K] {n : ℕ}

/-- Projective scaling restricts to the same full Laurent scaling on the torus. -/
@[reassoc] theorem torusToComponent_coordinateScaling (a : Kˣ) :
    (torusToComponent K).left ≫ ProjectiveLine.scaling K a =
      Spec.map (CommRingCat.ofHom (PolygonScaledReciprocal.scaling a).toRingHom) ≫
        (torusToComponent K).left := by
  change (ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K) ≫ _ =
    ProjectiveLine.overlapScaling K a ≫ ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K
  rw [Category.assoc, ProjectiveLine.left_scaling, ← Category.assoc,
    ProjectiveLine.overlapLeft_chartScaling, Category.assoc]

/-- Apply the specified unit on each full normalization component. -/
def componentsCoordinateScaling (a : Fin n → Kˣ) : components K n ⟶ components K n :=
  Sigma.desc fun i ↦ ProjectiveLine.scalingOver K (a i) ≫ componentι K n i

@[reassoc (attr := simp)]
theorem componentι_coordinateScaling (a : Fin n → Kˣ) (i : Fin n) :
    componentι K n i ≫ componentsCoordinateScaling K a =
      ProjectiveLine.scalingOver K (a i) ≫ componentι K n i := by
  simp [componentι, componentsCoordinateScaling]

/-- Every endpoint is fixed, so the normalization leg of the span is fixed. -/
@[reassoc (attr := simp)]
theorem toComponents_coordinateScaling (hn : 0 < n) (a : Fin n → Kˣ) :
    toComponents K n hn ≫ componentsCoordinateScaling K a = toComponents K n hn := by
  apply Sigma.hom_ext
  rintro ⟨i, b⟩
  change branchι K n i b ≫ _ = branchι K n i b ≫ _
  cases b <;> simp

@[simp]
theorem componentsCoordinateScaling_one : componentsCoordinateScaling K (n := n) 1 = 𝟙 _ := by
  apply Sigma.hom_ext
  intro i
  change componentι K n i ≫ _ = componentι K n i ≫ _
  simp

theorem componentsCoordinateScaling_mul (a b : Fin n → Kˣ) :
    componentsCoordinateScaling K (n := n) (a * b) =
      componentsCoordinateScaling K a ≫ componentsCoordinateScaling K b := by
  apply Sigma.hom_ext
  intro i
  change componentι K n i ≫ _ = componentι K n i ≫ _
  simp [ProjectiveLine.scalingOver_mul, Category.assoc, Pi.mul_apply]

variable (hn : 0 < n) {C : Over (Spec (CommRingCat.of K))}
variable (p : components K n ⟶ C) (q : nodes K n ⟶ C)
variable (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

/-- Descend scaling on the normalization and the identity on the nodes. -/
def polygonCoordinateScaling (a : Fin n → Kˣ) : C ⟶ C :=
  h.desc (componentsCoordinateScaling K a ≫ p) q (by
    rw [← Category.assoc, toComponents_coordinateScaling, h.w])

@[reassoc (attr := simp)]
theorem components_polygonCoordinateScaling (a : Fin n → Kˣ) :
    p ≫ polygonCoordinateScaling K hn p q h a = componentsCoordinateScaling K a ≫ p := by
  simp [polygonCoordinateScaling]

@[reassoc (attr := simp)]
theorem nodes_polygonCoordinateScaling (a : Fin n → Kˣ) :
    q ≫ polygonCoordinateScaling K hn p q h a = q := by
  simp [polygonCoordinateScaling]

@[reassoc]
theorem componentι_polygonCoordinateScaling (a : Fin n → Kˣ) (i : Fin n) :
    componentι K n i ≫ p ≫ polygonCoordinateScaling K hn p q h a =
      ProjectiveLine.scalingOver K (a i) ≫ componentι K n i ≫ p := by simp

@[reassoc]
theorem nodeι_polygonCoordinateScaling (a : Fin n → Kˣ) (i : Fin n) :
    nodeι K n i ≫ q ≫ polygonCoordinateScaling K hn p q h a = nodeι K n i ≫ q := by simp

@[simp]
theorem polygonCoordinateScaling_one : polygonCoordinateScaling K hn p q h 1 = 𝟙 C := by
  apply h.hom_ext <;> simp

theorem polygonCoordinateScaling_mul (a b : Fin n → Kˣ) :
    polygonCoordinateScaling K hn p q h (a * b) =
      polygonCoordinateScaling K hn p q h a ≫ polygonCoordinateScaling K hn p q h b := by
  apply h.hom_ext <;> simp [componentsCoordinateScaling_mul, Category.assoc]

/-- Independent component scaling is inverted by the pointwise inverse units. -/
def polygonCoordinateScalingIso (a : Fin n → Kˣ) : C ≅ C where
  hom := polygonCoordinateScaling K hn p q h a
  inv := polygonCoordinateScaling K hn p q h a⁻¹
  hom_inv_id := by rw [← polygonCoordinateScaling_mul, mul_inv_cancel, polygonCoordinateScaling_one]
  inv_hom_id := by rw [← polygonCoordinateScaling_mul, inv_mul_cancel, polygonCoordinateScaling_one]

@[simp]
theorem polygonCoordinateScalingIso_hom (a : Fin n → Kˣ) :
    (polygonCoordinateScalingIso K hn p q h a).hom = polygonCoordinateScaling K hn p q h a := rfl

@[simp]
theorem polygonCoordinateScalingIso_inv (a : Fin n → Kˣ) :
    (polygonCoordinateScalingIso K hn p q h a).inv = polygonCoordinateScaling K hn p q h a⁻¹ := rfl

end FLT.Mazur.PolygonPinching
