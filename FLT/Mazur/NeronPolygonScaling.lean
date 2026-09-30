/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveLineScaling
public import FLT.Mazur.NeronPolygonRotation

/-!
# Scalar automorphisms of a realized Néron polygon

Scale each normalization component, fix the nodes, and descend through the
specified cyclic pinching cocone. This constructs the scalar automorphisms
and proves that they commute with rotations, including for one component.
It does not construct the polygon or identify its relative smooth group.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.PolygonPinching

variable (K : Type u) [Field K] {n : ℕ}

/-- Apply the same scalar automorphism to every normalization component. -/
def componentsScaling (a : Kˣ) : components K n ⟶ components K n :=
  Sigma.desc fun i ↦ ProjectiveLine.scalingOver K a ≫ componentι K n i

@[reassoc (attr := simp)]
theorem componentι_scaling (a : Kˣ) (i : Fin n) :
    componentι K n i ≫ componentsScaling K a =
      ProjectiveLine.scalingOver K a ≫ componentι K n i := by
  simp [componentι, componentsScaling]

/-- Every endpoint is fixed, so the normalization leg of the span is fixed. -/
@[reassoc (attr := simp)]
theorem toComponents_scaling (hn : 0 < n) (a : Kˣ) :
    toComponents K n hn ≫ componentsScaling K a = toComponents K n hn := by
  apply Sigma.hom_ext
  rintro ⟨i, b⟩
  change branchι K n i b ≫ _ = branchι K n i b ≫ _
  cases b <;> simp

@[simp]
theorem componentsScaling_one : componentsScaling K (n := n) 1 = 𝟙 _ := by
  apply Sigma.hom_ext
  intro i
  change componentι K n i ≫ _ = componentι K n i ≫ _
  simp

theorem componentsScaling_mul (a b : Kˣ) :
    componentsScaling K (n := n) (a * b) = componentsScaling K a ≫ componentsScaling K b := by
  apply Sigma.hom_ext
  intro i
  change componentι K n i ≫ _ = componentι K n i ≫ _
  simp [ProjectiveLine.scalingOver_mul, Category.assoc]

/-- Uniform scaling commutes with permutation of the normalization components. -/
theorem componentsScaling_rotation [NeZero n] (a : Kˣ) (b : ZMod n) :
    componentsScaling K a ≫ componentsRotation K b =
      componentsRotation K b ≫ componentsScaling K a := by
  apply Sigma.hom_ext
  intro i
  change componentι K n i ≫ _ = componentι K n i ≫ _
  simp

variable (hn : 0 < n) {C : Over (Spec (CommRingCat.of K))}
variable (p : components K n ⟶ C) (q : nodes K n ⟶ C)
variable (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

/-- Descend scaling on the normalization and the identity on the nodes. -/
def polygonScaling (a : Kˣ) : C ⟶ C :=
  h.desc (componentsScaling K a ≫ p) q (by
    rw [← Category.assoc, toComponents_scaling, h.w])

@[reassoc (attr := simp)]
theorem components_polygonScaling (a : Kˣ) :
    p ≫ polygonScaling K hn p q h a = componentsScaling K a ≫ p := by
  simp [polygonScaling]

@[reassoc (attr := simp)]
theorem nodes_polygonScaling (a : Kˣ) : q ≫ polygonScaling K hn p q h a = q := by
  simp [polygonScaling]

@[reassoc]
theorem componentι_polygonScaling (a : Kˣ) (i : Fin n) :
    componentι K n i ≫ p ≫ polygonScaling K hn p q h a =
      ProjectiveLine.scalingOver K a ≫ componentι K n i ≫ p := by simp

@[reassoc]
theorem nodeι_polygonScaling (a : Kˣ) (i : Fin n) :
    nodeι K n i ≫ q ≫ polygonScaling K hn p q h a = nodeι K n i ≫ q := by simp

@[simp]
theorem polygonScaling_one : polygonScaling K hn p q h 1 = 𝟙 C := by
  apply h.hom_ext <;> simp

theorem polygonScaling_mul (a b : Kˣ) :
    polygonScaling K hn p q h (a * b) =
      polygonScaling K hn p q h a ≫ polygonScaling K hn p q h b := by
  apply h.hom_ext <;> simp [componentsScaling_mul, Category.assoc]

/-- Scaling is an automorphism with inverse given by the inverse scalar. -/
def polygonScalingIso (a : Kˣ) : C ≅ C where
  hom := polygonScaling K hn p q h a
  inv := polygonScaling K hn p q h a⁻¹
  hom_inv_id := by rw [← polygonScaling_mul, mul_inv_cancel, polygonScaling_one]
  inv_hom_id := by rw [← polygonScaling_mul, inv_mul_cancel, polygonScaling_one]

@[simp]
theorem polygonScalingIso_hom (a : Kˣ) :
    (polygonScalingIso K hn p q h a).hom = polygonScaling K hn p q h a := rfl

@[simp]
theorem polygonScalingIso_inv (a : Kˣ) :
    (polygonScalingIso K hn p q h a).inv = polygonScaling K hn p q h a⁻¹ := rfl

/-- The scalar and cyclic actions commute on the specified realization. -/
theorem polygonScaling_rotation [NeZero n] (a : Kˣ) (b : ZMod n) :
    polygonScaling K hn p q h a ≫ polygonRotation K hn p q h b =
      polygonRotation K hn p q h b ≫ polygonScaling K hn p q h a := by
  apply h.hom_ext
  · simp only [← Category.assoc, components_polygonScaling, components_polygonRotation]
    simp only [Category.assoc, components_polygonRotation, components_polygonScaling]
    rw [← Category.assoc, componentsScaling_rotation, Category.assoc]
  · simp

end FLT.Mazur.PolygonPinching
