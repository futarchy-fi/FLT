/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicCompleteLocalPoints
public import FLT.Mazur.WeierstrassSmoothAdicRoots

/-!
# Reconstructing actual complete-base smooth Weierstrass sections

A compatible tower of relative points supplies a section of the original
smooth group. Its structure map and every finite reduction are recovered.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonObj
namespace FLT.Mazur.WeierstrassSmoothCompleteSections

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open WeierstrassIntegralChart WeierstrassSmoothAdicReduction
variable {R : Type} [CommRing R] [IsLocalRing R]
  (W : WeierstrassCurve R) (I : Ideal R) (hI : I ≠ ⊤) [IsAdicComplete I R]

/-- Sections over the original complete coefficient ring. -/
abbrev Sections := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R R))) ⟶
  (integralSmoothGroup W).X

include hI in
/-- Actual positive-order restrictions detect complete smooth-group sections. -/
theorem section_ext {x y : Sections W}
    (h : ∀ m, sectionReduction W I m x = sectionReduction W I m y) : x = y := by
  apply Over.OverMorphism.ext
  apply AdicCompleteLocalPoints.hom_ext I hI
  intro m
  exact congrArg (fun z ↦ z.left) (h m)

variable (s : ∀ m, Points W I m) (hs : ∀ m, reduction W I m (s (m + 1)) = s m)

include hI hs in
/-- The entire compatible tower reconstructs a section, including its original base map. -/
theorem exists_section : ∃ x : Sections W, ∀ m, sectionReduction W I m x = s m := by
  have hc (m : ℕ) : Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.le_succ (m + 1))))) ≫ (s (m + 1)).left =
      (s m).left := congrArg (fun z ↦ z.left) (hs m)
  let x := AdicCompleteLocalPoints.lift I hI (fun m ↦ (s m).left) hc
  have hx (m : ℕ) : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (m + 1)))) ≫
      x = (s m).left := AdicCompleteLocalPoints.quotient_lift I hI _ hc m
  have hw : x ≫ (integralSmoothGroup W).X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap R R)) := by
    apply AdicCompleteAffinePoints.hom_ext I
    intro m
    rw [← Category.assoc, hx, (s m).w]
    rw [← Spec.map_comp]
    rfl
  exact ⟨Over.homMk x hw, fun m ↦ Over.OverMorphism.ext (hx m)⟩

/-- The reconstructed relative section over the original complete base. -/
def reconstruct : Sections W := (exists_section W I hI s hs).choose

/-- The reconstructed relative section retains every original positive-order point. -/
theorem reduction_reconstruct (m : ℕ) :
    sectionReduction W I m (reconstruct W I hI s hs) = s m :=
  (exists_section W I hI s hs).choose_spec m

/-- The reconstruction is unique as a full relative scheme morphism. -/
theorem reconstruct_unique (x : Sections W) (hx : ∀ m, sectionReduction W I m x = s m) :
    x = reconstruct W I hI s hs := by
  apply section_ext W I hI
  intro m
  rw [hx, reduction_reconstruct]

end FLT.Mazur.WeierstrassSmoothCompleteSections
