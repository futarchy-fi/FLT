/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXArithmeticIncidenceOpen

/-!
# Each initial standard puncture inside the original full tensor boundary

The restriction is constructed by the universal property of the original
principal open. Its square is cartesian on the entire standard puncture.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassModificationX
open PolygonArithmeticStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (π : R) (m : ℕ)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (ha : IsUnit W.a₁) (h2 : π ∣ W.a₂) (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6)
  (label : Bool) (hs : π ∣ s)
local notation "Q" => Quotient R π m
local notation "q" => algebraMap R Q
local notation "P" => arithmeticInitialPunctureInclusion π m W s ha hs
local notation "i" => PrincipalOpenTensor.inclusion Q (t W s b3 b4 b6)
local notation "F" => ite (label = true)
  (arithmeticOppositeInitialTensorNodeChart π m W s b3 b4 b6 ha h2 h3 h4 h6)
  (arithmeticInitialTensorNodeChart π m W s b3 b4 b6 ha h2 h3 h4 h6)

/-- The full standard initial puncture lies in the original tensor overlap. -/
theorem arithmeticInitialPuncture_tensor_range_subset : Set.range (P ≫ F) ⊆ Set.range i := by
  rintro _ ⟨z, rfl⟩
  have h := Set.ext_iff.mp (arithmeticInitialTensorNodes_puncture_preimage
    π m W s b3 b4 b6 ha h2 h3 h4 h6 label hs) (P z) |>.mpr ⟨z, rfl⟩
  cases label <;> exact h

/-- The exact restriction from each initial label into the original complete tensor boundary. -/
def arithmeticInitialPunctureToTensorBoundary :
    Spec (.of (Localization.Away (NodalFiber.p (q s)))) ⟶
      Spec (.of (Localization.Away ((1 : Q) ⊗ₜ[R] t W s b3 b4 b6))) :=
  IsOpenImmersion.lift i (P ≫ F)
    (arithmeticInitialPuncture_tensor_range_subset π m W s b3 b4 b6 ha h2 h3 h4 h6 label hs)

/-- The puncture restriction preserves every function of the full original initial chart. -/
@[reassoc] theorem arithmeticInitialPunctureToTensorBoundary_comp :
    arithmeticInitialPunctureToTensorBoundary π m W s b3 b4 b6 ha h2 h3 h4 h6 label hs ≫ i =
      P ≫ F :=
  IsOpenImmersion.lift_fac _ _ _

/-- The standard puncture is the full inverse image of the original tensor incidence open. -/
theorem arithmeticInitialPunctureToTensorBoundary_isPullback :
    IsPullback
      (arithmeticInitialPunctureToTensorBoundary π m W s b3 b4 b6 ha h2 h3 h4 h6 label hs)
      P i F := by
  let _ := arithmeticInitialPunctureInclusion_isOpenImmersion π m W s ha hs
  apply IsOpenImmersion.isPullback
  · exact (arithmeticInitialPunctureToTensorBoundary_comp
      π m W s b3 b4 b6 ha h2 h3 h4 h6 label hs).symm
  · apply TopologicalSpace.Opens.ext
    have h := arithmeticInitialTensorNodes_puncture_preimage
      π m W s b3 b4 b6 ha h2 h3 h4 h6 label hs
    cases label <;> exact h

end FLT.Mazur.WeierstrassModificationX
