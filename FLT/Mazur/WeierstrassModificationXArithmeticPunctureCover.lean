/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXArithmeticIncidencePullback
public import FLT.Mazur.BinaryOpenDescent

/-!
# The two standard punctures cover the full original arithmetic boundary

Both initial labels cover the exact original D(t), with their constructed
restriction maps. Equality on these punctures therefore detects every map
out of the complete tensor boundary.
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
  (hs : π ∣ s)
local notation "Q" => Quotient R π m
local notation "q" => algebraMap R Q
local notation "P" => arithmeticInitialPunctureInclusion π m W s ha hs
local notation "i" => PrincipalOpenTensor.inclusion Q (t W s b3 b4 b6)
local notation "F" b => ite (b = true)
  (arithmeticOppositeInitialTensorNodeChart π m W s b3 b4 b6 ha h2 h3 h4 h6)
  (arithmeticInitialTensorNodeChart π m W s b3 b4 b6 ha h2 h3 h4 h6)

local notation "u" b =>
  arithmeticInitialPunctureToTensorBoundary π m W s b3 b4 b6 ha h2 h3 h4 h6 b hs

/-- Each puncture restriction is an open of the actual complete tensor boundary. -/
instance arithmeticInitialPunctureToTensorBoundary_isOpenImmersion (label : Bool) :
    IsOpenImmersion (u label) := by
  have hf : IsOpenImmersion (F label) := by
    cases label
    · exact arithmeticInitialTensorNodeChart_isOpenImmersion π m W s b3 b4 b6 ha h2 h3 h4 h6
    · exact arithmeticOppositeInitialTensorNodeChart_isOpenImmersion
        π m W s b3 b4 b6 ha h2 h3 h4 h6
  exact MorphismProperty.of_isPullback
    (arithmeticInitialPunctureToTensorBoundary_isPullback
      π m W s b3 b4 b6 ha h2 h3 h4 h6 label hs).flip inferInstance

/-- Both full standard punctures jointly cover the entire original tensor incidence open. -/
theorem arithmeticInitialPunctures_tensor_cover
    (z : Spec (.of (Localization.Away ((1 : Q) ⊗ₜ[R] t W s b3 b4 b6)))) :
    z ∈ Set.range (u false) ∨ z ∈ Set.range (u true) := by
  obtain ⟨x, hx⟩ | ⟨x, hx⟩ :=
    arithmeticInitialTensorNodeCharts_cover π m W s b3 b4 b6 ha h2 h3 h4 h6 (i z)
  · have H := arithmeticInitialPunctureToTensorBoundary_isPullback
      π m W s b3 b4 b6 ha h2 h3 h4 h6 false hs
    obtain ⟨w, hw, _⟩ := Scheme.exists_preimage_of_isPullback H z x hx.symm
    exact Or.inl ⟨w, hw⟩
  · have H := arithmeticInitialPunctureToTensorBoundary_isPullback
      π m W s b3 b4 b6 ha h2 h3 h4 h6 true hs
    obtain ⟨w, hw, _⟩ := Scheme.exists_preimage_of_isPullback H z x hx.symm
    exact Or.inr ⟨w, hw⟩

/-- The constructed initial punctures form an actual binary open cover of the original overlap. -/
def arithmeticInitialPuncturesTensorCover :
    (Spec (.of (Localization.Away ((1 : Q) ⊗ₜ[R] t W s b3 b4 b6)))).OpenCover :=
  BinaryOpenDescent.cover (u false) (u true)
    (arithmeticInitialPunctures_tensor_cover π m W s b3 b4 b6 ha h2 h3 h4 h6 hs)

/-- Agreement on both initial standard punctures detects maps on the entire tensor boundary. -/
theorem arithmeticInitialPunctures_tensor_hom_ext {Y : Scheme}
    (f g : Spec (.of (Localization.Away ((1 : Q) ⊗ₜ[R] t W s b3 b4 b6))) ⟶ Y)
    (hfalse : (u false) ≫ f = (u false) ≫ g) (htrue : (u true) ≫ f = (u true) ≫ g) : f = g :=
  BinaryOpenDescent.hom_ext (u false) (u true)
    (arithmeticInitialPunctures_tensor_cover π m W s b3 b4 b6 ha h2 h3 h4 h6 hs)
    f g hfalse htrue

end FLT.Mazur.WeierstrassModificationX
