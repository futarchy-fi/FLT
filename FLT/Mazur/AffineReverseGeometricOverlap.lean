/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineSectionsReconstruction
public import FLT.Mazur.AffineTensorSectionIso

/-!
# Reconstructing an actual sheaf overlap from tensor coordinates

The two tensor scalar laws give an isomorphism of overlap section modules.
Affine quasi-coherent reconstruction then gives an actual sheaf isomorphism,
with exact round-trips in both directions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineGeometricOverlap
open AffineOverlapTensor AffineOverlapPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable (M : (Spec (.of S)).Modules) [M.IsQuasicoherent]
attribute [local instance] AffineOverlapPullback.instModuleCarrierCarrierOfCoefficients
local instance : IsScalarTower R S (coefficients S M) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
local instance (i : S →+* S ⊗[R] S) :
    ((pullback (Spec.map (CommRingCat.ofHom i))).obj M).IsQuasicoherent :=
  AffineModulePullbackSections.isQuasicoherent_pullback (CommRingCat.ofHom i) M
variable (e : coefficients S M ⊗[R] S ≃ₗ[S] S ⊗[R] coefficients S M)
variable (he : ∀ (n : coefficients S M) (s t : S), e (n ⊗ₜ[R] (s * t)) =
  (Algebra.lsmul R R (coefficients S M) s).lTensor S (e (n ⊗ₜ[R] t)))

/-- Recover an actual geometric overlap from a tensor isomorphism with both scalar laws. -/
def fromTensor : Overlap R S M :=
  AffineSectionsReconstruction.liftIso (sectionsIso R S M e he)

/-- The reconstructed sheaf isomorphism has the specified linear section map. -/
theorem fromTensor_sectionsIso :
    moduleSpecΓFunctor.mapIso (fromTensor R S M e he) = sectionsIso R S M e he :=
  AffineSectionsReconstruction.mapIso_liftIso _

/-- Reconstructed overlap maps act on sections by the original tensor formula. -/
theorem fromTensor_sections (x : coefficients S M ⊗[R] S) :
    moduleSpecΓFunctor.map (fromTensor R S M e he).hom (firstSections R S M x) =
      secondSections R S M (e x) := by
  have h := congrArg Iso.hom (fromTensor_sectionsIso R S M e he)
  exact (congrArg (fun f ↦ f (firstSections R S M x)) h).trans
    (sectionsIso_first R S M e he x)

/-- The tensor isomorphism is recovered exactly after sheaf reconstruction. -/
theorem tensorEquiv_fromTensor : tensorEquiv R S M (fromTensor R S M e he) = e := by
  apply LinearEquiv.ext
  intro x
  apply (secondSections R S M).injective
  exact (tensorEquiv_sections R S M _ x).trans (fromTensor_sections R S M e he x)

/-- Tensor coordinates determine an actual quasi-coherent overlap isomorphism uniquely. -/
theorem tensorEquiv_injective : Function.Injective (tensorEquiv R S M) := by
  intro a b h
  apply Iso.ext
  apply AffineSectionsReconstruction.map_injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := (firstSections R S M).surjective x
  rw [← tensorEquiv_sections, ← tensorEquiv_sections, h]

/-- Reconstructing the tensor coordinates of an actual sheaf overlap returns that overlap. -/
theorem fromTensor_tensorEquiv (a : Overlap R S M) :
    fromTensor R S M (tensorEquiv R S M a) (tensorEquiv_other_smul R S M a) = a :=
  tensorEquiv_injective R S M (tensorEquiv_fromTensor R S M _ _)

end FLT.Mazur.AffineGeometricOverlap
