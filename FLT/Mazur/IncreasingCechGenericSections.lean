/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IncreasingCechGenericKernel
public import FLT.Mazur.IncreasingCechZeroSections

/-!
# Generic tensor comparison for original global sections

The source consists of actual global sections, localized over the original
base. The target is the kernel of the tensorized actual bounded differential.
Transport of the target to functions on a geometric base change remains separate.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.IncreasingCechScalars
open AlgebraicGeometry FCurve Chow Chow.AffineBase
open scoped TensorProduct

variable {X : Scheme} {ι : Type} [LinearOrder ι]
  (M : X.Modules) (U : ι → X.Opens) {R : Type} [CommRing R]
  (ρ : R →+* Γ(X, ⊤)) (hCover : iSup U = ⊤) (S : Submonoid R)
  (B : Type) [AddCommGroup B] [Module (Localization S) B]

/-- Tensor the actual global-section restriction and then take the canonical kernel map. -/
def sectionsTensorKernel :
    B ⊗[Localization S] LocalizedModule S (baseSections M ρ ⊤) →ₗ[Localization S]
      ((localD M U ρ S 0).lTensor B).ker :=
  (LinearMap.tensorKer (Localization S) B (localD M U ρ S 0)).comp
    ((localizedSectionsZeroKernelEquiv M U ρ hCover S).toLinearMap.lTensor B)

/-- Pure tensors retain the original localized chart cycle in the ambient tensor term. -/
lemma sectionsTensorKernel_tmul (b : B)
    (s : LocalizedModule S (baseSections M ρ ⊤)) :
    (sectionsTensorKernel M U ρ hCover S B (b ⊗ₜ[Localization S] s)).val =
      b ⊗ₜ[Localization S] (localizedSectionsZeroKernelEquiv M U ρ hCover S s).val := by
  change (LinearMap.tensorKer (Localization S) B (localD M U ρ S 0)
    (((localizedSectionsZeroKernelEquiv M U ρ hCover S).toLinearMap.lTensor B)
      (b ⊗ₜ[Localization S] s))).val = _
  rw [LinearMap.lTensor_tmul]
  exact LinearMap.tensorKer_tmul _ _ _ b _

/-- Kernel bijectivity gives the comparison for actual global sections. -/
lemma sectionsTensorKernel_bijective
    (h : Function.Bijective (LinearMap.tensorKer (Localization S) B (localD M U ρ S 0))) :
    Function.Bijective (sectionsTensorKernel M U ρ hCover S B) :=
  h.comp (TensorProduct.congr (LinearEquiv.refl (Localization S) B)
    (localizedSectionsZeroKernelEquiv M U ρ hCover S)).bijective

variable {R : CommRingCat.{0}} [IsNoetherianRing R] [IsDomain R]
  (f : X ⟶ Spec R) [IsProper f] [Flat f] [X.IsSeparated] [Finite ι]
  (hU : ∀ i, IsAffineOpen (U i))

include hU in
/-- Actual global sections compute all coefficient kernels on one generic principal open. -/
theorem exists_generic_sectionsTensorKernel_bijective :
    ∃ r : R, r ≠ 0 ∧ ∀ (B : Type) [AddCommGroup B] [Module (Localization.Away r) B],
      Function.Bijective (sectionsTensorKernel (structureModule X) U
        (baseCohomologyScalars f) hCover (Submonoid.powers r) B) := by
  obtain ⟨r, hr, h⟩ := exists_generic_structure_tensorKer_bijective f U hU hCover
  exact ⟨r, hr, fun B _ _ ↦ sectionsTensorKernel_bijective (structureModule X) U
    (baseCohomologyScalars f) hCover (Submonoid.powers r) B (h 0 B)⟩

end FLT.Mazur.IncreasingCechScalars
