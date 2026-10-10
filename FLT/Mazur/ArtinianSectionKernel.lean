/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ChowWitnessSectionsLocalization
public import FLT.Mazur.TensorKernelArtinian

/-!
# Artinian lifting for the actual section equalizer

For a sheaf on an open cover, form the augmented complex using its original
restriction maps. Flatness of the overlap term and residue-field exactness of
this complex imply surjectivity on actual global sections. The geometric
identification of the residue complexes is a separate input, not a relative
H0 isomorphism assumption.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.ArtinianSectionKernel
open Chow
variable {X : Scheme} {R : Type} [CommRing R]
  (M : X.Modules) (ρ : R →+* Γ(X, ⊤))
  {ι : Type} (U : ι → X.Opens)

/-- The augmented chart map uses the original restriction of each global section. -/
def chartMap (a : R →ₗ[R] baseSections M ρ ⊤) :
    R →ₗ[R] (∀ i, baseSections M ρ (U i)) :=
  (baseDifference M ρ U).ker.subtype.comp ((baseRestrictEqualizer M ρ U).comp a)

/-- Its coordinates retain the actual restriction maps. -/
lemma chartMap_apply (a : R →ₗ[R] baseSections M ρ ⊤) (r : R) (i : ι) :
    chartMap M ρ U a r i = baseRestriction M ρ le_top (a r) := rfl

/-- Original sheaf restrictions make the augmented chart complex a complex. -/
lemma difference_chartMap (a : R →ₗ[R] baseSections M ρ ⊤) :
    (baseDifference M ρ U).comp (chartMap M ρ U a) = 0 := by
  apply LinearMap.ext
  intro r
  exact (baseRestrictEqualizer M ρ U (a r)).property

variable [IsArtinianRing R]

/-- Residue-field chart exactness lifts to surjectivity of the original global map. -/
theorem surjective_of_residue_exact (hU : ⨆ i, U i = ⊤)
    [Module.Flat R (∀ ij : ι × ι, baseSections M ρ (U ij.1 ⊓ U ij.2))]
    (a : R →ₗ[R] baseSections M ρ ⊤)
    (hres : ∀ (I : Ideal R) [I.IsMaximal],
      Function.Exact ((chartMap M ρ U a).lTensor (R ⧸ I))
        ((baseDifference M ρ U).lTensor (R ⧸ I))) : Function.Surjective a := by
  have h := TensorKernelArtinian.exact_of_residue_fields
    (chartMap M ρ U a) (baseDifference M ρ U) (difference_chartMap M ρ U a) hres
  intro s
  obtain ⟨r, hr⟩ := (h (baseRestrictEqualizer M ρ U s).val).mp
    (baseRestrictEqualizer M ρ U s).property
  refine ⟨r, (baseRestrictEqualizer_bijective M ρ U hU).injective ?_⟩
  exact Subtype.ext hr

/-- A given evaluation retraction makes the lifted global comparison bijective. -/
theorem bijective_of_residue_exact (hU : ⨆ i, U i = ⊤)
    [Module.Flat R (∀ ij : ι × ι, baseSections M ρ (U ij.1 ⊓ U ij.2))]
    (a : R →ₗ[R] baseSections M ρ ⊤) (e : baseSections M ρ ⊤ →ₗ[R] R)
    (he : e.comp a = LinearMap.id)
    (hres : ∀ (I : Ideal R) [I.IsMaximal],
      Function.Exact ((chartMap M ρ U a).lTensor (R ⧸ I))
        ((baseDifference M ρ U).lTensor (R ⧸ I))) : Function.Bijective a := by
  refine ⟨?_, surjective_of_residue_exact M ρ U hU a hres⟩
  intro x y hxy
  have hx := LinearMap.congr_fun he x
  have hy := LinearMap.congr_fun he y
  exact hx.symm.trans ((congrArg e hxy).trans hy)

/-- The actual chart complex stays exact with every coefficient module. -/
theorem exact_arbitrary_coefficients
    [Module.Flat R (∀ ij : ι × ι, baseSections M ρ (U ij.1 ⊓ U ij.2))]
    (a : R →ₗ[R] baseSections M ρ ⊤)
    (hres : ∀ (I : Ideal R) [I.IsMaximal],
      Function.Exact ((chartMap M ρ U a).lTensor (R ⧸ I))
        ((baseDifference M ρ U).lTensor (R ⧸ I)))
    (B : Type) [AddCommGroup B] [Module R B] :
    Function.Exact ((chartMap M ρ U a).lTensor B)
      ((baseDifference M ρ U).lTensor B) :=
  TensorKernelArtinian.exact_arbitrary_coefficients
    (chartMap M ρ U a) (baseDifference M ρ U) (difference_chartMap M ρ U a) hres B

end FLT.Mazur.ArtinianSectionKernel
