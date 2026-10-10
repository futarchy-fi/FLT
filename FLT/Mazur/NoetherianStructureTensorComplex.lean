/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NoetherianProperRelativeFunctions
public import FLT.Mazur.TensorKernelCyclic

/-!
# Universal tensor exactness over a Noetherian affine base

All quotient-ring base changes remain Noetherian. Their actual global-functions
comparison proves cyclic exactness of the original affine-cover complex.
Flatness of the overlap term extends this to every coefficient module.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
namespace FLT.Mazur.NoetherianStructureTensorComplex
open Chow PolygonStructureInclusion ArtinianSectionKernel ArtinianRelativeSectionCriterion
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X S : Scheme.{0}} (f : X ⟶ S) [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  [IsProper f] [Flat f] [GeometricallyConnected f] [GeometricallyReduced f]
  (s : S ⟶ X) (hs : s ≫ f = 𝟙 S)
  {ι : Type} [Finite ι] (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
  (hA : ∀ i, IsAffineOpen (U i))

include s hs hU hA in
/-- Every actual quotient-ring base change proves exactness with that cyclic coefficient. -/
theorem quotient_exact (I : Ideal Γ(S, ⊤)) :
    Function.Exact
      ((chartMap (structureModule X) f.appTop.hom U (scalarSections f)).lTensor (Γ(S, ⊤) ⧸ I))
      ((baseDifference (structureModule X) f.appTop.hom U).lTensor (Γ(S, ⊤) ⧸ I)) := by
  apply ProperFiberTensorComplex.exact_over_algebra f U hU hA
  let a := AffineBaseChangeCoefficients.baseMap S (Γ(S, ⊤) ⧸ I)
  exact (NoetherianProperRelativeFunctions.spec_appTop_bijective (pullback.snd f a)
    (SchemeProperGeometricFiberSections.baseChangedSection f s hs a)
    (SchemeProperGeometricFiberSections.baseChangedSection_projection f s hs a)).surjective

include s hs hU hA in
/-- The original affine-cover complex is exact with every coefficient module. -/
theorem cover_exact (B : Type) [AddCommGroup B] [Module Γ(S, ⊤) B] :
    Function.Exact
      ((chartMap (structureModule X) f.appTop.hom U (scalarSections f)).lTensor B)
      ((baseDifference (structureModule X) f.appTop.hom U).lTensor B) := by
  let _ : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  let _ := FlatStructureSectionComplex.overlapProduct_flat f U hA
  exact TensorKernelCyclic.exact_arbitrary_coefficients _ _
    (quotient_exact f s hs U hU hA)
    (difference_chartMap (structureModule X) f.appTop.hom U (scalarSections f)) B

end FLT.Mazur.NoetherianStructureTensorComplex
