/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineBaseChangeCoefficients
public import FLT.Mazur.CartesianStructureComplexExactness
public import FLT.Mazur.SchemeConnectedFiberSections

/-!
# Residue exactness from actual connected reduced proper fibers

The original coefficient algebra is identified with functions on its spectrum.
For a pointed proper family with geometrically connected reduced fibers, the
actual fiber theorem then proves exactness of the original cover complex over
every residue field, without a relative global-functions hypothesis.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
namespace FLT.Mazur.ProperFiberTensorComplex
open Chow FCurve ArtinianSectionKernel ArtinianRelativeSectionCriterion
open AffineBaseChangeCoefficients
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X S : Scheme} (f : X ⟶ S) [IsAffine S]
  {ι : Type} [Finite ι] (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
  (hA : ∀ i, IsAffineOpen (U i))

include hU hA in
/-- The tensor complex uses the original algebra action, not a transported replacement. -/
theorem exact_over_algebra (B : Type) [CommRing B] [Algebra Γ(S, ⊤) B]
    (hB : Function.Surjective (pullback.snd f (baseMap S B)).appTop) :
    Function.Exact
      ((chartMap (structureModule X) f.appTop.hom U (scalarSections f)).lTensor B)
      ((baseDifference (structureModule X) f.appTop.hom U).lTensor B) := by
  let : Algebra Γ(S, ⊤) Γ(Spec (.of B), ⊤) := (baseMap S B).appTop.hom.toAlgebra
  have H := CartesianStructureComplexExactness.exact_of_appTop_surjective
    (IsPullback.of_hasPullback f (baseMap S B)) U hU hA hB
  exact TensorKernelFiniteLength.exact_of_equiv _ _ (coefficientEquiv S B) H

variable [IsProper f] [GeometricallyConnected f] [GeometricallyReduced f]

include hU hA in
/-- Pointed connected reduced proper fibers give exactness over each actual residue quotient. -/
theorem residue_exact (s : S ⟶ X) (hs : s ≫ f = 𝟙 S)
    (I : Ideal Γ(S, ⊤)) [I.IsMaximal] :
    Function.Exact
      ((chartMap (structureModule X) f.appTop.hom U (scalarSections f)).lTensor
        (Γ(S, ⊤) ⧸ I))
      ((baseDifference (structureModule X) f.appTop.hom U).lTensor (Γ(S, ⊤) ⧸ I)) := by
  let _ := Ideal.Quotient.field I
  apply exact_over_algebra f U hU hA
  have H := SchemeConnectedFiberSections.pointedFiber_constantSections (K := Γ(S, ⊤) ⧸ I)
    f s hs (baseMap S (Γ(S, ⊤) ⧸ I))
  intro z
  obtain ⟨b, hb⟩ := H.surjective z
  exact ⟨(Scheme.ΓSpecIso (.of (Γ(S, ⊤) ⧸ I))).inv b, hb⟩

end FLT.Mazur.ProperFiberTensorComplex
