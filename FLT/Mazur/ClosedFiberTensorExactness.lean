/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFiberTensorComplex

/-!
# Tensor exactness from one actual connected reduced fiber

The cover complex over a field is exact when that particular proper fiber is
connected and reduced. No connectedness or reducedness of other fibers is used.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
namespace FLT.Mazur.ClosedFiberTensorExactness
open Chow FCurve ArtinianSectionKernel ArtinianRelativeSectionCriterion
open AffineBaseChangeCoefficients
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {X S : Scheme} (f : X ⟶ S) [IsAffine S] [IsProper f]
  {ι : Type} [Finite ι] (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
  (hA : ∀ i, IsAffineOpen (U i))
  (s : S ⟶ X) (hs : s ≫ f = 𝟙 S)

include hU hA s hs

/-- A single connected reduced field fiber gives exactness over its coefficient field. -/
theorem exact_over_field (K : Type) [Field K] [Algebra Γ(S, ⊤) K]
    [ConnectedSpace ↥(pullback f (baseMap S K))]
    [IsReduced (pullback f (baseMap S K))] :
    Function.Exact
      ((chartMap (structureModule X) f.appTop.hom U (scalarSections f)).lTensor K)
      ((baseDifference (structureModule X) f.appTop.hom U).lTensor K) := by
  apply ProperFiberTensorComplex.exact_over_algebra f U hU hA
  have H := constantGlobalSections_of_proper_connected_reduced_section
    (pullback.snd f (baseMap S K))
    (SchemeProperGeometricFiberSections.baseChangedSection f s hs (baseMap S K))
    (SchemeProperGeometricFiberSections.baseChangedSection_projection f s hs (baseMap S K))
  intro z
  obtain ⟨b, hb⟩ := H.surjective z
  exact ⟨(Scheme.ΓSpecIso (.of K)).inv b, hb⟩

/-- Only the chosen maximal-ideal fiber is needed for residue exactness. -/
theorem residue_exact (I : Ideal Γ(S, ⊤)) [I.IsMaximal]
    [ConnectedSpace ↥(pullback f (baseMap S (Γ(S, ⊤) ⧸ I)))]
    [IsReduced (pullback f (baseMap S (Γ(S, ⊤) ⧸ I)))] :
    Function.Exact
      ((chartMap (structureModule X) f.appTop.hom U (scalarSections f)).lTensor
        (Γ(S, ⊤) ⧸ I))
      ((baseDifference (structureModule X) f.appTop.hom U).lTensor (Γ(S, ⊤) ⧸ I)) := by
  let _ := Ideal.Quotient.field I
  exact exact_over_field f U hU hA s hs (Γ(S, ⊤) ⧸ I)

end FLT.Mazur.ClosedFiberTensorExactness
