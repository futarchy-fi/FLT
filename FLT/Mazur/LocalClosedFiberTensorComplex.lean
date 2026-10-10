/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocalClosedFiberBaseChange
public import FLT.Mazur.TensorKernelCyclic

/-!
# Universal tensor exactness from the local closed fiber

Every nonzero quotient of a local ring is local with the same closed point.
The actual local comparison therefore proves cyclic coefficient exactness.
The zero quotient is immediate, and flat overlap terms extend the result to
all coefficient modules, including infinite ones.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
namespace FLT.Mazur.LocalClosedFiberTensorComplex
open Chow PolygonStructureInclusion ArtinianSectionKernel ArtinianRelativeSectionCriterion
open Approximation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {X S : Scheme.{0}} (f : X ⟶ S) [IsAffine S]
  [IsNoetherianRing Γ(S, ⊤)] [IsLocalRing Γ(S, ⊤)]
  [IsProper f] [Flat f] [GeometricallyReduced f]
  (s : S ⟶ X) (hs : s ≫ f = 𝟙 S)
  (hc : S.isoSpec.inv (IsLocalRing.closedPoint Γ(S, ⊤)) ∈ geometricallyConnectedLocus f)
  {ι : Type} [Finite ι] (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
  (hA : ∀ i, IsAffineOpen (U i))

include s hs hc hU hA

/-- The actual closed fiber controls the cover complex with every cyclic coefficient. -/
theorem quotient_exact (I : Ideal Γ(S, ⊤)) :
    Function.Exact
      ((chartMap (structureModule X) f.appTop.hom U (scalarSections f)).lTensor (Γ(S, ⊤) ⧸ I))
      ((baseDifference (structureModule X) f.appTop.hom U).lTensor (Γ(S, ⊤) ⧸ I)) := by
  cases subsingleton_or_nontrivial (Γ(S, ⊤) ⧸ I) with
  | inl h =>
    let _ := h
    intro x
    exact ⟨fun _ ↦ ⟨0, Subsingleton.elim _ _⟩, fun _ ↦ Subsingleton.elim _ _⟩
  | inr h =>
    let _ := h
    let _ := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    let _ : IsLocalHom (algebraMap Γ(S, ⊤) (Γ(S, ⊤) ⧸ I)) :=
      IsLocalHom.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    apply ProperFiberTensorComplex.exact_over_algebra f U hU hA
    exact (LocalClosedFiberBaseChange.coefficient_appTop_bijective f s hs hc
      (Γ(S, ⊤) ⧸ I)).surjective

/-- A single local closed fiber supplies exactness for every coefficient module. -/
theorem cover_exact (B : Type) [AddCommGroup B] [Module Γ(S, ⊤) B] :
    Function.Exact
      ((chartMap (structureModule X) f.appTop.hom U (scalarSections f)).lTensor B)
      ((baseDifference (structureModule X) f.appTop.hom U).lTensor B) := by
  let _ : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  let _ := FlatStructureSectionComplex.overlapProduct_flat f U hA
  exact TensorKernelCyclic.exact_arbitrary_coefficients _ _
    (quotient_exact f s hs hc U hU hA)
    (difference_chartMap (structureModule X) f.appTop.hom U (scalarSections f)) B

end FLT.Mazur.LocalClosedFiberTensorComplex
