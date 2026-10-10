/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartesianStructureComplexExactness

/-!
# Gluing exact structure tensors to actual global functions

Exactness of the original tensor cover complex implies that all functions on
the changed scheme come from its base. Affine charts and affine overlaps
supply the local comparisons for arbitrary, possibly nonflat base change.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
namespace FLT.Mazur.CartesianStructureComplexGluing
open Chow FCurve ArtinianSectionKernel ArtinianRelativeSectionCriterion
open CartesianStructureSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {P X T S : Scheme}
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  (h : IsPullback p q f g) [IsAffine T] [IsAffine S]
  {ι : Type} [Finite ι] (U : ι → X.Opens)

include h in
/-- Exact tensors and actual sheaf gluing imply surjectivity of structural pullback. -/
theorem appTop_surjective_of_exact (hU : ⨆ i, U i = ⊤)
    (hA : ∀ i, IsAffineOpen (U i)) (hI : ∀ i j, IsAffineOpen (U i ⊓ U j)) :
    let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    Function.Exact
      ((chartMap (structureModule X) f.appTop.hom U (scalarSections f)).lTensor Γ(T, ⊤))
      ((baseDifference (structureModule X) f.appTop.hom U).lTensor Γ(T, ⊤)) →
        Function.Surjective q.appTop := by
  classical
  let _ := Fintype.ofFinite ι
  dsimp only
  let : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  intro hex z
  let a := chartMap (structureModule X) f.appTop.hom U (scalarSections f)
  let d := baseDifference (structureModule X) f.appTop.hom U
  let e := piRight Γ(S, ⊤) Γ(T, ⊤) Γ(T, ⊤)
    (fun i ↦ baseSections (structureModule X) f.appTop.hom (U i))
  choose t ht using fun i ↦ (comparison_bijective h (U i) (hA i)).surjective
    (baseRestriction (structureModule P) q.appTop.hom le_top z)
  have compat (i j : ι) :
      AlgebraTensorModule.lTensor Γ(T, ⊤) Γ(T, ⊤)
          (baseRestriction (structureModule X) f.appTop.hom inf_le_left) (t i) =
        AlgebraTensorModule.lTensor Γ(T, ⊤) Γ(T, ⊤)
          (baseRestriction (structureModule X) f.appTop.hom inf_le_right) (t j) := by
    apply (comparison_bijective h (U i ⊓ U j) (hI i j)).injective
    rw [comparison_lTensor, comparison_lTensor, ht, ht]
    change P.presheaf.map _ (P.presheaf.map _ z) = P.presheaf.map _ (P.presheaf.map _ z)
    simp only [← Functor.map_comp_apply]
    rfl
  have htzero : tensorSectionDifference Γ(T, ⊤) (structureModule X) f.appTop.hom U t = 0 := by
    ext ij
    exact sub_eq_zero.mpr (compat ij.1 ij.2).symm
  have hx : d.lTensor Γ(T, ⊤) (e.symm t) = 0 := by
    apply (piRight Γ(S, ⊤) Γ(T, ⊤) Γ(T, ⊤)
      (fun ij : ι × ι ↦ baseSections (structureModule X) f.appTop.hom
        (U ij.1 ⊓ U ij.2))).injective
    rw [map_zero]
    rw [tensorSectionDifference_eq] at htzero
    exact htzero
  obtain ⟨y, hy⟩ := (hex (e.symm t)).mp hx
  obtain ⟨b, rfl⟩ := (TensorProduct.rid Γ(S, ⊤) Γ(T, ⊤)).symm.surjective y
  refine ⟨b, ?_⟩
  apply (baseRestrictEqualizer_bijective (structureModule P) q.appTop.hom
    (fun i ↦ p ⁻¹ᵁ U i) (p.iSup_preimage_eq_top hU)).injective
  apply Subtype.ext
  funext i
  have hi := congrArg (fun w ↦ e w i) hy
  change b ⊗ₜ[Γ(S, ⊤)] a 1 i = e (e.symm t) i at hi
  rw [LinearEquiv.apply_symm_apply] at hi
  have hc := congrArg (comparison h (U i)) hi
  rw [comparison_chartMap_one, ht] at hc
  exact hc

end FLT.Mazur.CartesianStructureComplexGluing
