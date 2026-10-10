/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartesianStructureTensorRestrictions

/-!
# Exactness of the tensor complex from actual fiber functions

An arbitrary affine change of base identifies tensor cycles on a finite affine
cover with compatible actual functions. If the new scheme has only structural
functions, these cycles are the image of the original scalar augmentation.
Flatness of the change of base is not assumed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
namespace FLT.Mazur.CartesianStructureComplexExactness
open Chow FCurve ArtinianSectionKernel ArtinianRelativeSectionCriterion
open CartesianStructureSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {P X T S : Scheme}
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  (h : IsPullback p q f g) [IsAffine T] [IsAffine S]
  {ι : Type} [Finite ι] (U : ι → X.Opens)

include h in
/-- Actual constant functions after base change imply exactness of the tensor cover complex. -/
theorem exact_of_appTop_surjective (hU : ⨆ i, U i = ⊤)
    (hA : ∀ i, IsAffineOpen (U i)) (hq : Function.Surjective q.appTop) :
    let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    Function.Exact
      ((chartMap (structureModule X) f.appTop.hom U (scalarSections f)).lTensor Γ(T, ⊤))
      ((baseDifference (structureModule X) f.appTop.hom U).lTensor Γ(T, ⊤)) := by
  classical
  let _ := Fintype.ofFinite ι
  dsimp only
  let : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  let a := chartMap (structureModule X) f.appTop.hom U (scalarSections f)
  let d := baseDifference (structureModule X) f.appTop.hom U
  intro x
  constructor
  · intro hx
    let e := piRight Γ(S, ⊤) Γ(T, ⊤) Γ(T, ⊤)
      (fun i ↦ baseSections (structureModule X) f.appTop.hom (U i))
    let t := e x
    have ht : tensorSectionDifference Γ(T, ⊤) (structureModule X) f.appTop.hom U t = 0 := by
      rw [tensorSectionDifference_eq]
      change piRight Γ(S, ⊤) Γ(T, ⊤) Γ(T, ⊤) _
        (AlgebraTensorModule.lTensor Γ(T, ⊤) Γ(T, ⊤) d (e.symm (e x))) = 0
      rw [LinearEquiv.symm_apply_apply]
      change piRight Γ(S, ⊤) Γ(T, ⊤) Γ(T, ⊤) _ (d.lTensor Γ(T, ⊤) x) = 0
      rw [hx, map_zero]
    let v : ∀ i, baseSections (structureModule P) q.appTop.hom (p ⁻¹ᵁ U i) :=
      fun i ↦ comparison h (U i) (t i)
    have hv : v ∈ (baseDifference (structureModule P) q.appTop.hom
        (fun i ↦ p ⁻¹ᵁ U i)).ker := by
      rw [baseDifference_mem_ker]
      intro i j
      have hij := congrFun ht (i, j)
      change AlgebraTensorModule.lTensor Γ(T, ⊤) Γ(T, ⊤)
          (baseRestriction (structureModule X) f.appTop.hom inf_le_right) (t j) -
        AlgebraTensorModule.lTensor Γ(T, ⊤) Γ(T, ⊤)
          (baseRestriction (structureModule X) f.appTop.hom inf_le_left) (t i) = 0 at hij
      have H := congrArg (comparison h (U i ⊓ U j)) (sub_eq_zero.mp hij)
      rw [comparison_lTensor, comparison_lTensor] at H
      exact H.symm
    obtain ⟨z, hz⟩ := (baseRestrictEqualizer_bijective (structureModule P) q.appTop.hom
      (fun i ↦ p ⁻¹ᵁ U i) (p.iSup_preimage_eq_top hU)).surjective ⟨v, hv⟩
    obtain ⟨b, hb⟩ := hq z
    refine ⟨b ⊗ₜ[Γ(S, ⊤)] (1 : Γ(S, ⊤)), ?_⟩
    apply e.injective
    funext i
    apply (comparison_bijective h (U i) (hA i)).injective
    change comparison h (U i) (b ⊗ₜ[Γ(S, ⊤)] a 1 i) = comparison h (U i) (t i)
    rw [comparison_chartMap_one]
    change baseRestriction (structureModule P) q.appTop.hom le_top (q.appTop b) = v i
    rw [hb]
    exact congrArg (fun w ↦ w.val i) hz
  · rintro ⟨y, rfl⟩
    rw [← LinearMap.lTensor_comp_apply, difference_chartMap, LinearMap.lTensor_zero]
    rfl

end FLT.Mazur.CartesianStructureComplexExactness
