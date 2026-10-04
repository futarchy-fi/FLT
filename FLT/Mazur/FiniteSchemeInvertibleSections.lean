/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteSchemeLength
public import FLT.Mazur.ModuleSheafTensorAffineOpen
public import FLT.Mazur.PrincipalSectionExtension
public import Mathlib.RingTheory.Artinian.Module

/-!
# Sections of an invertible sheaf on a finite scheme

A tensor inverse gives an invertible module of global sections on an affine
scheme. Over a finite scheme over a field its section ring is Artinian, hence
semilocal. Its Picard group is trivial, proving the required dimension equality.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TensorProduct

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve

open ModuleSheafTensor

variable {k : Type} [Field k] {X : Scheme}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsFinite f]
  (M N : X.Modules) (hM : LocallyFreeRankOne M) (hN : LocallyFreeRankOne N)
  (e : tensor M N ≅ structureModule X)

include f in
/-- The section ring of a finite scheme over a field is Artinian. -/
theorem finiteScheme_globalSections_artinian : IsArtinianRing Γ(X, ⊤) := by
  let := (structureScalarMap f).toAlgebra
  have : Module.Finite k Γ(X, ⊤) := structureScalarMap_finite f
  exact IsArtinianRing.of_finite k Γ(X, ⊤)

include f hM hN e in
/-- The section module is invertible because its actual tensor inverse has affine sections. -/
theorem finiteScheme_sections_invertible : Module.Invertible Γ(X, ⊤) Γ(N, ⊤) := by
  have := hM.isFinitePresentation
  have := hN.isFinitePresentation
  have : IsAffine X := isAffine_of_isAffineHom f
  let t := (affineSectionsEquiv M N ⊤ (isAffineOpen_top X)).trans (sectionsCongr e ⊤)
  exact Module.Invertible.right t

/-- The section module is free of rank one over the finite section ring. -/
def finiteSchemeSectionsEquiv : Γ(N, ⊤) ≃ₗ[Γ(X, ⊤)] Γ(X, ⊤) := by
  have := finiteScheme_globalSections_artinian f
  have := finiteScheme_sections_invertible f M N hM hN e
  exact (Module.Invertible.free_iff_linearEquiv.mp inferInstance).some

include hM hN e in
/-- Scalar H⁰ of the invertible coefficient has the same dimension as the finite scheme. -/
theorem finiteScheme_invertible_h0_finrank :
    Module.finrank k (ModuleScalarH f N 0) = finiteSchemeLength f := by
  let := Module.compHom Γ(N, ⊤) (structureScalarMap f)
  let := Module.compHom Γ(X, ⊤) (structureScalarMap f)
  let a := finiteSchemeSectionsEquiv f M N hM hN e
  let b : Γ(N, ⊤) ≃ₗ[k] Γ(X, ⊤) :=
    { toAddEquiv := a.toAddEquiv
      map_smul' := fun r s ↦ a.map_smul (structureScalarMap f r) s }
  exact ((moduleScalarH0Equiv f N).trans (b.trans (scalarH0Equiv f).symm)).finrank_eq

end FLT.Mazur.FCurve
