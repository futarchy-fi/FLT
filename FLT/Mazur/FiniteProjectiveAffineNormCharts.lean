/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineOpenNorm
public import FLT.Mazur.FiniteFlatTranslationNormCharts
public import Mathlib.RingTheory.Flat.EquationalCriterion

/-!
# Constructed finite projective norm charts

Finite projectivity of the original section algebra supplies principal target
neighborhoods with bases of their entire original preimages. No invariance of
these neighborhoods and no global basis are assumed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Module TensorProduct
namespace FLT.Mazur.FiniteProjectiveAffineNormCharts
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- A basis over the canonical localization transfers to any actual localization ring. -/
def localizationBasis {R C S : Type u} [CommRing R] [CommRing C] [CommRing S]
    [Algebra R C] [Algebra R S] (r : R) [IsLocalization.Away r S] {n : ℕ}
    (b : Basis (Fin n) (Localization.Away r) (Localization.Away r ⊗[R] C)) :
    Basis (Fin n) S (S ⊗[R] C) := by
  let e := IsLocalization.algEquiv (.powers r) (Localization.Away r) S
  let _ := e.toRingHom.toAlgebra
  let _ : IsScalarTower R (Localization.Away r) S :=
    IsScalarTower.of_algebraMap_eq (fun a ↦ (e.commutes a).symm)
  exact (b.baseChange S).map
    (AlgebraTensorModule.cancelBaseChange R (Localization.Away r) S S C)

variable {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)

/-- Finite projective original sections give genuine free principal preimages at every point. -/
theorem exists_chart (y : Y) :
    let _ := f.appTop.hom.toAlgebra
    Module.Finite Γ(Y, ⊤) Γ(X, ⊤) → Module.Projective Γ(Y, ⊤) Γ(X, ⊤) →
    ∃ U : Y.affineOpens, y ∈ U.1 ∧ AffineOpenNorm.HasBasis f U := by
  let _ := f.appTop.hom.toAlgebra
  dsimp only
  intro hfinite hprojective
  let _ := hfinite
  let _ := hprojective
  let _ := Module.finitePresentation_of_projective Γ(Y, ⊤) Γ(X, ⊤)
  obtain ⟨r, hr, n, ⟨b⟩⟩ := FiniteFreeTranslationNorm.exists_principal_basis
    (S := Γ(X, ⊤)) (Y.isoSpec.hom y)
  let U : Y.affineOpens := ⟨Y.basicOpen r, (isAffineOpen_top Y).basicOpen r⟩
  refine ⟨U, ?_, ?_⟩
  · change y ∈ Y.basicOpen r
    rw [← Y.map_PrimeSpectrum_basicOpen_of_affine]
    exact hr
  · let _ := U.1.ι.appTop.hom.toAlgebra
    let _ := (f ∣_ U.1).appTop.hom.toAlgebra
    let _ : IsLocalization.Away r Γ(U.1, ⊤) := inferInstance
    let c := localizationBasis (C := Γ(X, ⊤)) (S := Γ(U.1, ⊤)) r b
    exact ⟨n, ⟨c.map (AffineCartesianNorm.tensorAlgEquiv _ _ _ _
      (isPullback_morphismRestrict f U.1).flip).toLinearEquiv⟩⟩

end FLT.Mazur.FiniteProjectiveAffineNormCharts
