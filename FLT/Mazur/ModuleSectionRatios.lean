/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleGlobalUnitGenerator
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Ratios of genuine generating sections

The inverse of the actual generating section morphism gives regular ratios.
These ratios define scheme morphisms to affine coordinate spaces, and changing
the generating section satisfies the multiplicative overlap identity.
-/

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
variable {X : Scheme.{u}} (M : X.Modules) (s : Γ(M, ⊤))
    [IsIso (globalSectionHom M s)]

/-- The regular ratio of an actual section to an actual generator. -/
def sectionRatio (t : Γ(M, ⊤)) : Γ(X, ⊤) :=
  (inv (globalSectionHom M s)).app ⊤ t

/-- Multiplication by the generating section recovers the numerator. -/
lemma sectionRatio_smul (t : Γ(M, ⊤)) : sectionRatio M s t • s = t := by
  have hg (r : Γ(X, ⊤)) : (globalSectionHom M s).app ⊤ r = r • s := by
    change r • (M.presheaf.map (𝟙 (op ⊤)) s) = r • s
    rw [M.presheaf.map_id, ConcreteCategory.id_apply]
  rw [← hg]
  exact congrArg (fun f ↦ f.app ⊤ t) (IsIso.inv_hom_id (globalSectionHom M s))

/-- Ratios respect multiplication of the numerator by a regular function. -/
lemma sectionRatio_smul_numerator (r : Γ(X, ⊤)) (t : Γ(M, ⊤)) :
    sectionRatio M s (r • t) = r * sectionRatio M s t :=
  Hom.app_smul (inv (globalSectionHom M s)) r t

/-- A section divided by itself has coordinate one. -/
@[simp] lemma sectionRatio_self : sectionRatio M s s = 1 := by
  have he := congrArg (fun f ↦ f.app ⊤ (1 : Γ(X, ⊤)))
    (IsIso.hom_inv_id (globalSectionHom M s))
  simp only [Hom.comp_app, AddCommGrpCat.comp_apply, globalSectionHom_top,
    Hom.id_app, AddCommGrpCat.id_apply] at he
  exact he

/-- Changing generators gives the usual multiplicative overlap identity. -/
lemma sectionRatio_change (t v : Γ(M, ⊤)) [IsIso (globalSectionHom M t)] :
    sectionRatio M s t * sectionRatio M t v = sectionRatio M s v := by
  rw [mul_comm, ← sectionRatio_smul_numerator, sectionRatio_smul]

/-- The ratio of two actual generators is a unit. -/
lemma sectionRatio_isUnit (t : Γ(M, ⊤)) [IsIso (globalSectionHom M t)] :
    IsUnit (sectionRatio M s t) := by
  apply IsUnit.of_mul_eq_one (sectionRatio M t s)
  rw [sectionRatio_change, sectionRatio_self]

/-- Evaluate affine-coordinate polynomials at the section ratios. -/
def sectionRatioRingMap {R : Type u} [CommRing R] (r : R →+* Γ(X, ⊤))
    {ι : Type u} (t : ι → Γ(M, ⊤)) : MvPolynomial ι R →+* Γ(X, ⊤) :=
  MvPolynomial.eval₂Hom r (sectionRatio M s ∘ t)

/-- The actual scheme morphism defined by a family of regular section ratios. -/
def sectionRatioMorphism {R : Type u} [CommRing R] (r : R →+* Γ(X, ⊤))
    {ι : Type u} (t : ι → Γ(M, ⊤)) : X ⟶ Spec (.of (MvPolynomial ι R)) :=
  X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (sectionRatioRingMap M s r t))

/-- The inverse image of a coordinate nonvanishing open is its ratio's basic open. -/
lemma sectionRatioMorphism_preimage {R : Type u} [CommRing R] (r : R →+* Γ(X, ⊤))
    {ι : Type u} (t : ι → Γ(M, ⊤)) (i : ι) :
    sectionRatioMorphism M s r t ⁻¹ᵁ PrimeSpectrum.basicOpen (MvPolynomial.X i) =
      X.basicOpen (sectionRatio M s (t i)) := by
  rw [sectionRatioMorphism, Scheme.Hom.comp_preimage, SpecMap_preimage_basicOpen,
    Scheme.toSpecΓ_preimage_basicOpen]
  simp [sectionRatioRingMap]

end FLT.Mazur.FCurve
