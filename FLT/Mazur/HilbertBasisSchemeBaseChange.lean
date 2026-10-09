/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBasisBaseChangeCover
public import FLT.Mazur.HilbertPrincipalBaseChangeMorphism
public import FLT.Mazur.HilbertBasisSchemeGluing

/-!
# Naturality of the actual glued Hilbert chart morphism

Principal localization coordinates identify the pulled-back local parameters.
The pulled-back principal cover then proves naturality of the glued morphism
under every scalar extension of a finitely presented flat quotient family.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (I : Type u) (d : ℕ)
variable (w : Fin d → MvPolynomial I R)
variable (S : Type u) [CommRing S] [Algebra R S] (J : Ideal (MvPolynomial I S))
variable [Module.FinitePresentation S (MvPolynomial I S ⧸ J)]
variable (T : Type u) [CommRing T] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

local instance : Module.FinitePresentation T
    (MvPolynomial I T ⧸ J.map (MvPolynomial.map (algebraMap S T))) :=
  polynomialQuotient_finitePresentation_baseChange I S J T

/-- Local classifying scheme morphisms commute with arbitrary scalar extension. -/
theorem neighborhoodChartMorphism_baseChange
    (r : PolynomialBasisNeighborhoods R I d w S J) :
    principalBaseChangeMorphism T r.val ≫ neighborhoodChartMorphism R I d w S J r =
      neighborhoodChartMorphism R I d w T (J.map (MvPolynomial.map (algebraMap S T)))
        (baseChangeNeighborhood R I d w S J T r) := by
  apply (cancel_epi (basicOpenIsoSpecAway (R := .of T) (algebraMap S T r.val)).inv).mp
  have h := neighborhoodChartMorphism_affine R I d w T
    (J.map (MvPolynomial.map (algebraMap S T))) (baseChangeNeighborhood R I d w S J T r)
  change (basicOpenIsoSpecAway (R := .of T) (algebraMap S T r.val)).inv ≫ _ = _ at h
  rw [h]
  have h₁ := congrArg (fun f ↦ f ≫ Spec.map
    (CommRingCat.ofHom (R := ChartRing R I d w)
      (neighborhoodClassifyingMap R I d w S J r).toRingHom))
    (principalBaseChangeMorphism_affine T r.val)
  simp only [Category.assoc] at h₁
  rw [neighborhoodChartMorphism, h₁, ← Spec.map_comp,
    baseChangeNeighborhood_classifyingMap]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  rfl

variable [Module.Flat S (MvPolynomial I S ⧸ J)]

/-- The map of intrinsic basis schemes restricts to the actual principal base-change map. -/
theorem polynomialBasisBaseChangeMorphism_restrict
    (r : PolynomialBasisNeighborhoods R I d w S J) :
    (polynomialBasisBaseChangeCover R I d w S J T).f r ≫
      polynomialBasisBaseChangeMorphism R I d w S J T =
    principalBaseChangeMorphism T r.val ≫ (polynomialBasisSchemeCover R I d w S J).f r := by
  rw [← cancel_mono (Scheme.Opens.ι (X := Spec (.of S)) (polynomialBasisOpen R I d w S J))]
  simp only [Category.assoc]
  change (Spec (.of T)).homOfLE (neighborhood_basicOpen_le R I d w T
      (J.map (MvPolynomial.map (algebraMap S T))) (baseChangeNeighborhood R I d w S J T r)) ≫
    polynomialBasisBaseChangeMorphism R I d w S J T ≫ _ =
      principalBaseChangeMorphism T r.val ≫
        (Spec (.of S)).homOfLE (neighborhood_basicOpen_le R I d w S J r) ≫ _
  simp only [polynomialBasisBaseChangeMorphism, principalBaseChangeMorphism,
    Scheme.Hom.resLE_comp_ι, Scheme.homOfLE_ι, ← Category.assoc]
  rfl

/-- The actual glued classifying morphism is natural under arbitrary base change. -/
theorem intrinsicChartMorphism_baseChange :
    polynomialBasisBaseChangeMorphism R I d w S J T ≫ intrinsicChartMorphism R I d w S J =
      intrinsicChartMorphism R I d w T (J.map (MvPolynomial.map (algebraMap S T))) := by
  apply (polynomialBasisBaseChangeCover R I d w S J T).hom_ext
  intro r
  rw [← Category.assoc, polynomialBasisBaseChangeMorphism_restrict, Category.assoc,
    intrinsicChartMorphism_restrict, neighborhoodChartMorphism_baseChange]
  exact (intrinsicChartMorphism_restrict R I d w T
    (J.map (MvPolynomial.map (algebraMap S T))) (baseChangeNeighborhood R I d w S J T r)).symm

end FLT.Mazur.HilbertChart
