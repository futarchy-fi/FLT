/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertPolynomialUniversalChartPullback
public import FLT.Mazur.HilbertPolynomialFamilyRestriction

/-!
# Ambient maps for polynomial families

A parameter morphism over the coefficient base induces a morphism of actual
polynomial ambient spaces. Its two projections characterize it uniquely.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (d : ℕ)
variable (S : Type u) [CommRing S] [Algebra R S]

/-- A parameter over the coefficient base induces its polynomial ambient morphism. -/
def polynomialAmbientMap (f : Spec (.of S) ⟶ polynomialHilbertScheme R I d)
    (hf : f ≫ polynomialHilbertStructure R I d =
      Spec.map (CommRingCat.ofHom (algebraMap R S))) :
    Spec (.of (MvPolynomial I S)) ⟶ polynomialHilbertAmbient R I d :=
  pullback.lift (Spec.map (CommRingCat.ofHom (MvPolynomial.C (R := S) (σ := I))) ≫ f)
    (Spec.map (CommRingCat.ofHom (MvPolynomial.map (algebraMap R S)))) (by
      rw [Category.assoc, hf, ← Spec.map_comp, ← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro r
      exact (MvPolynomial.map_C (algebraMap R S) r).symm)

/-- The first ambient projection is the original parameter after polynomial projection. -/
@[reassoc]
theorem polynomialAmbientMap_fst (f : Spec (.of S) ⟶ polynomialHilbertScheme R I d)
    (hf : f ≫ polynomialHilbertStructure R I d =
      Spec.map (CommRingCat.ofHom (algebraMap R S))) :
    polynomialAmbientMap R I d S f hf ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (MvPolynomial.C (R := S) (σ := I))) ≫ f :=
  pullback.lift_fst _ _ _

/-- The second ambient projection is the original scalar extension of polynomial space. -/
@[reassoc]
theorem polynomialAmbientMap_snd (f : Spec (.of S) ⟶ polynomialHilbertScheme R I d)
    (hf : f ≫ polynomialHilbertStructure R I d =
      Spec.map (CommRingCat.ofHom (algebraMap R S))) :
    polynomialAmbientMap R I d S f hf ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (MvPolynomial.map (algebraMap R S))) :=
  pullback.lift_snd _ _ _

variable (J : Ideal (MvPolynomial I S))
variable [Module.FinitePresentation S (MvPolynomial I S ⧸ J)]
variable [Module.Flat S (MvPolynomial I S ⧸ J)]
variable (hd : ∀ p : PrimeSpectrum S, Module.finrank p.asIdeal.ResidueField
  (MvPolynomial I p.asIdeal.ResidueField ⧸
    J.map (MvPolynomial.map (algebraMap S p.asIdeal.ResidueField))) = d)

/-- The actual ambient morphism belonging to an arbitrary finite flat quotient family. -/
def polynomialFamilyAmbientMap :
    Spec (.of (MvPolynomial I S)) ⟶ polynomialHilbertAmbient R I d :=
  polynomialAmbientMap R I d S (polynomialFamilyMorphism R I d S J hd)
    (polynomialFamilyMorphism_over R I d S J hd)

end FLT.Mazur.HilbertChart
