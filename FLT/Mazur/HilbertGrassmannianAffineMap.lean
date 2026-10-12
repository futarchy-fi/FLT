/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertFamilyGrassmannianSchemeNaturality
public import FLT.Mazur.HilbertPolynomialAffineClassification
public import FLT.Mazur.AffineMorphismAlgebraMap

/-!
# Grassmannian morphisms on actual affine Hilbert tests

Every affine test of the Hilbert scheme supplies its full universal ideal.
Its Grassmannian map is natural for arbitrary affine tests and determines
the original Hilbert morphism, through recovery of the entire ideal.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.HilbertChart
open GrassmannianChart
set_option backward.isDefEq.respectTransparency false
universe u
variable (R I : Type u) [CommRing R] (d : ℕ)
variable {ι κ : Type u} [Fintype ι] [Fintype κ]
  (b : Module.Basis ι R (MvPolynomial.restrictTotalDegree I R (d + 1)))
  (hκ : Fintype.card κ = Fintype.card ι - d)
variable (S : Type u) [CommRing S] [Algebra R S]
  (f : Spec (.of S) ⟶ polynomialHilbertScheme R I d)
  (hf : f ≫ polynomialHilbertStructure R I d = Spec.algebraMap R S)

/-- The Grassmannian map on an affine Hilbert test uses its entire actual universal ideal. -/
def hilbertAffineGrassmannianMap : Spec (.of S) ⟶
    ambientGrassmannianScheme R (MvPolynomial.restrictTotalDegree I R (d + 1)) κ d :=
  finiteFlatHilbertClassifyingMap R S I (polynomialParameterIdeal R I d S f hf) d
    (polynomialParameterIdeal_residueRank R I d S f hf) b hκ

/-- The affine Grassmannian map is over the original coefficient spectrum. -/
@[reassoc] theorem hilbertAffineGrassmannianMap_over :
    hilbertAffineGrassmannianMap R I d b hκ S f hf ≫
      ambientGrassmannianStructure R (MvPolynomial.restrictTotalDegree I R (d + 1)) κ d =
      Spec.algebraMap R S :=
  finiteFlatHilbertClassifyingMap_over R S I _ d _ b hκ

variable (T : Type u) [CommRing T] [Algebra R T]
  (g : Spec (.of T) ⟶ polynomialHilbertScheme R I d)
  (hg : g ≫ polynomialHilbertStructure R I d = Spec.algebraMap R T)

/-- The affine Grassmannian map commutes with every original coefficient algebra map. -/
theorem hilbertAffineGrassmannianMap_natural (a : S →ₐ[R] T)
    (ha : Spec.map (CommRingCat.ofHom a.toRingHom) ≫ f = g) :
    Spec.map (CommRingCat.ofHom a.toRingHom) ≫
        hilbertAffineGrassmannianMap R I d b hκ S f hf =
      hilbertAffineGrassmannianMap R I d b hκ T g hg :=
  finiteFlatHilbertClassifyingMap_natural R S T I _ d _ b hκ a _ _
    (polynomialParameterIdeal_baseChange R I d S f hf T a g hg ha).symm

/-- Arbitrary affine scheme test maps preserve the full Hilbert Grassmannian parameter. -/
theorem hilbertAffineGrassmannianMap_test
    (q : Spec (.of T) ⟶ Spec (.of S)) (hq : q ≫ f = g) :
    q ≫ hilbertAffineGrassmannianMap R I d b hκ S f hf =
      hilbertAffineGrassmannianMap R I d b hκ T g hg := by
  have hqs : q ≫ Spec.algebraMap R S = Spec.algebraMap R T := by
    rw [← hf, ← Category.assoc, hq, hg]
  let a := affineOverAlgHom R S T q hqs
  have ha : Spec.map (CommRingCat.ofHom a.toRingHom) = q :=
    affineOverAlgHom_spec R S T q hqs
  rw [← ha]
  exact hilbertAffineGrassmannianMap_natural R I d b hκ S f hf T g hg a
    (by rw [ha, hq])

/-- Equal affine Grassmannian maps recover equal Hilbert morphisms and their full ideals. -/
theorem hilbertAffineGrassmannianMap_injective
    (g : Spec (.of S) ⟶ polynomialHilbertScheme R I d)
    (hg : g ≫ polynomialHilbertStructure R I d = Spec.algebraMap R S)
    (h : hilbertAffineGrassmannianMap R I d b hκ S f hf =
      hilbertAffineGrassmannianMap R I d b hκ S g hg) : f = g := by
  apply polynomialParameterIdeal_injective R I d S f hf g hg
  exact finiteFlatHilbertClassifyingMap_injective R S I _ d _ b hκ _ _ h

end FLT.Mazur.HilbertChart
