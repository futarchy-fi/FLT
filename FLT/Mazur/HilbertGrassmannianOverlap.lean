/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertGrassmannianAffineMap
public import FLT.Mazur.PolynomialRelativeAffineCover

/-!
# Agreement of Hilbert Grassmannian maps on actual overlaps

Affine naturality proves agreement after every common scheme test, using
its actual affine cover and the coefficient structure induced by the base.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.HilbertChart
open GrassmannianChart
set_option backward.isDefEq.respectTransparency false
universe u
variable (R I : Type u) [CommRing R] (d : ℕ)
variable {ι κ : Type u} [Fintype ι] [Fintype κ]
  (b : Module.Basis ι R (MvPolynomial.restrictTotalDegree I R (d + 1)))
  (hκ : Fintype.card κ = Fintype.card ι - d)

/-- Affine Hilbert Grassmannian maps agree on arbitrary original common scheme tests. -/
theorem hilbertAffineGrassmannianMap_agree
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (f : Spec (.of S) ⟶ polynomialHilbertScheme R I d)
    (hf : f ≫ polynomialHilbertStructure R I d = Spec.algebraMap R S)
    (g : Spec (.of T) ⟶ polynomialHilbertScheme R I d)
    (hg : g ≫ polynomialHilbertStructure R I d = Spec.algebraMap R T)
    {Y : Scheme.{u}} (p : Y ⟶ Spec (.of S)) (q : Y ⟶ Spec (.of T))
    (hpq : p ≫ f = q ≫ g) :
    p ≫ hilbertAffineGrassmannianMap R I d b hκ S f hf =
      q ≫ hilbertAffineGrassmannianMap R I d b hκ T g hg := by
  apply Scheme.Cover.hom_ext Y.affineOpenCover.openCover
  intro i
  let U := Y.affineOpenCover.X i
  let _ := polynomialCoverAlgebra R (p ≫ f ≫ polynomialHilbertStructure R I d) i
  let c : Spec (.of U) ⟶ polynomialHilbertScheme R I d := Y.affineOpenCover.f i ≫ p ≫ f
  have hc : c ≫ polynomialHilbertStructure R I d = Spec.algebraMap R U := by
    simpa only [c, Category.assoc] using
      polynomialCoverAlgebra_over R (p ≫ f ≫ polynomialHilbertStructure R I d) i
  rw [← Category.assoc, ← Category.assoc]
  calc
    (Y.affineOpenCover.f i ≫ p) ≫ _ =
        hilbertAffineGrassmannianMap R I d b hκ U c hc :=
      hilbertAffineGrassmannianMap_test R I d b hκ S f hf U c hc _
        (Category.assoc _ _ _)
    _ = (Y.affineOpenCover.f i ≫ q) ≫ _ :=
      (hilbertAffineGrassmannianMap_test R I d b hκ T g hg U c hc _
        (by simp only [c, Category.assoc, ← hpq])).symm

end FLT.Mazur.HilbertChart
