/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertGrassmannianGluing

/-!
# Testing the global Hilbert Grassmannian morphism

The glued morphism recovers the full universal-ideal parameter on every
affine test. This is a scheme-level monomorphism, retaining all equations;
no immersion conclusion is inferred from that monomorphism.
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
local notation "H" => polynomialHilbertScheme R I d

/-- Every affine test recovers the Grassmannian parameter of the entire pulled-back ideal. -/
theorem hilbertGrassmannianMap_affineTest (S : Type u) [CommRing S] [Algebra R S]
    (f : Spec (.of S) ⟶ H)
    (hf : f ≫ polynomialHilbertStructure R I d = Spec.algebraMap R S) :
    f ≫ hilbertGrassmannianMap R I d b hκ =
      hilbertAffineGrassmannianMap R I d b hκ S f hf := by
  apply (show (Spec (.of S)).OpenCover from
    (H).affineOpenCover.openCover.pullback₁ f).hom_ext
  intro i
  change pullback.fst f ((H).affineOpenCover.f i) ≫ f ≫ _ = _
  rw [pullback.condition_assoc, hilbertGrassmannianMap_restrict]
  let _ := polynomialCoverAlgebra R (polynomialHilbertStructure R I d) i
  exact hilbertAffineGrassmannianMap_agree R I d b hκ
    ((H).affineOpenCover.X i) S ((H).affineOpenCover.f i)
    (polynomialCoverAlgebra_over R (polynomialHilbertStructure R I d) i)
    f hf _ _ pullback.condition.symm

/-- Equality after the constructed morphism recovers arbitrary original Hilbert scheme maps. -/
theorem hilbertGrassmannianMap_cancel {X : Scheme.{u}} (f g : X ⟶ H)
    (h : f ≫ hilbertGrassmannianMap R I d b hκ =
      g ≫ hilbertGrassmannianMap R I d b hκ) : f = g := by
  have hs : f ≫ polynomialHilbertStructure R I d =
      g ≫ polynomialHilbertStructure R I d := by
    have he := congrArg (fun q ↦ q ≫ ambientGrassmannianStructure R
      (MvPolynomial.restrictTotalDegree I R (d + 1)) κ d) h
    simpa only [Category.assoc, hilbertGrassmannianMap_over] using he
  apply Scheme.Cover.hom_ext X.affineOpenCover.openCover
  intro i
  let S := X.affineOpenCover.X i
  let _ := polynomialCoverAlgebra R (f ≫ polynomialHilbertStructure R I d) i
  have hf : (X.affineOpenCover.f i ≫ f) ≫ polynomialHilbertStructure R I d =
      Spec.algebraMap R S := by
    simpa only [Category.assoc] using
      polynomialCoverAlgebra_over R (f ≫ polynomialHilbertStructure R I d) i
  have hg : (X.affineOpenCover.f i ≫ g) ≫ polynomialHilbertStructure R I d =
      Spec.algebraMap R S := by
    rw [Category.assoc, ← hs, ← Category.assoc]
    exact hf
  apply hilbertAffineGrassmannianMap_injective R I d b hκ S _ hf _ hg
  rw [← hilbertGrassmannianMap_affineTest, ← hilbertGrassmannianMap_affineTest]
  simpa only [Category.assoc] using congrArg (fun q ↦ X.affineOpenCover.f i ≫ q) h

/-- The full Hilbert ideal parameter defines a monomorphism of schemes over the original base. -/
instance hilbertGrassmannianMap_mono : Mono (hilbertGrassmannianMap R I d b hκ) where
  right_cancellation f g h := hilbertGrassmannianMap_cancel R I d b hκ f g h

end FLT.Mazur.HilbertChart
