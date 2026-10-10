/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertPolynomialSchemeParameterIdeal
public import FLT.Mazur.HilbertPolynomialParameterInverse
public import FLT.Mazur.PolynomialRelativeAffineCover

/-!
# Faithfulness of scheme parameters from their full universal ideals

Equality of actual universal pullback ideals detects arbitrary scheme
parameters. On each affine base chart this is the proved affine inverse
law; the affine cover detects equality of the original morphisms.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.BaseAdicThickening

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (d : ℕ)
variable {X : Scheme.{u}} (s : X ⟶ Spec (.of R))
variable (f g : X ⟶ polynomialHilbertScheme R I d)
variable (hf : f ≫ polynomialHilbertStructure R I d = s)
variable (hg : g ≫ polynomialHilbertStructure R I d = s)

/-- Scheme parameters are determined by their full actual universal pullback ideals. -/
theorem polynomialSchemeParameterIdeal_injective
    (h : polynomialSchemeParameterIdeal R I d s f hf =
      polynomialSchemeParameterIdeal R I d s g hg) : f = g := by
  apply Scheme.Cover.hom_ext X.affineOpenCover.openCover
  intro i
  let S := X.affineOpenCover.X i
  let _ := polynomialCoverAlgebra R s i
  have hs := polynomialCoverAlgebra_over R s i
  have hfi : (X.affineOpenCover.f i ≫ f) ≫ polynomialHilbertStructure R I d =
      Spec.map (CommRingCat.ofHom (algebraMap R S)) := by rw [Category.assoc, hf, hs]
  have hgi : (X.affineOpenCover.f i ≫ g) ≫ polynomialHilbertStructure R I d =
      Spec.map (CommRingCat.ofHom (algebraMap R S)) := by rw [Category.assoc, hg, hs]
  apply polynomialParameterIdeal_injective R I d S _ hfi _ hgi
  have hi := congrArg (fun K ↦ K.comap
    (polynomialRelativeAffineChart R I s S (X.affineOpenCover.f i) hs)) h
  rw [polynomialSchemeParameterIdeal_affineTest,
    polynomialSchemeParameterIdeal_affineTest] at hi
  have hc := congrArg (coordinateIdeal (.of (MvPolynomial I S))) hi
  simpa only [coordinateIdeal_baseIdeal] using hc

end FLT.Mazur.HilbertChart
