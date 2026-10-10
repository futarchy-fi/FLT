/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertPolynomialParameterIdeal
public import FLT.Mazur.PolynomialRelativeAffineChart

/-!
# Universal polynomial ideals over arbitrary scheme parameters

Every parameter over a scheme gives an actual ideal in its relative
polynomial ambient space. Its affine restrictions are exactly the already
classified coordinate ideals, and arbitrary scheme base change preserves it.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.BaseAdicThickening

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (d : ℕ)
variable {X Y : Scheme.{u}} (s : X ⟶ Spec (.of R))
variable (f : X ⟶ polynomialHilbertScheme R I d)
variable (hf : f ≫ polynomialHilbertStructure R I d = s)

/-- A scheme parameter pulls the full universal ideal back to relative polynomial space. -/
def polynomialSchemeParameterIdeal : (polynomialRelativeAmbient R I s).IdealSheafData :=
  (polynomialUniversalIdeal R I d).comap
    (polynomialRelativeAmbientMap R I (polynomialHilbertStructure R I d) s f hf)

/-- Arbitrary scheme base change pulls back the full ideal of the parameter. -/
theorem polynomialSchemeParameterIdeal_baseChange
    (t : Y ⟶ Spec (.of R)) (g : Y ⟶ X) (hg : g ≫ s = t) :
    (polynomialSchemeParameterIdeal R I d s f hf).comap
        (polynomialRelativeAmbientMap R I s t g hg) =
      polynomialSchemeParameterIdeal R I d t (g ≫ f) (by rw [Category.assoc, hf, hg]) := by
  unfold polynomialSchemeParameterIdeal
  rw [← Scheme.IdealSheafData.comap_comp, polynomialRelativeAmbientMap_comp]

/-- On each affine base test the full ideal is the sheaf of the classified coordinate ideal. -/
theorem polynomialSchemeParameterIdeal_affineTest
    (S : Type u) [CommRing S] [Algebra R S]
    (a : Spec (.of S) ⟶ X)
    (ha : a ≫ s = Spec.map (CommRingCat.ofHom (algebraMap R S))) :
    (polynomialSchemeParameterIdeal R I d s f hf).comap
        (polynomialRelativeAffineChart R I s S a ha) =
      baseIdeal (.of (MvPolynomial I S))
        (polynomialParameterIdeal R I d S (a ≫ f) (by rw [Category.assoc, hf, ha])) := by
  unfold polynomialSchemeParameterIdeal
  rw [← Scheme.IdealSheafData.comap_comp, polynomialRelativeAffineChart_comp]
  exact (polynomialParameterIdeal_sheaf R I d S (a ≫ f) (by
    rw [Category.assoc, hf, ha])).symm

end FLT.Mazur.HilbertChart
