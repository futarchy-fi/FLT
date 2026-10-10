/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertPolynomialSchemeAffineNaturality

/-!
# Agreement of actual scheme family parameters on overlaps

Affine test naturality implies agreement on any common scheme test, by its
affine cover. In particular the canonical base-chart parameters satisfy the
pullback compatibility required to glue an actual global morphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.FCurve

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (d : ℕ)
variable {X : Scheme.{u}} (s : X ⟶ Spec (.of R))
variable (J : (polynomialRelativeAmbient R I s).IdealSheafData)
variable (hJ : FiniteLocallyFreeDegree (J.subschemeι ≫ pullback.fst _ _) d)

/-- Parameters for the same family agree on every common scheme test. -/
theorem polynomialSchemeAffineParameter_agree
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (a : Spec (.of S) ⟶ X)
    (ha : a ≫ s = Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (b : Spec (.of T) ⟶ X)
    (hb : b ≫ s = Spec.map (CommRingCat.ofHom (algebraMap R T)))
    {Y : Scheme.{u}} (p : Y ⟶ Spec (.of S)) (q : Y ⟶ Spec (.of T))
    (hpq : p ≫ a = q ≫ b) :
    p ≫ (polynomialSchemeAffineParameter R I d s J hJ S a ha).val =
      q ≫ (polynomialSchemeAffineParameter R I d s J hJ T b hb).val := by
  apply Scheme.Cover.hom_ext Y.affineOpenCover.openCover
  intro i
  let U := Y.affineOpenCover.X i
  let _ := polynomialCoverAlgebra R (p ≫ a ≫ s) i
  let c : Spec (.of U) ⟶ X := Y.affineOpenCover.f i ≫ p ≫ a
  have hc : c ≫ s = Spec.map (CommRingCat.ofHom (algebraMap R U)) := by
    simpa only [c, Category.assoc] using polynomialCoverAlgebra_over R (p ≫ a ≫ s) i
  rw [← Category.assoc, ← Category.assoc]
  calc
    (Y.affineOpenCover.f i ≫ p) ≫ _ =
        (polynomialSchemeAffineParameter R I d s J hJ U c hc).val :=
      polynomialSchemeAffineParameter_test R I d s J hJ S U a ha c hc _
        (Category.assoc _ _ _)
    _ = (Y.affineOpenCover.f i ≫ q) ≫ _ :=
      (polynomialSchemeAffineParameter_test R I d s J hJ T U b hb c hc _
        (by simp only [c, Category.assoc, ← hpq])).symm

/-- The actual family parameter on each canonical affine chart of the scheme base. -/
def polynomialSchemeCoverParameter (i : X.affineOpenCover.I₀) :
    Spec (X.affineOpenCover.X i) ⟶ polynomialHilbertScheme R I d := by
  let _ := polynomialCoverAlgebra R s i
  exact (polynomialSchemeAffineParameter R I d s J hJ (X.affineOpenCover.X i)
    (X.affineOpenCover.f i) (polynomialCoverAlgebra_over R s i)).val

/-- Every local family parameter retains its original base structure map. -/
theorem polynomialSchemeCoverParameter_over (i : X.affineOpenCover.I₀) :
    polynomialSchemeCoverParameter R I d s J hJ i ≫ polynomialHilbertStructure R I d =
      X.affineOpenCover.f i ≫ s := by
  let _ := polynomialCoverAlgebra R s i
  exact (polynomialSchemeAffineParameter R I d s J hJ (X.affineOpenCover.X i)
    (X.affineOpenCover.f i) (polynomialCoverAlgebra_over R s i)).property.trans
      (polynomialCoverAlgebra_over R s i).symm

/-- Canonical affine parameters agree on the actual scheme overlaps. -/
theorem polynomialSchemeCoverParameter_agree (i j : X.affineOpenCover.I₀) :
    pullback.fst (X.affineOpenCover.f i) (X.affineOpenCover.f j) ≫
        polynomialSchemeCoverParameter R I d s J hJ i =
      pullback.snd (X.affineOpenCover.f i) (X.affineOpenCover.f j) ≫
        polynomialSchemeCoverParameter R I d s J hJ j := by
  let _ := polynomialCoverAlgebra R s i
  let _ := polynomialCoverAlgebra R s j
  exact polynomialSchemeAffineParameter_agree R I d s J hJ
    (X.affineOpenCover.X i) (X.affineOpenCover.X j)
    (X.affineOpenCover.f i) (polynomialCoverAlgebra_over R s i)
    (X.affineOpenCover.f j) (polynomialCoverAlgebra_over R s j) _ _ pullback.condition

end FLT.Mazur.HilbertChart
