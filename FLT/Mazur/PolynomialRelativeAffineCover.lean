/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolynomialRelativeAffineChart
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-!
# A polynomial spectrum cover over every scheme base

The canonical affine cover of the base induces an actual cover by polynomial
spectra of its relative polynomial space. The coefficient algebras are read
from the original structure map, not supplied as extra data.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R]
variable {X : Scheme.{u}} (s : X ⟶ Spec (.of R))

/-- The coefficient-ring algebra on each canonical affine chart of the scheme base. -/
@[instance_reducible]
def polynomialCoverAlgebra (i : X.affineOpenCover.I₀) :
    Algebra R (X.affineOpenCover.X i) :=
  (Spec.preimage (X.affineOpenCover.f i ≫ s)).hom.toAlgebra

/-- The affine chart's coefficient algebra recovers its actual structure map. -/
theorem polynomialCoverAlgebra_over (i : X.affineOpenCover.I₀) :
    let _ := polynomialCoverAlgebra R s i
    X.affineOpenCover.f i ≫ s =
      Spec.map (CommRingCat.ofHom (algebraMap R (X.affineOpenCover.X i))) :=
  (Spec.map_preimage _).symm

/-- The polynomial spectrum above each base chart maps into the relative ambient space. -/
def polynomialRelativeCoverChart (i : X.affineOpenCover.I₀) :
    Spec (.of (MvPolynomial I (X.affineOpenCover.X i))) ⟶ polynomialRelativeAmbient R I s := by
  let _ := polynomialCoverAlgebra R s i
  exact polynomialRelativeAffineChart R I s (X.affineOpenCover.X i)
    (X.affineOpenCover.f i) (polynomialCoverAlgebra_over R s i)

/-- The polynomial chart is the full inverse image of its original base chart. -/
theorem polynomialRelativeCoverChart_isPullback (i : X.affineOpenCover.I₀) :
    IsPullback (polynomialRelativeCoverChart R I s i)
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C (R := X.affineOpenCover.X i) (σ := I))))
      (pullback.fst _ _) (X.affineOpenCover.f i) := by
  let _ := polynomialCoverAlgebra R s i
  exact polynomialRelativeAffineChart_isPullback R I s (X.affineOpenCover.X i)
    (X.affineOpenCover.f i) (polynomialCoverAlgebra_over R s i)

/-- Every polynomial cover chart is an open immersion into the relative ambient scheme. -/
instance polynomialRelativeCoverChart_isOpenImmersion (i : X.affineOpenCover.I₀) :
    IsOpenImmersion (polynomialRelativeCoverChart R I s i) :=
  MorphismProperty.of_isPullback (polynomialRelativeCoverChart_isPullback R I s i).flip
    (inferInstanceAs (IsOpenImmersion (X.affineOpenCover.f i)))

/-- Actual polynomial spectra form an affine open cover of relative polynomial space. -/
def polynomialRelativeAffineCover : (polynomialRelativeAmbient R I s).OpenCover where
  I₀ := X.affineOpenCover.I₀
  X i := Spec (.of (MvPolynomial I (X.affineOpenCover.X i)))
  f i := polynomialRelativeCoverChart R I s i
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun i ↦ inferInstance⟩
    let C := X.affineOpenCover.openCover.pullback₁
      (pullback.fst s (Spec.map (CommRingCat.ofHom (MvPolynomial.C (R := R) (σ := I)))))
    obtain ⟨i, y, hy⟩ := Scheme.Cover.exists_eq C x
    let q := polynomialRelativeCoverChart_isPullback R I s i
    refine ⟨i, q.isoPullback.inv y, ?_⟩
    exact (congrArg (fun f ↦ f y) q.isoPullback_inv_fst).trans hy

/-- Each member of the constructed relative polynomial cover is affine. -/
instance polynomialRelativeAffineCover_isAffine (i : X.affineOpenCover.I₀) :
    IsAffine ((polynomialRelativeAffineCover R I s).X i) :=
  inferInstanceAs (IsAffine (Spec (.of (MvPolynomial I (X.affineOpenCover.X i)))))

end FLT.Mazur.HilbertChart
