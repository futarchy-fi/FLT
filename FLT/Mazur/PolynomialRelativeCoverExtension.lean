/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolynomialRelativeAffineCover

/-!
# Polynomial ambient covers above arbitrary affine base covers

Every affine open cover of a scheme induces a polynomial spectrum cover of
its relative ambient space. This permits simultaneous refinement by the base
and by Hilbert parameter charts when detecting full ambient containments.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R]
variable {X : Scheme.{u}} (s : X ⟶ Spec (.of R)) (C : X.AffineOpenCover)

/-- Recover coefficient algebras from the actual maps of an arbitrary affine cover. -/
@[instance_reducible]
def polynomialAffineCoverAlgebra (i : C.I₀) : Algebra R (C.X i) :=
  (Spec.preimage (C.f i ≫ s)).hom.toAlgebra

/-- The recovered coefficient map is the original affine covering structure map. -/
theorem polynomialAffineCoverAlgebra_over (i : C.I₀) :
    let _ := polynomialAffineCoverAlgebra R s C i
    C.f i ≫ s = Spec.map (CommRingCat.ofHom (algebraMap R (C.X i))) :=
  (Spec.map_preimage _).symm

/-- The polynomial spectrum above an arbitrary affine base chart maps to the relative ambient. -/
def polynomialAffineCoverChart (i : C.I₀) :
    Spec (.of (MvPolynomial I (C.X i))) ⟶ polynomialRelativeAmbient R I s := by
  let _ := polynomialAffineCoverAlgebra R s C i
  exact polynomialRelativeAffineChart R I s (C.X i) (C.f i)
    (polynomialAffineCoverAlgebra_over R s C i)

/-- The polynomial chart is cartesian over its original affine cover chart. -/
theorem polynomialAffineCoverChart_isPullback (i : C.I₀) :
    IsPullback (polynomialAffineCoverChart R I s C i)
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C (R := C.X i) (σ := I))))
      (pullback.fst _ _) (C.f i) := by
  let _ := polynomialAffineCoverAlgebra R s C i
  exact polynomialRelativeAffineChart_isPullback R I s (C.X i) (C.f i)
    (polynomialAffineCoverAlgebra_over R s C i)

/-- The induced ambient chart is an open immersion. -/
instance polynomialAffineCoverChart_isOpenImmersion (i : C.I₀) :
    IsOpenImmersion (polynomialAffineCoverChart R I s C i) :=
  MorphismProperty.of_isPullback (polynomialAffineCoverChart_isPullback R I s C i).flip
    (inferInstanceAs (IsOpenImmersion (C.f i)))

/-- An arbitrary affine cover induces a cover by actual polynomial spectra. -/
def polynomialAffineCoverExtension : (polynomialRelativeAmbient R I s).OpenCover where
  I₀ := C.I₀
  X i := Spec (.of (MvPolynomial I (C.X i)))
  f i := polynomialAffineCoverChart R I s C i
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun i ↦ inferInstance⟩
    let D := C.openCover.pullback₁
      (pullback.fst s (Spec.map (CommRingCat.ofHom (MvPolynomial.C (R := R) (σ := I)))))
    obtain ⟨i, y, hy⟩ := Scheme.Cover.exists_eq D x
    let q := polynomialAffineCoverChart_isPullback R I s C i
    refine ⟨i, q.isoPullback.inv y, ?_⟩
    exact (congrArg (fun f ↦ f y) q.isoPullback_inv_fst).trans hy

end FLT.Mazur.HilbertChart
