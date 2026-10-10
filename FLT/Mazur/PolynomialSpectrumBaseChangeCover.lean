/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Polynomial spectra above an affine open cover

Polynomial extension commutes with arbitrary coefficient base change. An
open cover by coefficient spectra therefore induces an open cover by the
actual polynomial spectra, with no tensor-product presentation in its maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (S I : Type u) [CommRing S]

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- The polynomial spectrum square is cartesian under arbitrary coefficient extension. -/
theorem polynomialSpectrum_isPullback (T : Type u) [CommRing T] [Algebra S T] :
    IsPullback (Spec.map (CommRingCat.ofHom (MvPolynomial.C (R := T) (σ := I))))
      (Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := I) (algebraMap S T))))
      (Spec.map (CommRingCat.ofHom (algebraMap S T)))
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C (R := S) (σ := I)))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout S T (MvPolynomial I S) (MvPolynomial I T))

variable {ι : Type u} (T : ι → Type u) [∀ i, CommRing (T i)] [∀ i, Algebra S (T i)]
variable [∀ i, IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap S (T i))))]

/-- An open coefficient spectrum inclusion induces an open polynomial spectrum inclusion. -/
instance polynomialSpectrumMap_isOpenImmersion (i : ι) :
    IsOpenImmersion (Spec.map
      (CommRingCat.ofHom (MvPolynomial.map (σ := I) (algebraMap S (T i))))) :=
  MorphismProperty.of_isPullback (polynomialSpectrum_isPullback S I (T i))
    (inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap S (T i))))))

/-- An affine spectrum cover induces the cover by the actual extended polynomial spectra. -/
def polynomialSpectrumCover
    (h : ∀ x : Spec (.of S), ∃ i, ∃ y : Spec (.of (T i)),
      Spec.map (CommRingCat.ofHom (algebraMap S (T i))) y = x) :
    (Spec (.of (MvPolynomial I S))).OpenCover where
  I₀ := ι
  X i := Spec (.of (MvPolynomial I (T i)))
  f i := Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := I) (algebraMap S (T i))))
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun i ↦ inferInstance⟩
    let C : (Spec (.of S)).OpenCover :=
      { I₀ := ι
        X i := Spec (.of (T i))
        f i := Spec.map (CommRingCat.ofHom (algebraMap S (T i)))
        mem₀ := by
          rw [Scheme.presieve₀_mem_precoverage_iff]
          exact ⟨h, fun i ↦ inferInstance⟩ }
    let D := C.pullback₁
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C (R := S) (σ := I))))
    obtain ⟨i, y, hy⟩ := Scheme.Cover.exists_eq D x
    let q := (polynomialSpectrum_isPullback S I (T i)).flip
    refine ⟨i, q.isoPullback.inv y, ?_⟩
    exact (congrArg (fun f ↦ f y) q.isoPullback_inv_fst).trans hy

end FLT.Mazur.HilbertChart
