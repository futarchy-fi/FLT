/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityResidueBoundary

/-!
# The full infinity boundary is the torus punctured at one

Inverting the actual Z/Y function is equivalent to inverting T-1, over
arbitrary coefficient rings and their algebras. This identifies the whole
boundary, including nilpotents, rather than only its geometric points.
-/

@[expose] public noncomputable section
open IsLocalRing AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [CommRing K] (a : Kˣ)

/-- The original normalized Z function is a unit exactly when T-1 is a unit. -/
theorem splitNodalLaurentZ_isUnit_iff {A : Type*} [CommRing A]
    (f : K[T;T⁻¹] →+* A) :
    IsUnit (f (splitNodalLaurentZ a)) ↔ IsUnit (f (LaurentPolynomial.T 1 - 1)) := by
  have hc := ((a⁻¹).isUnit.map (algebraMap K K[T;T⁻¹])).map f
  have ht := (LaurentPolynomial.isUnit_T (R := K) (-1)).map f
  simp only [splitNodalLaurentZ, splitNodalLaurentX, map_mul, map_pow]
  rw [(Commute.all _ _).isUnit_mul_iff, isUnit_pow_iff (by decide : 3 ≠ 0),
    (Commute.all _ _).isUnit_mul_iff]
  simp only [hc, ht, true_and, and_true]

/-- The Laurent torus with the value one removed. -/
abbrev LaurentPuncture (K : Type u) [CommRing K] :=
  Localization.Away (LaurentPolynomial.T 1 - 1 : K[T;T⁻¹])

/-- The full Z-localization maps to the torus punctured at one. -/
def splitNodalLaurentBoundaryForward : Localization.Away (splitNodalLaurentZ a) →ₐ[K[T;T⁻¹]]
    LaurentPuncture K :=
  IsLocalization.Away.liftAlgHom (splitNodalLaurentZ a)
    (f := Algebra.ofId K[T;T⁻¹] (LaurentPuncture K)) ((splitNodalLaurentZ_isUnit_iff a
    (algebraMap K[T;T⁻¹] (LaurentPuncture K))).mpr (IsLocalization.Away.algebraMap_isUnit _))

/-- The punctured torus maps back to the entire original Z-localization. -/
def splitNodalLaurentBoundaryBackward : LaurentPuncture K →ₐ[K[T;T⁻¹]]
    Localization.Away (splitNodalLaurentZ a) :=
  IsLocalization.Away.liftAlgHom (LaurentPolynomial.T 1 - 1 : K[T;T⁻¹])
    (f := Algebra.ofId K[T;T⁻¹] (Localization.Away (splitNodalLaurentZ a)))
    ((splitNodalLaurentZ_isUnit_iff a
    (algebraMap K[T;T⁻¹] (Localization.Away (splitNodalLaurentZ a)))).mp
      (IsLocalization.Away.algebraMap_isUnit _))

/-- The entire boundary algebra is the Laurent torus punctured at one. -/
def splitNodalLaurentBoundaryEquiv : Localization.Away (splitNodalLaurentZ a) ≃ₐ[K[T;T⁻¹]]
    LaurentPuncture K :=
  AlgEquiv.ofAlgHom (splitNodalLaurentBoundaryForward a) (splitNodalLaurentBoundaryBackward a)
    (by
      apply IsLocalization.algHom_ext (Submonoid.powers (LaurentPolynomial.T 1 - 1 : K[T;T⁻¹]))
      exact Subsingleton.elim _ _)
    (by
      apply IsLocalization.algHom_ext (Submonoid.powers (splitNodalLaurentZ a))
      exact Subsingleton.elim _ _)

/-- The puncture comparison retains the restrictions of every Laurent function. -/
theorem splitNodalLaurentBoundaryEquiv_base (f : K[T;T⁻¹]) :
    splitNodalLaurentBoundaryEquiv a
      (algebraMap K[T;T⁻¹] (Localization.Away (splitNodalLaurentZ a)) f) =
        algebraMap K[T;T⁻¹] (LaurentPuncture K) f :=
  (splitNodalLaurentBoundaryEquiv a).commutes f

variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (hdepth : 0 < depth)

/-- The full original residue boundary is the actual punctured Laurent torus. -/
def infinityResiduePunctureEquiv : InfinityResidueBoundary D hdepth ≃ₐ[(ResidueField R)[T;T⁻¹]]
    LaurentPuncture (ResidueField R) := by
  unfold InfinityResidueBoundary
  rw [infinityResidueBoundaryFunction_eq]
  exact splitNodalLaurentBoundaryEquiv (WeierstrassDilatation.residueTangentUnit D)

/-- The puncture comparison retains every Laurent function on the original boundary. -/
theorem infinityResiduePunctureEquiv_base (f : (ResidueField R)[T;T⁻¹]) :
    infinityResiduePunctureEquiv D hdepth
      (algebraMap (ResidueField R)[T;T⁻¹] (InfinityResidueBoundary D hdepth) f) =
        algebraMap (ResidueField R)[T;T⁻¹] (LaurentPuncture (ResidueField R)) f :=
  (infinityResiduePunctureEquiv D hdepth).commutes f

end FLT.Mazur.WeierstrassIntegralChart
