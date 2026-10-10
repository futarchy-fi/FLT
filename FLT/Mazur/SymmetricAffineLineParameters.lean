/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem

/-!
# Coefficient parameters for unordered points on the affine line

Elementary symmetric polynomials give an actual morphism from ordered root
coordinates to coefficient affine space. Every invariant polynomial, and every
algebra map whose image is invariant, factors uniquely through the coefficient
map. This is the affine coordinate step, not a global curve quotient construction.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.SymmetricAffineLine

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The coefficient map sends the `i`-th coefficient coordinate to `e_(i+1)`. -/
def coefficientMap : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R :=
  (MvPolynomial.symmetricSubalgebra (Fin n) R).val.comp
    (MvPolynomial.esymmAlgEquiv (Fin n) R (Fintype.card_fin n)).toAlgHom

/-- The actual ordered-root to coefficient-parameter morphism. -/
def parameterMap : Spec (CommRingCat.of (MvPolynomial (Fin n) R)) ⟶
    Spec (CommRingCat.of (MvPolynomial (Fin n) R)) :=
  Spec.map (CommRingCat.ofHom (coefficientMap R n).toRingHom)

/-- No polynomial relation is introduced between the coefficient coordinates. -/
theorem coefficientMap_injective : Function.Injective (coefficientMap R n) :=
  Subtype.val_injective.comp (MvPolynomial.esymmAlgEquiv (Fin n) R (Fintype.card_fin n)).injective

/-- Every coefficient polynomial is invariant under permuting the ordered roots. -/
theorem coefficientMap_isSymmetric (p : MvPolynomial (Fin n) R) :
    (coefficientMap R n p).IsSymmetric :=
  (MvPolynomial.esymmAlgEquiv (Fin n) R (Fintype.card_fin n) p).property

/-- Every invariant polynomial has a unique expression in the coefficient coordinates. -/
theorem isSymmetric_iff_existsUnique (p : MvPolynomial (Fin n) R) :
    p.IsSymmetric ↔ ∃! q, coefficientMap R n q = p := by
  constructor
  · intro hp
    let e := MvPolynomial.esymmAlgEquiv (Fin n) R (Fintype.card_fin n)
    refine ⟨e.symm ⟨p, hp⟩, ?_, fun q hq ↦ coefficientMap_injective R n ?_⟩
    · exact congrArg Subtype.val (e.apply_symm_apply ⟨p, hp⟩)
    · exact hq.trans (congrArg Subtype.val (e.apply_symm_apply ⟨p, hp⟩)).symm
  · rintro ⟨q, rfl, _⟩
    exact coefficientMap_isSymmetric R n q

variable {A : Type u} [CommRing A] [Algebra R A]

/-- Invariant algebra maps factor uniquely through the actual coefficient map. -/
theorem invariantMap_existsUnique (φ : A →ₐ[R] MvPolynomial (Fin n) R)
    (hφ : ∀ a, (φ a).IsSymmetric) :
    ∃! ψ : A →ₐ[R] MvPolynomial (Fin n) R, (coefficientMap R n).comp ψ = φ := by
  let e := MvPolynomial.esymmAlgEquiv (Fin n) R (Fintype.card_fin n)
  let ψ := e.symm.toAlgHom.comp (φ.codRestrict _ hφ)
  have he : (coefficientMap R n).comp ψ = φ := by
    apply AlgHom.ext
    intro a
    exact congrArg Subtype.val (e.apply_symm_apply ⟨φ a, hφ a⟩)
  refine ⟨ψ, he, fun ψ' hψ' ↦ ?_⟩
  apply AlgHom.ext
  intro a
  apply coefficientMap_injective R n
  exact congrArg (fun h : A →ₐ[R] MvPolynomial (Fin n) R ↦ h a) (hψ'.trans he.symm)

end FLT.Mazur.SymmetricAffineLine
