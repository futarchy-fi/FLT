/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertChartParameterRecovery

/-!
# Classification is invariant under ambient algebra isomorphisms

An isomorphism commuting with the ambient generators carries the prescribed
polynomial basis to the prescribed polynomial basis. Consequently it preserves
the extracted coefficient and chart maps.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.HilbertChart

universe u v

variable (R : Type u) [CommRing R] (I : Type v) (d : ℕ)
variable {S A B : Type*} [CommRing S] [CommRing A] [CommRing B]
variable [Algebra R S] [Algebra S A] [Algebra S B]
variable [Algebra R A] [IsScalarTower R S A] [Algebra R B] [IsScalarTower R S B]
variable (v : Module.Basis (Fin d) S A) (v' : Module.Basis (Fin d) S B)
variable (x : I → A) (x' : I → B) (e : A ≃ₐ[S] B)

omit [Algebra R S] [Algebra R A] [IsScalarTower R S A]
  [Algebra R B] [IsScalarTower R S B] in
/-- Coordinates are unchanged by an isomorphism carrying the actual bases. -/
theorem repr_equiv_of_basis (hv : ∀ i, e (v i) = v' i) (a : A) :
    v'.repr (e a) = v.repr a := by
  have h : v'.repr.toLinearMap.comp e.toLinearMap = v.repr.toLinearMap := by
    apply v.ext
    intro i
    change v'.repr (e (v i)) = v.repr (v i)
    rw [hv, Module.Basis.repr_self, Module.Basis.repr_self]
  exact LinearMap.congr_fun h a

omit [Algebra R A] [IsScalarTower R S A] [Algebra R B] [IsScalarTower R S B] in
/-- Basis- and generator-preserving isomorphisms preserve every extracted parameter. -/
theorem readCoefficients_equiv (hv : ∀ i, e (v i) = v' i) (hx : ∀ i, e (x i) = x' i) :
    readCoefficients R I d v x = readCoefficients R I d v' x' := by
  apply coefficientMap_ext
  · intro i j k
    rw [readCoefficients_mul, readCoefficients_mul]
    change v.repr (v i * v j) k = v'.repr (v' i * v' j) k
    rw [← hv, ← hv, ← map_mul e, repr_equiv_of_basis d v v' e hv]
  · intro k
    rw [readCoefficients_unit, readCoefficients_unit]
    change v.repr 1 k = v'.repr 1 k
    rw [← map_one e, repr_equiv_of_basis d v v' e hv]
  · intro i k
    rw [readCoefficients_generator, readCoefficients_generator]
    rw [← hx, repr_equiv_of_basis d v v' e hv]

variable (w : Fin d → MvPolynomial I R)
variable (hw : ∀ i, MvPolynomial.aeval x (w i) = v i)
variable (hw' : ∀ i, MvPolynomial.aeval x' (w i) = v' i)

include hw hw' in
/-- Ambient-compatible isomorphisms automatically preserve the prescribed basis. -/
theorem equiv_prescribed_basis (hx : ∀ i, e (x i) = x' i) (i : Fin d) :
    e (v i) = v' i := by
  rw [← hw, ← hw']
  have h := MvPolynomial.comp_aeval_apply x (e.toAlgHom.restrictScalars R) (w i)
  simpa only [AlgHom.restrictScalars_apply, AlgEquiv.coe_toAlgHom, hx] using h

/-- The chart map of a quotient depends only on its ambient isomorphism class. -/
theorem classifyingMap_equiv (hx : ∀ i, e (x i) = x' i) :
    classifyingMap R I d v x w hw = classifyingMap R I d v' x' w hw' := by
  apply Ideal.Quotient.algHom_ext
  apply AlgHom.ext
  intro a
  change readCoefficients R I d v x a = readCoefficients R I d v' x' a
  exact AlgHom.congr_fun (readCoefficients_equiv R I d v v' x x' e
    (equiv_prescribed_basis R I d v v' x x' e w hw hw' hx) hx) a

end FLT.Mazur.HilbertChart
