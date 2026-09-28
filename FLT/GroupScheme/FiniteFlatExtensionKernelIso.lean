/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.GroupScheme.FiniteFlatIso
public import FLT.GroupScheme.ReverseExtHypothesis

/-!
# Replacing the kernel of an integral extension

An integral isomorphism of kernels transports the full extension, including
its torsor comparison and the formula for its second coordinate. The middle
model and its faithfully flat quotient remain the specified ones.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace ThreeAdicPlan

variable {R : Type} [CommRing R] [Algebra R ℚ]

/-- Replace the kernel through an integral isomorphism, retaining the quotient torsor. -/
def FiniteFlatExtension.transportKernel {A B H Q : FiniteFlatObject R}
    (E : FiniteFlatExtension A H Q) (e : A.Iso B) : FiniteFlatExtension B H Q where
  inclusion := e.symm.toBialgHom.comp E.inclusion
  quotient := E.quotient
  compositionZero := by
    change e.symm.toAlgEquiv.toAlgHom.comp
      (E.inclusion.toAlgHom.comp E.quotient.toAlgHom) = _
    rw [E.compositionZero]
    ext x
    exact e.symm.toAlgEquiv.commutes _
  pointsInjective := by
    intro a b hab
    apply (FiniteFlatObject.pointMap_bijective e.symm).1
    apply E.pointsInjective
    simpa only [FiniteFlatObject.pointMap_comp] using hab
  pointsSurjective := E.pointsSurjective
  pointsExact := by
    intro h
    rw [E.pointsExact]
    constructor
    · rintro ⟨a, ha⟩
      obtain ⟨b, hb⟩ := (FiniteFlatObject.pointMap_bijective e.symm).2 a
      exact ⟨b, by rw [FiniteFlatObject.pointMap_comp, hb, ha]⟩
    · rintro ⟨b, hb⟩
      exact ⟨FiniteFlatObject.pointMap e.symm.toBialgHom b,
        (FiniteFlatObject.pointMap_comp _ _ _).symm.trans hb⟩
  quotientFaithfullyFlat := E.quotientFaithfullyFlat
  torsorEquiv := E.torsorEquiv.trans
    (Algebra.TensorProduct.congr (AlgEquiv.refl : H.model.CoordinateRing ≃ₐ[
      H.model.CoordinateRing] H.model.CoordinateRing) e.symm.toAlgEquiv)
  torsorEquivSecond := by
    let quotientAlgebra := E.quotient.toAlgHom.toRingHom.toAlgebra
    intro b
    change Algebra.TensorProduct.congr _ _ (E.torsorEquiv (1 ⊗ₜ[Q.model.CoordinateRing] b)) = _
    rw [E.torsorEquivSecond, Algebra.TensorProduct.congr_apply]
    exact AlgHom.congr_fun (Algebra.TensorProduct.map_id_comp (S := R)
      (A := H.model.CoordinateRing) e.symm.toAlgEquiv.toAlgHom E.inclusion.toAlgHom).symm _

end ThreeAdicPlan
