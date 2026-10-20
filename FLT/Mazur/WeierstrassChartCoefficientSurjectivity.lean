/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassChartCoefficientRingMap

/-!
# Surjective coefficient maps on the full normalized cubic chart

A surjective base map induces a surjection of the entire chart algebra,
including both the cubic relation and the normalization relation.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R S : Type*} [CommRing R] [CommRing S]
  (f : R →+* S) (W : WeierstrassCurve R) (j : Fin 3)

/-- The coefficient comparison commutes with the full polynomial quotient. -/
theorem chartCoefficientRingMap_quotient :
    (chartCoefficientRingMap f W j).comp (Ideal.Quotient.mk (relations W j)) =
      (Ideal.Quotient.mk (relations (W.map f) j)).comp (MvPolynomial.map f) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, MvPolynomial.map_C]
    simpa only [← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap] using
      chartCoefficientRingMap_scalar f W j a
  · intro i
    simpa only [RingHom.comp_apply, MvPolynomial.map_X, coord] using
      chartCoefficientRingMap_coord f W j i

/-- Surjectivity of coefficients gives surjectivity on the complete original chart. -/
theorem chartCoefficientRingMap_surjective (hf : Function.Surjective f) :
    Function.Surjective (chartCoefficientRingMap f W j) := by
  have h : Function.Surjective
      ((Ideal.Quotient.mk (relations (W.map f) j)).comp (MvPolynomial.map f)) :=
    Ideal.Quotient.mk_surjective.comp (MvPolynomial.map_surjective f hf)
  rw [← chartCoefficientRingMap_quotient] at h
  intro y
  obtain ⟨p, hp⟩ := h y
  exact ⟨Ideal.Quotient.mk (relations W j) p, hp⟩

/-- Transport to the specified target cubic retains full coordinate surjectivity. -/
theorem chartCoefficientRingMapTo_surjective (hf : Function.Surjective f)
    (U : WeierstrassCurve S) (hW : W.map f = U) :
    Function.Surjective (chartCoefficientRingMapTo f W j U hW) := by
  subst U
  exact chartCoefficientRingMap_surjective f W j hf

end FLT.Mazur.WeierstrassIntegralChart
