/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianChartTransitionCocycle

/-!
# Inverse Grassmannian overlap transitions

Changing the quotient basis constructs membership in the reverse overlap.
The reverse change recovers the original coordinates, giving actual inverse
bijections between the two overlap coordinate sets over every coefficient ring.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.GrassmannianChart
variable {S : Type*} [CommRing S] {V W : Type*}
  [AddCommGroup V] [Module S V] [AddCommGroup W] [Module S W] {d : ℕ}

/-- The coordinate transition constructs membership in the reverse overlap. -/
theorem transitionBasis_symm_bijective (A : V →ₗ[S] (Fin d → S))
    (e : ((Fin d → S) × W) ≃ₗ[S] ((Fin d → S) × V))
    (h : Function.Bijective (transitionBasis A e)) :
    Function.Bijective (transitionBasis (chartTransition A e h) e.symm) := by
  have hc : Function.Bijective ((transitionBasis A e).comp
      (transitionBasis (chartTransition A e h) e.symm)) := by
    rw [← transitionBasis_comp A e e.symm h, e.symm_trans_self, transitionBasis_refl]
    exact Function.bijective_id
  exact (h.of_comp_iff' _).mp hc

/-- The reverse transition recovers every original complementary coordinate. -/
theorem chartTransition_symm (A : V →ₗ[S] (Fin d → S))
    (e : ((Fin d → S) × W) ≃ₗ[S] ((Fin d → S) × V))
    (h : Function.Bijective (transitionBasis A e)) :
    chartTransition (chartTransition A e h) e.symm (transitionBasis_symm_bijective A e h) = A := by
  simpa only [LinearEquiv.symm_trans_self, chartTransition_refl] using
    (chartTransition_cocycle A e e.symm h (transitionBasis_symm_bijective A e h)).symm

/-- Actual inverse coordinate bijections on the double-chart domains. -/
def chartOverlapCoordinateEquiv
    (e : ((Fin d → S) × W) ≃ₗ[S] ((Fin d → S) × V)) :
    {A : V →ₗ[S] (Fin d → S) // Function.Bijective (transitionBasis A e)} ≃
      {B : W →ₗ[S] (Fin d → S) // Function.Bijective (transitionBasis B e.symm)} where
  toFun A := ⟨chartTransition A.val e A.property, transitionBasis_symm_bijective _ _ _⟩
  invFun B := ⟨chartTransition B.val e.symm B.property,
    by
      simpa only [LinearEquiv.symm_symm] using
        (transitionBasis_symm_bijective B.val e.symm B.property)⟩
  left_inv A := Subtype.ext (chartTransition_symm A.val e A.property)
  right_inv B := by
    apply Subtype.ext
    simpa only [LinearEquiv.symm_symm] using chartTransition_symm B.val e.symm B.property

end FLT.Mazur.GrassmannianChart
