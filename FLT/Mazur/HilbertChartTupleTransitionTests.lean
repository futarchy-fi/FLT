/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertChartTupleTransition

/-!
# Affine tests and identity law for change of tuple

The transition domain is precisely where the second tuple forms a basis of
the first parameter's actual quotient. Changing a tuple to itself is the
identity on the full chart.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (I : Type u) (d : ℕ)
variable (w v : Fin d → MvPolynomial I R)

/-- Cache the coefficient ring for chart inference. -/
local instance transitionTestsCoefficientsRing : CommRing (Coefficients R I d) := inferInstance
/-- Cache the first chart ring for quotient inference. -/
local instance transitionTestsChartRing : CommRing (ChartRing R I d w) := inferInstance

/-- The transition domain tests the second basis in the actual ideal of the first parameter. -/
theorem chartTupleTransition_factorization_iff {S : Type u} [CommRing S] [Algebra R S]
    (f : ChartRing R I d w →ₐ[R] S) :
    (∃! g : Spec (.of S) ⟶ (chartTupleTransitionOpen R I d w v).toScheme,
      g ≫ (chartTupleTransitionOpen R I d w v).ι =
        Spec.map (CommRingCat.ofHom f.toRingHom)) ↔
    ∃ b : Module.Basis (Fin d) S (MvPolynomial I S ⧸ pointIdeal R I d w f),
      ∀ i, polynomialBasisTuple R I d v S (pointIdeal R I d w f) i = b i := by
  let _ := pointScalars R I d w f
  let _ := pointTower R I d w f
  have h := polynomialBasisScheme_affineFactorization_iff R I d v
    (ChartRing R I d w) (chartIdentityIdeal R I d w) S
  have he : (chartIdentityIdeal R I d w).map
      (MvPolynomial.map (algebraMap (ChartRing R I d w) S)) = pointIdeal R I d w f :=
    chartIdentityIdeal_map R I d w f
  rw [he] at h
  exact h

/-- The transition from a tuple to itself is defined on the entire chart. -/
theorem chartTupleTransitionOpen_self : chartTupleTransitionOpen R I d w w = ⊤ := by
  apply (intrinsicBasisOpen_eq_top_iff (R := ChartRing R I d w) _).mpr
  obtain ⟨b, hb⟩ := (idealOfPoint R I d w
    (S := ChartRing R I d w) (AlgHom.id R (ChartRing R I d w))).property
  exact ⟨b, fun i ↦ (hb i).symm⟩

/-- Changing a prescribed tuple to itself is the inclusion of its full domain. -/
theorem chartTupleTransition_self :
    chartTupleTransition R I d w w = (chartTupleTransitionOpen R I d w w).ι := by
  let _ : Module.FinitePresentation (ChartRing R I d w)
      (MvPolynomial I (ChartRing R I d w) ⧸
        (idealOfPoint R I d w (S := ChartRing R I d w)
          (AlgHom.id R (ChartRing R I d w))).val) :=
    inferInstanceAs (Module.FinitePresentation (ChartRing R I d w)
      (MvPolynomial I (ChartRing R I d w) ⧸ chartIdentityIdeal R I d w))
  have h := intrinsicChartMorphism_global R I d w (ChartRing R I d w)
    (idealOfPoint R I d w (S := ChartRing R I d w) (AlgHom.id R (ChartRing R I d w)))
  rw [idealClassifyingMap_idealOfPoint R I d w (ChartRing R I d w)
    (AlgHom.id R (ChartRing R I d w))] at h
  have hid : Spec.map (CommRingCat.ofHom (R := ChartRing R I d w)
      (S := ChartRing R I d w) (AlgHom.id R (ChartRing R I d w)).toRingHom) =
      𝟙 (Spec (.of (ChartRing R I d w))) := Spec.map_id _
  rw [hid, Category.comp_id] at h
  exact h

end FLT.Mazur.HilbertChart
