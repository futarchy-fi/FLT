/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertChartIdentityIdeal
public import FLT.Mazur.HilbertBasisAffineClassification
public import FLT.Mazur.HilbertBasisSchemeOver

/-!
# Actual change of prescribed polynomial tuple

The second tuple's intrinsic basis open in the first chart carries its actual
classifying morphism to the second chart. Every affine test preserves the
entire ambient quotient ideal under this change of chart.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (I : Type u) (d : ℕ)
variable (w v : Fin d → MvPolynomial I R)

/-- Cache the coefficient ring for chart inference. -/
local instance transitionCoefficientsRing : CommRing (Coefficients R I d) := inferInstance
/-- Cache the source chart ring for scheme inference. -/
local instance transitionSourceRing : CommRing (ChartRing R I d w) := inferInstance
/-- Cache the target chart ring for scheme inference. -/
local instance transitionTargetRing : CommRing (ChartRing R I d v) := inferInstance

/-- The actual open in the first chart where the second prescribed tuple is a basis. -/
def chartTupleTransitionOpen : (Spec (.of (ChartRing R I d w))).Opens :=
  polynomialBasisOpen R I d v (ChartRing R I d w) (chartIdentityIdeal R I d w)

/-- The actual change-of-tuple morphism, obtained by classifying the universal ambient ideal. -/
def chartTupleTransition :
    (chartTupleTransitionOpen R I d w v).toScheme ⟶ Spec (.of (ChartRing R I d v)) :=
  intrinsicChartMorphism R I d v (ChartRing R I d w) (chartIdentityIdeal R I d w)

/-- The change-of-tuple morphism respects the original base scheme. -/
theorem chartTupleTransition_over :
    chartTupleTransition R I d w v ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (ChartRing R I d v))) =
    (chartTupleTransitionOpen R I d w v).ι ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (ChartRing R I d w))) :=
  intrinsicChartMorphism_over R I d v (ChartRing R I d w) (chartIdentityIdeal R I d w)

/-- On every affine test, changing tuple preserves the actual ambient ideal. -/
theorem chartTupleTransition_affineTest {S : Type u} [CommRing S] [Algebra R S]
    (f : ChartRing R I d w →ₐ[R] S)
    (g : Spec (.of S) ⟶ (chartTupleTransitionOpen R I d w v).toScheme)
    (hg : g ≫ (chartTupleTransitionOpen R I d w v).ι =
      Spec.map (CommRingCat.ofHom f.toRingHom)) :
    ∃ a : ChartRing R I d v →ₐ[R] S,
      g ≫ chartTupleTransition R I d w v = Spec.map (CommRingCat.ofHom a.toRingHom) ∧
        pointIdeal R I d v a = pointIdeal R I d w f := by
  let _ := pointScalars R I d w f
  let _ := pointTower R I d w f
  have hf : ∃! k : Spec (.of S) ⟶ polynomialBasisScheme R I d v
      (ChartRing R I d w) (chartIdentityIdeal R I d w),
      k ≫ (chartTupleTransitionOpen R I d w v).ι =
        Spec.map (CommRingCat.ofHom (algebraMap (ChartRing R I d w) S)) := by
    refine ⟨g, hg, fun k hk ↦ ?_⟩
    exact (cancel_mono (chartTupleTransitionOpen R I d w v).ι).mp (hk.trans hg.symm)
  have hb := (polynomialBasisScheme_affineFactorization_iff R I d v
    (ChartRing R I d w) (chartIdentityIdeal R I d w) S).mp hf
  let J : PrescribedBasisIdeals R I d v S :=
    ⟨(chartIdentityIdeal R I d w).map
      (MvPolynomial.map (algebraMap (ChartRing R I d w) S)), hb⟩
  refine ⟨idealClassifyingMap R I d v S J, ?_, ?_⟩
  · exact intrinsicChartMorphism_affineTest R I d v (ChartRing R I d w)
      (chartIdentityIdeal R I d w) S hb g hg
  · exact (congrArg Subtype.val (idealOfPoint_idealClassifyingMap R I d v S J)).trans
      (chartIdentityIdeal_map R I d w f)

/-- Ideal preservation uniquely identifies the parameter after changing tuple. -/
theorem chartTupleTransition_affineTest_eq {S : Type u} [CommRing S] [Algebra R S]
    (f : ChartRing R I d w →ₐ[R] S)
    (g : Spec (.of S) ⟶ (chartTupleTransitionOpen R I d w v).toScheme)
    (hg : g ≫ (chartTupleTransitionOpen R I d w v).ι =
      Spec.map (CommRingCat.ofHom f.toRingHom))
    (a : ChartRing R I d v →ₐ[R] S) (ha : pointIdeal R I d v a = pointIdeal R I d w f) :
    g ≫ chartTupleTransition R I d w v = Spec.map (CommRingCat.ofHom a.toRingHom) := by
  obtain ⟨a', h, hi⟩ := chartTupleTransition_affineTest R I d w v f g hg
  have he := pointIdeal_injective R I d v S (hi.trans ha.symm)
  exact h.trans (congrArg (fun q : ChartRing R I d v →ₐ[R] S ↦
    Spec.map (CommRingCat.ofHom q.toRingHom)) he)

end FLT.Mazur.HilbertChart
