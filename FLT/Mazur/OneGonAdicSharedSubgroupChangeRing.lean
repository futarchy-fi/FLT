/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicSharedSubgroupCoherence
public import FLT.Mazur.OneGonAdicSharedSubgroupTower
public import FLT.Mazur.ArithmeticOneGonCommonCoefficientChangeRing

/-!
# Change-of-common-ring coherence of actual supplied finite subgroups

Extending the shared ring commutes with the comparison between independently
supplied stages, as an equality of compatible subgroup isomorphisms.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OneGonAdicIndependentModel
open Approximation OneGonAdicCharacterTower OneGonSmoothing CharacterSchemeBaseChange
open ArithmeticOneGonGeneralizedCurve WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n] (s u : Set R)
  (K L : Subalgebra ℤ R) [Algebra.FiniteType ℤ K] [Algebra.FiniteType ℤ L]
  (hKL : K ≤ L) (hS : base I t ht n s ≤ K) (hU : base I t ht n u ≤ K)
  (hs : complementaryInverse I t ht ∈ s) (hu : complementaryInverse I t ht ∈ u)

variable (i : (CoefficientStage (base I t ht n s))ᵒᵖ)
  (j : (CoefficientStage (base I t ht n u))ᵒᵖ)
  (hi : stageBase I t ht n s i ≤ K) (hj : stageBase I t ht n u j ≤ K)
  (b : (coefficientModelDiagram (base I t ht n s) (carrier I t ht n s).hom).obj i ⟶
    (integralSmoothOpen (equation (parameter I t ht n s))).toScheme)
  (hb : b ≫ (integralSmoothOpen (equation (parameter I t ht n s))).ι =
    (coefficientModelToInitial (base I t ht n s) (carrier I t ht n s).hom).app i ≫
      embedding I t ht n s)
  (c : (coefficientModelDiagram (base I t ht n u) (carrier I t ht n u).hom).obj j ⟶
    (integralSmoothOpen (equation (parameter I t ht n u))).toScheme)
  (hc : c ≫ (integralSmoothOpen (equation (parameter I t ht n u))).ι =
    (coefficientModelToInitial (base I t ht n u) (carrier I t ht n u).hom).app j ≫
      embedding I t ht n u)
  (hφs : Function.Surjective (OneGonFiniteCoefficientCoordinates.modelCoordinates t 1
    (canonicalCoordinates I t ht n) s))
  (hφu : Function.Surjective (OneGonFiniteCoefficientCoordinates.modelCoordinates t 1
    (canonicalCoordinates I t ht n) u))

/-- The full curve comparison commutes with extension of the actual shared ring. -/
theorem sharedCurveIso_changeRing :
    (sharedCurveTowerIso I t ht n s K L hS hKL hs).hom ≫
      (GeneralizedEllipticCurve.baseChangeFunctor (sharedRingMap K L hKL)).map
        (sharedCurveIso I t ht n s u K hS hU hs hu).hom =
    (sharedCurveIso I t ht n s u L (hS.trans hKL) (hU.trans hKL) hs hu).hom ≫
      (sharedCurveTowerIso I t ht n u K L hU hKL hu).hom := by
  let _ := sharedAlgebra I t ht n s K hS
  let _ := sharedAlgebra I t ht n u K hU
  let _ := sharedAlgebra I t ht n s L (hS.trans hKL)
  let _ := sharedAlgebra I t ht n u L (hU.trans hKL)
  let _ := sharedRingAlgebra K L hKL
  let _ : IsScalarTower (base I t ht n s) K L :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let _ : IsScalarTower (base I t ht n u) K L :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  rw [sharedCurveTowerIso_def, sharedCurveTowerIso_def, sharedCurveIso_def, sharedCurveIso_def]
  exact commonCoefficientIso_changeRing (base I t ht n s) (base I t ht n u) K L
    (parameter I t ht n s) (parameter I t ht n u)
    (parameter_complementaryUnit I t ht n s hs) (parameter_complementaryUnit I t ht n u hu)
    (shared_parameter_eq I t ht n s K hS u hU)

/-- Both routes compare the entire actual subgroups, not just their underlying curves. -/
theorem sharedFiniteSubgroupIso_changeRing :
    (sharedFiniteSubgroupTowerIso I t ht n s K L hS hKL i hi b hb hs hφs).trans
      ((sharedFiniteSubgroupIso I t ht n s u K hS hU hs hu i j hi hj b hb c hc hφs hφu).baseChange
        (sharedRingMap K L hKL)) =
    (sharedFiniteSubgroupIso I t ht n s u L (hS.trans hKL) (hU.trans hKL) hs hu
      i j (hi.trans hKL) (hj.trans hKL) b hb c hc hφs hφu).trans
        (sharedFiniteSubgroupTowerIso I t ht n u K L hU hKL j hj c hc hu hφu) := by
  apply GeneralizedEllipticCurve.FiniteSubgroup.CompatibleIso.ext_curve_hom
  exact sharedCurveIso_changeRing I t ht n s u K L hKL hS hU hs hu

end FLT.Mazur.OneGonAdicIndependentModel
