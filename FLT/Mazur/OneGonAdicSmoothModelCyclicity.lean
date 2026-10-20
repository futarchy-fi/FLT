/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicSmoothModelSubgroup
public import FLT.Mazur.RootsOfUnitySubgroupCyclicity
public import FLT.Mazur.GeneralizedCurveCartierDescent

/-!
# Cyclicity of the actual finite coefficient subgroup

The intrinsic character generator retains its torsion relation and full
orbit product. The cyclotomic fppf cover proves cyclicity of the descended
subgroup on the same generalized curve, with its entire Cartier ideal.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace FLT.Mazur.OneGonAdicCharacterTower

open WeierstrassIntegralChart OneGonSmoothing

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n]

instance smoothModelGroup_relativeDimension :
    SmoothOfRelativeDimension 1 (smoothModelCurve I t ht n).group.hom := by
  let _ : SmoothOfRelativeDimension 1 (algebraicCurve I t ht n).group.hom :=
    integralSmoothStructure_relativeDimension (equation (algebraicParameter I t ht n))
  exact MorphismProperty.pullback_snd _ _ inferInstance

/-- The specialized root is a section of the actual descended subgroup. -/
def smoothModelGenerator
    (φ : IntegralCyclotomicCoordinates.Coordinate n →+* smoothModelBase I t ht n) :
    𝟙_ (Over (Spec (.of (smoothModelBase I t ht n)))) ⟶
      (smoothModelFiniteSubgroup I t ht n).carrier :=
  (smoothModelFiniteSubgroup I t ht n).rootsGenerator (smoothModelCharacterIso I t ht n) φ

/-- The actual descended generator retains its full torsion relation. -/
theorem smoothModelGenerator_pow
    (φ : IntegralCyclotomicCoordinates.Coordinate n →+* smoothModelBase I t ht n) :
    smoothModelGenerator I t ht n φ ^ n = 1 :=
  (smoothModelFiniteSubgroup I t ht n).rootsGenerator_pow (smoothModelCharacterIso I t ht n) φ

/-- Its full intrinsic orbit product vanishes, retaining nilpotents and repeated sections. -/
theorem smoothModelGenerator_intrinsic_orbit
    (φ : IntegralCyclotomicCoordinates.Coordinate n →+* smoothModelBase I t ht n) :
    ∏ k : Fin n, (smoothModelGenerator I t ht n φ ^ k.val).left.ker = ⊥ :=
  (smoothModelFiniteSubgroup I t ht n).rootsGenerator_intrinsic_orbit
    (smoothModelCharacterIso I t ht n) φ

/-- The specialized cyclotomic root generates the whole original model Cartier divisor. -/
theorem smoothModelGenerator_isCartierGenerator
    (φ : IntegralCyclotomicCoordinates.Coordinate n →+* smoothModelBase I t ht n) :
    (smoothModelFiniteSubgroup I t ht n).IsCartierGenerator (smoothModelGenerator I t ht n φ) :=
  (smoothModelFiniteSubgroup I t ht n).rootsGenerator_isCartierGenerator
    (smoothModelCharacterIso I t ht n) φ

/-- The orbit in the whole model curve is exactly the full descended ideal. -/
theorem smoothModelGenerator_ideal_eq
    (φ : IntegralCyclotomicCoordinates.Coordinate n →+* smoothModelBase I t ht n) :
    (smoothModelFiniteSubgroup I t ht n).ideal =
      ∏ k : Fin n, ((smoothModelGenerator I t ht n φ ^ k.val) ≫
        smoothModelEmbedding I t ht n).left.ker := by
  rw [← smoothModelFiniteSubgroup_curveMap]
  exact (smoothModelGenerator_isCartierGenerator I t ht n φ).2.2

/-- The constructed finite coefficient subgroup is cyclic on its genuine generalized curve. -/
theorem smoothModelFiniteSubgroup_isCyclic : (smoothModelFiniteSubgroup I t ht n).IsCyclic :=
  (smoothModelFiniteSubgroup I t ht n).isCyclic_of_rootsIso (smoothModelCharacterIso I t ht n)

/-- Its entire ideal is relative Cartier over the finite coefficient base. -/
theorem smoothModelFiniteSubgroup_relativeCartier :
    FCurve.RelativeEffectiveCartier (smoothModelCurve I t ht n).curve.hom
      (smoothModelFiniteSubgroup I t ht n).ideal :=
  (smoothModelFiniteSubgroup_isCyclic I t ht n).relativeEffectiveCartier _

end FLT.Mazur.OneGonAdicCharacterTower
