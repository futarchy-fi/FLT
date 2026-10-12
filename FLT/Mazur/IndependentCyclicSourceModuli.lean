/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IndependentCyclicSourceMarking
public import FLT.Mazur.UniversalWeierstrassCyclicSourceModuli

/-!
# Genuine modular objects from independent cyclic parameters

The entire smooth original family and its actual Cartier cyclic subgroup are
constructed from the independent parameter. Auxiliary/cyclic coprimality is
not needed for the subgroup, cyclicity, or ampleness proofs.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.UniversalWeierstrass
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T : Scheme}
  (f : T ⟶ (independentCyclicAuxiliaryScheme n).left)

/-- The whole original cubic over the actual independent source parameter. -/
def independentCyclicSourceCurve : GeneralizedEllipticCurve T :=
  universalCurve.baseChange (independentCyclicAuxiliaryPoint n f ≫ levelFour.hom)

/-- The source is smooth of relative dimension one over its original base. -/
instance independentCyclicSourceCurve_smoothDimension :
    SmoothOfRelativeDimension 1 (independentCyclicSourceCurve n f).curve.hom := by
  let _ := WeierstrassIntegralChart.integralCurveStructure_smooth_dimension
    smoothEquation smoothEquation_discriminant
  change SmoothOfRelativeDimension 1 (pullback.snd
    (WeierstrassIntegralChart.integralCurveStructure smoothEquation) _)
  exact MorphismProperty.pullback_snd _ _ inferInstance

/-- The original full source cubic is smooth. -/
instance independentCyclicSourceCurve_smooth :
    Smooth (independentCyclicSourceCurve n f).curve.hom :=
  SmoothOfRelativeDimension.smooth 1 _

/-- The source cubic stays geometrically integral under every base change. -/
instance independentCyclicSourceCurve_geometricallyIntegral :
    GeometricallyIntegral (independentCyclicSourceCurve n f).curve.hom := by
  change GeometricallyIntegral (pullback.snd
    (WeierstrassIntegralChart.integralCurveStructure smoothEquation) _)
  infer_instance

/-- The actual finite subgroup cut out by the original cyclic source sections. -/
def independentCyclicSourceSubgroup : (independentCyclicSourceCurve n f).FiniteSubgroup n :=
  (independentCyclicSourceCurve n f).relativeCyclicSubgroup
    (independentCyclicSourceMarking n f) (independentCyclicSourceMarking_distinct n f)

/-- The constructed subgroup has its actual Cartier generator. -/
theorem independentCyclicSourceSubgroup_cartier :
    (independentCyclicSourceSubgroup n f).IsCartierGenerator
      ((independentCyclicSourceCurve n f).relativeCyclicGenerator
        (independentCyclicSourceMarking n f) (independentCyclicSourceMarking_distinct n f)) :=
  (independentCyclicSourceCurve n f).relativeCyclicGenerator_isCartierGenerator
    (independentCyclicSourceMarking n f) (independentCyclicSourceMarking_distinct n f)

/-- The actual positive cyclic subgroup is ample on the smooth source curve. -/
theorem independentCyclicSourceSubgroup_isAmple : (independentCyclicSourceSubgroup n f).IsAmple :=
  (independentCyclicSourceSubgroup n f).isAmple_of_smooth (NeZero.pos n)
    (independentCyclicSourceSubgroup_cartier n f).2.1.1

/-- The original independent source determines a genuine ample cyclic object. -/
def independentCyclicSourceLevel : ampleCyclicLevels T n :=
  ⟨⟨independentCyclicSourceCurve n f, independentCyclicSourceSubgroup n f⟩,
    (independentCyclicSourceSubgroup_cartier n f).isCyclic _,
    independentCyclicSourceSubgroup_isAmple n f⟩

/-- Its class retains the actual full curve and cyclic Cartier subgroup. -/
def independentCyclicSourceModuliClass : ampleCyclicClasses T n :=
  Quotient.mk _ (independentCyclicSourceLevel n f)

end FLT.Mazur.UniversalWeierstrass
