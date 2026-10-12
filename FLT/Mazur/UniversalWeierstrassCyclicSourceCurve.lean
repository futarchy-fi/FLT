/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassCyclicOriginalMarking
public import FLT.Mazur.UniversalWeierstrassCyclicLevel
public import FLT.Mazur.SmoothGeneralizedCurveGroupIso

/-!
# The original full marked source family as a generalized elliptic curve

Retain the original coefficient map on every source scheme. Its full marking
constructs an actual finite cyclic subgroup, with the original Cartier generator.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.UniversalWeierstrass
open AuxiliaryLevel GeneralizedEllipticCurve UniversallyDistinctSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (n : ℕ) [NeZero n] {T : Scheme} (f : T ⟶ (cyclicAuxiliaryScheme n).left)

/-- The whole original cubic over the full source point, retaining its coefficient map. -/
def cyclicSourceCurve : GeneralizedEllipticCurve T :=
  universalCurve.baseChange (cyclicSchemeAuxiliaryPoint n f ≫ levelFour.hom)

/-- The source curve has the exact original smooth group used by the full family relation. -/
theorem cyclicSourceCurve_group :
    (cyclicSourceCurve n f).group =
      (auxiliarySchemeGroup (cyclicSchemeAuxiliaryPoint n f)).X := rfl

/-- The whole source curve is smooth of relative dimension one. -/
instance cyclicSourceCurve_smooth :
    SmoothOfRelativeDimension 1 (cyclicSourceCurve n f).curve.hom := by
  let _ := WeierstrassIntegralChart.integralCurveStructure_smooth_dimension
    smoothEquation smoothEquation_discriminant
  change SmoothOfRelativeDimension 1 (pullback.snd
    (WeierstrassIntegralChart.integralCurveStructure smoothEquation) _)
  exact MorphismProperty.pullback_snd _ _ inferInstance

/-- Geometric integrality of the original cubic persists on the source family. -/
instance cyclicSourceCurve_geometricallyIntegral :
    GeometricallyIntegral (cyclicSourceCurve n f).curve.hom := by
  change GeometricallyIntegral (pullback.snd
    (WeierstrassIntegralChart.integralCurveStructure smoothEquation) _)
  infer_instance

/-- The cyclic factor consists of the original full marked source sections. -/
def cyclicSourceMarking : Multiplicative (ZMod n) →*
    (𝟙_ (Over T) ⟶ (cyclicSourceCurve n f).group) :=
  (cyclicSchemeOriginalMarking n f).comp (MonoidHom.inr _ _)

/-- The original source cyclic sections remain distinct on every nonempty test scheme. -/
theorem cyclicSourceMarking_distinct :
    UniversallyDistinct (fun i : ZMod n ↦ cyclicSourceMarking n f (Multiplicative.ofAdd i)) := by
  intro V g hV i j hij
  let _ : Nonempty (Over.mk
    (V.hom ≫ f ≫ (cyclicAuxiliaryScheme n).hom)).left := hV
  let k : Over.mk (V.hom ≫ f ≫ (cyclicAuxiliaryScheme n).hom) ⟶ cyclicAuxiliaryScheme n :=
    Over.homMk (V.hom ≫ f) (Category.assoc _ _ _)
  have hh := faithful_marking_injective universalGroup (CyclicLabels n) k
  apply congrArg (fun c : CyclicLabels n ↦ c.2.toAdd)
    (hh (a₁ := (1, Multiplicative.ofAdd i)) (a₂ := (1, Multiplicative.ofAdd j)) ?_)
  apply Over.OverMorphism.ext
  have he := congrArg (fun s : V ⟶ (cyclicSourceCurve n f).group ↦ s.left ≫
    pullback.fst universalGroup.hom (cyclicSchemeAuxiliaryPoint n f ≫ levelFour.hom)) hij
  have hg : g.left = V.hom := by simpa using g.w
  change (g.left ≫ (cyclicSchemeOriginalMarking n f (1, Multiplicative.ofAdd i)).left) ≫
    pullback.fst universalGroup.hom _ =
      (g.left ≫ (cyclicSchemeOriginalMarking n f (1, Multiplicative.ofAdd j)).left) ≫
        pullback.fst universalGroup.hom _ at he
  rw [Category.assoc, Category.assoc, cyclicSchemeOriginalMarking_fst,
    cyclicSchemeOriginalMarking_fst, hg] at he
  change (V.hom ≫ f) ≫ (cyclicAuxiliaryInclusion n ≫
    value universalGroup (CyclicLabels n) (1, Multiplicative.ofAdd i)).left =
      (V.hom ≫ f) ≫ (cyclicAuxiliaryInclusion n ≫
        value universalGroup (CyclicLabels n) (1, Multiplicative.ofAdd j)).left
  simpa only [Category.assoc] using he

/-- The actual finite subgroup constructed from the original source marking. -/
def cyclicSourceSubgroup : (cyclicSourceCurve n f).FiniteSubgroup n :=
  (cyclicSourceCurve n f).relativeCyclicSubgroup
    (cyclicSourceMarking n f) (cyclicSourceMarking_distinct n f)

/-- The original source generator has the full Cartier orbit condition. -/
theorem cyclicSourceSubgroup_cartier :
    (cyclicSourceSubgroup n f).IsCartierGenerator
      ((cyclicSourceCurve n f).relativeCyclicGenerator
        (cyclicSourceMarking n f) (cyclicSourceMarking_distinct n f)) :=
  (cyclicSourceCurve n f).relativeCyclicGenerator_isCartierGenerator
    (cyclicSourceMarking n f) (cyclicSourceMarking_distinct n f)

end FLT.Mazur.UniversalWeierstrass
