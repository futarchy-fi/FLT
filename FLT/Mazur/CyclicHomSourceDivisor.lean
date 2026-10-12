/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicHomAuxiliaryScheme
public import FLT.Mazur.CyclicMarkingOrbitDivisor
public import FLT.Mazur.UniversalWeierstrassCyclicSourceModuli
public import FLT.Mazur.GroupMarkingBaseChange

/-!
# The actual orbit divisor over the cyclic homomorphism parameter scheme

Every ambient parameter carries the full source curve and a finite locally free
Cartier divisor of rank n. Coincident sections contribute repeated ideal factors.
Being a subgroup remains an additional condition on this divisor.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.UniversalWeierstrass
open AuxiliaryLevel GeneralizedEllipticCurve WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T : Scheme} (f : T ⟶ (cyclicHomAuxiliaryScheme n).left)

/-- The actual auxiliary coordinate of an unrestricted cyclic parameter. -/
def cyclicHomAuxiliaryPoint : T ⟶ levelFour.left := f ≫ (cyclicHomAuxiliary n).left

/-- The full source cubic on the exact original coefficient base. -/
def cyclicHomSourceCurve : GeneralizedEllipticCurve T :=
  universalCurve.baseChange (cyclicHomAuxiliaryPoint n f ≫ levelFour.hom)

/-- The source remains a smooth relative curve on arbitrary tests. -/
instance cyclicHomSourceCurve_smoothDimension :
    SmoothOfRelativeDimension 1 (cyclicHomSourceCurve n f).curve.hom := by
  let _ := integralCurveStructure_smooth_dimension smoothEquation smoothEquation_discriminant
  change SmoothOfRelativeDimension 1 (pullback.snd (integralCurveStructure smoothEquation) _)
  exact MorphismProperty.pullback_snd _ _ inferInstance

/-- The cyclic parameter has the same coefficient map as the auxiliary coordinate. -/
def cyclicHomSourcePoint :
    (Over.map (cyclicHomAuxiliaryPoint n f ≫ levelFour.hom)).obj (𝟙_ (Over T)) ⟶
      homScheme universalGroup (Multiplicative (ZMod n)) :=
  Over.homMk (f ≫ (cyclicHomParameter n).left) (by
    change (f ≫ (cyclicHomParameter n).left) ≫ _ =
      𝟙 T ≫ (cyclicHomAuxiliaryPoint n f ≫ levelFour.hom)
    rw [Category.id_comp, Category.assoc, (cyclicHomParameter n).w]
    rw [cyclicHomAuxiliaryPoint, Category.assoc, (cyclicHomAuxiliary n).w])

/-- Realize all cyclic labels on the actual source curve. -/
def cyclicHomSourceMarking : Multiplicative (ZMod n) →*
    (𝟙_ (Over T) ⟶ (cyclicHomSourceCurve n f).group) :=
  GroupMarkingBaseChange.marking (cyclicHomAuxiliaryPoint n f ≫ levelFour.hom)
    universalGroup (𝟙_ (Over T)) (markingOf _ _ (cyclicHomSourcePoint n f))

/-- Projection retains the exact original universal cyclic label. -/
@[reassoc] theorem cyclicHomSourceMarking_fst (i : Multiplicative (ZMod n)) :
    (cyclicHomSourceMarking n f i).left ≫
      pullback.fst universalGroup.hom (cyclicHomAuxiliaryPoint n f ≫ levelFour.hom) =
        f ≫ (cyclicHomParameter n ≫ value _ _ i).left := by
  have h := GroupMarkingBaseChange.marking_fst
    (cyclicHomAuxiliaryPoint n f ≫ levelFour.hom) universalGroup (𝟙_ (Over T))
    (markingOf _ _ (cyclicHomSourcePoint n f)) i
  exact h.trans (by
    change (f ≫ (cyclicHomParameter n).left) ≫ (value _ _ i).left = _
    rw [Over.comp_left, Category.assoc])

/-- The source divisor retains a factor for every cyclic label. -/
def cyclicHomSourceIdeal : (cyclicHomSourceCurve n f).curve.left.IdealSheafData :=
  (cyclicHomSourceCurve n f).cyclicMarkingIdeal (cyclicHomSourceMarking n f)

/-- The actual source orbit product is relative Cartier on every test. -/
theorem cyclicHomSourceIdeal_cartier : FCurve.RelativeEffectiveCartier
    (cyclicHomSourceCurve n f).curve.hom (cyclicHomSourceIdeal n f) :=
  (cyclicHomSourceCurve n f).cyclicMarkingIdeal_cartier (cyclicHomSourceMarking n f)

/-- The actual divisor has degree n even for nonfaithful cyclic markings. -/
theorem cyclicHomSourceIdeal_degree : FCurve.FiniteLocallyFreeDegree
    ((cyclicHomSourceIdeal n f).subschemeι ≫ (cyclicHomSourceCurve n f).curve.hom) n :=
  (cyclicHomSourceCurve n f).cyclicMarkingIdeal_degree (cyclicHomSourceMarking n f)

end FLT.Mazur.UniversalWeierstrass
