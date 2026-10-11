/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingSmoothGroup
public import FLT.Mazur.GroupMarkingTransportEquations
public import FLT.Mazur.UniversalWeierstrassAuxiliaryFullMarkingSections

/-!
# The complete auxiliary marking on the original smooth one-gon

On every scheme over the original boundary base, an actual auxiliary point
supplies a homomorphism into the original boundary group. All sixteen labels,
their order-four equations, and their original universal sections are retained.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonObj
namespace FLT.Mazur.OneGonSmoothing
open WeierstrassIntegralChart UniversalWeierstrass
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R]
  (t : R) (h₂ : IsUnit (2 : R)) (ht : IsUnit t) (hf : IsUnit (1 + 432 * t))
  {T : Over (Spec (.of R))}
  (p : (Over.map (Spec.map (CommRingCat.ofHom (smoothParameter t h₂ ht hf)))).obj T ⟶
    levelFour)

/-- The entire original auxiliary marking on the universal coefficient pullback. -/
def smoothCoefficientMarking : Labels 4 →* (T ⟶ (smoothUniversalGroup t h₂ ht hf).X) :=
  GroupMarkingBaseChange.marking _
    (integralCurveGroup smoothEquation smoothEquation_discriminant).X T
    (AuxiliaryLevel.markingOf universalGroup (Labels 4) (p ≫ auxiliaryInclusion 4))

attribute [local irreducible] smoothGroup smoothUniversalGroup

/-- The full auxiliary homomorphism on the unchanged original boundary group. -/
def smoothFullMarking : Labels 4 →* (T ⟶ (smoothGroup t ht hf).X) :=
  GroupMarkingTransport.transport _ _ (smoothUniversalGroupIso t h₂ ht hf).symm
    (smoothCoefficientMarking t h₂ ht hf p)

/-- The full boundary marking compares label by label with the universal pullback marking. -/
theorem smoothFullMarking_compare (a : Labels 4) :
    smoothFullMarking t h₂ ht hf p a ≫
      (smoothUniversalGroupIso t h₂ ht hf).hom.hom.hom.hom =
        smoothCoefficientMarking t h₂ ht hf p a :=
  GroupMarkingTransport.transport_compare _ _ (smoothUniversalGroupIso t h₂ ht hf).symm
    (smoothCoefficientMarking t h₂ ht hf p) a

attribute [local semireducible] smoothGroup smoothUniversalGroup

/-- The original boundary marking retains each original universal auxiliary section. -/
@[reassoc] theorem smoothFullMarking_universal (a : Labels 4) :
    (smoothFullMarking t h₂ ht hf p a).left ≫ smoothUniversalMorphism t h₂ ht hf =
      p.left ≫ (auxiliaryMarking 4 a).left := by
  rw [← smoothUniversalGroupIso_fst, ← Category.assoc, ← Over.comp_left,
    smoothFullMarking_compare]
  exact (GroupMarkingBaseChange.marking_fst _
    (integralCurveGroup smoothEquation smoothEquation_discriminant).X T _ a).trans
    (congrArg Over.Hom.left
      (AuxiliaryLevel.markingOf_comp universalGroup (Labels 4) p (auxiliaryInclusion 4) a))

attribute [local irreducible] smoothGroup

/-- All sixteen labels are distinct on every nonempty original test scheme. -/
theorem smoothFullMarking_injective [Nonempty T.left] :
    Function.Injective (smoothFullMarking t h₂ ht hf p) := by
  unfold smoothFullMarking
  apply (GroupMarkingTransport.transport_injective_iff _ _ _ _).mpr
  unfold smoothCoefficientMarking
  apply (GroupMarkingBaseChange.marking_injective_iff _ _ T _).mpr
  let _ : Nonempty ((Over.map
    (Spec.map (CommRingCat.ofHom (smoothParameter t h₂ ht hf)))).obj T).left :=
      inferInstanceAs (Nonempty T.left)
  exact auxiliaryMarking_injective 4 p

/-- Every label is killed by four in the original boundary group. -/
theorem smoothFullMarking_pow (a : Labels 4) :
    smoothFullMarking t h₂ ht hf p a ^ 4 = 1 :=
  GroupMarkingTransport.marking_pow_eq_one _ (smoothFullMarking t h₂ ht hf p) a 4
    (labels_pow 4 a)

/-- Changing the source scheme pulls back every original boundary label. -/
theorem smoothFullMarking_natural {U : Over (Spec (.of R))} (k : U ⟶ T) (a : Labels 4) :
    smoothFullMarking t h₂ ht hf
      ((Over.map (Spec.map (CommRingCat.ofHom (smoothParameter t h₂ ht hf)))).map k ≫ p) a =
        k ≫ smoothFullMarking t h₂ ht hf p a := by
  apply GroupMarkingTransport.transport_natural
  intro c
  change GroupMarkingBaseChange.pointsMulEquiv _ _ U
    (AuxiliaryLevel.markingOf universalGroup (Labels 4)
      ((_ ≫ p) ≫ auxiliaryInclusion 4) c) = _
  rw [Category.assoc, AuxiliaryLevel.markingOf_comp]
  exact (Over.mapPullbackAdj _).homEquiv_naturality_left k _

end FLT.Mazur.OneGonSmoothing
