/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassCyclicNormalizationPoint

/-!
# Original cyclic markings on the actual source family

The realized complete marking retains every original universal label. Its
auxiliary factor is exactly the existing auxiliary marking, and its cyclic
factor retains its exact order on all nonempty source schemes.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.UniversalWeierstrass
open AuxiliaryLevel WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (n : ℕ) [NeZero n] {T : Scheme} (f : T ⟶ (cyclicAuxiliaryScheme n).left)
local notation "aO" => cyclicSchemeAuxiliaryPoint n f
local notation "G" => auxiliarySchemeGroup aO

/-- All original labels on the actual source group family. -/
def cyclicSchemeOriginalMarking : CyclicLabels n →* (𝟙_ (Over T) ⟶ (G).X) :=
  markingOf (G).X (CyclicLabels n)
    (cyclicSchemeOriginalParameter n f ≫ faithfulInclusion (G).X (CyclicLabels n))

/-- The actual full marking projects to exactly the original scheme-valued labels. -/
@[reassoc] theorem cyclicSchemeOriginalMarking_fst (c : CyclicLabels n) :
    (cyclicSchemeOriginalMarking n f c).left ≫
      pullback.fst universalGroup.hom (aO ≫ levelFour.hom) =
        f ≫ (cyclicAuxiliaryInclusion n ≫ value universalGroup (CyclicLabels n) c).left := by
  have hv := cartesianGroupParameter_value (aO ≫ levelFour.hom)
    (integralCurveGroup smoothEquation smoothEquation_discriminant) G (Iso.refl _)
    (CyclicLabels n) (cyclicSchemeGroupPoint n f) c
  change cyclicSchemeOriginalMarking n f c = _ at hv
  rw [hv]
  have hp := cartesianGroupMarking_projection (aO ≫ levelFour.hom)
    (integralCurveGroup smoothEquation smoothEquation_discriminant) G (Iso.refl _)
    (CyclicLabels n) (cyclicSchemeGroupPoint n f) c
  change _ ≫ 𝟙 _ ≫ pullback.fst universalGroup.hom (aO ≫ levelFour.hom) = _ at hp
  rw [Category.id_comp] at hp
  exact hp

/-- Forgetting the cyclic factor retains every auxiliary label as an actual scheme map. -/
@[reassoc] theorem forgetCyclic_value (c : Labels 4) :
    (forgetCyclic n).left ≫ (auxiliaryMarking 4 c).left =
      (cyclicAuxiliaryInclusion n ≫ value universalGroup (CyclicLabels n) (c, 1)).left := by
  change (forgetCyclic n ≫ auxiliaryInclusion 4 ≫ value universalGroup (Labels 4) c).left = _
  rw [← Category.assoc, forgetCyclic_inclusion]
  simp only [forgetCyclicEquations, Category.assoc, relabel_value, MonoidHom.inl_apply]

/-- The full original marking restricts to precisely the original auxiliary source marking. -/
theorem cyclicSchemeOriginalMarking_auxiliary (c : Labels 4) :
    cyclicSchemeOriginalMarking n f (c, 1) = auxiliarySchemeMarking aO c := by
  apply auxiliarySchemeMarking_ext
  rw [cyclicSchemeOriginalMarking_fst]
  change _ = (f ≫ (forgetCyclic n).left) ≫ (auxiliaryMarking 4 c).left
  rw [Category.assoc, forgetCyclic_value]

/-- The original full source marking is faithful on every nonempty scheme. -/
theorem cyclicSchemeOriginalMarking_injective [Nonempty T] :
    Function.Injective (cyclicSchemeOriginalMarking n f) := by
  let _ : Nonempty (𝟙_ (Over T)).left := inferInstanceAs (Nonempty T)
  exact faithful_marking_injective (G).X (CyclicLabels n) (cyclicSchemeOriginalParameter n f)

/-- The original cyclic generator has its exact order on the actual source family. -/
theorem cyclicSchemeOriginalMarking_order [Nonempty T] :
    orderOf (cyclicSchemeOriginalMarking n f (cyclicLabel n)) = n :=
  (orderOf_injective _ (cyclicSchemeOriginalMarking_injective n f) (cyclicLabel n)).trans
    (cyclicLabel_order n)

end FLT.Mazur.UniversalWeierstrass
