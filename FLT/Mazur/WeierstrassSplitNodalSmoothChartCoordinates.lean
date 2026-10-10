/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitNodalGroupCoordinates

/-!
# Smooth multiplication in the original nodal chart coordinates

Equality of actual curve-valued inputs identifies their Laurent coordinates.
Consequently the full smooth group product uses the same units as the original
Y-chart maps, with no restriction on the common source scheme.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CartesianMonoidalCategory MonObj

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (a : Rˣ) (s : X ⟶ Spec (.of R))

/-- The inverse smooth-locus isomorphism preserves the actual inclusion in the cubic. -/
@[reassoc] theorem splitNodalSmooth_inverse_inclusion :
    (splitNodalRelativeSmoothOverIso a).inv.left ≫ splitNodalTorusToCurve a =
      (integralSmoothOpen (splitNodalEquation a)).ι := by
  rw [← splitNodalTorusToSmooth_inclusion, ← Category.assoc]
  change ((splitNodalRelativeSmoothIso a).inv ≫
    (splitNodalRelativeSmoothIso a).hom) ≫ _ = _
  rw [Iso.inv_hom_id, Category.id_comp]

/-- Every smooth-locus input has a compatible presentation in the original Y chart. -/
theorem splitNodalSmooth_exists_chart (v : Over.mk s ⟶ splitNodalSmoothOver a) :
    ∃ p : X ⟶ chartScheme (splitNodalEquation a) 1,
      p ≫ chartStructure (splitNodalEquation a) 1 = s ∧
      v.left ≫ (integralSmoothOpen (splitNodalEquation a)).ι =
        p ≫ integralCurveChart (splitNodalEquation a) 1 := by
  let p := v ≫ (splitNodalRelativeSmoothOverIso a).inv ≫ (splitNodalTorusOverIso a).hom
  refine ⟨p.left, p.w, ?_⟩
  change _ = (v.left ≫ (splitNodalRelativeSmoothOverIso a).inv.left ≫
    (splitNodalTorusIso a).hom) ≫ _
  rw [Category.assoc, Category.assoc]
  change _ = v.left ≫ (splitNodalRelativeSmoothOverIso a).inv.left ≫ splitNodalTorusToCurve a
  rw [splitNodalSmooth_inverse_inclusion]

/-- Common smooth and chart inputs have the same actual Laurent homomorphism. -/
theorem splitNodalSmooth_input_laurent
    (v : Over.mk s ⟶ splitNodalSmoothOver a)
    (p : X ⟶ chartScheme (splitNodalEquation a) 1)
    (hp : p ≫ chartStructure (splitNodalEquation a) 1 = s)
    (h : v.left ≫ (integralSmoothOpen (splitNodalEquation a)).ι =
      p ≫ integralCurveChart (splitNodalEquation a) 1) :
    let _ := specSectionAlgebra s
    specSectionAlgHom s (v ≫ (splitNodalRelativeSmoothOverIso a).inv).left
        (v ≫ (splitNodalRelativeSmoothOverIso a).inv).w =
      (specSectionAlgHom s p hp).comp (splitNodalLaurentToChart a) := by
  let _ := specSectionAlgebra s
  have ht : (v ≫ (splitNodalRelativeSmoothOverIso a).inv).left =
      p ≫ (splitNodalTorusIso a).inv := by
    apply (cancel_mono (splitNodalTorusToCurve a)).mp
    rw [Over.comp_left, Category.assoc, splitNodalSmooth_inverse_inclusion]
    rw [splitNodalTorusToCurve, Category.assoc, Iso.inv_hom_id_assoc]
    exact h
  apply AlgHom.coe_ringHom_injective
  change specSectionHom (v ≫ (splitNodalRelativeSmoothOverIso a).inv).left = _
  rw [ht]
  change specSectionHom (p ≫ Spec.map
    (CommRingCat.ofHom (splitNodalLaurentToChart a).toRingHom)) = _
  rw [specSectionHom_comp]
  rfl

/-- The smooth group multiplication uses exactly the Laurent units of common chart inputs. -/
theorem splitNodalSmooth_multiplication_chart_coordinates
    (v w : Over.mk s ⟶ splitNodalSmoothOver a)
    (p q : X ⟶ chartScheme (splitNodalEquation a) 1)
    (hp : p ≫ chartStructure (splitNodalEquation a) 1 = s)
    (hq : q ≫ chartStructure (splitNodalEquation a) 1 = s)
    (hv : v.left ≫ (integralSmoothOpen (splitNodalEquation a)).ι =
      p ≫ integralCurveChart (splitNodalEquation a) 1)
    (hw : w.left ≫ (integralSmoothOpen (splitNodalEquation a)).ι =
      q ≫ integralCurveChart (splitNodalEquation a) 1) :
    let _ := specSectionAlgebra s
    let _ := splitNodalSmoothCommGrpObj a
    let P := specSectionAlgHom s p hp
    let Q := specSectionAlgHom s q hq
    (lift v w ≫ μ[splitNodalSmoothOver a]).left ≫
        (integralSmoothOpen (splitNodalEquation a)).ι =
      specSectionMorphism (LaurentUnitPoints.evalUnit (R := R)
        (splitNodalChartUnit a P * splitNodalChartUnit a Q)).toRingHom ≫
          splitNodalTorusToCurve a := by
  let _ := specSectionAlgebra s
  let _ := splitNodalSmoothCommGrpObj a
  have h := splitNodalSmooth_multiplication_coordinates s a v w
  dsimp only at h ⊢
  rw [splitNodalSmooth_input_laurent a s v p hp hv,
    splitNodalSmooth_input_laurent a s w q hq hw] at h
  exact h

end FLT.Mazur.WeierstrassIntegralChart
