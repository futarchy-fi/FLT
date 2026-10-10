/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitNodalSmoothAdditionComparison
public import FLT.Mazur.WeierstrassSmoothGroup

/-!
# The full smooth nodal group is the multiplicative group

The new smooth law agrees with the older transported torus law on the same
carrier. The geometric Laurent comparison is consequently a group isomorphism.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory MonObj
open scoped LaurentPolynomial

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (a : Rˣ)

/-- The Laurent counit is evaluation at the unit one. -/
theorem laurentCounit_eq_evalUnit_one :
    Bialgebra.counitAlgHom R R[T;T⁻¹] = LaurentUnitPoints.evalUnit (R := R) (1 : Rˣ) := by
  apply LaurentUnitPoints.hom_ext <;>
    simp [Bialgebra.counitAlgHom, LaurentPolynomial.counit_T]

/-- The older nodal group identity is exactly the constructed smooth zero section. -/
theorem splitNodalSmoothGroup_one_eq :
    let _ := splitNodalSmoothCommGrpObj a
    η[splitNodalSmoothOver a] = integralSmoothOverZero (splitNodalEquation a) := by
  let _ := splitNodalSmoothCommGrpObj a
  dsimp only
  rw [splitNodalSmoothGroup_identity]
  apply Over.OverMorphism.ext
  change η[MultiplicativeGroupScheme.gm R].left ≫
    (splitNodalRelativeSmoothIso a).hom = integralSmoothZero (splitNodalEquation a)
  rw [one_spec_asOver_spec_left, laurentCounit_eq_evalUnit_one]
  exact splitNodalSmooth_torus_identity_zero a

/-- The older nodal group multiplication is the constructed smooth addition over the base. -/
theorem splitNodalSmoothGroup_mul_eq :
    let _ := splitNodalSmoothCommGrpObj a
    μ[splitNodalSmoothOver a] = integralSmoothOverAddition (splitNodalEquation a) := by
  let _ := splitNodalSmoothCommGrpObj a
  dsimp only
  apply Over.OverMorphism.ext
  change _ = smoothFactorAddition (splitNodalEquation a)
  rw [splitNodalSmoothAddition_eq_transported, splitNodalTransportedAddition_def]

/-- The identity on the smooth carrier identifies the two independently constructed groups. -/
def splitNodalSmoothGroupComparison :
    integralSmoothGroup (splitNodalEquation a) ≅ splitNodalSmoothGroup a := by
  refine CommGrp.mkIso (Iso.refl _) ?_ ?_
  · change integralSmoothOverZero (splitNodalEquation a) ≫ 𝟙 _ = _
    rw [Category.comp_id]
    exact (splitNodalSmoothGroup_one_eq a).symm
  · change integralSmoothOverAddition (splitNodalEquation a) ≫ 𝟙 _ =
      (𝟙 _ ⊗ₘ 𝟙 _) ≫ _
    rw [Category.comp_id, tensorHom_id, id_whiskerRight, Category.id_comp]
    exact (splitNodalSmoothGroup_mul_eq a).symm

/-- The original Laurent geometric comparison is a commutative-group isomorphism. -/
def splitNodalTorusSmoothGroupIso :
    CommGrp.mk (MultiplicativeGroupScheme.gm R) ≅ splitNodalSmoothGroup a := by
  let _ := splitNodalSmoothCommGrpObj a
  exact CommGrp.mkIso' (splitNodalRelativeSmoothOverIso a)

/-- The full smooth law of a split-nodal equation is the multiplicative group over the base. -/
def integralSmoothSplitNodalTorusIso :
    integralSmoothGroup (splitNodalEquation a) ≅ CommGrp.mk (MultiplicativeGroupScheme.gm R) :=
  splitNodalSmoothGroupComparison a ≪≫ (splitNodalTorusSmoothGroupIso a).symm

/-- The nodal comparison retains the original inverse Laurent parametrization. -/
theorem integralSmoothSplitNodalTorusIso_hom :
    (integralSmoothSplitNodalTorusIso a).hom.hom.hom.hom =
      (splitNodalRelativeSmoothOverIso a).inv := by
  change 𝟙 _ ≫ _ = _
  exact Category.id_comp _

end FLT.Mazur.WeierstrassIntegralChart
