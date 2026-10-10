/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitNodalRelativeSmooth
public import FLT.Mazur.WeierstrassSplitNodalChartGroup
public import FLT.Mazur.WeierstrassSplitNodalNegationComparison
public import FLT.Mazur.WeierstrassSmoothNegation

/-!
# A commutative group on the entire relative split nodal smooth locus

Transport along the proved isomorphism equips the actual full smooth open
with a commutative group structure. Its torus identity and inversion agree
with the original restricted zero and negation morphisms.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory MonObj
open scoped LaurentPolynomial

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (a : Rˣ)

/-- The entire relative smooth open as a scheme over the original base. -/
abbrev splitNodalSmoothOver : Over (Spec (.of R)) :=
  Over.mk (integralSmoothStructure (splitNodalEquation a))

/-- The full smooth locus inherits the torus group by the proved geometric isomorphism. -/
abbrev splitNodalSmoothGrpObj : GrpObj (splitNodalSmoothOver a) :=
  GrpObj.ofIso (splitNodalRelativeSmoothOverIso a)

/-- Commutativity is transported from the multiplicative group. -/
abbrev splitNodalSmoothCommGrpObj : CommGrpObj (splitNodalSmoothOver a) where
  __ := splitNodalSmoothGrpObj a
  mul_comm := by
    change (β_ _ _).hom ≫
      ((splitNodalRelativeSmoothOverIso a).inv ⊗ₘ (splitNodalRelativeSmoothOverIso a).inv) ≫
        MonObj.mul ≫ (splitNodalRelativeSmoothOverIso a).hom = _
    rw [← BraidedCategory.braiding_naturality_assoc, IsCommMonObj.mul_comm_assoc]
    rfl

/-- The actual full relative smooth locus, with its proved commutative group laws. -/
def splitNodalSmoothGroup : CommGrp (Over (Spec (.of R))) := by
  letI := splitNodalSmoothCommGrpObj a
  exact ⟨splitNodalSmoothOver a⟩

/-- The group carrier is the full relative smooth open of the original glued cubic. -/
theorem splitNodalSmoothGroup_carrier :
    (splitNodalSmoothGroup a).X = splitNodalSmoothOver a := rfl

/-- Multiplication on the full smooth locus is the transported torus multiplication. -/
theorem splitNodalSmoothGroup_multiplication :
    let _ := splitNodalSmoothCommGrpObj a
    μ[splitNodalSmoothOver a] =
      ((splitNodalRelativeSmoothOverIso a).inv ⊗ₘ (splitNodalRelativeSmoothOverIso a).inv) ≫
        μ[MultiplicativeGroupScheme.gm R] ≫ (splitNodalRelativeSmoothOverIso a).hom := rfl

/-- Its identity is the torus identity followed by the full smooth-locus comparison. -/
theorem splitNodalSmoothGroup_identity :
    let _ := splitNodalSmoothCommGrpObj a
    η[splitNodalSmoothOver a] =
      η[MultiplicativeGroupScheme.gm R] ≫ (splitNodalRelativeSmoothOverIso a).hom := rfl

/-- Unit one is the original smooth zero section as an actual scheme morphism. -/
theorem splitNodalSmooth_torus_identity_zero :
    Spec.map (CommRingCat.ofHom
      (LaurentUnitPoints.evalUnit (R := R) (1 : Rˣ)).toRingHom) ≫
        (splitNodalRelativeSmoothIso a).hom = integralSmoothZero (splitNodalEquation a) := by
  apply (cancel_mono (integralSmoothOpen (splitNodalEquation a)).ι).mp
  change (Spec.map _ ≫ splitNodalTorusToSmooth a) ≫ _ = _
  rw [Category.assoc, splitNodalTorusToSmooth_inclusion,
    splitNodalTorus_identity_zero, integralSmoothZero_inclusion]

/-- Laurent inversion is the original negation restricted to the entire smooth open. -/
@[reassoc] theorem splitNodalSmooth_torus_negation :
    Spec.map (CommRingCat.ofHom LaurentPolynomial.invert.toAlgHom.toRingHom) ≫
        (splitNodalRelativeSmoothIso a).hom =
      (splitNodalRelativeSmoothIso a).hom ≫ integralSmoothNegation (splitNodalEquation a) := by
  apply (cancel_mono (integralSmoothOpen (splitNodalEquation a)).ι).mp
  change (Spec.map _ ≫ splitNodalTorusToSmooth a) ≫ _ =
    (splitNodalTorusToSmooth a ≫ integralSmoothNegation _) ≫ _
  rw [Category.assoc, splitNodalTorusToSmooth_inclusion,
    splitNodalTorusToCurve_negation, Category.assoc, integralSmoothNegation_inclusion,
    splitNodalTorusToSmooth_inclusion_assoc]

end FLT.Mazur.WeierstrassIntegralChart
