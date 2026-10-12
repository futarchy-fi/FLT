/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartesianHomMarkingParameter
public import FLT.Mazur.CyclicHomAuxiliaryScheme
public import FLT.Mazur.PointedCubicCoefficientParameter
public import FLT.Mazur.PointedCubicCyclicAuxiliaryCover

/-!
# Original cyclic homomorphisms on the auxiliary coefficient cover

The same etale auxiliary cover accepts arbitrary cyclic markings. Cyclic
sections need not be distinct, and no etaleness of a cyclic subgroup is used.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve
open WeierstrassIntegralChart UniversalWeierstrass AuxiliaryLevel
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (W : WeierstrassCurve Γ(S, ⊤)) [W.IsElliptic]
  (h₂ : IsUnit (2 : Γ(S, ⊤))) {n : ℕ} [NeZero n]
  (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ (pointedCubicFamily W).group))
local notation "G" => integralCurveGroup smoothEquation smoothEquation_discriminant

/-- Every original cyclic marking projects through its exact five coefficients. -/
def pointedCubicHomCoefficientParameter :
    (Over.map (pointedCubicCoefficientBase W h₂)).obj (pointedCubicAuxiliaryCover W h₂) ⟶
      homScheme universalGroup (Multiplicative (ZMod n)) :=
  cartesianHomParameter (pointedCubicCoefficientBase W h₂) G
    (pointedCubicCoefficientGroup W) (pointedCubicCoefficientGroupIso W h₂) _
    (pointedCubicAuxiliaryBaseTest W h₂ ≫ liftMarking _ _ φ)

/-- Pair the original auxiliary labels with the unrestricted cyclic homomorphism. -/
def pointedCubicHomAuxiliaryParameter :
    (Over.map (pointedCubicCoefficientBase W h₂)).obj (pointedCubicAuxiliaryCover W h₂) ⟶
      cyclicHomAuxiliaryScheme n :=
  cyclicHomLift n
    (pointedCubicFullCoefficientParameter W h₂ (Labels 4) (pointedCubicAuxiliaryParameter W h₂))
    (pointedCubicHomCoefficientParameter W h₂ φ)

/-- The ambient parameter retains exactly the original coefficient morphism. -/
@[reassoc] theorem pointedCubicHomAuxiliaryParameter_base :
    (pointedCubicHomAuxiliaryParameter W h₂ φ).left ≫ (cyclicHomAuxiliaryScheme n).hom =
      (pointedCubicAuxiliaryCover W h₂).hom ≫ pointedCubicCoefficientBase W h₂ :=
  (pointedCubicHomAuxiliaryParameter W h₂ φ).w

/-- Every label retains its original section after the group comparison and projection. -/
theorem pointedCubicHomAuxiliaryParameter_value (i : Multiplicative (ZMod n)) :
    (pointedCubicHomAuxiliaryParameter W h₂ φ ≫ cyclicHomParameter n ≫ value _ _ i).left =
      (pointedCubicAuxiliaryCover W h₂).hom ≫ (φ i).left ≫
        (pointedCubicCoefficientGroupIso W h₂).hom.hom.hom.hom.left ≫
          pullback.fst universalGroup.hom (pointedCubicCoefficientBase W h₂) := by
  rw [← Category.assoc, pointedCubicHomAuxiliaryParameter, cyclicHomLift_cyclic]
  have hv := cartesianHomParameter_value (pointedCubicCoefficientBase W h₂) G
    (pointedCubicCoefficientGroup W) (pointedCubicCoefficientGroupIso W h₂)
    (Multiplicative (ZMod n))
    (pointedCubicAuxiliaryBaseTest W h₂ ≫ liftMarking _ _ φ) i
  exact hv.trans (by
    rw [Category.assoc, liftMarking_value, Over.comp_left, Category.assoc]
    rfl)

include h₂ φ in
/-- Arbitrary cyclic homomorphisms admit actual auxiliary parameters on an etale cover. -/
theorem exists_pointedCubic_hom_auxiliary_cover :
    ∃ (U : Scheme) (g : U ⟶ S), Etale g ∧ Surjective g ∧
      ∃ f : U ⟶ (cyclicHomAuxiliaryScheme n).left,
        f ≫ (cyclicHomAuxiliaryScheme n).hom = g ≫ pointedCubicCoefficientBase W h₂ :=
  ⟨(pointedCubicAuxiliaryCover W h₂).left, (pointedCubicAuxiliaryCover W h₂).hom,
    inferInstance, inferInstance, (pointedCubicHomAuxiliaryParameter W h₂ φ).left,
    pointedCubicHomAuxiliaryParameter_base W h₂ φ⟩

end FLT.Mazur.GeneralizedEllipticCurve
