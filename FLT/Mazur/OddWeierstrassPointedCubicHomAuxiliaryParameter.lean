/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartesianHomMarkingParameter
public import FLT.Mazur.OddWeierstrassCyclicHomAuxiliaryScheme
public import FLT.Mazur.OddWeierstrassPointedCubicCoefficientParameter

/-!
# Odd-chart original cyclic homomorphisms on the auxiliary coefficient cover

The same etale auxiliary cover accepts arbitrary cyclic markings. Cyclic
sections need not be distinct, and no etaleness of a cyclic subgroup is used.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OddWeierstrassParameter
open WeierstrassIntegralChart GeneralizedEllipticCurve AuxiliaryLevel
open UniversalWeierstrass (Labels)
open IntegralWeierstrassParameter (oddChartEquation oddChart_discriminant)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (W : WeierstrassCurve Γ(S, ⊤)) [W.IsElliptic]
  (h₃ : IsUnit (3 : Γ(S, ⊤))) {n : ℕ} [NeZero n]
  (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ (pointedCubicFamily W).group))
local notation "G" => integralCurveGroup oddChartEquation oddChart_discriminant

/-- The actual auxiliary cover as a test over its original base. -/
def pointedCubicAuxiliaryBaseTest : pointedCubicAuxiliaryCover W h₃ ⟶ 𝟙_ (Over S) :=
  Over.homMk (pointedCubicAuxiliaryCover W h₃).hom (Category.comp_id _)

/-- Every original cyclic marking projects through its exact five coefficients. -/
def pointedCubicHomCoefficientParameter :
    (Over.map (pointedCubicCoefficientBase W h₃)).obj (pointedCubicAuxiliaryCover W h₃) ⟶
      homScheme universalGroup (Multiplicative (ZMod n)) :=
  cartesianHomParameter (pointedCubicCoefficientBase W h₃) G
    (pointedCubicCoefficientGroup W) (pointedCubicCoefficientGroupIso W h₃) _
    (pointedCubicAuxiliaryBaseTest W h₃ ≫ liftMarking _ _ φ)

/-- Pair the original auxiliary labels with the unrestricted cyclic homomorphism. -/
def pointedCubicHomAuxiliaryParameter :
    (Over.map (pointedCubicCoefficientBase W h₃)).obj (pointedCubicAuxiliaryCover W h₃) ⟶
      cyclicHomAuxiliaryScheme n :=
  cyclicHomLift n
    (pointedCubicFullCoefficientParameter W h₃ (Labels 3) (pointedCubicAuxiliaryParameter W h₃))
    (pointedCubicHomCoefficientParameter W h₃ φ)

/-- The ambient parameter retains exactly the original coefficient morphism. -/
@[reassoc] theorem pointedCubicHomAuxiliaryParameter_base :
    (pointedCubicHomAuxiliaryParameter W h₃ φ).left ≫ (cyclicHomAuxiliaryScheme n).hom =
      (pointedCubicAuxiliaryCover W h₃).hom ≫ pointedCubicCoefficientBase W h₃ :=
  (pointedCubicHomAuxiliaryParameter W h₃ φ).w

/-- Every label retains its original section after the group comparison and projection. -/
theorem pointedCubicHomAuxiliaryParameter_value (i : Multiplicative (ZMod n)) :
    (pointedCubicHomAuxiliaryParameter W h₃ φ ≫ cyclicHomParameter n ≫ value _ _ i).left =
      (pointedCubicAuxiliaryCover W h₃).hom ≫ (φ i).left ≫
        (pointedCubicCoefficientGroupIso W h₃).hom.hom.hom.hom.left ≫
          pullback.fst universalGroup.hom (pointedCubicCoefficientBase W h₃) := by
  rw [← Category.assoc, pointedCubicHomAuxiliaryParameter, cyclicHomLift_cyclic]
  have hv := cartesianHomParameter_value (pointedCubicCoefficientBase W h₃) G
    (pointedCubicCoefficientGroup W) (pointedCubicCoefficientGroupIso W h₃)
    (Multiplicative (ZMod n))
    (pointedCubicAuxiliaryBaseTest W h₃ ≫ liftMarking _ _ φ) i
  exact hv.trans (by
    rw [Category.assoc, liftMarking_value, Over.comp_left, Category.assoc]
    rfl)

include h₃ φ in
/-- Arbitrary cyclic homomorphisms admit actual auxiliary parameters on an etale cover. -/
theorem exists_pointedCubic_hom_auxiliary_cover :
    ∃ (U : Scheme) (g : U ⟶ S), Etale g ∧ Surjective g ∧
      ∃ f : U ⟶ (cyclicHomAuxiliaryScheme n).left,
        f ≫ (cyclicHomAuxiliaryScheme n).hom = g ≫ pointedCubicCoefficientBase W h₃ :=
  ⟨(pointedCubicAuxiliaryCover W h₃).left, (pointedCubicAuxiliaryCover W h₃).hom,
    inferInstance, inferInstance, (pointedCubicHomAuxiliaryParameter W h₃ φ).left,
    pointedCubicHomAuxiliaryParameter_base W h₃ φ⟩

end FLT.Mazur.OddWeierstrassParameter
