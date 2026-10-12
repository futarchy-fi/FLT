/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearAction
public import FLT.Mazur.WeierstrassCoefficientShearSpecialization
public import FLT.Mazur.WeierstrassSmoothCoefficientSpecialization

/-!
# Functoriality of the full original action under coefficient specialization

The actual coefficient map specializes both the original smooth input and the
entire glued model input. The original integral action determines the output.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
  (r : S) (v : T) (j : ℕ) (hj : j ≤ n) (f : S →ₐ[R] T)
local notation "fS" => integralSmoothStructure (W.map (algebraMap R S))
local notation "fT" => integralSmoothStructure (W.map (algebraMap R T))
local notation "gS" => coefficientShearGluedStructure hπ data S r j hj
local notation "gT" => coefficientShearGluedStructure hπ data T v j hj
local notation "M" => coefficientShearSpecialization hπ data S T r v j hj f
local notation "U" => originalSmoothSpecialization W f
local notation "b" => Spec.map (CommRingCat.ofHom f.toRingHom)
local notation "PS" => coefficientShearOriginalActionProduct hπ data S r j hj
local notation "PT" => coefficientShearOriginalActionProduct hπ data T v j hj

/-- The specialized original smooth input and full model input lie over the same base. -/
theorem coefficientShearSpecializationDomain_condition :
    (pullback.fst fT gT ≫ U) ≫ fS = (pullback.snd fT gT ≫ M) ≫ gS := by
  simp only [Category.assoc, originalSmoothSpecialization_structure,
    coefficientShearSpecialization_structure]
  simpa only [Category.assoc] using
    congrArg (· ≫ b) (pullback.condition (f := fT) (g := gT))

/-- The genuine coefficient specialization on the entire original action domain. -/
def coefficientShearSpecializationDomain :
    coefficientShearActionDomain hπ data T v j hj ⟶
      coefficientShearActionDomain hπ data S r j hj :=
  pullback.lift (pullback.fst fT gT ≫ U) (pullback.snd fT gT ≫ M)
    (coefficientShearSpecializationDomain_condition hπ data S T r v j hj f)

/-- Specialization retains the whole original smooth parameter map. -/
@[reassoc] theorem coefficientShearSpecializationDomain_parameter :
    coefficientShearSpecializationDomain hπ data S T r v j hj f ≫ pullback.fst fS gS =
      pullback.fst fT gT ≫ U := pullback.lift_fst _ _ _

/-- Specialization retains the entire original model map. -/
@[reassoc] theorem coefficientShearSpecializationDomain_model :
    coefficientShearSpecializationDomain hπ data S T r v j hj f ≫ pullback.snd fS gS =
      pullback.snd fT gT ≫ M := pullback.lift_snd _ _ _

/-- Both specialized inputs retain their original integral domain pair. -/
@[reassoc] theorem coefficientShearSpecializationDomain_original :
    coefficientShearSpecializationDomain hπ data S T r v j hj f ≫ PS = PT := by
  apply pullback.hom_ext
  · rw [Category.assoc, coefficientShearOriginalActionProduct_parameter,
      coefficientShearSpecializationDomain_parameter_assoc,
      originalSmoothSpecialization_projection, coefficientShearOriginalActionProduct_parameter]
  · rw [Category.assoc, coefficientShearOriginalActionProduct_model,
      coefficientShearSpecializationDomain_model_assoc,
      coefficientShearSpecialization_projection, coefficientShearOriginalActionProduct_model]

/-- The independently constructed complete action commutes with actual coefficient change. -/
theorem coefficientShearAction_specialization :
    coefficientShearAction hπ data T v j hj ≫ M =
      coefficientShearSpecializationDomain hπ data S T r v j hj f ≫
        coefficientShearAction hπ data S r j hj := by
  apply (coefficientShearGlued_isPullback hπ data S r j hj).hom_ext
  · simp only [Category.assoc]
    rw [coefficientShearSpecialization_structure, coefficientShearAction_structure_assoc,
      coefficientShearAction_structure, coefficientShearSpecializationDomain_parameter_assoc,
      originalSmoothSpecialization_structure]
    simp only [integralSmoothStructure, Category.assoc]
  · simp only [Category.assoc]
    rw [coefficientShearSpecialization_projection, coefficientShearAction_projection,
      coefficientShearAction_projection, coefficientShearSpecializationDomain_original_assoc]

end FLT.Mazur.WeierstrassDividedDepth
