/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityTripleCommonInputs
public import FLT.Mazur.WeierstrassSpecSections

/-!
# Global-section algebras on the all-infinity triple member

The four genuine domain projections induce coefficient-preserving algebra maps
into the same global-section ring. Their five input identities are inherited
from the actual triple product, with no equality of final outputs assumed.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open FLT.Mazur.ProjectiveSpace

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

/-- The actual five input identities on this full-cover member. -/
theorem infinityTripleFull_inputRelations :
    infinityTripleFullFirst W hΔ ≫ Spec.map (CommRingCat.ofHom (infinityInputRight W).toRingHom) =
      infinityTripleFullLast W hΔ ≫ Spec.map (CommRingCat.ofHom (infinityInputLeft W).toRingHom) ∧
    infinityTripleFullLeft W hΔ ≫ Spec.map (CommRingCat.ofHom (infinityInputLeft W).toRingHom) =
        infinityTripleFullFirst W hΔ ≫ infinityAdditionSpec W ∧
    infinityTripleFullLeft W hΔ ≫ Spec.map (CommRingCat.ofHom (infinityInputRight W).toRingHom) =
      infinityTripleFullLast W hΔ ≫ Spec.map (CommRingCat.ofHom (infinityInputRight W).toRingHom) ∧
    infinityTripleFullRight W hΔ ≫ Spec.map (CommRingCat.ofHom (infinityInputLeft W).toRingHom) =
      infinityTripleFullFirst W hΔ ≫ Spec.map (CommRingCat.ofHom (infinityInputLeft W).toRingHom) ∧
    infinityTripleFullRight W hΔ ≫ Spec.map (CommRingCat.ofHom (infinityInputRight W).toRingHom) =
        infinityTripleFullLast W hΔ ≫ infinityAdditionSpec W :=
  infinityTriple_commonInputs W hΔ (infinityTripleFullMap W hΔ)
    (infinityTripleFullFirst W hΔ) (infinityTripleFullLast W hΔ)
    (infinityTripleFullLeft W hΔ) (infinityTripleFullRight W hΔ)
    (infinityTripleFullFirst_inputs W hΔ) (infinityTripleFullLast_inputs W hΔ)
    (infinityTripleFullLeft_inputs W hΔ) (infinityTripleFullRight_inputs W hΔ)

/-- The coefficient map of the first domain projection. -/
def infinityTripleFullBase : InfinityTripleFull W hΔ ⟶ Spec (.of R) :=
  infinityTripleFullFirst W hΔ ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (InfinityAdditionOpen W)))

/-- The last domain projection has the same coefficient map. -/
theorem infinityTripleFullLast_base :
    infinityTripleFullLast W hΔ ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (InfinityAdditionOpen W))) =
      infinityTripleFullBase W hΔ := by
  have he := congrArg (fun a => a ≫ chartStructure W 1)
    (infinityTripleFull_inputRelations W hΔ).1
  simp only [Category.assoc, chartStructure, specAlgHom_base] at he
  exact he.symm

/-- The left domain projection has the same coefficient map. -/
theorem infinityTripleFullLeft_base :
    infinityTripleFullLeft W hΔ ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (InfinityAdditionOpen W))) =
      infinityTripleFullBase W hΔ := by
  have he := congrArg (fun a => a ≫ chartStructure W 1)
    (infinityTripleFull_inputRelations W hΔ).2.1
  simp only [Category.assoc, chartStructure, infinityAdditionSpec, specAlgHom_base] at he
  exact he

/-- The right domain projection has the same coefficient map. -/
theorem infinityTripleFullRight_base :
    infinityTripleFullRight W hΔ ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (InfinityAdditionOpen W))) =
      infinityTripleFullBase W hΔ := by
  have he := congrArg (fun a => a ≫ chartStructure W 1)
    (infinityTripleFull_inputRelations W hΔ).2.2.2.1
  simp only [Category.assoc, chartStructure, specAlgHom_base] at he
  exact he

/-- The common coefficient algebra on global sections of the true all-infinity open. -/
@[instance_reducible] def infinityTripleFullSectionAlgebra :
    Algebra R Γ(InfinityTripleFull W hΔ, ⊤) := specSectionAlgebra (infinityTripleFullBase W hΔ)

attribute [local instance] infinityTripleFullSectionAlgebra

/-- The actual first infinity law specialized to the common global-section algebra. -/
def infinityTripleFullFirstAlg : InfinityAdditionOpen W →ₐ[R] Γ(InfinityTripleFull W hΔ, ⊤) :=
  specSectionAlgHom (infinityTripleFullBase W hΔ) (infinityTripleFullFirst W hΔ) rfl

/-- The actual last infinity law specialized to the common global-section algebra. -/
def infinityTripleFullLastAlg : InfinityAdditionOpen W →ₐ[R] Γ(InfinityTripleFull W hΔ, ⊤) :=
  specSectionAlgHom (infinityTripleFullBase W hΔ) (infinityTripleFullLast W hΔ)
    (infinityTripleFullLast_base W hΔ)

/-- The actual left infinity law specialized to the common global-section algebra. -/
def infinityTripleFullLeftAlg : InfinityAdditionOpen W →ₐ[R] Γ(InfinityTripleFull W hΔ, ⊤) :=
  specSectionAlgHom (infinityTripleFullBase W hΔ) (infinityTripleFullLeft W hΔ)
    (infinityTripleFullLeft_base W hΔ)

/-- The actual right infinity law specialized to the common global-section algebra. -/
def infinityTripleFullRightAlg : InfinityAdditionOpen W →ₐ[R] Γ(InfinityTripleFull W hΔ, ⊤) :=
  specSectionAlgHom (infinityTripleFullBase W hΔ) (infinityTripleFullRight W hΔ)
    (infinityTripleFullRight_base W hΔ)

/-- The middle input relation holds in the actual common coefficient algebra. -/
theorem infinityTripleFullAlg_middle :
    (infinityTripleFullFirstAlg W hΔ).comp (infinityInputRight W) =
      (infinityTripleFullLastAlg W hΔ).comp (infinityInputLeft W) :=
  specSectionAlgHom_comp_eq (infinityTripleFullBase W hΔ)
    (infinityTripleFullFirst W hΔ) (infinityTripleFullLast W hΔ)
    rfl (infinityTripleFullLast_base W hΔ) _ _
    (infinityTripleFull_inputRelations W hΔ).1

/-- The left input relation holds in the actual common coefficient algebra. -/
theorem infinityTripleFullAlg_left :
    (infinityTripleFullLeftAlg W hΔ).comp (infinityInputLeft W) =
      (infinityTripleFullFirstAlg W hΔ).comp (infinityAdditionChart W) :=
  specSectionAlgHom_comp_eq (infinityTripleFullBase W hΔ)
    (infinityTripleFullLeft W hΔ) (infinityTripleFullFirst W hΔ)
    (infinityTripleFullLeft_base W hΔ) rfl _ _
    (infinityTripleFull_inputRelations W hΔ).2.1

/-- The third input relation holds in the actual common coefficient algebra. -/
theorem infinityTripleFullAlg_third :
    (infinityTripleFullLeftAlg W hΔ).comp (infinityInputRight W) =
      (infinityTripleFullLastAlg W hΔ).comp (infinityInputRight W) :=
  specSectionAlgHom_comp_eq (infinityTripleFullBase W hΔ)
    (infinityTripleFullLeft W hΔ) (infinityTripleFullLast W hΔ)
    (infinityTripleFullLeft_base W hΔ) (infinityTripleFullLast_base W hΔ) _ _
    (infinityTripleFull_inputRelations W hΔ).2.2.1

/-- The first input relation holds in the actual common coefficient algebra. -/
theorem infinityTripleFullAlg_first :
    (infinityTripleFullRightAlg W hΔ).comp (infinityInputLeft W) =
      (infinityTripleFullFirstAlg W hΔ).comp (infinityInputLeft W) :=
  specSectionAlgHom_comp_eq (infinityTripleFullBase W hΔ)
    (infinityTripleFullRight W hΔ) (infinityTripleFullFirst W hΔ)
    (infinityTripleFullRight_base W hΔ) rfl _ _
    (infinityTripleFull_inputRelations W hΔ).2.2.2.1

/-- The right input relation holds in the actual common coefficient algebra. -/
theorem infinityTripleFullAlg_right :
    (infinityTripleFullRightAlg W hΔ).comp (infinityInputRight W) =
      (infinityTripleFullLastAlg W hΔ).comp (infinityAdditionChart W) :=
  specSectionAlgHom_comp_eq (infinityTripleFullBase W hΔ)
    (infinityTripleFullRight W hΔ) (infinityTripleFullLast W hΔ)
    (infinityTripleFullRight_base W hΔ) (infinityTripleFullLast_base W hΔ) _ _
    (infinityTripleFull_inputRelations W hΔ).2.2.2.2

end FLT.Mazur.WeierstrassIntegralChart
