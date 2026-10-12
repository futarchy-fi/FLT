/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeCyclicSubgroup
public import FLT.Mazur.CompatibleSubgroupIso

/-!
# Compatible comparisons of subgroups constructed from cyclic markings

A full generalized-curve comparison carrying each cyclic section to its
counterpart preserves the actual constant subgroup and its whole-curve inclusion.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve
open UniversallyDistinctSections
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {E F : GeneralizedEllipticCurve S} {n : ℕ} [NeZero n]
  (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ E.group))
  (ψ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ F.group))
  (hφ : UniversallyDistinct (fun i : ZMod n ↦ φ (Multiplicative.ofAdd i)))
  (hψ : UniversallyDistinct (fun i : ZMod n ↦ ψ (Multiplicative.ofAdd i)))
  (e : E ≅ F) (h : ∀ i, φ i ≫ e.hom.group = ψ i)

include h in
/-- Section compatibility implies compatibility of the actual subgroup inclusions. -/
theorem relativeCyclicSubgroup_compare_inclusion :
    (E.relativeCyclicSubgroup φ hφ).inclusion ≫ e.hom.group =
      (F.relativeCyclicSubgroup ψ hψ).inclusion := by
  apply Sigma.hom_ext
  intro i
  change ConstantCyclicGroup.component S n i ≫
    (ConstantCyclicSectionMap.toScheme φ ≫ e.hom.group) =
      ConstantCyclicGroup.component S n i ≫ ConstantCyclicSectionMap.toScheme ψ
  rw [ConstantCyclicSectionMap.component_toScheme_assoc,
    ConstantCyclicSectionMap.component_toScheme]
  exact h _

/-- The original constructed subgroups are compatibly isomorphic, with every label retained. -/
def relativeCyclicSubgroupCompatibleIso :
    FiniteSubgroup.CompatibleIso (E.relativeCyclicSubgroup φ hφ)
      (F.relativeCyclicSubgroup ψ hψ) where
  curve := e
  subgroup := Iso.refl (ConstantCyclicGroup.model S n)
  isMonHom := inferInstanceAs (IsMonHom (𝟙 (ConstantCyclicGroup.model S n)))
  compatible := by
    change ((E.relativeCyclicSubgroup φ hφ).inclusion ≫ E.inclusion) ≫ e.hom.curve =
      (𝟙 _) ≫ ((F.relativeCyclicSubgroup ψ hψ).inclusion ≫ F.inclusion)
    rw [Category.id_comp, Category.assoc, e.hom.inclusion, ← Category.assoc,
      relativeCyclicSubgroup_compare_inclusion φ ψ hφ hψ e h]

/-- The compatible subgroup comparison retains the specified Cartier-generator section. -/
theorem relativeCyclicSubgroupCompatibleIso_generator :
    E.relativeCyclicGenerator φ hφ ≫
      (relativeCyclicSubgroupCompatibleIso φ ψ hφ hψ e h).subgroup.hom =
        F.relativeCyclicGenerator ψ hψ := Category.comp_id _

end FLT.Mazur.GeneralizedEllipticCurve
