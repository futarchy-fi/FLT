/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeCyclicSubgroupComparison
public import FLT.Mazur.PolygonCyclicDivisorPullback

/-!
# Comparing a cyclic marking with the actual pulled-back subgroup

The finite coproduct comparison retains each original component section.
Compatibility of sections therefore gives a compatible isomorphism with the
actual base change of the original Cartier subgroup.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve
open UniversallyDistinctSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S T : Scheme} {E : GeneralizedEllipticCurve S} {F : GeneralizedEllipticCurve T}
  {n : ℕ} [NeZero n] (g : T ⟶ S)
  (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ E.group))
  (ψ : Multiplicative (ZMod n) →* (𝟙_ (Over T) ⟶ F.group))
  (hφ : UniversallyDistinct (fun i : ZMod n ↦ φ (Multiplicative.ofAdd i)))
  (hψ : UniversallyDistinct (fun i : ZMod n ↦ ψ (Multiplicative.ofAdd i)))
  (e : F ≅ E.baseChange g)
  (h : ∀ i, ψ i ≫ e.hom.group =
    Functor.LaxMonoidal.ε (Over.pullback g) ≫ (Over.pullback g).map (φ i))

include h in
/-- The constant-group pullback comparison commutes with the actual subgroup inclusion. -/
theorem relativeCyclicSubgroup_pullback_inclusion :
    (F.relativeCyclicSubgroup ψ hψ).inclusion ≫ e.hom.group =
      (ConstantCyclicPullback.equivalence g n).hom ≫
        ((E.relativeCyclicSubgroup φ hφ).baseChange g).inclusion := by
  apply Sigma.hom_ext
  intro i
  change ConstantCyclicGroup.component T n i ≫
    (ConstantCyclicSectionMap.toScheme ψ ≫ e.hom.group) =
      ConstantCyclicGroup.component T n i ≫
        (ConstantCyclicPullback.equivalence g n).hom ≫
          (Over.pullback g).map (ConstantCyclicSectionMap.toScheme φ)
  rw [ConstantCyclicSectionMap.component_toScheme_assoc,
    ConstantCyclicPullback.component_equivalence_assoc, ← Functor.map_comp,
    ConstantCyclicSectionMap.component_toScheme]
  exact h _

/-- The original finite subgroup, including its curve inclusion, commutes with pullback. -/
def relativeCyclicSubgroupPullbackCompatibleIso :
    FiniteSubgroup.CompatibleIso (F.relativeCyclicSubgroup ψ hψ)
      ((E.relativeCyclicSubgroup φ hφ).baseChange g) where
  curve := e
  subgroup := ConstantCyclicPullback.equivalence g n
  isMonHom := ConstantCyclicPullback.equivalence_isMonHom g n
  compatible := by
    change ((F.relativeCyclicSubgroup ψ hψ).inclusion ≫ F.inclusion) ≫ e.hom.curve =
      (ConstantCyclicPullback.equivalence g n).hom ≫
        (((E.relativeCyclicSubgroup φ hφ).baseChange g).inclusion ≫
          (E.baseChange g).inclusion)
    rw [Category.assoc, e.hom.inclusion, ← Category.assoc,
      relativeCyclicSubgroup_pullback_inclusion g φ ψ hφ hψ e h, Category.assoc]

/-- The subgroup comparison retains the original generator under monoidal base change. -/
theorem relativeCyclicSubgroupPullbackCompatibleIso_generator :
    F.relativeCyclicGenerator ψ hψ ≫
      (relativeCyclicSubgroupPullbackCompatibleIso g φ ψ hφ hψ e h).subgroup.hom =
        Functor.LaxMonoidal.ε (Over.pullback g) ≫
          (Over.pullback g).map (E.relativeCyclicGenerator φ hφ) :=
  ConstantCyclicPullback.component_equivalence g n 1

end FLT.Mazur.GeneralizedEllipticCurve
