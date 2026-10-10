/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSmoothIntegralSection
public import FLT.Mazur.WeierstrassSmoothPointEquiv
public import FLT.Mazur.EllipticReductionKernel

/-!
# Arithmetic E₀ equals the actual smooth integral sections

Every section of the smooth integral scheme has a unique classical generic
point. The geometric smoothness criterion puts that point in the original
arithmetic subgroup, giving a bijection that retains both generic and special
restriction maps. Compatibility with geometric addition is a separate statement.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {K : Type u} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)

/-- Sections of the actual relative smooth scheme over the original valuation ring. -/
abbrev smoothIntegralSection :=
  Over.mk (𝟙 (Spec (.of A))) ⟶ Over.mk (integralSmoothStructure W)

/-- An original arithmetic E₀ point defines a section over the coefficient spectrum. -/
def e0ToSmoothSection (P : ellipticE0 A W) : smoothIntegralSection A W :=
  Over.homMk (smoothIntegralPointSection A W P.val P.property)
    (smoothIntegralPointSection_structure A W P.val P.property)

/-- Generic restriction of an actual integral smooth section. -/
def smoothSectionGeneric (s : smoothIntegralSection A W) :
    smoothCurveFieldPoint (K := K) W :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ s.left)
    (by rw [Category.assoc, s.w]; exact Category.comp_id _)

/-- The generic restriction remembers the exact point of the original subgroup. -/
theorem e0ToSmoothSection_generic (P : ellipticE0 A W) :
    smoothSectionGeneric A W (e0ToSmoothSection A W P) = projectiveToSmoothOver W P.val := by
  apply Over.OverMorphism.ext
  exact smoothIntegralPointSection_generic A W P.val P.property

/-- Distinct points of the original E₀ subgroup define distinct smooth sections. -/
theorem e0ToSmoothSection_injective : Function.Injective (e0ToSmoothSection A W) := by
  intro P Q h
  apply Subtype.ext
  apply projectiveToSmoothOver_injective W
  rw [← e0ToSmoothSection_generic A W P, ← e0ToSmoothSection_generic A W Q, h]

/-- Every smooth integral section comes from the actual arithmetic E₀ subgroup. -/
theorem e0ToSmoothSection_surjective : Function.Surjective (e0ToSmoothSection A W) := by
  intro s
  obtain ⟨P, hP⟩ := projectiveToSmoothOver_surjective W (smoothSectionGeneric A W s)
  have hg : Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ s.left =
      projectiveToSmooth W P := (congrArg Over.Hom.left hP).symm
  have hs : SmoothReduction A W P :=
    (smoothReduction_iff_exists_smooth_section A W P).mpr ⟨s.left, s.w, hg⟩
  refine ⟨⟨P, hs⟩, Over.OverMorphism.ext ?_⟩
  exact (smoothIntegralPointSection_unique A W P hs s.left s.w hg).symm

/-- The original subgroup and the actual integral smooth sections are canonically equivalent. -/
def e0SmoothSectionEquiv : ellipticE0 A W ≃ smoothIntegralSection A W :=
  Equiv.ofBijective (e0ToSmoothSection A W)
    ⟨e0ToSmoothSection_injective A W, e0ToSmoothSection_surjective A W⟩

/-- Special restriction of this equivalence is the original arithmetic reduction homomorphism. -/
theorem e0SmoothSectionEquiv_special (P : ellipticE0 A W) :
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
        (e0SmoothSectionEquiv A W P).left =
      projectiveToSmooth W (smoothReductionHom A W P) :=
  smoothIntegralPointSection_special A W P.val P.property

end FLT.Mazur.WeierstrassIntegralChart
