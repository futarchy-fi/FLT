/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityGlobalDomain
public import FLT.Mazur.WeierstrassTripleFullInputs

/-!
# The genuine all-infinity member of the full triple cover

Select the original infinity addition neighborhood for all four laws in the
existing full cover. The resulting projections preserve the original pairs,
so this is a concrete open of the actual triple product, not a formal domain.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

/-- The infinity neighborhood is an original member of the global addition cover. -/
def infinityAdditionCoverIndex : (integralCurveAdditionCover W hΔ).I₀ :=
  ⟨⟨true, true⟩, ⟨.infinity, PUnit.unit⟩⟩

/-- Its actual global input map is the original infinity-domain inclusion. -/
theorem infinityAdditionCoverIndex_map :
    (integralCurveAdditionCover W hΔ).f (infinityAdditionCoverIndex W hΔ) =
      infinityGlobalDomain W := by
  change (𝟙 _ ≫ infinityAdditionInclusion W) ≫ integralCurveProductChart W true true = _
  rw [Category.id_comp]
  rfl

/-- Its actual local law is the normalized infinity formula. -/
theorem infinityAdditionCoverIndex_local :
    integralCurveAdditionLocal W hΔ (infinityAdditionCoverIndex W hΔ) =
      infinityAdditionSpec W ≫ integralCurveChart W 1 := rfl

/-- Choose all four original infinity neighborhoods in the existing full refinement. -/
def infinityTripleFullIndex : (integralCurveTripleFullCover W hΔ).I₀ :=
  ⟨⟨infinityAdditionCoverIndex W hΔ, infinityAdditionCoverIndex W hΔ⟩,
    ⟨infinityAdditionCoverIndex W hΔ, infinityAdditionCoverIndex W hΔ⟩⟩

/-- The actual all-infinity open in the full triple cover. -/
abbrev InfinityTripleFull :=
  (integralCurveTripleFullCover W hΔ).X (infinityTripleFullIndex W hΔ)

/-- Its inclusion into the original triple product. -/
abbrev infinityTripleFullMap : InfinityTripleFull W hΔ ⟶ integralCurveTriple W :=
  (integralCurveTripleFullCover W hΔ).f (infinityTripleFullIndex W hΔ)

/-- Projection to the first actual inner infinity domain. -/
def infinityTripleFullFirst : InfinityTripleFull W hΔ ⟶ Spec (.of (InfinityAdditionOpen W)) :=
  integralCurveTripleFullInner W hΔ (infinityTripleFullIndex W hΔ) ≫
    integralCurveTripleInnerLeftDomain W hΔ (infinityTripleFullIndex W hΔ).2

/-- Projection to the last actual inner infinity domain. -/
def infinityTripleFullLast : InfinityTripleFull W hΔ ⟶ Spec (.of (InfinityAdditionOpen W)) :=
  integralCurveTripleFullInner W hΔ (infinityTripleFullIndex W hΔ) ≫
    integralCurveTripleInnerRightDomain W hΔ (infinityTripleFullIndex W hΔ).2

/-- Projection to the left actual outer infinity domain. -/
def infinityTripleFullLeft : InfinityTripleFull W hΔ ⟶ Spec (.of (InfinityAdditionOpen W)) :=
  integralCurveTripleFullOuter W hΔ (infinityTripleFullIndex W hΔ) ≫
    integralCurveTripleLeftDomain W hΔ (infinityTripleFullIndex W hΔ).1

/-- Projection to the right actual outer infinity domain. -/
def infinityTripleFullRight : InfinityTripleFull W hΔ ⟶ Spec (.of (InfinityAdditionOpen W)) :=
  integralCurveTripleFullOuter W hΔ (infinityTripleFullIndex W hΔ) ≫
    integralCurveTripleRightDomain W hΔ (infinityTripleFullIndex W hΔ).1

/-- The first infinity law has the actual first input pair. -/
theorem infinityTripleFullFirst_inputs :
    infinityTripleFullFirst W hΔ ≫ infinityGlobalDomain W =
      infinityTripleFullMap W hΔ ≫ integralCurveTriplePair W := by
  have he := integralCurveTripleInnerLeftDomain_inputs W hΔ
    (infinityTripleFullIndex W hΔ).2
  change integralCurveTripleInnerLeftDomain W hΔ (infinityTripleFullIndex W hΔ).2 ≫
    (integralCurveAdditionCover W hΔ).f (infinityAdditionCoverIndex W hΔ) = _ at he
  rw [infinityAdditionCoverIndex_map] at he
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun a => integralCurveTripleFullInner W hΔ
      (infinityTripleFullIndex W hΔ) ≫ a) he).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun a => a ≫ integralCurveTriplePair W)
          (integralCurveTripleFullInner_inputs W hΔ (infinityTripleFullIndex W hΔ)))))

/-- The last infinity law has the actual last input pair. -/
theorem infinityTripleFullLast_inputs :
    infinityTripleFullLast W hΔ ≫ infinityGlobalDomain W =
      infinityTripleFullMap W hΔ ≫ integralCurveTripleLastPair W := by
  have he := integralCurveTripleInnerRightDomain_inputs W hΔ
    (infinityTripleFullIndex W hΔ).2
  change integralCurveTripleInnerRightDomain W hΔ (infinityTripleFullIndex W hΔ).2 ≫
    (integralCurveAdditionCover W hΔ).f (infinityAdditionCoverIndex W hΔ) = _ at he
  rw [infinityAdditionCoverIndex_map] at he
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun a => integralCurveTripleFullInner W hΔ
      (infinityTripleFullIndex W hΔ) ≫ a) he).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun a => a ≫ integralCurveTripleLastPair W)
          (integralCurveTripleFullInner_inputs W hΔ (infinityTripleFullIndex W hΔ)))))

/-- The left infinity law has the actual first sum and third input. -/
theorem infinityTripleFullLeft_inputs :
    infinityTripleFullLeft W hΔ ≫ infinityGlobalDomain W =
      infinityTripleFullMap W hΔ ≫ integralCurveAddFirstPair W hΔ := by
  have he := integralCurveTripleFull_leftPair W hΔ (infinityTripleFullIndex W hΔ)
  change integralCurveTripleFullOuter W hΔ (infinityTripleFullIndex W hΔ) ≫
    integralCurveTripleLeftDomain W hΔ (infinityTripleFullIndex W hΔ).1 ≫
    (integralCurveAdditionCover W hΔ).f (infinityAdditionCoverIndex W hΔ) = _ at he
  rw [infinityAdditionCoverIndex_map] at he
  exact (Category.assoc _ _ _).trans he

/-- The right infinity law has the actual first input and last sum. -/
theorem infinityTripleFullRight_inputs :
    infinityTripleFullRight W hΔ ≫ infinityGlobalDomain W =
      infinityTripleFullMap W hΔ ≫ integralCurveAddLastPair W hΔ := by
  have he := integralCurveTripleFull_rightPair W hΔ (infinityTripleFullIndex W hΔ)
  change integralCurveTripleFullOuter W hΔ (infinityTripleFullIndex W hΔ) ≫
    integralCurveTripleRightDomain W hΔ (infinityTripleFullIndex W hΔ).1 ≫
    (integralCurveAdditionCover W hΔ).f (infinityAdditionCoverIndex W hΔ) = _ at he
  rw [infinityAdditionCoverIndex_map] at he
  exact (Category.assoc _ _ _).trans he

end FLT.Mazur.WeierstrassIntegralChart
