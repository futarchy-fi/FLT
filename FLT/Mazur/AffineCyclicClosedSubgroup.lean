/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.AffineRationalGroupSection
public import FLT.Mazur.RationalCyclicSubgroup

/-!
# The closed subgroup of a specified affine cyclic embedding

Every label maps to its original affine point. The finite etale degree is
scheme-theoretic, and membership in the original subgroup is retained.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj

namespace FLT.Mazur.WeierstrassIntegralChart

variable {K : Type} [Field K] [DecidableEq K] (W : WeierstrassCurve K) [W.IsElliptic]
  {n : ℕ} (f : ZMod n →+ W.toAffine.Point) (hf : Function.Injective f)

/-- The prescribed affine cyclic embedding as a homomorphism into actual sections. -/
def affineCyclicSections : Multiplicative (ZMod n) →*
    (𝟙_ (Over (Spec (.of K))) ⟶ (integralGeneralizedEllipticCurve W W.isUnit_Δ).group) :=
  ((affineRationalGroupSectionAddHom W).comp f).toMultiplicativeLeft

/-- The section marking retains precisely the original affine value. -/
theorem affineCyclicSections_apply (i : ZMod n) :
    affineCyclicSections W f (Multiplicative.ofAdd i) =
      (affineRationalGroupSectionAddHom W (f i)).toMul := rfl

include hf in
/-- The section marking remains injective. -/
theorem affineCyclicSections_injective : Function.Injective (affineCyclicSections W f) := by
  intro i j h
  exact congrArg Multiplicative.ofAdd
    (hf (affineRationalGroupSectionAddHom_injective W h))

variable [NeZero n]

/-- The actual finite etale closed subgroup constructed from the affine embedding. -/
def affineCyclicClosedSubgroup :
    (integralGeneralizedEllipticCurve W W.isUnit_Δ).FiniteSubgroup n := by
  have : IsSeparated (integralGeneralizedEllipticCurve W W.isUnit_Δ).group.hom :=
    inferInstanceAs (IsSeparated (integralCurveStructure W))
  exact
    { carrier := ConstantCyclicGroup.model (Spec (.of K)) n
      inclusion := ConstantCyclicSectionMap.toScheme (affineCyclicSections W f)
      closed := ConstantCyclicSectionClosed.closed _ (affineCyclicSections_injective W f hf)
      degree := ConstantCyclicFiniteEtale.degree K n }

/-- The finite closed subgroup is etale over the field. -/
theorem affineCyclicClosedSubgroup_etale :
    Etale (affineCyclicClosedSubgroup W f hf).carrier.hom :=
  ConstantCyclicFiniteEtale.etale K n

/-- Every component recovers exactly the specified affine point as a scheme section. -/
theorem affineCyclicClosedSubgroup_component (i : ZMod n) :
    ConstantCyclicGroup.component (Spec (.of K)) n i ≫
      (affineCyclicClosedSubgroup W f hf).inclusion =
        (affineRationalGroupSectionAddHom W (f i)).toMul :=
  ConstantCyclicSectionMap.component_toScheme (affineCyclicSections W f) i

/-- The original affine image is exactly the set of included component sections. -/
theorem affineCyclicClosedSubgroup_mem (P : W.toAffine.Point) :
    (∃ i : ZMod n, ConstantCyclicGroup.component (Spec (.of K)) n i ≫
      (affineCyclicClosedSubgroup W f hf).inclusion =
        (affineRationalGroupSectionAddHom W P).toMul) ↔ P ∈ f.range := by
  simp only [affineCyclicClosedSubgroup_component]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, affineRationalGroupSectionAddHom_injective W hi⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, rfl⟩

/-- Its closed immersion has the actual product of the original point ideals as kernel. -/
theorem affineCyclicClosedSubgroup_kernel :
    (affineCyclicClosedSubgroup W f hf).inclusion.left.ker =
      ∏ i : ZMod n, ((affineRationalGroupSectionAddHom W (f i)).toMul).left.ker := by
  have : IsSeparated (integralGeneralizedEllipticCurve W W.isUnit_Δ).group.hom :=
    inferInstanceAs (IsSeparated (integralCurveStructure W))
  exact (ConstantCyclicSectionClosed.product_eq_kernel (affineCyclicSections W f)
    (affineCyclicSections_injective W f hf)).symm

end FLT.Mazur.WeierstrassIntegralChart
