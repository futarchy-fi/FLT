/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.DiscreteFieldUnits
public import FLT.LocalClassFieldTheory.IntegralUnitInvariants

/-!
# Field units as invariant coefficients

For any closed normal Galois subgroup, its invariant field units are the
units of its fixed field. The comparison respects the quotient action.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

set_option backward.isDefEq.respectTransparency false

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  (N : ClosedSubgroup Gal(L/K))

attribute [local instance] fieldUnitAction

local notation "E" => IntermediateField.fixedField N.toSubgroup
local notation "ρ" => Representation.ofDistribMulAction ℤ Gal(L/K) (Additive Lˣ)

/-- Inclusion of the fixed-field units into the invariant coefficient module. -/
def fieldUnitInvariantInclusion : Additive Eˣ →ₗ[ℤ]
    Representation.invariants ((ρ).comp N.toSubgroup.subtype) :=
  (Units.map (E).val.toMonoidHom).toAdditive.toIntLinearMap.codRestrict _ fun u g => by
    apply Additive.toMul.injective
    apply Units.ext
    have h := (Additive.toMul u : Eˣ).val.property
    rw [IntermediateField.mem_fixedField_iff] at h
    exact h g g.property

/-- Fixed units descend together with their inverses. -/
theorem fieldUnitInvariantInclusion_bijective :
    Function.Bijective (fieldUnitInvariantInclusion K L N) := by
  constructor
  · intro u v h
    apply Additive.toMul.injective
    apply Units.ext
    apply Subtype.ext
    exact congrArg (fun w : Representation.invariants ((ρ).comp N.toSubgroup.subtype) =>
      (↑(Additive.toMul w.val) : L)) h
  · intro u
    have hx : (↑(Additive.toMul u.val) : L) ∈ E := by
      rw [IntermediateField.mem_fixedField_iff]
      intro g hg
      exact congrArg (fun w : Additive Lˣ => (↑(Additive.toMul w) : L))
        (u.property ⟨g, hg⟩)
    let x : E := ⟨↑(Additive.toMul u.val), hx⟩
    have hn : x ≠ 0 := fun h => (Additive.toMul u.val).ne_zero (congrArg Subtype.val h)
    refine ⟨Additive.ofMul (Units.mk0 x hn), ?_⟩
    apply Subtype.ext
    apply Additive.toMul.injective
    exact Units.ext rfl

/-- The actual coefficient equivalence with fixed-field units. -/
def fieldUnitInvariantEquiv : Additive Eˣ ≃ₗ[ℤ]
    Representation.invariants ((ρ).comp N.toSubgroup.subtype) :=
  LinearEquiv.ofBijective (fieldUnitInvariantInclusion K L N)
    (fieldUnitInvariantInclusion_bijective K L N)

variable [IsGalois K L] [N.Normal]

/-- The fixed-field coefficient equivalence intertwines the quotient Galois action. -/
theorem fieldUnitInvariantEquiv_equivariant (g : Gal(L/K) ⧸ N.toSubgroup)
    (u : Additive Eˣ) :
    fieldUnitInvariantEquiv K L N (InfiniteGalois.normalAutEquivQuotient N g • u) =
      (ρ).quotientToInvariants N.toSubgroup g (fieldUnitInvariantEquiv K L N u) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N.toSubgroup g
  apply Subtype.ext
  apply Additive.toMul.injective
  apply Units.ext
  exact AlgEquiv.restrictNormal_apply E g (Additive.toMul u : Eˣ)

/-- The induced comparison on ordinary cohomology in every degree. -/
def fieldUnitInvariantCohomologyIso (i : ℕ) :
    groupCohomology (Rep.of ((ρ).quotientToInvariants N.toSubgroup)) i ≅
      groupCohomology (Rep.ofAlgebraAutOnUnits K E) i := by
  apply CategoryTheory.Iso.symm
  refine groupCohomology.mapIso (InfiniteGalois.normalAutEquivQuotient N).symm
    (fieldUnitInvariantEquiv K L N) ?_ i
  intro g
  apply LinearMap.ext
  intro u
  change fieldUnitInvariantEquiv K L N (g • (show Additive Eˣ from u)) = _
  have h := fieldUnitInvariantEquiv_equivariant K L N
    ((InfiniteGalois.normalAutEquivQuotient N).symm g) u
  convert h using 1
  simp only [MulEquiv.apply_symm_apply]

end LocalClassFieldTheory
