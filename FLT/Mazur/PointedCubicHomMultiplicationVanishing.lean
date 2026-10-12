/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicHomMultiplicationEquation
public import FLT.Mazur.PointedCubicHomRetainedSubgroup

/-!
# Original cyclic subgroups satisfy the full source multiplication equation

The original Cartier subgroup is retained on the auxiliary cover. Its proven
ideal equality forces vanishing of the actual multiplication obstruction;
no new subgroup witness or distinctness hypothesis is supplied by the caller.
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
  (H : (pointedCubicFamily W).FiniteSubgroup n)
  {P : 𝟙_ (Over S) ⟶ H.carrier} (hP : H.IsCartierGenerator P)
  (hφ : H.generatorCurveMarking hP = φ)
local notation "f" => Over.Hom.left (pointedCubicHomAuxiliaryParameter W h₂ φ)

include hφ in
/-- The original parameter kills the entire scheme-theoretic multiplication obstruction. -/
theorem pointedCubicHomMultiplicationEquation_zero : cyclicHomMultiplicationEquation n f = 0 :=
  cyclicHomMultiplicationEquation_of_subgroup n f (pointedCubicHomRetainedSubgroup W h₂ φ H)
    (pointedCubicHomRetained_ideal W h₂ φ H hP hφ)

/-- The subgroup reconstructed from vanishing has exactly the retained original ideal. -/
theorem pointedCubicHomEquationSubgroup_ideal :
    (cyclicHomSubgroup n f (pointedCubicHomMultiplicationEquation_zero W h₂ φ H hP hφ)).ideal =
      (pointedCubicHomRetainedSubgroup W h₂ φ H).ideal := by
  rw [cyclicHomSubgroup_ideal, pointedCubicHomRetained_ideal W h₂ φ H hP hφ]

/-- The reconstructed subgroup is compatibly isomorphic to the actual retained original. -/
def pointedCubicHomEquationSubgroupIso : FiniteSubgroup.CompatibleIso
    (cyclicHomSubgroup n f (pointedCubicHomMultiplicationEquation_zero W h₂ φ H hP hφ))
    (pointedCubicHomRetainedSubgroup W h₂ φ H) :=
  FiniteSubgroup.compatibleIsoOfIdealEq _ _ (pointedCubicHomEquationSubgroup_ideal W h₂ φ H hP hφ)

end FLT.Mazur.GeneralizedEllipticCurve
