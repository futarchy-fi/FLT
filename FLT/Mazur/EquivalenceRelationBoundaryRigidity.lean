/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationBoundaryTestDescent
public import FLT.Mazur.SchemeFiniteGroupFreeRigidity

/-!
# Rigidity of the actual normalized boundary chart covers

The original normalized-frame action is free. Its full boundary chart and
every test-ideal-power chart are therefore formally unramified over their
unchanged coefficient schemes. This concerns the chart covers, not the
still-unidentified original scalar-image projection.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open AffineScalarBoundaryNilpotence FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] source action restrictedAction boundaryProduct
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (n : ℕ) (o : Fin n) (U : (source p q (Fin n) o).Opens)
  (e : CategoryTheory.EquivalenceRelation p q)
  (hU : ∀ g : Equiv.Perm (Fin n), (action e (Fin n) o g).hom ⁻¹ᵁ U = U)
  [IsAffine U.toScheme]
  {R T : Type} [CommRing R] [CommRing T]
  (s : R →+* invariantCoordinates (restrictedAction (action e (Fin n) o) U hU))
  (κ : R →+* T)
local notation "ρ" => restrictedAction (action e (Fin n) o) U hU
local notation "π" => chartBoundaryProduct n o U e hU s κ

/-- Freeness proves rigidity of the full original boundary chart without a residue hypothesis. -/
theorem chartBoundaryProduct_formallyUnramified : FormallyUnramified π := by
  let _ := quotientMap_formallyUnramified_of_free ρ (boundaryChart_action_free n o U e hU)
  unfold chartBoundaryProduct
  exact MorphismProperty.pullback_snd _ _ inferInstance

/-- On the full chart, a nilpotent test detects exact arrows over the original product. -/
theorem chartBoundaryProduct_nilpotent_hom_ext {Z Z₀ : Scheme.{0}} (i : Z₀ ⟶ Z)
    [IsClosedImmersion i] (hi : IsNilpotent i.ker)
    (a b : Z ⟶ chartBoundary n o U e hU s κ)
    (hab : i ≫ a = i ≫ b) (hs : a ≫ π = b ≫ π) : a = b := by
  let _ := chartBoundaryProduct_formallyUnramified n o U e hU s κ
  exact FormallyUnramified.hom_ext i hi π hab hs

variable [Etale p] [TopologicalSpace.NoetherianSpace U.toScheme] (k : ℕ)

/-- Every full ideal-power test chart inherits rigidity at its original order. -/
theorem boundaryTestChartProjection_formallyUnramified :
    FormallyUnramified (boundaryTestChartProjection n o U e hU s κ k) := by
  let _ := quotientMap_formallyUnramified_of_free ρ (boundaryChart_action_free n o U e hU)
  unfold boundaryTestChartProjection
  exact MorphismProperty.pullback_snd _ _ inferInstance

end FLT.Mazur.EquivalenceRelationNormalizedFrames
