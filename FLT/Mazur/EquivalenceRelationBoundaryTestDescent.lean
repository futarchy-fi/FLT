/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationBoundaryFaithful
public import FLT.Mazur.EquivalenceRelationBoundaryTestFactorization

/-!
# Effective descent on every original test neighborhood

The original matching-rank chart is a finite faithfully flat cover of the
full test-ideal neighborhood at every order. The neighborhood retains its
actual coefficients and nilpotents. Coverage of the whole product is separate.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open RelativeOrderedTuples AffineScalarBoundaryNilpotence
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] source action restrictedAction boundaryProduct boundaryCoordinate
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (n : ℕ) (o : Fin n) (U : (source p q (Fin n) o).Opens)
  (e : CategoryTheory.EquivalenceRelation p q)
  (hU : ∀ g : Equiv.Perm (Fin n), (action e (Fin n) o g).hom ⁻¹ᵁ U = U)
  [IsAffine U.toScheme] [TopologicalSpace.NoetherianSpace U.toScheme]
  {R T : Type} [CommRing R] [CommRing T]
  (s : R →+* invariantCoordinates (restrictedAction (action e (Fin n) o) U hU))
  (κ : R →+* T) (k : ℕ)
local notation "ρ" => restrictedAction (action e (Fin n) o) U hU
local notation "tests" => completeAffineOrbitTests e (Fin n) o U hU
local notation "π" => boundaryTestChartProjection n o U e hU s κ k

/-- Each full original test neighborhood is affine, with its actual ideal-power structure. -/
instance boundaryTestThickening_affine : IsAffine (boundaryTestThickening s κ tests k) :=
  isAffine_of_isAffineHom (boundaryTestThickeningMap s κ tests k)

/-- Every test-order chart is finite over the full original test neighborhood. -/
instance boundaryTestChartProjection_finite : IsFinite π := by
  let _ := quotientMap_finite_of_free ρ (boundaryChart_action_free n o U e hU)
  unfold boundaryTestChartProjection
  infer_instance

/-- Every test-order chart is flat over the full original test neighborhood. -/
instance boundaryTestChartProjection_flat : Flat π := by
  let _ := quotientMap_flat_of_free ρ (boundaryChart_action_free n o U e hU)
  unfold boundaryTestChartProjection
  infer_instance

/-- The finite flat map covers every point and every original test component. -/
instance boundaryTestChartProjection_surjective_instance : Surjective π := by
  unfold boundaryTestChartProjection
  infer_instance

/-- The actual test chart is affine. -/
instance boundaryTestChart_affine : IsAffine (boundaryTestChart n o U e hU s κ k) :=
  isAffine_of_isAffineHom π

/-- The matching test chart gives effective scheme descent at every original order. -/
instance boundaryTestChartProjection_effectiveEpi : EffectiveEpi π := by
  infer_instance

/-- Coefficients of each test neighborhood embed faithfully flatly in its original chart. -/
theorem boundaryTestChartProjection_faithfullyFlat : (π).appTop.hom.FaithfullyFlat :=
  (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine π).mp
    ⟨inferInstance, inferInstance⟩

/-- Compatible functions descend to the full nonreduced test neighborhood uniquely. -/
theorem boundaryTestChartProjection_sections (t : Γ(boundaryTestChart n o U e hU s κ k, ⊤))
    (ht : (pullback.fst π π).appTop t = (pullback.snd π π).appTop t) :
    ∃! u : Γ(boundaryTestThickening s κ tests k, ⊤), (π).appTop u = t :=
  SchemeEffectiveEpiSections.sections_existsUnique (IsPullback.of_hasPullback π π) t ht

variable [QuasiCompact p]
local instance testDescentOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance testDescentOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›

/-- This genuine flat cover factors through a finite matching original rank stage. -/
theorem boundaryTest_faithful_rank_factor [AlgebraicGeometry.IsNoetherian A] :
    ∃ (l : ℕ) (w : boundaryTestChart n o U e hU s κ k ⟶
        rankPullbackThickening (Over.mk p) (chartBoundaryEndpoint n o U e hU s κ) n l),
      w ≫ rankPullbackMap (Over.mk p) (chartBoundaryEndpoint n o U e hU s κ) n l =
        boundaryTestChartMap n o U e hU s κ k := by
  simpa only [Category.id_comp] using
    exists_boundaryTestChart_rank_factor n o U e hU s κ k (𝟙 _)

end FLT.Mazur.EquivalenceRelationNormalizedFrames
