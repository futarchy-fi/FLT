/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitResidualCorrectionCoordinates

/-!
# Localizing the exact residual correction quotient

The original mixed correction quotient retains the quotient of actual residual
coefficients by actual supported corrections. Flat localization detects this
quotient, giving one original scalar denominator and one compatible boundary-zero
family. No residue-field injectivity or existence of such a family is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open RelativeRelationOrbit InvariantOpenRelationDiagram
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] relativeFppfSheaf AmpleLineBundle
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
attribute [local irreducible] relation fst snd equivalence
  EquivalenceRelationNormalizedFrames.source
namespace OrbitBoundaryAtlas.FiniteAtlas
attribute [local irreducible] finiteCharts lifts obstruction
  scalarFamily normalizedBoundaryChartMap normalizedOrbitBoundaryCoefficient
local notation "e" => equivalence f hL d V c k
variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
set_option quotPrecheck false
local notation "E" => (pullOpen e W).val

variable (hW : IsAffineOpen (pullOpen (equivalence f hL d V c k) W).val)
local notation "Charts" => finiteCharts f hL d V c k W hW

local notation "ef" => fullRelationSchemeEquivalence f hL d V c k
local notation "Ω" => (invariantSheaf e).obj.obj (op W)
local notation "Cc" => mixedCoordinateRing f hL d V c k W hW

attribute [local instance] originalCorrectionMixedAlgebra
attribute [local instance] originalMixedResidualAlgebra
local notation "Cr" => originalMixedResidualRing f hL d V c k W hW
local notation "N" => originalMixedBoundaryKernel f hL d V c k W hW
local notation "extR" => originalMixedResidualExtension f hL d V c k W hW
local notation "resR" => originalMixedResidualRestriction f hL d V c k W hW

local notation "extF" => originalResidualFamilyExtension f hL d V c k W hW
local notation "resF" => originalResidualFamilyRestriction f hL d V c k W hW

attribute [local instance] originalCorrectionChartAlgebra originalCorrectionBoundaryAlgebra
local notation "Ac" => chartCoordinateRing f hL d V c k W hW
local notation "Hb" => originalCorrectionBoundaryHom f hL d V c k W hW
local notation "Fp" => originalCorrectionFirstHom f hL d V c k W hW
local notation "Gq" => originalCorrectionSecondHom f hL d V c k W hW
local notation "K" => originalBoundaryMixedCorrectionImage f hL d V c k W hW
local notation "δ" => BoundaryCorrectionIdeal.mixedDiscrepancy Fp Gq

local notation "Kr" => originalResidualCorrectionModule f hL d V c k W hW

/-- The actual residual correction quotient maps into the full original mixed quotient. -/
def originalResidualQuotientInclusion :
    ((∀ j l : Charts, Cr j l) ⧸ Kr) →ₗ[Ω] ((∀ j l : Charts, Cc j l) ⧸ K) :=
  (Kr).mapQ K extF le_rfl

/-- The comparison preserves the exact extended representative. -/
theorem originalResidualQuotientInclusion_mk (a : ∀ j l : Charts, Cr j l) :
    originalResidualQuotientInclusion f hL d V c k W hW ((Kr).mkQ a) =
      (K).mkQ (extF a) := rfl

/-- No actual residual correction class is lost in the full original correction quotient. -/
theorem originalResidualQuotientInclusion_injective :
    Function.Injective (originalResidualQuotientInclusion f hL d V c k W hW) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm
  · intro x hx
    obtain ⟨a, rfl⟩ := (Kr).mkQ_surjective x
    change (K).mkQ (extF a) = 0 at hx
    exact (Submodule.Quotient.mk_eq_zero Kr).mpr ((Submodule.Quotient.mk_eq_zero K).mp hx)
  · exact bot_le

open TensorProduct
variable (S : Type*) [CommRing S]
  [Algebra ((invariantSheaf (equivalence f hL d V c k)).obj.obj (op W)) S]

/-- Every flat scalar extension preserves the actual residual quotient inclusion. -/
theorem originalResidualQuotient_baseChange_injective [Module.Flat Ω S] :
    Function.Injective
      ((originalResidualQuotientInclusion f hL d V c k W hW).baseChange S) :=
  Module.Flat.lTensor_preserves_injective_linearMap _
    (originalResidualQuotientInclusion_injective f hL d V c k W hW)

/-- Flat scalar extension detects exactly the original residual correction class. -/
theorem originalResidualQuotient_tmul_zero_iff [Module.Flat Ω S]
    (a : ∀ j l : Charts, Cr j l) :
    (1 ⊗ₜ[Ω] (Kr).mkQ a : S ⊗[Ω] ((∀ j l : Charts, Cr j l) ⧸ Kr)) = 0 ↔
      (1 ⊗ₜ[Ω] (K).mkQ (extF a) : S ⊗[Ω] ((∀ j l : Charts, Cc j l) ⧸ K)) = 0 := by
  have hi := originalResidualQuotient_baseChange_injective f hL d V c k W hW S
  rw [← (hi.eq_iff)]
  simp only [LinearMap.baseChange_tmul, originalResidualQuotientInclusion_mk, map_zero]

/-- Localization vanishing retains one original denominator and exact residual correction. -/
theorem originalResidualQuotient_localized_zero_iff (U : Submonoid Ω) [IsLocalization U S]
    (a : ∀ j l : Charts, Cr j l) :
    (1 ⊗ₜ[Ω] (Kr).mkQ a : S ⊗[Ω] ((∀ j l : Charts, Cr j l) ⧸ Kr)) = 0 ↔
      ∃ b : U, b.val • a ∈ Kr := by
  change TensorProduct.mk Ω S _ 1 ((Kr).mkQ a) = 0 ↔ _
  rw [IsLocalizedModule.eq_zero_iff U]
  simp only [Submonoid.smul_def, ← map_smul]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, (Submodule.Quotient.mk_eq_zero Kr).mp hb⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, (Submodule.Quotient.mk_eq_zero Kr).mpr hb⟩

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
