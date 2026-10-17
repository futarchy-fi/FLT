/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitBoundaryLinearSystem
public import FLT.Mazur.BoundaryCorrectionLocalCokernel
public import FLT.Mazur.HilbertBoundaryCertifiedAlgebra

/-!
# Original boundary certificates from pointwise finite cokernel constructions

At each maximal ideal of the actual original boundary source, localize the
original invariant scalars at its contraction. A finite divisible submodule
of the full correction cokernel containing the scalar error gives an original
nonvanishing multiplier there. Together these construct the finite source
coefficient identity and the original boundary cover, with no global ambient
source test map. The pointwise finite cokernel input remains to be proved.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TensorProduct
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open RelativeRelationOrbit InvariantOpenRelationDiagram
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency true
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

variable (hW : IsAffineOpen (pullOpen (equivalence f hL d V c k) W).val)
local notation "Charts" => finiteCharts f hL d V c k W hW

attribute [local irreducible] originalChartScalarMap
local notation "Ω" => (invariantSheaf e).obj.obj (op W)
local notation "Ac" => chartCoordinateRing f hL d V c k W hW
local notation "Bc" => chartBoundaryCoordinateRing f hL d V c k W hW
local notation "Cc" => mixedCoordinateRing f hL d V c k W hW

attribute [local instance] originalCorrectionChartAlgebra originalCorrectionBoundaryAlgebra
  originalCorrectionMixedAlgebra
local notation "Hb" => originalCorrectionBoundaryHom f hL d V c k W hW
local notation "Fp" => originalCorrectionFirstHom f hL d V c k W hW
local notation "Gq" => originalCorrectionSecondHom f hL d V c k W hW
variable (t : (invariantSheaf (originalClosedEquivalence f hL d V c k)).obj.obj
  (op ((TopologicalSpace.Opens.map (originalClosedInvariantMap f hL d V c k).base).obj W)))
local notation "u" => lifts f hL d V c k W hW t
local notation "K" => LinearMap.ker (originalCorrectionSystem f hL d V c k W hW t)

local notation "ec" => originalClosedEquivalence f hL d V c k
local notation "m" => originalClosedInvariantMap f hL d V c k
local notation "Wc" => (TopologicalSpace.Opens.map (m).base).obj W
local notation "T" => (sourceSheaf ec).obj.obj (op Wc)
local notation "κ" => ((invariantInclusion ec).hom.app (op Wc)).hom.comp
  (originalClosedSectionPullback f hL d V c k W)

attribute [local irreducible] FiniteErrorLinearLifting.tensorPair
  BoundaryCorrectionIdeal.correctionSystem
  originalCorrectionBoundaryHom originalCorrectionFirstHom originalCorrectionSecondHom


attribute [local irreducible] BoundaryCorrectionIdeal.ambientCorrectionOperator
  BoundaryCorrectionIdeal.ambientScalarError

/-- Finite local input data on the actual source, before any lifting certificate is deduced. -/
def originalLocalCokernelData : Prop :=
  ∀ (P : Ideal T) [P.IsMaximal],
      let S := Localization.AtPrime (P.comap κ)
      let F := BoundaryCorrectionIdeal.ambientCorrectionOperator Hb Fp Gq u S
      ∃ Q : Submodule S
          ((S ⊗[Ω] ((∀ j : Charts, Bc j) × ∀ j l : Charts, Cc j l)) ⧸ LinearMap.range F),
        Q.FG ∧ Q ≤ IsLocalRing.maximalIdeal S • Q ∧
          (LinearMap.range F).mkQ
            (BoundaryCorrectionIdeal.ambientScalarError Hb Fp Gq u S) ∈ Q

attribute [local irreducible] originalLocalCokernelData

/-- Pointwise local cokernel constructions certify the original closed source. -/
theorem originalLocalCokernel_certified
    (h : originalLocalCokernelData f hL d V c k W hW t) :
    t ∈ originalBoundaryCertifiedSections f hL d V c k W := by
  rw [originalLocalCokernelData] at h
  have ht := BoundaryCorrectionIdeal.localCokernel_source_map_eq_top Hb Fp Gq u κ h
  have hI := (BoundaryCorrectionIdeal.range_correctionMultiplier Hb Fp Gq u).symm.trans
    (originalCorrectionSystem_multiplier_range f hL d V c k W hW t)
  rw [hI] at ht
  exact ht

/-- Pointwise local constructions give an actual finite coefficient identity on the source. -/
theorem originalLocalCokernel_certificate
    (h : originalLocalCokernelData f hL d V c k W hW t) :
    ∃ a : originalBoundaryLiftIdeal f hL d V c k W t →₀ T,
      a.sum (fun v b ↦ b * (invariantInclusion ec).hom.app (op Wc)
        ((m).c.app (op W) v.val)) = 1 :=
  (mem_originalBoundaryCertifiedSections_iff f hL d V c k W t).mp
    (originalLocalCokernel_certified f hL d V c k W hW t h)

/-- The finite identity covers the entire unchanged original boundary of the orbit domain. -/
theorem originalLocalCokernel_cover
    (h : originalLocalCokernelData f hL d V c k W hW t) :
    (TopologicalSpace.Opens.map (m).base).obj
      (originalBoundaryLiftOpen f hL d V c k W t) = Wc :=
  (mem_originalBoundaryCertifiedSections_iff_cover f hL d V c k W t hW).mp
    (originalLocalCokernel_certified f hL d V c k W hW t h)

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
