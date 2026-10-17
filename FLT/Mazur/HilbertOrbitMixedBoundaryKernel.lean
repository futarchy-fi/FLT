/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitBoundaryMixedCokernel
public import FLT.Mazur.EquivalenceRelationChartKernelDiscrepancy

/-!
# The exact mixed boundary submodule of the actual finite atlas

Both the chosen discrepancies and all removable corrections lie in the
product of the original mixed boundary ideals. These are exact ideals,
not their radicals or their residue images.
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
local notation "E" => (pullOpen e W).val

variable (hW : IsAffineOpen (pullOpen (equivalence f hL d V c k) W).val)
local notation "Charts" => finiteCharts f hL d V c k W hW

attribute [local irreducible] originalChartScalarMap
local notation "Ω" => (invariantSheaf e).obj.obj (op W)
local notation "Ac" => chartCoordinateRing f hL d V c k W hW
local notation "Bc" => chartBoundaryCoordinateRing f hL d V c k W hW
local notation "Cc" => mixedCoordinateRing f hL d V c k W hW

local notation "ec" => originalClosedEquivalence f hL d V c k
local notation "m" => originalClosedInvariantMap f hL d V c k
local notation "Wc" => (TopologicalSpace.Opens.map (m).base).obj W
local notation "D" => (invariantSheaf ec).obj.obj (op Wc)
local notation "ρ" => originalClosedSectionPullback f hL d V c k W

attribute [local instance] originalBoundarySectionAlgebra originalCorrectionBoundaryAlgebra
  originalCorrectionChartAlgebra originalCorrectionMixedAlgebra
attribute [local irreducible] originalBoundaryCoefficientLinearMap
  BoundaryCorrectionIdeal.originalCorrectionOperator
  originalCorrectionBoundaryHom originalCorrectionFirstHom originalCorrectionSecondHom
local notation "Hb" => originalCorrectionBoundaryHom f hL d V c k W hW
local notation "Fp" => originalCorrectionFirstHom f hL d V c k W hW
local notation "Gq" => originalCorrectionSecondHom f hL d V c k W hW
local notation "β" => originalBoundaryCoefficientLinearMap f hL d V c k W hW
local notation "i" => Over.Hom.left (originalBoundarySourceMap f hL d V c k)
local notation "ef" => fullRelationSchemeEquivalence f hL d V c k
local notation "n" => fun j : Charts ↦ j.val.size
local notation "o" => fun j : Charts ↦ j.val.label
local notation "U" => fun j : Charts ↦ j.val.domain
local notation "hU" => fun j : Charts ↦ j.val.stable
local notation "Cmix" => (∀ j l : Charts, Cc j l)

/-- The product of all exact mixed boundary kernels, over original invariant scalars. -/
def originalMixedBoundaryKernel : Submodule Ω Cmix :=
  Submodule.pi Set.univ fun j ↦ Submodule.pi Set.univ fun l ↦
    (RingHom.ker (MixedFrames.mixedChartBoundaryInclusion
      j.val.label l.val.label j.val.domain l.val.domain i).appTop.hom).restrictScalars Ω

/-- Membership tests every independent mixed coordinate on its exact closed boundary. -/
theorem mem_originalMixedBoundaryKernel_iff (v : Cmix) :
    v ∈ originalMixedBoundaryKernel f hL d V c k W hW ↔
      ∀ j l : Charts, v j l ∈ RingHom.ker (MixedFrames.mixedChartBoundaryInclusion
        j.val.label l.val.label j.val.domain l.val.domain i).appTop.hom := by
  simp only [originalMixedBoundaryKernel, Submodule.mem_pi, Set.mem_univ, forall_const,
    Submodule.restrictScalars_mem]

set_option backward.isDefEq.respectTransparency false in
/-- The actual chosen discrepancy already lies in the exact mixed boundary module. -/
theorem originalLiftDiscrepancy_mem_boundary (t : D) :
    BoundaryCorrectionIdeal.mixedDiscrepancy Fp Gq (lifts f hL d V c k W hW t) ∈
      originalMixedBoundaryKernel f hL d V c k W hW := by
  unfold originalCorrectionFirstHom originalCorrectionSecondHom
  rw [mem_originalMixedBoundaryKernel_iff]
  exact lifts_difference f hL d V c k W hW t

set_option backward.isDefEq.respectTransparency false in
/-- Exact boundary-zero chart families give exact boundary-zero full discrepancies. -/
theorem originalKernelDiscrepancy_mem_boundary (v : ∀ j : Charts, Ac j)
    (hv : BoundaryCorrectionIdeal.boundaryCoordinates Hb v = 0) :
    BoundaryCorrectionIdeal.mixedDiscrepancy Fp Gq v ∈
      originalMixedBoundaryKernel f hL d V c k W hW := by
  unfold originalCorrectionFirstHom originalCorrectionSecondHom
  rw [mem_originalMixedBoundaryKernel_iff]
  apply MixedFrames.ChartFamily.difference_mem_kernel_of_restriction_zero
    ef n o U hU i (Over.Hom.left (originalClosedArrow f hL d V c k))
    (Over.Hom.left (originalClosedFst f hL d V c k))
    (Over.Hom.left (originalClosedSnd f hL d V c k))
    (originalClosedFst_isPullback f hL d V c k)
    (congrArg Over.Hom.left (originalClosedArrow_snd f hL d V c k)) v
  unfold originalCorrectionBoundaryHom normalizedBoundaryChartMap at hv
  funext j
  exact congrArg Subtype.val (congrFun hv j)

/-- Every removable discrepancy belongs to the exact mixed boundary module. -/
theorem originalMixedCorrectionImage_le_boundary :
    originalBoundaryMixedCorrectionImage f hL d V c k W hW ≤
      originalMixedBoundaryKernel f hL d V c k W hW := by
  rintro _ ⟨v, hv, rfl⟩
  exact originalKernelDiscrepancy_mem_boundary f hL d V c k W hW v hv

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
