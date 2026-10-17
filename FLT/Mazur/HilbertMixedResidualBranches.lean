/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertNormalizedAffineNeighborhood
public import FLT.Mazur.EquivalenceRelationMixedResidualOpen

/-!
# Residual original Hilbert relations with independent frame sizes

The original affine tuple envelope proves separatedness of every normalized
Hilbert source. Thus the mixed subframe comparison is closed without an extra
geometric assumption. Its residual open retains all other original arrows,
and every complete first-endpoint fiber avoids this residual part.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "p" => Over.Hom.left (fst f hL d V c k)
local notation "q" => Over.Hom.left (snd f hL d V c k)
local notation "e" => fullRelationSchemeEquivalence f hL d V c k

/-- The original affine envelope proves separatedness of the entire normalized Hilbert source. -/
theorem normalizedFrameSource_separated (n : ℕ) (o : Fin n) :
    (source p q (Fin n) o).IsSeparated := by
  let _ := RelativeOrderedTuples.finTuples_affine (firstRelationEnvelope (A := A) V) n
  have h : IsSeparated (normalizedFrameEnvelopeMap f hL d V c k n o ≫
      terminal.from _) := inferInstance
  constructor
  rwa [terminal.comp_from] at h

variable (n m : ℕ) (o : Fin n) (o' : Fin m)

/-- The finite subframe comparison is closed in the full original mixed Hilbert relation. -/
theorem normalizedMixedComparison_closed :
    IsClosedImmersion (MixedFrames.embeddingComparison e o o') := by
  let _ := normalizedFrameSource_separated f hL d V c k m o'
  exact MixedFrames.embeddingComparison_closed e o o'

/-- An actual residual open for independent original Hilbert frames of arbitrary sizes. -/
def normalizedMixedResidualOpen : (MixedFrames.relation p q (Fin n) (Fin m) o o').Opens := by
  let _ := normalizedFrameSource_separated f hL d V c k m o'
  exact MixedFrames.mixedResidualOpen e o o'

/-- Every residual original mixed arrow has incomplete first endpoint. -/
theorem normalizedMixedResidualOpen_first_incomplete
    (x : (normalizedMixedResidualOpen f hL d V c k n m o o').toScheme) :
    ((normalizedMixedResidualOpen f hL d V c k n m o o').ι ≫
      MixedFrames.fst p q (Fin n) (Fin m) o o') x ∉
        completePointLocus («p» := p) («q» := q) (Fin n) o := by
  let _ := normalizedFrameSource_separated f hL d V c k m o'
  exact MixedFrames.mixedResidualOpen_first_incomplete e o o' x

end FLT.Mazur.HilbertChart.AffineRestriction
