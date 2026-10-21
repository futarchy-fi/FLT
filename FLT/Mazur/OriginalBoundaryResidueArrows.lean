/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryComparisonLocalClosedImage
public import FLT.Mazur.SchemeScalarComparisonResidueTests

/-!
# Residue-field arrows for the unchanged original boundary

Full original comparison coverage is tested by arrows into the actual boundary
relation, with both residue-field endpoints prescribed. The original invariant
scalars remain unchanged. Local image geometry is still an explicit input.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RingPairInvariantFlatScalars SchemeScalarImageQuotient SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q) (J : A.IdealSheafData)
  (hJ : J.comap p = J.comap q)
local notation "R" => invariants p.appTop.hom q.appTop.hom
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
set_option quotPrecheck false
local notation "f" => scalarMorphism (algebraMap R Γ(J.subscheme, ⊤))
local notation "a" => pullback.snd p J.subschemeι
local notation "b" => InvariantIdealRelation.snd J p q hJ
local notation "h" => originalBoundary_scalar_condition p q J hJ
local notation "k" => originalBoundaryComparison p q J hJ
local notation "m" => originalBoundaryKernelImage p q J
variable (U : (Spec (.of (Scalars (scalarMorphism
    (algebraMap (invariants p.appTop.hom q.appTop.hom) Γ(J.subscheme, ⊤)))))).Opens)
local notation "W" => m ⁻¹ᵁ U

/-- Both actual residue-field endpoints satisfy the original invariant scalar equation. -/
theorem originalBoundary_residue_endpoint_condition (w : (W).toScheme) :
    (W).toScheme.fromSpecResidueField w ≫ (W).ι ≫ pullback.fst f f ≫ f =
      (W).toScheme.fromSpecResidueField w ≫ (W).ι ≫ pullback.snd f f ≫ f := by
  rw [pullback.condition]

variable [Etale p]
  [Etale ((projection (scalarMorphism
    (algebraMap (invariants p.appTop.hom q.appTop.hom) Γ(J.subscheme, ⊤)))) ∣_ U)]

include e in
/-- Coverage means an actual boundary arrow with both original residue-field endpoints. -/
theorem originalBoundary_mem_range_iff_residue_arrow (w : (W).toScheme) :
    w.val ∈ Set.range k ↔
      ∃ d : Spec ((W).toScheme.residueField w) ⟶ pullback p J.subschemeι,
        d ≫ a = (W).toScheme.fromSpecResidueField w ≫ (W).ι ≫ pullback.fst f f ∧
        d ≫ b = (W).toScheme.fromSpecResidueField w ≫ (W).ι ≫ pullback.snd f f := by
  let _ : Mono (pullback.lift a b h) := originalBoundaryComparison_mono e J hJ
  exact SchemeScalarComparisonResidueTests.mem_range_iff_residue_arrow f a b h U w

include e in
/-- The whole original fiber is covered exactly when all its two-endpoint tests lift. -/
theorem originalBoundary_fiber_coverage_iff_residue_arrows
    (y : Spec (.of (Scalars f))) (hy : y ∈ U) :
    (∀ w : (pullback f f : Scheme), m w = y → w ∈ Set.range k) ↔
      ∀ w : (W).toScheme, m w.val = y →
        ∃ d : Spec ((W).toScheme.residueField w) ⟶ pullback p J.subschemeι,
          d ≫ a = (W).toScheme.fromSpecResidueField w ≫ (W).ι ≫ pullback.fst f f ∧
          d ≫ b = (W).toScheme.fromSpecResidueField w ≫ (W).ι ≫ pullback.snd f f := by
  let _ : Mono (pullback.lift a b h) := originalBoundaryComparison_mono e J hJ
  exact SchemeScalarComparisonResidueTests.fiber_coverage_iff_residue_arrows f a b h U y hy

end FLT.Mazur.EquivalenceRelationOrderedFrames
