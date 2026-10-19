/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineOrbitProjection
public import FLT.Mazur.CyclicCharacteristicChartResidualSections

/-!
# The actual locally ringed maps from the affine parameter cover

Each original affine parameter map factors through its constructed quotient
open as a locally ringed morphism. Its underlying map has the quotient topology.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (i : InvariantAffineIndex n)

/-- The original affine source projection to the full invariant locally ringed quotient. -/
def affineLocallyRingedProjection :
    (invariantAffineChart n i).toLocallyRingedSpace ⟶ invariantLocallyRingedSpace n :=
  (invariantAffineInclusion n i).toLRSHom ≫ chartLocallyRingedProjection n i.1

/-- Its underlying map is the full orbit projection of the original affine source. -/
theorem affineLocallyRingedProjection_base (x : invariantAffineChart n i) :
    (affineLocallyRingedProjection n i).base x =
      chartProjection n i.1 (invariantAffineInclusion n i x) := by
  change (chartLocallyRingedProjection n i.1).base (invariantAffineInclusion n i x) = _
  rw [chartLocallyRingedProjection_base]
  rfl

/-- Factor the original affine source map through its exact quotient open. -/
def affineToInvariantOpen :
    (invariantAffineChart n i).toLocallyRingedSpace ⟶
      invariantOpenSpace n (affineOrbitOpen n i) :=
  LocallyRingedSpace.IsOpenImmersion.lift
    ((invariantLocallyRingedSpace n).ofRestrict (affineOrbitOpen n i).isOpenEmbedding)
    (affineLocallyRingedProjection n i) (by
      rintro _ ⟨x, rfl⟩
      refine ⟨affineOrbitProjection n i x, ?_⟩
      exact (affineLocallyRingedProjection_base n i x).symm)

/-- The factorization preserves the full locally ringed map, including its section pullbacks. -/
@[reassoc] theorem affineToInvariantOpen_comp :
    affineToInvariantOpen n i ≫ (invariantLocallyRingedSpace n).ofRestrict
      (affineOrbitOpen n i).isOpenEmbedding = affineLocallyRingedProjection n i :=
  LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _

/-- Its base map is exactly the original affine source quotient map. -/
theorem affineToInvariantOpen_base :
    (affineToInvariantOpen n i).base = affineOrbitProjection n i := by
  ext x
  apply Subtype.ext
  have h := congrArg (fun f => f.base x) (affineToInvariantOpen_comp n i)
  exact h.trans (affineLocallyRingedProjection_base n i x)

/-- The locally ringed factor retains the actual quotient topology. -/
theorem affineToInvariantOpen_isQuotientMap :
    Topology.IsQuotientMap (affineToInvariantOpen n i).base := by
  rw [affineToInvariantOpen_base]
  exact affineOrbitProjection_isQuotientMap n i

end FLT.Mazur.CyclicCharacteristicOrbit
