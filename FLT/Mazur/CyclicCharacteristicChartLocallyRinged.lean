/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicInvariantAffineComparison
public import FLT.Mazur.CyclicCharacteristicResidualChartQuotient

/-!
# The original normalized chart over its characteristic orbit open

The actual locally ringed projection factors through its exact characteristic
open. This factorization retains the quotient topology and the original map of
regular functions; it does not assert that the characteristic open is affine.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- The locally ringed projection of an original normalized chart. -/
def chartLocallyRingedProjection (b : Bool) :
    (normalizedLocus n b).toLocallyRingedSpace ⟶ invariantLocallyRingedSpace n :=
  (normalizedDisjointInclusion n b).toLRSHom ≫ invariantLocallyRingedProjection n

/-- Its underlying map is the full comparison orbit map. -/
theorem chartLocallyRingedProjection_base (b : Bool) :
    (chartLocallyRingedProjection n b).base =
      (normalizedDisjointInclusion n b).base ≫ quotientMap n := by
  change _ ≫ (invariantLocallyRingedProjection n).base = _
  rw [invariantLocallyRingedProjection_base]

/-- The original projection factors as a locally ringed morphism into its exact open. -/
def chartToInvariantOpen (b : Bool) :
    (normalizedLocus n b).toLocallyRingedSpace ⟶
      invariantOpenSpace n (integerOpen n (chartInteger b)) :=
  LocallyRingedSpace.IsOpenImmersion.lift
    ((invariantLocallyRingedSpace n).ofRestrict
      (integerOpen n (chartInteger b)).isOpenEmbedding)
    (chartLocallyRingedProjection n b) (by
      rintro _ ⟨x, rfl⟩
      refine ⟨⟨chartProjection n b x, normalized_mem_integerOpen n b x⟩, ?_⟩
      rw [chartLocallyRingedProjection_base]
      rfl)

/-- The factorization is equality of locally ringed morphisms, including section maps. -/
@[reassoc] theorem chartToInvariantOpen_comp (b : Bool) :
    chartToInvariantOpen n b ≫ (invariantLocallyRingedSpace n).ofRestrict
      (integerOpen n (chartInteger b)).isOpenEmbedding =
        chartLocallyRingedProjection n b :=
  LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _

/-- Its base map is exactly the already constructed characteristic quotient map. -/
theorem chartToInvariantOpen_base (b : Bool) :
    (chartToInvariantOpen n b).base = chartToIntegerOpen n b := by
  ext x
  apply Subtype.ext
  have h := congrArg (fun f => f.base x) (chartToInvariantOpen_comp n b)
  change ((chartToInvariantOpen n b).base x).val = _ at h
  rw [chartLocallyRingedProjection_base] at h
  exact h

/-- The locally ringed factor has the actual quotient topology. -/
theorem chartToInvariantOpen_isQuotientMap (b : Bool) :
    Topology.IsQuotientMap (chartToInvariantOpen n b).base := by
  rw [chartToInvariantOpen_base]
  exact chartToIntegerOpen_isQuotientMap n b

/-- Its entire sheaf map is the invariant inclusion followed by original chart pullback. -/
theorem chartLocallyRingedProjection_toShHom (b : Bool) :
    (chartLocallyRingedProjection n b).toShHom =
      (normalizedDisjointInclusion n b).toShHom ≫ toRingedSpace n := by
  change (normalizedDisjointInclusion n b).toShHom ≫
    (invariantLocallyRingedProjection n).toShHom = _
  rw [invariantLocallyRingedProjection_toShHom]

end FLT.Mazur.CyclicCharacteristicOrbit
