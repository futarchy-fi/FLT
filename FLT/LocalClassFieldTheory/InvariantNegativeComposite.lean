/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.CoinducedInvariantSequence
public import FLT.LocalClassFieldTheory.InvariantNegativeFirstBoundary
public import FLT.LocalClassFieldTheory.NegativeCupQuotient

/-!
# The actual invariant connecting composite

Norming the concrete primitive over the subgroup lifts the first boundary.
Its quotient norm is the full norm, so the composite is the unscaled
quotient descent of the original negative cup.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology groupHomology

variable {G : Type} [Group G] [Fintype G] (M : Rep.{0} ℤ G)
  (c : cocycles₂ M) (N : Subgroup G) [N.Normal] [Fintype N] [Fintype (G ⧸ N)]

local notation "I" => coinducedCoefficients M
local notation "Q" => shiftedCoefficients M
local notation "b" => shiftedTwoCocycle M c
local notation "MQ" => Rep.quotientToInvariants M N
local notation "IQ" => Rep.quotientToInvariants I N
local notation "QQ" => Rep.quotientToInvariants Q N
local notation "C" => coinducedInvariantSequence M N
local notation "q" => QuotientGroup.mk' N

variable (hQ : Limits.IsZero (tateCohomology (Rep.res N.subtype (shiftedCoefficients M)) 0))
  (hX : Limits.IsZero (tateCohomology (Rep.res N.subtype
    (oneCocycleExtension (shiftedCoefficients M) (shiftedTwoCocycle M c))) 0))

/-- The two actual invariant connecting maps in degree minus two. -/
def invariantNegativeComposite
    (hQ : Limits.IsZero (tateCohomology (Rep.res N.subtype Q) 0))
    (hX : Limits.IsZero (tateCohomology (Rep.res N.subtype (oneCocycleExtension Q b)) 0)) :
    tateCohomology (Rep.trivial ℤ (G ⧸ N) ℤ) (-2) ⟶ tateCohomology MQ 0 := by
  let f : tateCohomology (Rep.trivial ℤ (G ⧸ N) ℤ) (-2) ⟶ tateCohomology QQ (-1) :=
    TateCohomology.δ (oneCocycleInvariantSequence_shortExact Q b N hX) (-2)
  let g : tateCohomology QQ (-1) ⟶ tateCohomology MQ 0 :=
    TateCohomology.δ (coinducedInvariantSequence_shortExact M N hQ) (-1)
  exact f ≫ g

/-- The quotient norm of the normed primitive is the included ambient cocycle sum. -/
theorem invariant_primitive_norm (g : G) :
    (C).f.hom (quotientInvariantEquiv M N (twoCocycleSumInvariant M c g⁻¹)).val =
      (IQ).norm.hom (subgroupNormInvariant I N (twoCocyclePrimitive M c g⁻¹)) := by
  apply Subtype.ext
  exact ((quotientNorm_subgroupNorm I N _).trans (twoCocyclePrimitive_norm M c g⁻¹)).symm

/-- Evaluating both invariant connecting maps gives the deflated ambient invariant. -/
theorem invariantNegativeComposite_generator (g : G) :
    invariantNegativeComposite M c N hQ hX (tateScalarGenerator ℤ (G ⧸ N) (q g)) =
      tateInvariantClass MQ (quotientInvariantEquiv M N (twoCocycleSumInvariant M c g⁻¹)) := by
  obtain ⟨hz, he⟩ := oneCocycleInvariant_negative_boundary Q b N hX g
  change TateCohomology.δ (coinducedInvariantSequence_shortExact M N hQ) (-1)
    (TateCohomology.δ (oneCocycleInvariantSequence_shortExact Q b N hX) (-2) _) = _
  rw [he]
  apply tate_boundary_negative_one C (coinducedInvariantSequence_shortExact M N hQ) _ hz
    (subgroupNormInvariant I N (twoCocyclePrimitive M c g⁻¹))
  · exact subgroupNormInvariant_map N (shiftedProjection M) _
  · exact invariant_primitive_norm M c N g

/-- The two invariant boundaries equal the unscaled descended negative cup. -/
theorem invariantNegativeComposite_eq_negativeCupQuotient :
    (invariantNegativeComposite M c N hQ hX).hom.toAddMonoidHom =
      negativeCupQuotient M N (H2π M c) := by
  ext x
  obtain ⟨g, rfl⟩ := tateScalarGenerator_surjective (G ⧸ N) x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N g
  exact (invariantNegativeComposite_generator M c N hQ hX g).trans
    (negativeCupQuotient_generator M N c g).symm

end LocalClassFieldTheory
