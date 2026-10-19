/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineResidualTests
public import FLT.Mazur.CyclicCharacteristicOppositeLocallyRinged

/-!
# The opposite-characteristic cover of a saturated affine domain

Pull the original transition cover back to the exact inverse image of the
selected affine quotient open. Its target parameters factor through the original
affine chart, so no residual comparison is replaced by a pointwise relation.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b : Bool) (j : (invariantAffineCover n (!b)).I₀)
local notation "i" => (Sigma.mk (!b) j : InvariantAffineIndex n)

/-- The exact opposite-chart domain above the selected affine quotient open. -/
def affineOppositeOpen : (normalizedLocus n b).Opens :=
  (Opens.map (TopCat.ofHom ⟨chartProjection n b, chartProjection_continuous n b⟩)).obj
    (affineOrbitOpen n i)

/-- Every point of this domain lies in the existing opposite-characteristic overlap. -/
theorem affineOppositeOpen_le : affineOppositeOpen n b j ≤ transitionOpen n b := by
  intro x hx
  exact (mem_integerOpen_iff n (chartInteger (!b)) b x).mp
    (affineOrbitOpen_le n i hx)

/-- The actual inclusion into the original transition domain. -/
def affineOppositeToTransition :
    (affineOppositeOpen n b j).toScheme ⟶ (transitionOpen n b).toScheme :=
  (normalizedLocus n b).homOfLE (affineOppositeOpen_le n b j)

/-- Restriction retains the original opposite-chart inclusion. -/
@[reassoc] theorem affineOppositeToTransition_comp :
    affineOppositeToTransition n b j ≫ (transitionOpen n b).ι =
      (affineOppositeOpen n b j).ι := (normalizedLocus n b).homOfLE_ι _

/-- The original fppf transition family restricted to the exact affine orbit domain. -/
def affineOppositeCover :
    Scheme.Cover.{0} Scheme.fppfPrecoverage (affineOppositeOpen n b j).toScheme :=
  (transitionCover n b).pullback₁ (affineOppositeToTransition n b j)

/-- The transition target stays in the selected affine chart. -/
theorem affineOppositeTarget_range (k : (transitionCover n b).I₀) :
    Set.range (pullback.snd (affineOppositeToTransition n b j)
      ((transitionCover n b).f k) ≫ transitionTarget n b k) ⊆
        Set.range (invariantAffineInclusion n i) := by
  rintro _ ⟨x, rfl⟩
  rw [← affineOrbitOpen_preimage]
  let r := pullback.snd (affineOppositeToTransition n b j) ((transitionCover n b).f k)
  let l := pullback.fst (affineOppositeToTransition n b j) ((transitionCover n b).f k)
  have he := (projection_eq_iff n _ _).mpr
    (related_of_unmarked n (transition_unmarkedRelated n b k)
      (pullback.snd (affineOppositeToTransition n b j) ((transitionCover n b).f k) x))
  change chartProjection n (!b)
    (transitionTarget n b k (r x)) =
      chartProjection n b (transitionSource n b k (r x)) at he
  change chartProjection n (!b) (transitionTarget n b k (r x)) ∈ affineOrbitOpen n i
  rw [he]
  have hp := congrArg (fun f => f x)
    (pullback.condition (f := affineOppositeToTransition n b j)
      (g := (transitionCover n b).f k))
  have hpc := congrArg (fun y => (transitionOpen n b).ι y) hp
  change ((affineOppositeToTransition n b j) ≫ (transitionOpen n b).ι)
    (l x) = transitionSource n b k (r x) at hpc
  rw [affineOppositeToTransition_comp] at hpc
  rw [← hpc]
  exact (pullback.fst (affineOppositeToTransition n b j) ((transitionCover n b).f k) x).2

/-- The opposite cover's genuine parameter map into the original selected affine chart. -/
def affineOppositeTarget (k : (transitionCover n b).I₀) :
    (affineOppositeCover n b j).X k ⟶ invariantAffineChart n i :=
  IsOpenImmersion.lift (invariantAffineInclusion n i)
    (pullback.snd (affineOppositeToTransition n b j) ((transitionCover n b).f k) ≫
      transitionTarget n b k) (affineOppositeTarget_range n b j k)

/-- The factor retains the original transition parameter as a scheme morphism. -/
@[reassoc] theorem affineOppositeTarget_inclusion (k : (transitionCover n b).I₀) :
    affineOppositeTarget n b j k ≫ invariantAffineInclusion n i =
      pullback.snd (affineOppositeToTransition n b j) ((transitionCover n b).f k) ≫
        transitionTarget n b k := IsOpenImmersion.lift_fac _ _ _

end FLT.Mazur.CyclicCharacteristicOrbit
