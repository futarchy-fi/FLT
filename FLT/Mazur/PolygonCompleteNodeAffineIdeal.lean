/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonOriginalNodeClosed

/-!
# The actual affine maximal ideal of a complete polygon node

On every affine neighborhood of the specified complete node, its maximal
ideal contains the original parameter q. Its image on each original stage
is exactly the ideal of the specified stage node, rather than an arbitrary
ideal supplied to an abstract comparison.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] family exactVeroneseProj originalStageToCompatibleProj
attribute [local instance] originalStageToCompatibleProj_isClosedImmersion

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (i : Fin n) (U : (exactVeroneseProj K n h).affineOpens)
  (hx : completeNode K n h i ∈ U.1)

/-- The maximal ideal of the specified complete node on this actual affine open. -/
def completeNodeAffineIdeal : Ideal Γ(exactVeroneseProj K n h, U) :=
  (U.2.primeIdealOf ⟨completeNode K n h i, hx⟩).asIdeal

/-- The complete node's affine ideal is maximal because the actual point is closed. -/
instance completeNodeAffineIdeal_maximal : (completeNodeAffineIdeal K n h i U hx).IsMaximal :=
  U.2.primeIdealOf_isMaximal_of_isClosed _ (completeNode_isClosed K n h i)

include hx in
/-- The original stage node lies over every chosen affine neighborhood of the complete node. -/
theorem originalStageNode_mem_preimage (m : ℕ) :
    originalStageNode K n h m i ∈ originalStageToCompatibleProj K n h m ⁻¹ᵁ U := by
  change originalStageToCompatibleProj K n h m (originalStageNode K n h m i) ∈ U.1
  rwa [originalStageNode_toComplete]

/-- The ideal of the original stage node on the actual preimage affine open. -/
def originalNodeAffineIdeal (m : ℕ) :
    Ideal Γ((family K m n h).left, originalStageToCompatibleProj K n h m ⁻¹ᵁ U) :=
  ((U.2.preimage (originalStageToCompatibleProj K n h m)).primeIdealOf
    ⟨originalStageNode K n h m i, originalStageNode_mem_preimage K n h i U hx m⟩).asIdeal

/-- The original stage node ideal is maximal on the actual affine preimage. -/
instance originalNodeAffineIdeal_maximal (m : ℕ) :
    (originalNodeAffineIdeal K n h i U hx m).IsMaximal :=
  (U.2.preimage (originalStageToCompatibleProj K n h m)).primeIdealOf_isMaximal_of_isClosed
    _ (originalStageNode_isClosed K m n h i)

/-- The actual section restriction pulls the stage node ideal back to the complete node ideal. -/
theorem originalNodeAffineIdeal_comap (m : ℕ) :
    (originalNodeAffineIdeal K n h i U hx m).comap
      ((originalStageToCompatibleProj K n h m).app U).hom =
        completeNodeAffineIdeal K n h i U hx := by
  have he := IsAffineOpen.comap_primeIdealOf_appLE U.1 U.2
    (originalStageToCompatibleProj K n h m ⁻¹ᵁ U)
    (U.2.preimage (originalStageToCompatibleProj K n h m)) le_rfl
    (originalStageNode_mem_preimage K n h i U hx m)
  simpa only [Scheme.Hom.appLE, homOfLE_refl, CategoryTheory.op_id,
    CategoryTheory.Functor.map_id, Category.comp_id, originalStageNode_toComplete,
    completeNodeAffineIdeal, originalNodeAffineIdeal, PrimeSpectrum.comap_asIdeal] using
      congrArg PrimeSpectrum.asIdeal he

/-- The complete maximal ideal maps to exactly the specified original stage node ideal. -/
theorem completeNodeAffineIdeal_map (m : ℕ) :
    originalStageAffineIdeal K n h U m (completeNodeAffineIdeal K n h i U hx) =
      originalNodeAffineIdeal K n h i U hx m := by
  rw [originalStageAffineIdeal, ← originalNodeAffineIdeal_comap K n h i U hx m]
  exact Ideal.map_comap_of_surjective _ (originalStage_app_surjective K n h m U) _

/-- The chosen complete node's maximal ideal contains the actual original power-series parameter. -/
theorem completeNodeAffineIdeal_parameter :
    completeAffineScalars K n h U PowerSeries.X ∈ completeNodeAffineIdeal K n h i U hx := by
  have hk : RingHom.ker ((originalStageToCompatibleProj K n h 0).app U).hom ≤
      completeNodeAffineIdeal K n h i U hx := by
    rw [← originalNodeAffineIdeal_comap K n h i U hx 0]
    exact Ideal.ker_le_comap _
  apply hk
  rw [originalStage_app_ker, pow_one, compatibleProjAdicIdeal_affine]
  exact Ideal.subset_span (Set.mem_singleton _)

end FLT.Mazur.PolygonInfinitesimalStages
