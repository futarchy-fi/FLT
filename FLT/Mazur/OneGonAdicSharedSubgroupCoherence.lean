/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicSharedSubgroupIso
public import FLT.Mazur.CompatibleSubgroupIsoFaithful

/-!
# Three-presentation coherence for actual supplied finite subgroups

All three independently supplied smooth stages refine to the same finite ring.
The resulting compatible subgroup isomorphisms obey the cocycle equation as
bundled maps, including their source groups and full inclusions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OneGonAdicIndependentModel
open Approximation OneGonAdicCharacterTower OneGonSmoothing CharacterSchemeBaseChange
open ArithmeticOneGonGeneralizedCurve WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n] (s u : Set R)
  (K : Subalgebra ℤ R) [Algebra.FiniteType ℤ K]
  (hS : base I t ht n s ≤ K) (hU : base I t ht n u ≤ K)
  (hs : complementaryInverse I t ht ∈ s) (hu : complementaryInverse I t ht ∈ u)

variable (i : (CoefficientStage (base I t ht n s))ᵒᵖ)
  (j : (CoefficientStage (base I t ht n u))ᵒᵖ)
  (hi : stageBase I t ht n s i ≤ K) (hj : stageBase I t ht n u j ≤ K)
  (b : (coefficientModelDiagram (base I t ht n s) (carrier I t ht n s).hom).obj i ⟶
    (integralSmoothOpen (equation (parameter I t ht n s))).toScheme)
  (hb : b ≫ (integralSmoothOpen (equation (parameter I t ht n s))).ι =
    (coefficientModelToInitial (base I t ht n s) (carrier I t ht n s).hom).app i ≫
      embedding I t ht n s)
  (c : (coefficientModelDiagram (base I t ht n u) (carrier I t ht n u).hom).obj j ⟶
    (integralSmoothOpen (equation (parameter I t ht n u))).toScheme)
  (hc : c ≫ (integralSmoothOpen (equation (parameter I t ht n u))).ι =
    (coefficientModelToInitial (base I t ht n u) (carrier I t ht n u).hom).app j ≫
      embedding I t ht n u)
  (hφs : Function.Surjective (OneGonFiniteCoefficientCoordinates.modelCoordinates t 1
    (canonicalCoordinates I t ht n) s))
  (hφu : Function.Surjective (OneGonFiniteCoefficientCoordinates.modelCoordinates t 1
    (canonicalCoordinates I t ht n) u))

variable (v : Set R) (hV : base I t ht n v ≤ K)
  (hv : complementaryInverse I t ht ∈ v)
  (k : (CoefficientStage (base I t ht n v))ᵒᵖ)
  (hk : stageBase I t ht n v k ≤ K)
  (d : (coefficientModelDiagram (base I t ht n v) (carrier I t ht n v).hom).obj k ⟶
    (integralSmoothOpen (equation (parameter I t ht n v))).toScheme)
  (hd : d ≫ (integralSmoothOpen (equation (parameter I t ht n v))).ι =
    (coefficientModelToInitial (base I t ht n v) (carrier I t ht n v).hom).app k ≫
      embedding I t ht n v)
  (hφv : Function.Surjective (OneGonFiniteCoefficientCoordinates.modelCoordinates t 1
    (canonicalCoordinates I t ht n) v))

/-- The actual three supplied subgroups satisfy the full compatible cocycle equation. -/
theorem sharedFiniteSubgroupIso_trans :
    (sharedFiniteSubgroupIso I t ht n s u K hS hU hs hu i j hi hj b hb c hc hφs hφu).trans
      (sharedFiniteSubgroupIso I t ht n u v K hU hV hu hv j k hj hk c hc d hd hφu hφv) =
        sharedFiniteSubgroupIso I t ht n s v K hS hV hs hv i k hi hk b hb d hd hφs hφv := by
  apply GeneralizedEllipticCurve.FiniteSubgroup.CompatibleIso.ext_curve_hom
  exact sharedCurveIso_trans I t ht n s u K hS hU hs hu v hV hv

/-- The actual refined subgroup compared with itself has the full identity comparison. -/
theorem sharedFiniteSubgroupIso_refl :
    sharedFiniteSubgroupIso I t ht n s s K hS hS hs hs i i hi hi b hb b hb hφs hφs =
      GeneralizedEllipticCurve.FiniteSubgroup.CompatibleIso.refl
        (sharedFiniteSubgroup I t ht n s K hS i hi b hb hs hφs) := by
  apply GeneralizedEllipticCurve.FiniteSubgroup.CompatibleIso.ext_curve_hom
  exact congrArg Iso.hom (sharedCurveIso_refl I t ht n s K hS hs)

/-- Reversing the two actual presentations gives the inverse compatible subgroup map. -/
theorem sharedFiniteSubgroupIso_symm :
    (sharedFiniteSubgroupIso I t ht n s u K hS hU hs hu i j hi hj b hb c hc hφs hφu).symm =
      sharedFiniteSubgroupIso I t ht n u s K hU hS hu hs j i hj hi c hc b hb hφu hφs := by
  apply GeneralizedEllipticCurve.FiniteSubgroup.CompatibleIso.ext_curve_hom
  change (sharedCurveIso I t ht n s u K hS hU hs hu).inv =
    (sharedCurveIso I t ht n u s K hU hS hu hs).hom
  apply (cancel_epi (sharedCurveIso I t ht n s u K hS hU hs hu).hom).mp
  rw [Iso.hom_inv_id, sharedCurveIso_trans, sharedCurveIso_refl]
  rfl

end FLT.Mazur.OneGonAdicIndependentModel
