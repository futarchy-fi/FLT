/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryAmpleRefinementModuli
public import FLT.Mazur.CompatibleSubgroupRefinementCast

/-!
# Coherence of the actual ample boundary subgroup refinements

The existing compatible subgroup comparisons are the canonical presentation
transports. Consequently identity and composite base refinements obey the
full subgroup cocycle, retaining the actual universal curves and inclusions.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicBoundaryParameter
open GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T U V : Scheme} (E : GeneralizedEllipticCurve S)
  [IsSeparated E.group.hom] [SmoothOfRelativeDimension 1 E.group.hom]
  (n : ℕ) [NeZero n]

local instance ampleCoherentPullbackGroup_separated {W : Scheme} (f : W ⟶ S) :
    IsSeparated (E.baseChange f).group.hom :=
  inferInstanceAs (IsSeparated (pullback.snd E.group.hom f))

local instance ampleCoherentPullbackGroup_smooth {W : Scheme} (f : W ⟶ S) :
    SmoothOfRelativeDimension 1 (E.baseChange f).group.hom :=
  MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) E.group.hom f
    inferInstance

/-- The original refinement comparison is exactly the canonical compatible transport. -/
theorem ampleBaseRefinementSubgroupIso_eq_transport
    (g : T ⟶ S) (h : U ⟶ S) (f : U ⟶ T) (w : f ≫ g = h) :
    ampleBaseRefinementSubgroupIso E n g h f w =
      compatibleRefinementTransport (ampleUniversalLevel E n).val.2
        (ampleBaseChangeToOriginal g E n) (ampleBaseChangeToOriginal h E n)
        (ampleBaseRefinement E n g h f w) (ampleBaseRefinement_original E n g h f w).symm
        (ampleBaseChangeSubgroupIso g E n) (ampleBaseChangeSubgroupIso h E n) :=
  compatibleRefinementTransport_cast _ _ _ _ (ampleBaseRefinement_original E n g h f w) _ _

/-- The identity refinement acts identically on the entire ample universal subgroup. -/
theorem ampleBaseRefinementSubgroupIso_id (g : T ⟶ S) :
    (ampleBaseRefinementSubgroupIso E n g g (𝟙 T) (Category.id_comp g)).trans
      (compatibleBaseChangeIdEq (ampleUniversalLevel (E.baseChange g) n).val.2
        (ampleBaseRefinement E n g g (𝟙 T) (Category.id_comp g))
        (ampleBaseRefinement_id E n g)) =
      CompatibleIso.refl (ampleUniversalLevel (E.baseChange g) n).val.2 := by
  rw [ampleBaseRefinementSubgroupIso_eq_transport]
  exact compatibleRefinementTransport_id_eq _ _ _ _ _ _

/-- The actual full subgroup comparisons satisfy the base-refinement composition law. -/
theorem ampleBaseRefinementSubgroupIso_comp
    (g : T ⟶ S) (h : U ⟶ S) (k : V ⟶ S) (f : U ⟶ T) (j : V ⟶ U)
    (w : f ≫ g = h) (v : j ≫ h = k) :
    (ampleBaseRefinementSubgroupIso E n h k j v).trans
      ((ampleBaseRefinementSubgroupIso E n g h f w).baseChange
        (ampleBaseRefinement E n h k j v)) =
    (ampleBaseRefinementSubgroupIso E n g k (j ≫ f)
      (by rw [Category.assoc, w, v])).trans
      (compatibleBaseChangeCompEq (ampleUniversalLevel (E.baseChange g) n).val.2
        (ampleBaseRefinement E n g h f w) (ampleBaseRefinement E n h k j v)
        (ampleBaseRefinement E n g k (j ≫ f) (by rw [Category.assoc, w, v]))
        (ampleBaseRefinement_comp E n g h k f j w v).symm) := by
  rw [ampleBaseRefinementSubgroupIso_eq_transport,
    ampleBaseRefinementSubgroupIso_eq_transport, ampleBaseRefinementSubgroupIso_eq_transport]
  exact compatibleRefinementTransport_comp_eq _ _ _ _
    (ampleBaseRefinement_original E n g h f w) _ _ _ _ _
    (ampleBaseRefinement_original E n h k j v).symm
    (ampleBaseRefinement_comp E n g h k f j w v).symm
    (ampleBaseRefinement_original E n g k (j ≫ f) (by rw [Category.assoc, w, v])).symm _

end FLT.Mazur.CyclicBoundaryParameter
