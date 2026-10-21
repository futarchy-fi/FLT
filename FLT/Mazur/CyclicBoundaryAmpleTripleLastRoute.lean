/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryAmpleTripleLastPresentation
public import FLT.Mazur.CyclicBoundaryAmpleRefinementCoherence

/-!
# The last-two-stages route for full ample subgroups

The tail uses the existing two-stage tower comparison followed by the actual
associativity refinement. Composing it with the existing last-two-stages
comparison agrees with the direct triple comparison on the full universal subgroup.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicBoundaryParameter
open GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T U V : Scheme} (g : T ⟶ S) (h : U ⟶ T) (k : V ⟶ U)
  (E : GeneralizedEllipticCurve S)
  [IsSeparated E.group.hom] [SmoothOfRelativeDimension 1 E.group.hom]
  (n : ℕ) [NeZero n]

local instance ampleTripleRoute_separated {X Y : Scheme}
    (F : GeneralizedEllipticCurve X) [IsSeparated F.group.hom] (f : Y ⟶ X) :
    IsSeparated (F.baseChange f).group.hom :=
  inferInstanceAs (IsSeparated (pullback.snd F.group.hom f))

local instance ampleTripleRoute_smooth {X Y : Scheme}
    (F : GeneralizedEllipticCurve X) [SmoothOfRelativeDimension 1 F.group.hom] (f : Y ⟶ X) :
    SmoothOfRelativeDimension 1 (F.baseChange f).group.hom :=
  MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) F.group.hom f
    inferInstance

local notation "H" => Sigma.snd (Subtype.val (ampleUniversalLevel E n))
local notation "p" => ampleBaseChangeToOriginal (k ≫ (h ≫ g)) E n
local notation "r" => ampleBaseChangeToOriginal ((k ≫ h) ≫ g) E n
local notation "s" => ampleBaseChangeToOriginal (k ≫ h) (E.baseChange g) n ≫
  ampleBaseChangeToOriginal g E n
local notation "q" => ampleBaseChangeToOriginal k
  (GeneralizedEllipticCurve.baseChange (E.baseChange g) h) n ≫
  ampleBaseChangeToOriginal h (E.baseChange g) n ≫ ampleBaseChangeToOriginal g E n
local notation "t₁" => Iso.hom (ampleBaseChangeTowerIso h k (E.baseChange g) n)
local notation "t₂" => Iso.hom (ampleBaseChangeTowerIso g (k ≫ h) E n)
local notation "w" => Eq.trans (Category.id_comp (k ≫ (h ≫ g)))
  (Eq.symm (Category.assoc k h g))
local notation "t₃" => ampleBaseRefinement E n (k ≫ (h ≫ g)) ((k ≫ h) ≫ g) (𝟙 V) (w)
local notation "J" => Sigma.snd (Subtype.val
  (ampleUniversalLevel (E.baseChange (k ≫ (h ≫ g))) n))

/-- The last route retains the original parameter after its final two comparisons. -/
@[reassoc] theorem ampleTowerLastTail_original :
    ((t₂) ≫ (t₃)) ≫ (p) = (s) := by
  rw [Category.assoc, ampleBaseRefinement_original, ampleBaseChangeTowerIso_original]

/-- The tail retains the actual tower comparison and the actual associativity refinement. -/
def ampleTowerLastTailSubgroupIso :
    CompatibleIso (ampleUniversalLevel ((E.baseChange g).baseChange (k ≫ h)) n).val.2
      ((J).baseChange ((t₂) ≫ (t₃))) :=
  (ampleTowerIsoSubgroupIso g (k ≫ h) E n).trans
    (((ampleBaseRefinementSubgroupIso E n (k ≫ (h ≫ g)) ((k ≫ h) ≫ g) (𝟙 V) (w)).baseChange
      (t₂)).trans (compatibleBaseChangeComp (J) (t₃) (t₂)).symm)

/-- The independently constructed tail is the full original-presentation transport. -/
theorem ampleTowerLastTailSubgroupIso_eq_transport :
    ampleTowerLastTailSubgroupIso g h k E n =
      compatibleRefinementTransport (H) (p) (s) ((t₂) ≫ (t₃))
        (ampleTowerLastTail_original g h k E n).symm
        (ampleBaseChangeSubgroupIso (k ≫ (h ≫ g)) E n)
        (ampleBaseChangeTowerSubgroupIso g (k ≫ h) E n) := by
  unfold ampleTowerLastTailSubgroupIso
  rw [ampleTowerIsoSubgroupIso_eq_transport, ampleBaseRefinementSubgroupIso_eq_transport]
  rw [← CompatibleIso.trans_assoc, compatibleRefinementTransport_comp]
  rw [CompatibleIso.trans_assoc, CompatibleIso.trans_symm, CompatibleIso.trans_refl]

/-- The last-two-stages route agrees with the direct route as full compatible subgroup data. -/
theorem ampleTripleTowerSubgroupIso_last :
    (ampleTowerIsoSubgroupIso h k (E.baseChange g) n).trans
      ((ampleTowerLastTailSubgroupIso g h k E n).baseChange (t₁)) =
    (ampleTripleTowerSubgroupIso g h k E n).trans
      (compatibleBaseChangeCompEq (J) ((t₂) ≫ (t₃)) (t₁)
        (ampleTripleTowerIso g h k E n).hom (ampleTripleTower_last g h k E n).symm) := by
  rw [ampleTowerLastSubgroupIso_eq_transport, ampleTowerLastTailSubgroupIso_eq_transport]
  exact compatibleRefinementTransport_comp_eq (H) (p) (s) ((t₂) ≫ (t₃))
    (ampleTowerLastTail_original g h k E n) _ _ (q) (t₁)
    (ampleTripleTowerIso g h k E n).hom
    (by rw [ampleBaseChangeTowerIso_original_assoc])
    (ampleTripleTower_last g h k E n).symm (ampleTripleTowerIso_original g h k E n).symm _

end FLT.Mazur.CyclicBoundaryParameter
