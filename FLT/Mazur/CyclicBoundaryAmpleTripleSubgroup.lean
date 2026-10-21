/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryAmpleTripleTower
public import FLT.Mazur.CyclicBoundaryAmpleTowerCoherence

/-!
# Full universal subgroups in three-stage ample towers

The actual iterated universal subgroup is compared with the original family.
Presentation transport then identifies the full subgroup over the direct triple
comparison and over the independently constructed lift of the first two stages.
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

local instance ampleTripleSubgroup_separated {X Y : Scheme}
    (F : GeneralizedEllipticCurve X) [IsSeparated F.group.hom] (f : Y ⟶ X) :
    IsSeparated (F.baseChange f).group.hom :=
  inferInstanceAs (IsSeparated (pullback.snd F.group.hom f))

local instance ampleTripleSubgroup_smooth {X Y : Scheme}
    (F : GeneralizedEllipticCurve X) [SmoothOfRelativeDimension 1 F.group.hom] (f : Y ⟶ X) :
    SmoothOfRelativeDimension 1 (F.baseChange f).group.hom :=
  MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) F.group.hom f
    inferInstance

local notation "D" => GeneralizedEllipticCurve.baseChange
  (GeneralizedEllipticCurve.baseChange (GeneralizedEllipticCurve.baseChange E g) h) k

local notation "H" => Sigma.snd (Subtype.val (ampleUniversalLevel E n))
local notation "q" => ampleBaseChangeToOriginal k
  (GeneralizedEllipticCurve.baseChange (GeneralizedEllipticCurve.baseChange E g) h) n ≫
  ampleBaseChangeToOriginal h (E.baseChange g) n ≫ ampleBaseChangeToOriginal g E n
local notation "p" => ampleBaseChangeToOriginal (k ≫ (h ≫ g)) E n
local notation "r" => ampleBaseChangeToOriginal k (E.baseChange (h ≫ g)) n ≫
  ampleBaseChangeToOriginal (h ≫ g) E n

/-- The triple comparison retains the actual original ample parameter. -/
@[reassoc] theorem ampleTripleTowerIso_original :
    (ampleTripleTowerIso g h k E n).hom ≫ (p) = (q) :=
  (ampleTripleTower_isPullback g h k E n).isoIsPullback_hom_fst _ _
    (ampleBaseChangeToOriginal_isPullback (k ≫ (h ≫ g)) E n)

/-- The first-stage lift retains the original parameter through both base changes. -/
@[reassoc] theorem ampleTowerFirstLift_original_parameter :
    ampleTowerFirstLift g h k E n ≫ (r) = (q) := by
  rw [ampleTowerFirstLift_original_assoc, ampleBaseChangeTowerIso_original]

/-- Three actual subgroup pullbacks retain the full original modular family. -/
def ampleTriplePresentation :
    CompatibleIso (ampleUniversalLevel (D) n).val.2 ((H).baseChange (q)) :=
  (ampleBaseChangeSubgroupIso k ((E.baseChange g).baseChange h) n).trans
    (((ampleBaseChangeTowerSubgroupIso g h E n).baseChange
      (ampleBaseChangeToOriginal k ((E.baseChange g).baseChange h) n)).trans
        (compatibleBaseChangeComp (H)
          (ampleBaseChangeToOriginal h (E.baseChange g) n ≫
            ampleBaseChangeToOriginal g E n)
          (ampleBaseChangeToOriginal k ((E.baseChange g).baseChange h) n)).symm)

/-- The direct triple parameter comparison identifies the entire universal subgroup. -/
def ampleTripleTowerSubgroupIso :
    CompatibleIso (ampleUniversalLevel (D) n).val.2
      ((ampleUniversalLevel (E.baseChange (k ≫ (h ≫ g))) n).val.2.baseChange
        (ampleTripleTowerIso g h k E n).hom) :=
  compatibleRefinementTransport (H) (p) (q) (ampleTripleTowerIso g h k E n).hom
    (ampleTripleTowerIso_original g h k E n).symm
    (ampleBaseChangeSubgroupIso (k ≫ (h ≫ g)) E n) (ampleTriplePresentation g h k E n)

/-- The lift of the first two stages transports their full compatible subgroup data. -/
def ampleTowerFirstLiftSubgroupIso :
    CompatibleIso (ampleUniversalLevel (D) n).val.2
      ((ampleUniversalLevel ((E.baseChange (h ≫ g)).baseChange k) n).val.2.baseChange
        (ampleTowerFirstLift g h k E n)) :=
  compatibleRefinementTransport (H) (r) (q) (ampleTowerFirstLift g h k E n)
    (ampleTowerFirstLift_original_parameter g h k E n).symm
    (ampleBaseChangeTowerSubgroupIso (h ≫ g) k E n) (ampleTriplePresentation g h k E n)

/-- The first route and the direct triple route agree as full compatible isomorphisms. -/
theorem ampleTripleTowerSubgroupIso_first :
    (ampleTowerFirstLiftSubgroupIso g h k E n).trans
      ((ampleTowerIsoSubgroupIso (h ≫ g) k E n).baseChange
        (ampleTowerFirstLift g h k E n)) =
    (ampleTripleTowerSubgroupIso g h k E n).trans
      (compatibleBaseChangeCompEq (ampleUniversalLevel (E.baseChange (k ≫ (h ≫ g))) n).val.2
        (ampleBaseChangeTowerIso (h ≫ g) k E n).hom (ampleTowerFirstLift g h k E n)
        (ampleTripleTowerIso g h k E n).hom (ampleTripleTower_first g h k E n).symm) := by
  rw [ampleTowerIsoSubgroupIso_eq_transport]
  exact compatibleRefinementTransport_comp_eq (H) (p) (r)
    (ampleBaseChangeTowerIso (h ≫ g) k E n).hom
    (ampleBaseChangeTowerIso_original (h ≫ g) k E n) _ _ (q)
    (ampleTowerFirstLift g h k E n) (ampleTripleTowerIso g h k E n).hom
    (ampleTowerFirstLift_original_parameter g h k E n).symm
    (ampleTripleTower_first g h k E n).symm (ampleTripleTowerIso_original g h k E n).symm _

end FLT.Mazur.CyclicBoundaryParameter
