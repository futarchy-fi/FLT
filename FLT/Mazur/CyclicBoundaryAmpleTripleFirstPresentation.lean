/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryAmpleTripleSubgroup
public import FLT.Mazur.CompatibleSubgroupComparisonSquare

/-!
# The independent first-two-stages ample subgroup comparison

Pull back the existing two-stage comparison through the last parameter
projection, flatten the pullbacks, and compare through the cartesian lift.
The resulting full subgroup comparison equals the original-presentation transport.
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

local instance ampleTripleFirst_separated {X Y : Scheme}
    (F : GeneralizedEllipticCurve X) [IsSeparated F.group.hom] (f : Y ⟶ X) :
    IsSeparated (F.baseChange f).group.hom :=
  inferInstanceAs (IsSeparated (pullback.snd F.group.hom f))

local instance ampleTripleFirst_smooth {X Y : Scheme}
    (F : GeneralizedEllipticCurve X) [SmoothOfRelativeDimension 1 F.group.hom] (f : Y ⟶ X) :
    SmoothOfRelativeDimension 1 (F.baseChange f).group.hom :=
  MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) F.group.hom f
    inferInstance

local notation "H" => Sigma.snd (Subtype.val (ampleUniversalLevel E n))
local notation "A" => Sigma.snd (Subtype.val
  (ampleUniversalLevel (E.baseChange (h ≫ g)) n))
local notation "p" => ampleBaseChangeToOriginal (h ≫ g) E n
local notation "q" => ampleBaseChangeToOriginal h (E.baseChange g) n ≫
  ampleBaseChangeToOriginal g E n
local notation "r" => ampleBaseChangeToOriginal k
  (GeneralizedEllipticCurve.baseChange (E.baseChange g) h) n
local notation "s" => ampleBaseChangeToOriginal k (E.baseChange (h ≫ g)) n
local notation "t" => Iso.hom (ampleBaseChangeTowerIso g h E n)
local notation "j" => ampleTowerFirstLift g h k E n
local notation "a" => ampleBaseChangeSubgroupIso (h ≫ g) E n
local notation "b" => ampleBaseChangeTowerSubgroupIso g h E n
local notation "d" => ampleBaseChangeSubgroupIso k
  (GeneralizedEllipticCurve.baseChange (E.baseChange g) h) n
local notation "e" => ampleBaseChangeSubgroupIso k (E.baseChange (h ≫ g)) n
local notation "w" => Eq.symm (ampleTowerFirstLift_original g h k E n)

/-- The independent route uses the existing two-stage comparison and canonical pullbacks. -/
def ampleTowerFirstIndependentSubgroupIso :
    CompatibleIso (ampleUniversalLevel (((E.baseChange g).baseChange h).baseChange k) n).val.2
      ((ampleUniversalLevel ((E.baseChange (h ≫ g)).baseChange k) n).val.2.baseChange (j)) :=
  ((d).trans ((ampleTowerIsoSubgroupIso g h E n).baseChange (r))).trans
    ((compatibleBaseChangeComp (A) (t) (r)).symm.trans
      ((compatibleBaseChangeCompEq (A) (s) (j) ((r) ≫ (t)) (w)).trans
        ((e).baseChange (j)).symm))

/-- The direct two-stage presentation recovers the actual final base-change comparison. -/
theorem ampleTowerFirstTarget_recovery :
    compatibleRefinementTransport (H) (p) ((s) ≫ (p)) (s) rfl (a)
      (ampleBaseChangeTowerSubgroupIso (h ≫ g) k E n) = (e) :=
  compatibleRefinementTransport_extension_recovery (H) (p) (a) (s) (e)

/-- The triple presentation recovers the actual last base-change comparison. -/
theorem ampleTowerFirstSource_recovery :
    compatibleRefinementTransport (H) (q) ((r) ≫ (q)) (r) rfl (b)
      (ampleTriplePresentation g h k E n) = (d) :=
  compatibleRefinementTransport_extension_recovery (H) (q) (b) (r) (d)

/-- The independently pulled-back comparison is the existing first-lift subgroup transport. -/
theorem ampleTowerFirstIndependentSubgroupIso_eq :
    ampleTowerFirstIndependentSubgroupIso g h k E n =
      ampleTowerFirstLiftSubgroupIso g h k E n := by
  have hf := ampleTowerIsoSubgroupIso_refinement g h E n (r)
    (ampleTriplePresentation g h k E n)
  rw [ampleTowerFirstSource_recovery] at hf
  have hc := compatibleRefinementTransport_comp_eq (H) (p) ((s) ≫ (p)) (s)
    rfl (a) (ampleBaseChangeTowerSubgroupIso (h ≫ g) k E n) ((r) ≫ (q)) (j)
    ((r) ≫ (t)) (ampleTowerFirstLift_original_parameter g h k E n).symm (w)
    (by rw [Category.assoc, ampleBaseChangeTowerIso_original])
    (ampleTriplePresentation g h k E n)
  rw [ampleTowerFirstTarget_recovery] at hc
  exact CompatibleIso.compare_presentation_square_cancel (d)
    ((ampleTowerIsoSubgroupIso g h E n).baseChange (r)) _
    (compatibleBaseChangeComp (A) (t) (r))
    (compatibleBaseChangeCompEq (A) (s) (j) ((r) ≫ (t)) (w))
    (ampleTowerFirstLiftSubgroupIso g h k E n) ((e).baseChange (j)) hf hc

end FLT.Mazur.CyclicBoundaryParameter
