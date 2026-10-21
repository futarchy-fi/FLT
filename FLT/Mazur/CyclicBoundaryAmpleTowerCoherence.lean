/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryAmpleTowerModuli
public import FLT.Mazur.CompatibleSubgroupRefinementCast

/-!
# Full subgroup coherence of the actual ample tower comparison

The actual tower comparison is the uniquely determined compatible transport
between its direct and iterated presentations. It commutes with further
parameter refinement at the level of full curves and actual finite subgroups.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicBoundaryParameter
open GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T U : Scheme} (g : T ⟶ S) (h : U ⟶ T) (E : GeneralizedEllipticCurve S)
  [IsSeparated E.group.hom] [SmoothOfRelativeDimension 1 E.group.hom]
  (n : ℕ) [NeZero n]

local instance ampleCoherentTowerGroup_separated {V W : Scheme}
    (F : GeneralizedEllipticCurve V) [IsSeparated F.group.hom] (f : W ⟶ V) :
    IsSeparated (F.baseChange f).group.hom :=
  inferInstanceAs (IsSeparated (pullback.snd F.group.hom f))

local instance ampleCoherentTowerGroup_smooth {V W : Scheme}
    (F : GeneralizedEllipticCurve V) [SmoothOfRelativeDimension 1 F.group.hom] (f : W ⟶ V) :
    SmoothOfRelativeDimension 1 (F.baseChange f).group.hom :=
  MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) F.group.hom f
    inferInstance

local notation "H" => Sigma.snd (Subtype.val (ampleUniversalLevel E n))
local notation "p" => ampleBaseChangeToOriginal (h ≫ g) E n
local notation "q" => ampleBaseChangeToOriginal h (E.baseChange g) n ≫
  ampleBaseChangeToOriginal g E n
local notation "t" => Iso.hom (ampleBaseChangeTowerIso g h E n)
local notation "a" => ampleBaseChangeSubgroupIso (h ≫ g) E n
local notation "b" => ampleBaseChangeTowerSubgroupIso g h E n
local notation "w" => Eq.symm (ampleBaseChangeTowerIso_original g h E n)

/-- The existing tower comparison is the exact compatible presentation transport. -/
theorem ampleTowerIsoSubgroupIso_eq_transport :
    ampleTowerIsoSubgroupIso g h E n = compatibleRefinementTransport (H) (p) (q) (t) (w)
      (a) (b) :=
  compatibleRefinementTransport_cast _ _ _ _ (ampleBaseChangeTowerIso_original g h E n) _ _

/-- The tower square commutes as an equality of full compatible subgroup isomorphisms. -/
theorem ampleTowerIsoSubgroupIso_presentation :
    (ampleTowerIsoSubgroupIso g h E n).trans ((a).baseChange (t)) =
      (b).trans (compatibleBaseChangeCompEq (H) (p) (t) (q) (w)) := by
  rw [ampleTowerIsoSubgroupIso_eq_transport]
  exact compatibleRefinementTransport_presentation _ _ _ _ (w) _ _

/-- Further parameter refinement commutes with the actual tower subgroup comparison. -/
theorem ampleTowerIsoSubgroupIso_refinement {V : Scheme}
    (f : V ⟶ ampleParameter ((E.baseChange g).baseChange h) n)
    {D : GeneralizedEllipticCurve V} {J : D.FiniteSubgroup n}
    (c : CompatibleIso J ((H).baseChange (f ≫ (q)))) :
    (compatibleRefinementTransport (H) (q) (f ≫ (q)) f rfl (b) c).trans
      ((ampleTowerIsoSubgroupIso g h E n).baseChange f) =
    (compatibleRefinementTransport (H) (p) (f ≫ (q)) (f ≫ (t))
      (by rw [Category.assoc, ampleBaseChangeTowerIso_original]) (a) c).trans
      (compatibleBaseChangeComp (ampleUniversalLevel (E.baseChange (h ≫ g)) n).val.2
        (t) f) := by
  rw [ampleTowerIsoSubgroupIso_eq_transport]
  exact compatibleRefinementTransport_comp (H) (p) (q) (f ≫ (q)) (t) f (w) rfl (a) (b) c

end FLT.Mazur.CyclicBoundaryParameter
