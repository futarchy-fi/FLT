/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TorusRootsOfUnityCartier
public import FLT.Mazur.RootsOfUnityNonEtale
public import FLT.Mazur.OneGonOriginalGroupComparison

/-!
# Nonetale roots-of-unity subgroups on the original pinched one-gon

The original torus coordinate embeds the actual roots-of-unity group into the
full pinched curve. Its whole-curve ideal is relative Cartier on every base
change. In prime characteristic its carrier is nonetale.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry MonObj

namespace FLT.Mazur.OneGonSmoothing

variable (K : Type) [Field K]
local notation "E" => PolygonGeneralizedCurve.curve K 1 Nat.zero_lt_one
  (OneGonNormalization.normalizationOver K) (OneGonNormalization.nodes K)
  (OneGonGlobalPushout.isPushout K Nat.zero_lt_one)

/-- The original torus coordinate, as an isomorphism to the original smooth group. -/
def rootsOfUnityTorusIso : MultiplicativeGroupScheme.gm K ≅ (E).group :=
  (CommGrp.forget (Over (Spec (.of K)))).mapIso (originalOneGonGroupTorusIso K).symm

instance rootsOfUnityTorusIso_isMonHom : IsMonHom (rootsOfUnityTorusIso K).hom :=
  inferInstanceAs (IsMonHom (originalOneGonGroupTorusIso K).inv.hom.hom.hom)

/-- The torus coordinate is exactly the original singleton component. -/
theorem rootsOfUnityTorusIso_hom :
    (rootsOfUnityTorusIso K).hom = PolygonSplitGroup.component K 1 0 := by
  apply (cancel_mono (rootsOfUnityTorusIso K).inv).mp
  rw [Iso.hom_inv_id]
  exact (originalOneGonGroupTorusIso_component K 0).symm

/-- The actual roots-of-unity subgroup of the original pinched curve. -/
def originalRootsOfUnitySubgroup (n : ℕ) [NeZero n] : (E).FiniteSubgroup n :=
  (E).torusRootsOfUnitySubgroup (rootsOfUnityTorusIso K) n

/-- The full-curve inclusion uses the original pinched torus map. -/
theorem originalRootsOfUnitySubgroup_curveMap (n : ℕ) [NeZero n] :
    (originalRootsOfUnitySubgroup K n).curveMap.left =
      (RootsOfUnityScheme.inclusion K n).left ≫ OneGonGluing.torus K := by
  change ((E).torusRootsOfUnitySubgroup (rootsOfUnityTorusIso K) n).curveMap.left = _
  rw [GeneralizedEllipticCurve.torusRootsOfUnitySubgroup_curveMap, rootsOfUnityTorusIso_hom]
  change (RootsOfUnityScheme.inclusion K n).left ≫
    (PolygonSplitGroup.component K 1 0 ≫ (E).inclusion).left = _
  rw [originalOneGon_inclusion_component]

/-- The full pinched curve carries the actual relative Cartier subgroup divisor. -/
theorem originalRootsOfUnitySubgroup_relativeCartier (n : ℕ) [NeZero n] :
    FCurve.RelativeEffectiveCartier (E).curve.hom (originalRootsOfUnitySubgroup K n).ideal :=
  (E).torusRootsOfUnitySubgroup_relativeCartier (rootsOfUnityTorusIso K) n

/-- Arbitrary one-gon tests retain the divisor with all of its multiplicities. -/
theorem originalRootsOfUnitySubgroup_baseChange_relativeCartier (n : ℕ) [NeZero n]
    {T : Scheme} (g : T ⟶ Spec (.of K)) :
    FCurve.RelativeEffectiveCartier ((E).baseChange g).curve.hom
      ((originalRootsOfUnitySubgroup K n).baseChange g).ideal :=
  (E).torusRootsOfUnitySubgroup_baseChange_relativeCartier (rootsOfUnityTorusIso K) n g

/-- The prime-characteristic boundary example is outside the etale marking construction. -/
theorem originalRootsOfUnitySubgroup_not_etale (p : ℕ) [Fact p.Prime] [CharP K p] :
    ¬ Etale (originalRootsOfUnitySubgroup K p).carrier.hom :=
  RootsOfUnityNonEtale.not_etale p K

end FLT.Mazur.OneGonSmoothing
