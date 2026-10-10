/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXMiddleIncidence
public import FLT.Mazur.WeierstrassSuccessiveXMiddleComponents
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Limits

/-!
# The full empty intersection of the ordered horizontal lines

The original comaximal line ideals give an empty scheme pullback. Its
cartesian square keeps the two distinct ordered component immersions.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (c : R) (h2 : W.a₂ = 0)
  (ha : IsUnit W.a₁)
local notation "L₁" => middleLineImmersion W c h2 0 (middle_first_root W)
local notation "L₂" => middleLineImmersion W c h2 (-W.a₁) (middle_second_root W)

include ha in
/-- The two actual ordered line images have no common point. -/
theorem middleLineImmersions_disjoint : Disjoint (Set.range L₁) (Set.range L₂) := by
  rw [range_middleLineImmersion, range_middleLineImmersion, Set.disjoint_iff_inter_eq_empty,
    ← PrimeSpectrum.zeroLocus_sup, middle_lines_disjoint W c ha]
  exact PrimeSpectrum.zeroLocus_univ

include ha in
/-- The entire categorical line intersection is empty. -/
theorem middleLinePullback_isEmpty : IsEmpty (pullback L₁ L₂ : Scheme.{u}) :=
  Scheme.isEmpty_pullback _ _ (middleLineImmersions_disjoint W c h2 ha)

include ha in
/-- The original ordered line intersection square is the empty scheme square. -/
theorem middleLines_isPullback :
    IsPullback (Scheme.emptyTo (Spec (.of (Polynomial R))))
      (Scheme.emptyTo (Spec (.of (Polynomial R)))) L₁ L₂ := by
  let _ := middleLinePullback_isEmpty W c h2 ha
  apply IsPullback.of_iso_pullback ⟨Scheme.empty_ext _ _⟩
    (asIso (Scheme.emptyTo (pullback L₁ L₂)))
  · exact Scheme.empty_ext _ _
  · exact Scheme.empty_ext _ _

/-- An explicit isomorphism with the full ordered line intersection. -/
def middleLinesPullbackIso : (∅ : Scheme.{u}) ≅ pullback L₁ L₂ :=
  (middleLines_isPullback W c h2 ha).isoPullback

/-- The empty intersection comparison preserves the first ordered projection. -/
@[reassoc] theorem middleLinesPullbackIso_first :
    (middleLinesPullbackIso W c h2 ha).hom ≫ pullback.fst L₁ L₂ = Scheme.emptyTo _ :=
  (middleLines_isPullback W c h2 ha).isoPullback_hom_fst

/-- The empty intersection comparison preserves the opposite ordered projection. -/
@[reassoc] theorem middleLinesPullbackIso_second :
    (middleLinesPullbackIso W c h2 ha).hom ≫ pullback.snd L₁ L₂ = Scheme.emptyTo _ :=
  (middleLines_isPullback W c h2 ha).isoPullback_hom_snd

end FLT.Mazur.WeierstrassSuccessiveX
