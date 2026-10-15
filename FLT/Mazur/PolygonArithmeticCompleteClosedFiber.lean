/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticOriginalAdicSquare
public import FLT.Mazur.PolygonArithmeticResidueFiber

/-!
# The original polygon as the closed fiber of the complete candidate

Pasting the original closed-stage square with the actual adic realization
identifies the complete candidate's closed fiber, preserving its original maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.PolygonArithmeticStages

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] family originalStageToCompatibleProj

variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π)
  (n : ℕ) (h : 2 ≤ n) [NeZero n]

local notation "K" => IsLocalRing.ResidueField A

/-- The closed coefficient point of the original arithmetic coefficient base. -/
def completeClosedBase : Spec (.of K) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))

omit [IsNoetherianRing A] [IsDomain A] [NeZero n] in
/-- Reduction through every original coefficient stage is the same closed base point. -/
theorem residueBase_toIntegral (m : ℕ) :
    residueBase A π (parameter_residue_zero A π hgen) m ≫ baseToIntegral A π m =
      completeClosedBase A := by
  rw [residueBase, baseToIntegral, completeClosedBase, ← Spec.map_comp]
  rfl

/-- The original polygon's closed inclusion in the actual complete candidate. -/
def completeClosedFiberInclusion :
    PolygonCyclicAtlas.scheme K n h ⟶ exactVeroneseProj A π n h hne hgen :=
  residueFiberInclusion A π (parameter_residue_zero A π hgen) 0 n h ≫
    originalStageToCompatibleProj A π hne hgen n h 0

/-- The complete candidate has the original cyclic polygon as its cartesian closed fiber. -/
theorem completeClosedFiber_isPullback :
    IsPullback (completeClosedFiberInclusion A π hne hgen n h)
      (PolygonCyclicAtlas.toBase K n h)
      (exactVeroneseProjToBase A π n h hne hgen) (completeClosedBase A) := by
  have hp := (residueFiberInclusion_isPullback A π
    (parameter_residue_zero A π hgen) 0 n h).paste_horiz
    (originalStageToCompatibleProj_isPullback A π hne hgen n h 0)
  rw [residueBase_toIntegral A π hgen] at hp
  exact hp

/-- The actual closed fiber is isomorphic to the original polygon. -/
def completeClosedFiberIso : PolygonCyclicAtlas.scheme K n h ≅
    pullback (exactVeroneseProjToBase A π n h hne hgen) (completeClosedBase A) :=
  (completeClosedFiber_isPullback A π hne hgen n h).isoPullback

/-- The comparison preserves the original polygon's inclusion in the total scheme. -/
@[reassoc] theorem completeClosedFiberIso_fst :
    (completeClosedFiberIso A π hne hgen n h).hom ≫ pullback.fst _ _ =
      completeClosedFiberInclusion A π hne hgen n h :=
  (completeClosedFiber_isPullback A π hne hgen n h).isoPullback_hom_fst

/-- The comparison preserves the original polygon's structure morphism. -/
@[reassoc] theorem completeClosedFiberIso_snd :
    (completeClosedFiberIso A π hne hgen n h).hom ≫ pullback.snd _ _ =
      PolygonCyclicAtlas.toBase K n h :=
  (completeClosedFiber_isPullback A π hne hgen n h).isoPullback_hom_snd

end FLT.Mazur.PolygonArithmeticStages
