/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicInvariantLocallyRinged

/-!
# The universal property of the full invariant locally ringed quotient

Maps from the explicit orbit space and invariant sheaf are precisely maps from
the original source equal on the full comparison scheme. No scheme structure
or descended universal curve is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]
local notation "src" => disjointComparisonSource n
local notation "tgt" => disjointComparisonTarget n

/-- The explicit locally ringed projection coequalizes both full comparison maps. -/
theorem invariantLocallyRingedProjection_condition :
    (src).toLRSHom ≫ invariantLocallyRingedProjection n =
      (tgt).toLRSHom ≫ invariantLocallyRingedProjection n := by
  dsimp only [invariantLocallyRingedProjection, locallyRingedProjection]
  rw [← Category.assoc, ← Category.assoc, coequalizer.condition]

instance invariantLocallyRingedProjection_epi : Epi (invariantLocallyRingedProjection n) := by
  unfold invariantLocallyRingedProjection locallyRingedProjection
  infer_instance

/-- Every invariant locally ringed map descends through the explicit full orbit quotient. -/
def invariantLocallyRingedDescend {Y : LocallyRingedSpace}
    (f : (normalizedDisjointSource n).toLocallyRingedSpace ⟶ Y)
    (h : (src).toLRSHom ≫ f = (tgt).toLRSHom ≫ f) :
    invariantLocallyRingedSpace n ⟶ Y :=
  (invariantLocallyRingedIso n).inv ≫ coequalizer.desc f h

/-- Descent recovers the original locally ringed morphism on the original source. -/
theorem invariantLocallyRingedDescend_fac {Y : LocallyRingedSpace}
    (f : (normalizedDisjointSource n).toLocallyRingedSpace ⟶ Y)
    (h : (src).toLRSHom ≫ f = (tgt).toLRSHom ≫ f) :
    invariantLocallyRingedProjection n ≫ invariantLocallyRingedDescend n f h = f := by
  dsimp only [invariantLocallyRingedProjection, invariantLocallyRingedDescend]
  rw [Category.assoc, Iso.hom_inv_id_assoc]
  exact coequalizer.π_desc _ _

/-- The original source determines the descended locally ringed morphism uniquely. -/
theorem invariantLocallyRingedDescend_unique {Y : LocallyRingedSpace}
    (f : (normalizedDisjointSource n).toLocallyRingedSpace ⟶ Y)
    (h : (src).toLRSHom ≫ f = (tgt).toLRSHom ≫ f)
    (g : invariantLocallyRingedSpace n ⟶ Y)
    (hg : invariantLocallyRingedProjection n ≫ g = f) :
    g = invariantLocallyRingedDescend n f h := by
  apply (cancel_epi (invariantLocallyRingedProjection n)).mp
  exact hg.trans (invariantLocallyRingedDescend_fac n f h).symm

/-- The explicit invariant locally ringed space is a cofork of the actual comparison maps. -/
def invariantLocallyRingedCofork : Cofork (src).toLRSHom (tgt).toLRSHom :=
  Cofork.ofπ (invariantLocallyRingedProjection n) (invariantLocallyRingedProjection_condition n)

/-- It satisfies the full coequalizer universal property in locally ringed spaces. -/
def invariantLocallyRingedCoforkIsColimit : IsColimit (invariantLocallyRingedCofork n) := by
  apply Cofork.IsColimit.mk'
  intro s
  exact ⟨invariantLocallyRingedDescend n s.π s.condition,
    invariantLocallyRingedDescend_fac n s.π s.condition,
    fun {g} hg ↦ invariantLocallyRingedDescend_unique n s.π s.condition g hg⟩

end FLT.Mazur.CyclicCharacteristicOrbit
