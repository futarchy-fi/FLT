/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticCompleteBase
public import FLT.Mazur.PolygonArithmeticSystem
public import FLT.Mazur.PolygonPowerSeriesSystem

/-!
# Arithmetic thickenings as Cartesian fibers of one integral base map

The same map Spec A → Spec A[[t]] gives every finite arithmetic coefficient
square. All original arithmetic stages and labeled sections lie over Spec A,
and their specialization preserves the power-series structure maps.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonArithmeticStages
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (A : Type u) [CommRing A] (π : A)

/-- The original finite arithmetic thickening inside its integral base. -/
def baseToIntegral (m : ℕ) : Spec (.of (Quotient A π m)) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (ideal A π ^ (m + 1))))

instance baseToIntegral_isClosedImmersion (m : ℕ) : IsClosedImmersion (baseToIntegral A π m) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- Adjacent arithmetic thickenings retain their original inclusion in Spec A. -/
@[reassoc] theorem baseRestriction_toIntegral (m : ℕ) :
    baseRestriction A π m ≫ baseToIntegral A π (m + 1) = baseToIntegral A π m := by
  rw [baseRestriction, baseToIntegral, baseToIntegral, ← Spec.map_comp]
  rfl

/-- All original arithmetic coefficient stages lie over the same integral spectrum. -/
def baseIntegralStructure : baseSystem A π ⟶ (Functor.const ℕ).obj (Spec (.of A)) :=
  NatTrans.ofSequence (baseToIntegral A π) (by
    intro m
    change (Functor.ofSequence (baseRestriction A π)).map (homOfLE (Nat.le_succ m)) ≫
      baseToIntegral A π (m + 1) = baseToIntegral A π m ≫ 𝟙 _
    rw [Functor.ofSequence_map_homOfLE_succ, Category.comp_id, baseRestriction_toIntegral])

variable (n : ℕ) (h : 2 ≤ n)

/-- The marked arithmetic polygon system over the original integral base. -/
def stageIntegralStructure : stageSystem A π n h ⟶ (Functor.const ℕ).obj (Spec (.of A)) :=
  systemStructure A π n h ≫ baseIntegralStructure A π

/-- The original labeled sections retain the full integral coefficient map at every order. -/
theorem systemMarking_integral (i : Fin n) :
    systemMarking A π n h i ≫ stageIntegralStructure A π n h = baseIntegralStructure A π := by
  rw [stageIntegralStructure, ← Category.assoc, systemMarking_structure, Category.id_comp]

variable [IsAdicComplete (ideal A π) A]

/-- The justified integral base map, sending the universal parameter to the original π. -/
def integralToSeries : Spec (.of A) ⟶ Spec (.of (PowerSeries A)) :=
  Spec.map (CommRingCat.ofHom (completeSpecialization A π).toRingHom)

instance integralToSeries_isClosedImmersion : IsClosedImmersion (integralToSeries A π) :=
  IsClosedImmersion.spec_of_surjective _ (completeSpecialization_surjective A π)

/-- Each original arithmetic coefficient stage is the actual Cartesian base change. -/
theorem baseToIntegral_isPullback (m : ℕ) :
    IsPullback (baseToIntegral A π m) (specializationBase A π m)
      (integralToSeries A π) (PolygonInfinitesimalStages.baseToSeries A m) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (completeSpecialization_isPushout A π m)

/-- The original finite coefficient maps agree over the justified complete integral base. -/
@[reassoc] theorem baseToIntegral_toSeries (m : ℕ) :
    baseToIntegral A π m ≫ integralToSeries A π =
      specializationBase A π m ≫ PolygonInfinitesimalStages.baseToSeries A m :=
  (baseToIntegral_isPullback A π m).w

/-- Every original finite family specialization retains the same integral power-series map. -/
@[reassoc] theorem specializationFamily_toSeries (m : ℕ) :
    specializationFamily A π m n h ≫ (PolygonInfinitesimalStages.family A m n h).hom ≫
        PolygonInfinitesimalStages.baseToSeries A m =
      (family A π m n h).hom ≫ baseToIntegral A π m ≫ integralToSeries A π := by
  rw [specializationFamily_base_assoc, baseToIntegral_toSeries]

end FLT.Mazur.PolygonArithmeticStages
