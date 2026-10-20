/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicOrbitScheme
public import FLT.Mazur.CyclicCharacteristicLocallyRingedDescent

/-!
# Scheme descent through the actual full invariant quotient

The original full comparison arrows are coequalized as scheme maps, and every
invariant scheme morphism descends uniquely. This includes nonaffine targets.
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

/-- The scheme projection coequalizes the original full comparison arrows. -/
@[reassoc] theorem invariantOrbitSchemeProjection_condition :
    (src) ≫ invariantOrbitSchemeProjection n = (tgt) ≫ invariantOrbitSchemeProjection n := by
  apply Scheme.Hom.ext'
  exact invariantLocallyRingedProjection_condition n

/-- Every invariant scheme morphism descends through the original invariant quotient. -/
def invariantOrbitSchemeDescend {Y : Scheme} (f : normalizedDisjointSource n ⟶ Y)
    (h : (src) ≫ f = (tgt) ≫ f) : invariantOrbitScheme n ⟶ Y :=
  ⟨invariantLocallyRingedDescend n f.toLRSHom (congrArg Scheme.Hom.toLRSHom h)⟩

/-- The descended morphism recovers the original scheme morphism. -/
@[reassoc] theorem invariantOrbitSchemeDescend_fac {Y : Scheme}
    (f : normalizedDisjointSource n ⟶ Y) (h : (src) ≫ f = (tgt) ≫ f) :
    invariantOrbitSchemeProjection n ≫ invariantOrbitSchemeDescend n f h = f := by
  apply Scheme.Hom.ext'
  exact invariantLocallyRingedDescend_fac n f.toLRSHom _

/-- The original source determines the descended scheme map uniquely. -/
theorem invariantOrbitSchemeDescend_unique {Y : Scheme}
    (f : normalizedDisjointSource n ⟶ Y) (h : (src) ≫ f = (tgt) ≫ f)
    (g : invariantOrbitScheme n ⟶ Y) (hg : invariantOrbitSchemeProjection n ≫ g = f) :
    g = invariantOrbitSchemeDescend n f h := by
  apply Scheme.Hom.ext'
  exact invariantLocallyRingedDescend_unique n f.toLRSHom _ g.toLRSHom
    (congrArg Scheme.Hom.toLRSHom hg)

/-- The original full comparison arrows have this explicit scheme cofork. -/
def invariantOrbitSchemeCofork : Cofork (src) (tgt) :=
  Cofork.ofπ (invariantOrbitSchemeProjection n) (invariantOrbitSchemeProjection_condition n)

/-- The constructed scheme satisfies the full scheme coequalizer universal property. -/
def invariantOrbitSchemeCoforkIsColimit : IsColimit (invariantOrbitSchemeCofork n) := by
  apply Cofork.IsColimit.mk'
  intro s
  exact ⟨invariantOrbitSchemeDescend n s.π s.condition,
    invariantOrbitSchemeDescend_fac n s.π s.condition,
    fun {g} hg => invariantOrbitSchemeDescend_unique n s.π s.condition g hg⟩

end FLT.Mazur.CyclicCharacteristicOrbit
