/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianIndexedOverlapScheme
public import FLT.Mazur.GrassmannianTripleOverlapRestriction

/-!
# Indexed restricted triple-overlap maps

The original-chart categorical pullback maps to the next overlap by the actual
localization construction. These maps give the cyclic pullback transitions used
in scheme gluing, with both projection identities and the third-chart cocycle.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R M ι : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype ι] {d : ℕ}
  (i j k : AmbientChartIndex R M ι d)

/-- The categorical triple domain over the original indexed chart. -/
abbrev indexedTripleOverlap := pullback (indexedOverlapInclusion i j) (indexedOverlapInclusion i k)

/-- The next overlap restriction, constructed from the actual triple localization. -/
def indexedTripleNext : indexedTripleOverlap i j k ⟶ indexedOverlapScheme j k :=
  ambientTripleNextRestriction (ambientChartChange i j) (ambientChartChange j k)
    (ambientChartChange i k) (ambientChartChange_trans i j k)

/-- Restriction agrees with the original chart transition into the middle chart. -/
@[reassoc] theorem indexedTripleNext_square :
    indexedTripleNext i j k ≫ indexedOverlapInclusion j k =
      pullback.fst _ _ ≫ indexedChartTransition i j :=
  ambientTripleNextRestriction_square _ _ _ _

/-- The two paths from the triple domain into the third chart agree. -/
@[reassoc] theorem indexedTripleNext_cocycle :
    indexedTripleNext i j k ≫ indexedChartTransition j k =
      pullback.snd _ _ ≫ indexedChartTransition i k :=
  ambientTripleNextRestriction_cocycle _ _ _ _

/-- The actual cyclic transition between the categorical triple pullbacks. -/
def indexedTripleTransition : indexedTripleOverlap i j k ⟶ indexedTripleOverlap j k i :=
  pullback.lift (indexedTripleNext i j k)
    (pullback.fst _ _ ≫ (indexedOverlapIso i j).hom) (by
      rw [Category.assoc, indexedOverlapIso_factor, indexedTripleNext_square])

/-- The first projection is the constructed restriction to the next overlap. -/
@[reassoc] theorem indexedTripleTransition_fst :
    indexedTripleTransition i j k ≫ pullback.fst _ _ = indexedTripleNext i j k :=
  pullback.lift_fst _ _ _

/-- The second projection is the original overlap identification. -/
@[reassoc] theorem indexedTripleTransition_snd :
    indexedTripleTransition i j k ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ (indexedOverlapIso i j).hom :=
  pullback.lift_snd _ _ _

/-- After two cyclic changes the first projection is the third original overlap transition. -/
@[reassoc] theorem indexedTripleTransition_twice_fst :
    indexedTripleTransition i j k ≫ indexedTripleTransition j k i ≫ pullback.fst _ _ =
      pullback.snd _ _ ≫ (indexedOverlapIso i k).hom := by
  apply (cancel_mono (indexedOverlapInclusion k i)).mp
  simp only [Category.assoc, indexedTripleTransition_fst_assoc, indexedTripleNext_square]
  rw [indexedTripleNext_cocycle, indexedOverlapIso_factor]

end FLT.Mazur.GrassmannianChart
