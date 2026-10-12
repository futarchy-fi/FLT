/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianTripleOverlapOriginalPullback

/-!
# Restricted transitions on the categorical triple pullback

Transport the constructed localization maps along the canonical pullback
isomorphism. The composite coordinate change may be supplied under a proved
equality, so these maps can be used for an indexed ambient atlas.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R : Type u} [CommRing R] {ι κ ν : Type u}
  [Fintype ι] [Fintype κ] [Fintype ν] {d : ℕ}
  (e : ((Fin d → R) × (κ → R)) ≃ₗ[R] ((Fin d → R) × (ι → R)))
  (f : ((Fin d → R) × (ν → R)) ≃ₗ[R] ((Fin d → R) × (κ → R)))
  (g : ((Fin d → R) × (ν → R)) ≃ₗ[R] ((Fin d → R) × (ι → R)))
  (h : f.trans e = g)

/-- Restrict the first chart transition to the actual next overlap on the triple pullback. -/
def ambientTripleNextRestriction :
    pullback
      (principalOverlapInclusion (ambientBlockP e.toLinearMap) (ambientBlockQ e.toLinearMap))
      (principalOverlapInclusion (ambientBlockP g.toLinearMap) (ambientBlockQ g.toLinearMap)) ⟶
        ambientOverlapScheme f := by
  subst g
  exact (tripleOverlapOriginalPullbackIso e f).inv ≫ tripleOverlapNextScheme e f

/-- The restricted map agrees with the original first transition in the middle chart. -/
@[reassoc] theorem ambientTripleNextRestriction_square :
    ambientTripleNextRestriction e f g h ≫
      principalOverlapInclusion (ambientBlockP f.toLinearMap) (ambientBlockQ f.toLinearMap) =
      pullback.fst _ _ ≫ localizedChartTransitionScheme
        (ambientBlockP e.toLinearMap) (ambientBlockQ e.toLinearMap)
        (ambientBlockU e.toLinearMap) (ambientBlockT e.toLinearMap) := by
  subst g
  apply (cancel_epi (tripleOverlapOriginalPullbackIso e f).hom).mp
  simp only [ambientTripleNextRestriction, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [Category.assoc, tripleOverlapOriginalPullbackIso_fst_assoc]
  exact (tripleOverlapScheme_square e f).symm

/-- The restricted successive transitions equal the composite transition in the third chart. -/
@[reassoc] theorem ambientTripleNextRestriction_cocycle :
    ambientTripleNextRestriction e f g h ≫ localizedChartTransitionScheme
      (ambientBlockP f.toLinearMap) (ambientBlockQ f.toLinearMap)
      (ambientBlockU f.toLinearMap) (ambientBlockT f.toLinearMap) =
      pullback.snd _ _ ≫ localizedChartTransitionScheme
        (ambientBlockP g.toLinearMap) (ambientBlockQ g.toLinearMap)
        (ambientBlockU g.toLinearMap) (ambientBlockT g.toLinearMap) := by
  subst g
  apply (cancel_epi (tripleOverlapOriginalPullbackIso e f).hom).mp
  simp only [ambientTripleNextRestriction, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [Category.assoc, tripleOverlapOriginalPullbackIso_snd_assoc]
  exact (tripleOverlapScheme_cocycle e f).symm

end FLT.Mazur.GrassmannianChart
