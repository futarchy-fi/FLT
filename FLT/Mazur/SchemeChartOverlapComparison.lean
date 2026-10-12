/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Full chart overlaps under reparametrization

Chart isomorphisms commuting with the actual embeddings identify the entire
scheme intersections, retain both projections, and commute with exchanging charts.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.SchemeChartOverlapComparison
variable {A B A' B' X : Scheme} (a : A ⟶ X) (b : B ⟶ X)
  (a' : A' ⟶ X) (b' : B' ⟶ X) (e : A ≅ A') (f : B ≅ B')
  (he : e.hom ≫ a' = a) (hf : f.hom ≫ b' = b)

/-- The full intersections are isomorphic over both original chart projections. -/
def overlapIso : pullback a b ≅ pullback a' b' :=
  asIso (pullback.map a b a' b' e.hom f.hom (𝟙 X)
    (by simpa only [Category.comp_id] using he.symm)
    (by simpa only [Category.comp_id] using hf.symm))

/-- The overlap comparison retains the first actual chart coordinate morphism. -/
@[reassoc] theorem overlapIso_fst :
    (overlapIso a b a' b' e f he hf).hom ≫ pullback.fst a' b' =
      pullback.fst a b ≫ e.hom := by
  simp only [overlapIso, asIso_hom, pullback.lift_fst]

/-- The overlap comparison retains the second actual chart coordinate morphism. -/
@[reassoc] theorem overlapIso_snd :
    (overlapIso a b a' b' e f he hf).hom ≫ pullback.snd a' b' =
      pullback.snd a b ≫ f.hom := by
  simp only [overlapIso, asIso_hom, pullback.lift_snd]

/-- The inverse comparison retains the full first coordinate morphism. -/
@[reassoc] theorem overlapIso_inv_fst :
    (overlapIso a b a' b' e f he hf).inv ≫ pullback.fst a b =
      pullback.fst a' b' ≫ e.inv := by
  apply (cancel_epi (overlapIso a b a' b' e f he hf).hom).mp
  simp only [Iso.hom_inv_id_assoc, overlapIso_fst_assoc, Iso.hom_inv_id, Category.comp_id]

/-- The inverse comparison retains the full second coordinate morphism. -/
@[reassoc] theorem overlapIso_inv_snd :
    (overlapIso a b a' b' e f he hf).inv ≫ pullback.snd a b =
      pullback.snd a' b' ≫ f.inv := by
  apply (cancel_epi (overlapIso a b a' b' e f he hf).hom).mp
  simp only [Iso.hom_inv_id_assoc, overlapIso_snd_assoc, Iso.hom_inv_id, Category.comp_id]

/-- Exchanging the two charts commutes with their full overlap comparison. -/
@[reassoc] theorem overlapIso_symmetry :
    (overlapIso a b a' b' e f he hf).hom ≫ (pullbackSymmetry a' b').hom =
      (pullbackSymmetry a b).hom ≫ (overlapIso b a b' a' f e hf he).hom := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullbackSymmetry_hom_comp_fst, overlapIso_snd,
      overlapIso_fst, pullbackSymmetry_hom_comp_fst_assoc]
  · simp only [Category.assoc, pullbackSymmetry_hom_comp_snd, overlapIso_fst,
      overlapIso_snd, pullbackSymmetry_hom_comp_snd_assoc]

/-- The comparison commutes with every morphism out of the original common target. -/
@[reassoc] theorem overlapIso_over {Y : Scheme} (g : X ⟶ Y) :
    (overlapIso a b a' b' e f he hf).hom ≫ pullback.fst a' b' ≫ a' ≫ g =
      pullback.fst a b ≫ a ≫ g := by
  rw [overlapIso_fst_assoc, ← Category.assoc e.hom, he]

end FLT.Mazur.SchemeChartOverlapComparison
