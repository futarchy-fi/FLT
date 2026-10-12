/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SheafPullbackMapNormalization

/-!
# Refinement of maps in affine-test coordinates

A map between named coordinate pullbacks gives a map between iterated
pullbacks. Coherence of the named maps implies coherence of the resulting
maps on tests, as needed for gluing on arbitrary schemes.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.SheafPullbackCoordinateRefinement
open SheafPullbackPathComparison
universe u
variable {S T X Y Z : Scheme.{u}}
variable (z : T ⟶ X) (p : X ⟶ Y) (q : X ⟶ Z)
  (f : T ⟶ Y) (g : T ⟶ Z) (hf : z ≫ p = f) (hg : z ≫ q = g)
variable {M : Y.Modules} {N : Z.Modules}

/-- Express a map between named coordinates as a map between the actual test pullbacks. -/
def coordinateMap (a : (pullback f).obj M ⟶ (pullback g).obj N) :
    (pullback z).obj ((pullback p).obj M) ⟶
      (pullback z).obj ((pullback q).obj N) :=
  (comparison z p f hf).hom.app M ≫ a ≫ (comparison z q g hg).inv.app N

/-- Invertibility is retained when passing from named coordinates to test pullbacks. -/
instance coordinateMap_isIso (a : (pullback f).obj M ⟶ (pullback g).obj N) [IsIso a] :
    IsIso (coordinateMap z p q f g hf hg a) := by
  unfold coordinateMap
  infer_instance

/-- The test map recovers the original map on named coordinates. -/
@[reassoc] theorem coordinateMap_comparison
    (a : (pullback f).obj M ⟶ (pullback g).obj N) :
    coordinateMap z p q f g hf hg a ≫ (comparison z q g hg).hom.app N =
      (comparison z p f hf).hom.app M ≫ a := by
  simp only [coordinateMap, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

/-- Named coordinate refinement gives the geometric refinement equation for the test maps. -/
@[reassoc] theorem coordinateMap_refine
    (t : S ⟶ T) (z' : S ⟶ X) (hz : t ≫ z = z')
    (f' : S ⟶ Y) (g' : S ⟶ Z) (hf' : z' ≫ p = f') (hg' : z' ≫ q = g')
    (htf : t ≫ f = f') (htg : t ≫ g = g')
    (a : (pullback f).obj M ⟶ (pullback g).obj N)
    (a' : (pullback f').obj M ⟶ (pullback g').obj N)
    (ha : (pullback t).map a ≫ (comparison t g g' htg).hom.app N =
      (comparison t f f' htf).hom.app M ≫ a') :
    (pullback t).map (coordinateMap z p q f g hf hg a) ≫
        (comparison t z z' hz).hom.app ((pullback q).obj N) =
      (comparison t z z' hz).hom.app ((pullback p).obj M) ≫
        coordinateMap z' p q f' g' hf' hg' a' := by
  apply (cancel_mono ((comparison z' q g' hg').hom.app N)).mp
  simp only [Category.assoc, coordinateMap_comparison]
  rw [← comparison_assoc t z q z' g g' hz hg htg hg']
  simp only [coordinateMap, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc (pullback t) ((comparison z q g hg).inv.app N),
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [ha, ← Category.assoc, comparison_assoc t z p z' f f' hz hf htf hf',
    Category.assoc]

end FLT.Mazur.SheafPullbackCoordinateRefinement
