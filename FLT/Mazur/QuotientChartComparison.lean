/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.CategoryTheory.Functor.EpiMono

/-!
# Comparing original quotient charts through global isomorphisms

A global ambient-compatible isomorphism induces an isomorphism between the
original quotient charts that respects their complete quotient projections.
-/

@[expose] public section
open CategoryTheory
namespace FLT.Mazur.QuotientChartComparison
universe u v u' v'
variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
variable (F : C ⥤ D) {S T Q P : C} {V N N' : D}
variable (q : S ⟶ Q) (p : T ⟶ P) (s : S ≅ T) (e : Q ≅ P)
variable (c : F.obj S ≅ V) (c' : F.obj T ≅ V)
  (t : F.obj Q ≅ N) (t' : F.obj P ≅ N')
variable (v : V ⟶ N) (w : V ⟶ N')

/-- The induced original-chart isomorphism preserves every ambient quotient coordinate. -/
@[reassoc] theorem projection
    (he : q ≫ e.hom = s.hom ≫ p)
    (hc : F.map s.hom ≫ c'.hom = c.hom)
    (hq : F.map q ≫ t.hom = c.hom ≫ v)
    (hp : F.map p ≫ t'.hom = c'.hom ≫ w) :
    v ≫ (t.symm ≪≫ F.mapIso e ≪≫ t').hom = w := by
  apply (cancel_epi c.hom).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [← Category.assoc c.hom v, ← hq]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← F.map_comp_assoc, he, F.map_comp, Category.assoc, hp,
    ← Category.assoc (F.map s.hom), hc]

end FLT.Mazur.QuotientChartComparison
