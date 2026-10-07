/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeDescentPairTransport

/-!
# Pullback and refinement squares for descent transport

The path comparisons identify pulled-back transport with transport along
composite maps. On a refinement's double overlap, the refined datum is exactly
the transport between its two composite projections into the original cover.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeGeometricDescent.Data
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y T Z : Scheme.{u}} {p : Y ⟶ X} {M : Y.Modules} (D : Data p M)

/-- Pullback of transport respects the two ordinary pullback composition charts. -/
@[reassoc]
theorem transport_pullback_hom (b c : T ⟶ Y) (w : b ≫ p = c ≫ p) (t : Z ⟶ T)
    (wt : (t ≫ b) ≫ p = (t ≫ c) ≫ p) :
    (pullback t).map (D.transport b c w).hom ≫ (pullbackComp t c).hom.app M =
      (pullbackComp t b).hom.app M ≫ (D.transport (t ≫ b) (t ≫ c) wt).hom := by
  have h := D.transport_pullback b c w t (t ≫ b) (t ≫ c) rfl rfl wt
  rw [← h]
  simp only [SchemeOverlapDiagonalChart.normalize, SheafPullbackPathComparison.comparison,
    pullbackCongr, eqToIso_refl, Iso.trans_refl, Iso.trans_hom, Iso.symm_hom,
    Iso.app_inv, Iso.app_hom, Functor.mapIso_hom, Iso.hom_inv_id_app_assoc]

/-- The two routes around any rectangle of maps over one base map agree. -/
theorem transport_rectangle (a b c d : T ⟶ Y)
    (hab : a ≫ p = b ≫ p) (hbd : b ≫ p = d ≫ p)
    (hac : a ≫ p = c ≫ p) (hcd : c ≫ p = d ≫ p) :
    (D.transport a b hab).hom ≫ (D.transport b d hbd).hom =
      (D.transport a c hac).hom ≫ (D.transport c d hcd).hom := by
  rw [D.transport_comp, D.transport_comp]

variable {X' Y' : Scheme.{u}} (q : Y' ⟶ X') (a : X' ⟶ X) (b : Y' ⟶ Y)
variable (w : q ≫ a = b ≫ p)

include w in
/-- The refined double-overlap projections have the same image in the original base. -/
theorem refinement_pair_condition :
    (Limits.pullback.fst q q ≫ b) ≫ p = (Limits.pullback.snd q q ≫ b) ≫ p := by
  rw [Category.assoc, Category.assoc, ← w, ← Category.assoc, ← Category.assoc,
    Limits.pullback.condition]

/-- The actual refined overlap is transport between the two composite cover projections. -/
theorem refine_overlap_transport :
    (D.refine p q a b w).overlap =
      (pullbackComp (Limits.pullback.fst q q) b).app M ≪≫
        D.transport (Limits.pullback.fst q q ≫ b) (Limits.pullback.snd q q ≫ b)
          (refinement_pair_condition q a b w) ≪≫
            ((pullbackComp (Limits.pullback.snd q q) b).app M).symm :=
  (SchemeOverlapRefinementCocycle.restrict_eq_refine p q a b w M D.overlap).symm

/-- The refined overlap satisfies its transport reconstruction square. -/
@[reassoc]
theorem refine_overlap_transport_hom :
    (D.refine p q a b w).overlap.hom ≫
        (pullbackComp (Limits.pullback.snd q q) b).hom.app M =
      (pullbackComp (Limits.pullback.fst q q) b).hom.app M ≫
        (D.transport (Limits.pullback.fst q q ≫ b) (Limits.pullback.snd q q ≫ b)
          (refinement_pair_condition q a b w)).hom := by
  rw [D.refine_overlap_transport q a b w]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

end FLT.Mazur.SchemeGeometricDescent.Data
