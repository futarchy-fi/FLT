/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperSmoothLineSheafDescent
public import FLT.Mazur.GeometricAcyclicRankOne

/-!
# Noetherian models for lines on arbitrary affine smooth families

The base is only affine, not Noetherian. Every independently specified line
has a proper smooth Noetherian model and an actual cartesian recovery square.
This identifies its geometric acyclic rank-one condition with the condition
on its actual direct image.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.CartierAbel
open FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X S : Scheme.{0}} [IsAffine S] (f : X ⟶ S) [IsProper f] [Smooth f]
  (L : X.Modules) (hL : LocallyFreeRankOne L)

include hL in
/-- An arbitrary affine smooth family and line have a proper smooth Noetherian model. -/
theorem smoothAffineLine_noetherian_model :
    ∃ (Y B : Scheme.{0}) (q : Y ⟶ B) (a : X ⟶ Y) (b : S ⟶ B) (M : Y.Modules),
      IsLocallyNoetherian B ∧ IsProper q ∧ Smooth q ∧ LocallyFreeRankOne M ∧
        IsPullback a f q b ∧ Nonempty ((pullback a).obj M ≅ L) := by
  obtain ⟨R, hR, _, Y, q, M, hq, hsm, hM, a, ha, he⟩ :=
    Approximation.exists_proper_smooth_line_sheaf_descent
      (f ≫ S.isoSpec.hom) L hL ∅ Set.finite_empty
  let _ : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  have H : IsPullback (𝟙 X) f (f ≫ S.isoSpec.hom) S.isoSpec.hom :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  refine ⟨Y, Spec (.of R), q, a,
    S.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom R.val.toRingHom), M,
    inferInstance, hq, hsm, hM, ?_, he⟩
  simpa only [Category.id_comp] using H.paste_horiz ha

include hL in
/-- Geometric acyclicity computes the actual direct image on any affine smooth base. -/
theorem smoothAffine_geometricAcyclicRankOne_iff_actual :
    GeometricAcyclicRankOne f L ↔ AcyclicRankOne f L := by
  obtain ⟨Y, B, q, a, b, M, hB, hq, hsm, hM, h, ⟨e⟩⟩ :=
    smoothAffineLine_noetherian_model f L hL
  exact (geometricAcyclicRankOne_iso f e).symm.trans
    ((geometricAcyclicRankOne_iff_actual q h M hM).trans (acyclicRankOne_iso f e))

end FLT.Mazur.CartierAbel
