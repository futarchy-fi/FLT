/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveGraphTransport
public import FLT.Mazur.GeneralizedCurvePullbackCoherence

/-!
# Graph rotations through an equivariant Cartesian presentation

A specified action presentation on one base change retains graph rotations
on every further field fiber. The comparison uses actual iterated pullbacks.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.GeneralizedCurveGraph
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} (f : T ⟶ S) {G X : Over S} {H Y : Over T}
  [LocallyOfFinitePresentation X.hom] [LocallyOfFinitePresentation Y.hom]
  (d : H ≅ (Over.pullback f).obj G) (e : Y ≅ (Over.pullback f).obj X)
  (a : G ⊗ X ⟶ X) (b : H ⊗ Y ⟶ Y)
  (hab : b ≫ e.hom = (d.hom ⊗ₘ e.hom) ≫
    Functor.LaxMonoidal.μ (Over.pullback f) G X ≫ (Over.pullback f).map a)
  {L : Type} [Field L] (g : Spec (.of L) ⟶ T)

include hab in
omit [LocallyOfFinitePresentation X.hom] [LocallyOfFinitePresentation Y.hom] in
/-- The actual pulled-back actions are intertwined after a further field extension. -/
theorem cartesian_action_pullback :
    (Functor.LaxMonoidal.μ (Over.pullback g) H Y ≫ (Over.pullback g).map b) ≫
      (Over.pullback g).map e.hom =
    ((Over.pullback g).map d.hom ⊗ₘ (Over.pullback g).map e.hom) ≫
      Functor.LaxMonoidal.μ (Over.pullback g) ((Over.pullback f).obj G)
        ((Over.pullback f).obj X) ≫
      (Over.pullback g).map
        (Functor.LaxMonoidal.μ (Over.pullback f) G X ≫ (Over.pullback f).map a) := by
  rw [Category.assoc, ← Functor.map_comp, hab]
  simp only [Functor.map_comp, ← Category.assoc]
  rw [Functor.LaxMonoidal.μ_natural]

include hab in
/-- Field rotations descend from any equivariant Cartesian presentation of the whole action. -/
theorem fiberRotations_of_cartesian (hb : FiberRotations b g) :
    FiberRotations a (g ≫ f) := by
  let _ : LocallyOfFinitePresentation ((Over.pullback f).obj X).hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd X.hom f))
  let _ : LocallyOfFinitePresentation ((Over.pullback g).obj Y).hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd Y.hom g))
  let _ : LocallyOfFinitePresentation
      ((Over.pullback g).obj ((Over.pullback f).obj X)).hom :=
    inferInstanceAs (LocallyOfFinitePresentation
      (pullback.snd ((Over.pullback f).obj X).hom g))
  let _ : LocallyOfFinitePresentation ((Over.pullback (g ≫ f)).obj X).hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd X.hom (g ≫ f)))
  let F := Over.pullback g
  let af := Functor.LaxMonoidal.μ (Over.pullback f) G X ≫ (Over.pullback f).map a
  let ag := Functor.LaxMonoidal.μ (Over.pullback (g ≫ f)) G X ≫
    (Over.pullback (g ≫ f)).map a
  let afg := Functor.LaxMonoidal.μ F ((Over.pullback f).obj G)
    ((Over.pullback f).obj X) ≫ F.map af
  let ec : (Over.pullback (g ≫ f)).obj X ≅ F.obj ((Over.pullback f).obj X) :=
    (Over.pullbackComp g f).app X
  let dc : (Over.pullback (g ≫ f)).obj G ≅ F.obj ((Over.pullback f).obj G) :=
    (Over.pullbackComp g f).app G
  have hr : Rotations afg := rotations_of_iso (F.mapIso e) (F.mapIso d) _ _
    (cartesian_action_pullback f d e a b hab g) hb
  have hc : ag ≫ ec.hom = (dc.hom ⊗ₘ ec.hom) ≫ afg := by
    simpa only [ag, afg, af, F, ec, dc, Iso.app_hom, Functor.comp_obj,
      Functor.comp_map, Functor.LaxMonoidal.comp_μ, Functor.map_comp, Category.assoc]
      using MonoidalActionMap.naturality a (Over.pullbackComp g f).hom
  have hi : afg ≫ ec.inv = (dc.inv ⊗ₘ ec.inv) ≫ ag := by
    apply (cancel_mono ec.hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc, hc,
      ← Category.assoc, tensorHom_comp_tensorHom, Iso.inv_hom_id, Iso.inv_hom_id,
      tensorHom_id, id_whiskerRight, Category.id_comp]
  exact rotations_of_iso ec.symm dc.symm afg ag hi hr

end FLT.Mazur.GeneralizedCurveGraph
