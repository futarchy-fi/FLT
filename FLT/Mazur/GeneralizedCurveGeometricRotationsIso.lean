/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveGraphTransport

/-!
# Geometric rotations are invariant under equivariant isomorphisms

The comparison transports every geometric fiber and its full incidence graph.
This allows an independently constructed action on an original curve to inherit
the rotation property from an explicitly identified polygonal model.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.GeneralizedCurveGraph
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {G H X Y : Over S}

/-- Equivariance survives the actual monoidal pullback of both actions. -/
theorem equivariant_pullback {T : Scheme} (f : T ⟶ S) (e : X ≅ Y) (d : G ≅ H)
    (a : G ⊗ X ⟶ X) (b : H ⊗ Y ⟶ Y)
    (hab : a ≫ e.hom = (d.hom ⊗ₘ e.hom) ≫ b) :
    (Functor.LaxMonoidal.μ (Over.pullback f) G X ≫ (Over.pullback f).map a) ≫
      ((Over.pullback f).mapIso e).hom =
        (((Over.pullback f).mapIso d).hom ⊗ₘ ((Over.pullback f).mapIso e).hom) ≫
          Functor.LaxMonoidal.μ (Over.pullback f) H Y ≫ (Over.pullback f).map b := by
  simp only [Functor.mapIso_hom]
  rw [Category.assoc, ← Functor.map_comp, hab, Functor.map_comp, ← Category.assoc,
    ← Functor.LaxMonoidal.μ_natural, Category.assoc]

variable [LocallyOfFinitePresentation X.hom] [LocallyOfFinitePresentation Y.hom]

/-- All geometric rotation conditions transport with the actual equivariant curve. -/
theorem geometricRotations_of_iso (e : X ≅ Y) (d : G ≅ H)
    (a : G ⊗ X ⟶ X) (b : H ⊗ Y ⟶ Y)
    (hab : a ≫ e.hom = (d.hom ⊗ₘ e.hom) ≫ b) (ha : GeometricRotations a) :
    GeometricRotations b := by
  intro L _ _ f hn
  let F := Over.pullback f
  let _ : LocallyOfFinitePresentation (F.obj X).hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd X.hom f))
  let _ : LocallyOfFinitePresentation (F.obj Y).hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd Y.hom f))
  have hns : ¬ Smooth (F.obj X).hom := by
    intro hx
    apply hn
    have hi : IsIso (F.mapIso e).inv.left :=
      inferInstanceAs (IsIso ((Over.forget _).map (F.mapIso e).inv))
    have he : (F.mapIso e).inv.left ≫ (F.obj X).hom = (F.obj Y).hom := Over.w _
    rw [← he]
    infer_instance
  exact rotations_of_iso (F.mapIso e) (F.mapIso d) _ _
    (equivariant_pullback f e d a b hab) (ha L f hns)

end FLT.Mazur.GeneralizedCurveGraph
