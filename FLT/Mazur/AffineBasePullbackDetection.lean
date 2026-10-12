/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Cover.Open

/-!
# Affine base tests detect maps of actual scheme families

Pull back the affine cover of the original base to the original source family.
Equality on these pullbacks detects equality of the original scheme morphisms.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.AffineBasePullbackDetection
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Equality after all affine base changes detects a morphism over the original base. -/
theorem hom_ext {T : Scheme} {X Y : Over T} (f g : X ⟶ Y)
    (h : ∀ (U : Scheme) [IsAffine U] (k : U ⟶ T),
      (Over.pullback k).map f = (Over.pullback k).map g) : f = g := by
  apply Over.OverMorphism.ext
  apply Scheme.Cover.hom_ext (T.affineCover.pullback₁ X.hom)
  intro i
  change pullback.fst X.hom (T.affineCover.f i) ≫ f.left =
    pullback.fst X.hom (T.affineCover.f i) ≫ g.left
  have he := congrArg (fun z ↦ z.left ≫ pullback.fst Y.hom (T.affineCover.f i))
    (h (T.affineCover.X i) (T.affineCover.f i))
  simpa only [Over.pullback_map_left, pullback.lift_fst] using he

/-- Equality of original family isomorphisms can be checked after every affine base change. -/
theorem iso_ext {T : Scheme} {X Y : Over T} (e d : X ≅ Y)
    (h : ∀ (U : Scheme) [IsAffine U] (k : U ⟶ T),
      (Over.pullback k).mapIso e = (Over.pullback k).mapIso d) : e = d := by
  apply Iso.ext
  exact hom_ext e.hom d.hom (fun U _ k ↦ congrArg Iso.hom (h U k))

end FLT.Mazur.AffineBasePullbackDetection
