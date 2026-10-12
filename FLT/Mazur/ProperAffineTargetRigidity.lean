/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NoetherianProperRelativeFunctions

/-!
# Maps from proper connected reduced families to affine schemes

Over an affine Noetherian base, the actual structure-map comparison on functions
is an isomorphism. Evaluation on a section therefore determines any morphism
from the whole original family to an affine scheme, including nilpotent bases.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FCurve

variable {X S Y : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (f : X ⟶ S) [IsProper f] [Flat f] [GeometricallyConnected f] [GeometricallyReduced f]
  (s : S ⟶ X) (hs : s ≫ f = 𝟙 S) [IsAffine Y]

include hs

/-- A morphism from the original proper family to an affine scheme is constant along fibers. -/
theorem proper_to_affine_eq_section (a : X ⟶ Y) : a = f ≫ s ≫ a := by
  let e := NoetherianProperRelativeFunctions.sectionsIso f s hs
  have he : s.appTop ≫ f.appTop = 𝟙 _ := by
    rw [← NoetherianProperRelativeFunctions.sectionsIso_inv f s hs,
      ← NoetherianProperRelativeFunctions.sectionsIso_hom f s hs]
    exact e.inv_hom_id
  apply ext_of_isAffine
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Category.assoc, he,
    Category.comp_id]

/-- Agreement on the original section detects equality of maps to an affine target. -/
theorem proper_to_affine_ext (a b : X ⟶ Y) (hab : s ≫ a = s ≫ b) : a = b := by
  rw [proper_to_affine_eq_section f s hs a, proper_to_affine_eq_section f s hs b, hab]

end FLT.Mazur.FCurve
