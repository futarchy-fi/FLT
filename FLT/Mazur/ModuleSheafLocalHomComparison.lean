/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafLocalHomRefinement
public import FLT.Mazur.AffineIteratedPullbackSections

/-!
# Local morphisms for a specified refinement map

A pullback comparison equation along a commuting triangle gives equality
of the corresponding local maps on every subopen of the smaller image.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.ModuleSheafOpenImmersionLocalHom

open ModuleSheafMorphismGluing AffineIteratedPullbackSections

variable {X Y Z : Scheme.{u}} (i : Y ⟶ X) (t : Z ⟶ Y) (d : Z ⟶ X)
variable [IsOpenImmersion i] [IsOpenImmersion t] [IsOpenImmersion d]
variable {M N : X.Modules}

/-- A commuting refinement triangle gives inclusion of its image opens. -/
lemma refinementRange_le_of_eq (hd : t ≫ i = d) : d.opensRange ≤ i.opensRange := by
  subst d
  exact refinementRange_le i t

/-- A comparison equation implies equality of local maps on every smaller image subopen. -/
lemma localHom_refine_of_eq (hd : t ≫ i = d)
    (a : (pullback i).obj M ⟶ (pullback i).obj N)
    (b : (pullback d).obj M ⟶ (pullback d).obj N)
    (hab : (pullback t).map a ≫ (compositeIso t i d hd N).hom =
      (compositeIso t i d hd M).hom ≫ b)
    (T : X.Opens) (hT : T ≤ d.opensRange) (hI : T ≤ i.opensRange) :
    localApp (localHom d b) hT = localApp (localHom i a) hI := by
  subst d
  simp only [compositeIso, pullbackCongr, eqToIso_refl] at hab
  have hb : b = (pullbackComp t i).inv.app M ≫ (pullback t).map a ≫
      (pullbackComp t i).hom.app N := by
    apply (cancel_epi ((pullbackComp t i).hom.app M)).mp
    rw [Iso.hom_inv_id_app_assoc]
    exact hab.symm
  rw [hb]
  exact localHom_refine_app i t a T hT

end FLT.Mazur.ModuleSheafOpenImmersionLocalHom
