/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GroupTorsionScheme
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_

/-!
# Transport of the full torsion scheme through an actual group isomorphism

An isomorphism of group schemes identifies their torsion equalizers. The
comparison retains the original inclusion and every torsion-valued section,
so it transports scheme-theoretic bases, including over nonreduced tests.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonObj

namespace FLT.Mazur.GroupTorsionScheme

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {S : Scheme} (G H : CommGrp (Over S)) (e : G ≅ H) (n : ℕ)

/-- Transport the original torsion equation using the actual underlying group map. -/
def transport : scheme G.X n ⟶ scheme H.X n :=
  lift H.X n (inclusion G.X n ≫ e.hom.hom.hom.hom) (by
    change ((IsMonHom.monoidHom e.hom.hom.hom.hom _)
      (inclusion G.X n)) ^ n = 1
    rw [← map_pow, inclusion_pow, map_one])

/-- Transport of the full torsion scheme retains its original inclusion in the group. -/
@[reassoc (attr := simp)] theorem transport_inclusion :
    transport G H e n ≫ inclusion H.X n = inclusion G.X n ≫ e.hom.hom.hom.hom :=
  lift_inclusion _ _ _ _

/-- Transport and inverse transport return the full original torsion equalizer. -/
theorem transport_symm : transport G H e n ≫ transport H G e.symm n = 𝟙 _ := by
  apply equalizer.hom_ext
  change (transport G H e n ≫ transport H G e.symm n) ≫ inclusion G.X n = _
  rw [Category.assoc, transport_inclusion, ← Category.assoc, transport_inclusion,
    Category.assoc]
  have h : e.hom.hom.hom.hom ≫ e.inv.hom.hom.hom = 𝟙 _ :=
    congrArg (fun k => k.hom.hom.hom) e.hom_inv_id
  change inclusion G.X n ≫ (e.hom.hom.hom.hom ≫ e.inv.hom.hom.hom) =
    𝟙 _ ≫ inclusion G.X n
  rw [h, Category.comp_id, Category.id_comp]

/-- The full torsion schemes are isomorphic, with their scheme structures preserved. -/
def transportIso : scheme G.X n ≅ scheme H.X n where
  hom := transport G H e n
  inv := transport H G e.symm n
  hom_inv_id := transport_symm G H e n
  inv_hom_id := transport_symm H G e.symm n

/-- The comparison carries each killed section to its actual transported group section. -/
@[reassoc] theorem lift_transport {T : Over S} (p : T ⟶ G.X) (hp : p ^ n = 1) :
    lift G.X n p hp ≫ transport G H e n ≫ inclusion H.X n = p ≫ e.hom.hom.hom.hom := by
  rw [transport_inclusion, ← Category.assoc, lift_inclusion]

end FLT.Mazur.GroupTorsionScheme
