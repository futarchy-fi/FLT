/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicInitialParameter
public import FLT.Mazur.ArithmeticOneGonRoots

/-!
# The explicit original roots embedding at the initial adic stage

The existing arithmetic roots subgroup gives the bundled boundary homomorphism.
Transport in the category of commutative group schemes retains its closedness,
without expanding the arithmetic group law or assuming the order invertible.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.OneGonAdicCharacterTower

open OneGonSmoothing

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Postcomposition with a bundled group isomorphism preserves closed immersion. -/
theorem closedImmersion_comp_groupIso {S : Scheme} {G H K : CommGrp (Over S)}
    (f : G ⟶ H) (e : H ≅ K) [IsClosedImmersion f.hom.hom.hom.left] :
    IsClosedImmersion (f ≫ e.hom).hom.hom.hom.left := by
  let F := CommGrp.forget (Over S) ⋙ Over.forget S
  change IsClosedImmersion (F.map (f ≫ e.hom))
  rw [F.map_comp]
  let _ : IsIso (F.map e.hom) := inferInstance
  let _ : IsClosedImmersion (F.map f) := ‹IsClosedImmersion f.hom.hom.hom.left›
  exact inferInstanceAs (IsClosedImmersion (F.map f ≫ F.map e.hom))

variable {R : Type} [CommRing R] (n : ℕ) [NeZero n]

/-- The actual arithmetic boundary subgroup as a bundled homomorphism. -/
def boundaryRootsHom : CommGrp.mk (CharacterSchemeBaseChange.model R (ZMod n)) ⟶
    relativeGroup (0 : R) :=
  InducedCategory.homMk (Grp.homMk (ArithmeticOneGonRoots.subgroup R n).inclusion)

instance boundaryRootsHom_isClosedImmersion :
    IsClosedImmersion (boundaryRootsHom (R := R) n).hom.hom.hom.left :=
  (ArithmeticOneGonRoots.subgroup R n).closed

variable (I : Ideal R) (t : R) (ht : t ∈ I)

attribute [local irreducible] initialBoundaryIso boundaryRootsHom

/-- The original initial roots embedding, with its original group law. -/
def initialRootsHom : stageSource I (ZMod n) 0 ⟶ stageGroup I t 0 :=
  boundaryRootsHom n ≫ (initialBoundaryIso I t ht).hom

instance initialRootsHom_isClosedImmersion :
    IsClosedImmersion (initialRootsHom n I t ht).hom.hom.hom.left :=
  closedImmersion_comp_groupIso (boundaryRootsHom n) (initialBoundaryIso I t ht)

end FLT.Mazur.OneGonAdicCharacterTower
