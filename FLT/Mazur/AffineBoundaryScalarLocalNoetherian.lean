/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineBoundaryScalarLocalProduct
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Noetherian full scalar-local boundary products

Finite type of the chart over the original scalars suffices: the boundary
source, and hence its stalk, is Noetherian. No Noetherianity of the original
invariant scalar ring is needed, and no reduction of the product is made.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.AffineScalarBoundaryNilpotence
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R B T : Type} [CommRing R] [CommRing B] [CommRing T]
  (s : R →+* B) (κ : R →+* T) [IsNoetherianRing T]

omit [IsNoetherianRing T] in
/-- The unchanged boundary product is finite type over its actual boundary source. -/
theorem boundaryScalarProjection_finiteType (hs : s.FiniteType) :
    LocallyOfFiniteType (boundaryScalarProjection s κ) := by
  let _ : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom s)) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr hs
  unfold boundaryScalarProjection
  infer_instance

/-- The entire boundary product is Noetherian over the Noetherian boundary source. -/
theorem boundaryProduct_noetherian (hs : s.FiniteType) :
    IsNoetherian (boundaryProduct s κ) := by
  let _ := boundaryScalarProjection_finiteType s κ hs
  let _ := LocallyOfFiniteType.isLocallyNoetherian (boundaryScalarProjection s κ)
  exact ⟨⟩

/-- Localization at the boundary prime preserves Noetherianity of the full product. -/
theorem boundaryScalarLocalProduct_noetherian (hs : s.FiniteType) (P : PrimeSpectrum T) :
    IsNoetherian (boundaryScalarLocalProduct s κ P) := by
  let _ := boundaryScalarProjection_finiteType s κ hs
  let π := pullback.snd (boundaryScalarProjection s κ) ((Spec (.of T)).fromSpecStalk P)
  let _ : LocallyOfFiniteType π := by dsimp only [π]; infer_instance
  let _ := LocallyOfFiniteType.isLocallyNoetherian π
  change IsNoetherian (pullback (boundaryScalarProjection s κ)
    ((Spec (.of T)).fromSpecStalk P))
  exact ⟨⟩

end FLT.Mazur.AffineScalarBoundaryNilpotence
