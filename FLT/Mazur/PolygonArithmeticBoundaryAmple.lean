/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticResidueLine
public import FLT.Mazur.PolygonInfinitesimalStageAmple

/-!
# Ample polarizations on the original arithmetic stages

The original residue polygon boundary has its proved cubic embedding.
Finite-surjective descent makes the actual arithmetic boundary ample at
every order over a Noetherian local ring with principal maximal ideal.
The coefficient ring need not contain its residue field.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry IsLocalRing
namespace FLT.Mazur.PolygonArithmeticStages
open FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (π : A)
  (hgen : maximalIdeal A = ideal A π) (m n : ℕ) (h : 2 ≤ n)

include hgen in
/-- The actual boundary line is ample on every whole arithmetic thickening. -/
theorem boundaryLine_ample : AmpleLineBundle (boundaryLine A π m n h) := by
  let _ : NeZero n := ⟨by omega⟩
  let hπ := parameter_residue_zero A π hgen
  let _ := family_proper A π hgen m n h
  let _ := residueFiberInclusion_surjective A π hgen hπ m n h
  apply ampleLineBundle_of_finiteSurjective (family A π m n h).hom
    (residueFiberInclusion A π hπ m n h) (boundaryLine_rankOne A π m n h)
  exact (PolygonInfinitesimalStages.specialBoundaryLine_ample (ResidueField A) n h).of_iso
    (boundaryLineResidueIso A π hπ m n h)

include hgen in
/-- The arithmetic polarizations are relatively ample over the unchanged quotient bases. -/
theorem boundaryLine_relativelyAmple :
    RelativelyAmpleLineBundle (family A π m n h).hom (boundaryLine A π m n h) :=
  (boundaryLine_ample A π hgen m n h).relative_of_affine _

variable [IsDomain A] [IsDiscreteValuationRing A]

omit [IsLocalRing A] [IsNoetherianRing A] in
/-- An actual uniformizer gives an ample marked arithmetic stage in mixed characteristic. -/
theorem boundaryLine_ample_of_irreducible (hπ : Irreducible π) :
    AmpleLineBundle (boundaryLine A π m n h) :=
  boundaryLine_ample A π ((IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ) m n h

end FLT.Mazur.PolygonArithmeticStages
