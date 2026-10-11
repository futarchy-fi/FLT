/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorSectionGeneratorOpen
public import FLT.Mazur.ProperAmpleSectionAffine

/-!
# Affineness of the actual ample divisor complement

The canonical section identifies the complement with an affine generator
open of the original ample divisor line on a proper scheme.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FCurve
variable {R : Type} [CommRing R] [IsNoetherianRing R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] {I : X.IdealSheafData} (hI : EffectiveCartier I)

include f

/-- The actual support complement of an ample effective divisor is affine. -/
theorem isAffineOpen_divisorComplement (hA : AmpleLineBundle (divisorLineBundle I hI)) :
    IsAffineOpen I.support.compl := by
  rw [← divisorSection_generatorOpen hI]
  exact hA.isAffineOpen_section f (divisorSection hI ⊤)

end FLT.Mazur.FCurve
