/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FlatStructureCohomology
public import FLT.Mazur.SpectrumRingCohomologyCoordinates
public import FLT.Mazur.SpectrumFieldCohomologyCoordinates

/-!
# Flat spectrum base change preserves free structure cohomology rank

The actual affine-cover cohomology comparison and spectrum coefficient
coordinates identify fiber dimension with the original free module rank.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.IncreasingCechCartesian

open FCurve Chow.AffineBase

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R L : Type} [CommRing R] [Nontrivial R] [Field L]
  {P X : Scheme} [X.IsSeparated]
  {p : P ⟶ X} {q : P ⟶ Spec (.of L)} {f : X ⟶ Spec (.of R)}
  {g : Spec (.of L) ⟶ Spec (.of R)} (h : IsPullback p q f g)
  {ι : Type} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i)) (hCover : iSup U = ⊤)

include h hU hCover in
/-- Flat base change to a field preserves the rank of actual free positive cohomology. -/
theorem flat_structure_cohomology_finrank (hg : g.appTop.hom.Flat) (n : ℕ)
    [Module.Free R (ModuleRingH (baseCohomologyScalars f) (structureModule X) (n + 1))] :
    Module.finrank L (ScalarH q (n + 1)) =
      Module.finrank R
        (ModuleRingH (baseCohomologyScalars f) (structureModule X) (n + 1)) := by
  let _ := SpectrumFieldCohomologyCoordinates.globalSectionsField L
  let _ : Nontrivial Γ(Spec (.of R), ⊤) :=
    (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm.injective.nontrivial
  let _ := g.appTop.hom.toAlgebra
  let _ := SpectrumRingCohomologyCoordinates.cohomology_free f (structureModule X) (n + 1)
  rw [← (moduleScalarHUnitEquiv q (n + 1)).finrank_eq,
    ← SpectrumFieldCohomologyCoordinates.cohomology_finrank]
  exact (flatStructureCohomologyEquiv h U hU hCover hg n).finrank_eq.symm.trans
    ((Module.finrank_baseChange (R := Γ(Spec (.of L), ⊤))
      (S := Γ(Spec (.of R), ⊤))).trans
      (SpectrumRingCohomologyCoordinates.cohomology_finrank f (structureModule X) (n + 1)))

end FLT.Mazur.IncreasingCechCartesian
