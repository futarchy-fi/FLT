/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedDepthNegation
public import FLT.Mazur.WeierstrassDividedInitialExterior
public import FLT.Mazur.WeierstrassModificationNegation

/-!
# The actual initial exterior supplies the recursive negative

The original incidence reflection preserves the actual initial attachment.
This supplies a constructed base case, using the original coefficient data,
for iteration of the whole successor negatives with retained exteriors.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] {W : WeierstrassCurve R} {π : R} {k : ℕ}
  (d : Data W π k)
open WeierstrassModificationX

/-- The actual initial exterior carries the original incidence reflection. -/
def initialExteriorNegationIso : (initialExterior d).carrier ≅ (initialExterior d).carrier :=
  initialReflectionIso W (π ^ k) d.b3 d.b4 d.b6

/-- The initial exterior attachment is the exact original two-chart overlap. -/
@[reassoc] theorem initialExterior_attach_chart :
    (initialExterior d).attach ≫ xChart W (π ^ k) d.b3 d.b4 d.b6 =
      boundaryInclusion d ≫ dividedChart W (π ^ k) d.b3 d.b4 d.b6 := by
  change (overlapIso W (π ^ k) d.b3 d.b4 d.b6).inv ≫
    xOpenInclusion W (π ^ k) d.b3 d.b4 d.b6 ≫ xChart W (π ^ k) d.b3 d.b4 d.b6 = _
  rw [chart_overlap]
  simp only [overlapToDivided, Category.assoc, Iso.inv_hom_id_assoc]
  rfl

variable [IsDomain R] [IsBezout R] (hπ : π ≠ 0)

include hπ in
/-- The exact initial exterior attachment is equivariant for the constructed negatives. -/
@[reassoc] theorem initialExteriorNegationIso_attach :
    (boundaryNegationIso d).hom ≫ (initialExterior d).attach =
      (initialExterior d).attach ≫ (initialExteriorNegationIso d).hom := by
  apply (cancel_mono (xChart W (π ^ k) d.b3 d.b4 d.b6)).mp
  simp only [Category.assoc, initialExterior_attach_chart]
  rw [boundaryNegationIso_inclusion_assoc]
  change boundaryInclusion d ≫
    (WeierstrassDilatation.negationIso W (π ^ k) d.b3 d.b4 d.b6).hom ≫ _ = _
  rw [← dividedChart_modificationNegation W (π ^ k) d.b3 d.b4 d.b6
    d.factor3 d.factor4 d.factor6 (pow_ne_zero k hπ)]
  rw [← initialExterior_attach_chart_assoc, xChart_modificationNegation]
  rfl

omit [IsDomain R] [IsBezout R] in
/-- The entire initial exterior negative is involutive. -/
@[reassoc] theorem initialExteriorNegationIso_comp :
    (initialExteriorNegationIso d).hom ≫ (initialExteriorNegationIso d).hom = 𝟙 _ := by
  change (initialExteriorNegationIso d).hom ≫ (initialExteriorNegationIso d).inv = _
  exact Iso.hom_inv_id _

end FLT.Mazur.WeierstrassDividedDepth
