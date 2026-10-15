/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothRadicalBaseChange
public import FLT.Mazur.EnvelopeBoundaryIdealTransport

/-!
# Exact boundary ideals along smooth affine maps

The original envelope denominator ideal is radical. On a Noetherian affine
source its pullback along a smooth affine map remains radical. Equality of
pulled-back interiors therefore gives equality of the actual ideals, without
assuming that the original base is reduced.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeOpenEnvelope
universe u
variable {Y X Z : Scheme.{u}} (π : Y ⟶ X) (O : Y.Opens)
  [IsAffine X] [IsLocallyNoetherian X] [IsAffine Z]

/-- Smooth affine pullback preserves the exact radical boundary ideal. -/
theorem map_denominator_isRadical (a : Z ⟶ X) [Smooth a] :
    ((denominatorIdeal π.appTop.hom O).map a.appTop.hom).IsRadical := by
  let _ := IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  let _ := a.appTop.hom.toAlgebra
  let _ : Algebra.Smooth Γ(X, ⊤) Γ(Z, ⊤) :=
    RingHom.smooth_algebraMap.mp (HasRingHomProperty.appTop (P := @Smooth) a inferInstance)
  exact Approximation.radical_map_of_smooth Γ(X, ⊤) Γ(Z, ⊤) _
    (denominatorIdeal_isRadical π.appTop.hom O)

/-- Invariance under smooth endpoints identifies the full ideals, not just their radicals. -/
theorem map_denominator_eq_of_smooth (a b : Z ⟶ X) [Smooth a] [Smooth b]
    (h : a ⁻¹ᵁ fullFiberInterior π O = b ⁻¹ᵁ fullFiberInterior π O) :
    (denominatorIdeal π.appTop.hom O).map a.appTop.hom =
      (denominatorIdeal π.appTop.hom O).map b.appTop.hom := by
  have he := radical_map_denominator_eq π O a b h
  rwa [(map_denominator_isRadical π O a).radical,
    (map_denominator_isRadical π O b).radical] at he

end FLT.Mazur.SchemeOpenEnvelope
