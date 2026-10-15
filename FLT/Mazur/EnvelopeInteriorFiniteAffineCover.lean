/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteEnvelopeInteriorEquations

/-!
# A constructed finite affine atlas of the original envelope interior

Generators of the actual denominator ideal provide a finite scheme open
cover, with principal affine domains in the original source. This covers
exactly the interior; it does not assert that every full fiber is interior.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeOpenEnvelope
universe u
variable {Y X : Scheme.{u}} (π : Y ⟶ X) (O : Y.Opens)
  [IsAffine X] [IsLocallyNoetherian X]

/-- Choose finite generators of the actual source denominator ideal. -/
def interiorGenerators : Finset Γ(X, ⊤) :=
  (exists_finite_interior_equations π O).choose

/-- The chosen equations generate the entire ideal, including over nonreduced source rings. -/
theorem interiorGenerators_span :
    Ideal.span (interiorGenerators π O : Set Γ(X, ⊤)) = denominatorIdeal π.appTop.hom O :=
  (exists_finite_interior_equations π O).choose_spec.1

/-- Each chosen principal domain lies inside the original full interior. -/
theorem interiorGenerators_le (r : interiorGenerators π O) :
    X.basicOpen r.val ≤ fullFiberInterior π O := by
  apply (basicOpen_le_fullFiberInterior_iff π O r.val).mpr
  rw [← interiorGenerators_span π O]
  exact Ideal.subset_span r.property

/-- An actual finite open cover by the original affine principal domains. -/
def interiorAffineCover : (fullFiberInterior π O).toScheme.OpenCover where
  I₀ := interiorGenerators π O
  X r := (X.basicOpen r.val).toScheme
  f r := X.homOfLE (interiorGenerators_le π O r)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun r ↦ inferInstance⟩
    obtain ⟨r, hr, hx⟩ :=
      (interior_iff_generator π O _ (interiorGenerators_span π O) x.val).mp x.property
    refine ⟨⟨r, hr⟩, ⟨x.val, hx⟩, ?_⟩
    apply Subtype.ext
    exact congrArg (fun g : (X.basicOpen r).toScheme ⟶ X ↦ g ⟨x.val, hx⟩)
      (X.homOfLE_ι (interiorGenerators_le π O ⟨r, hr⟩))

instance interiorAffineCover_finite : Finite (interiorAffineCover π O).I₀ :=
  inferInstanceAs (Finite (interiorGenerators π O))

instance interiorAffineCover_affine (r : (interiorAffineCover π O).I₀) :
    IsAffine ((interiorAffineCover π O).X r) :=
  inferInstanceAs (IsAffine (X.basicOpen r.val).toScheme)

/-- The atlas maps retain their original principal inclusions as entire scheme morphisms. -/
@[reassoc]
theorem interiorAffineCover_map (r : (interiorAffineCover π O).I₀) :
    (interiorAffineCover π O).f r ≫ (fullFiberInterior π O).ι = (X.basicOpen r.val).ι :=
  X.homOfLE_ι (interiorGenerators_le π O r)

end FLT.Mazur.SchemeOpenEnvelope
