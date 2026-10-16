/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingIncomingMarking
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Full affine ideal sheaves of the two incident arithmetic markings

The actual spectrum morphisms have exactly the original coordinate kernels.
This comparison identifies ideals of sections, with all nilpotents retained.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (t : R) (a : Rˣ)

/-- The ideal of a spectrum morphism in the original source-ring coordinates. -/
theorem specMap_kernel_coordinate {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) :
    ((Spec.map (CommRingCat.ofHom f)).ker.ideal ⟨⊤, isAffineOpen_top _⟩).comap
      (Scheme.ΓSpecIso (.of A)).inv.hom = RingHom.ker f := by
  rw [Scheme.ker_of_isAffine]
  simp only [Scheme.IdealSheafData.ofIdealTop_ideal, homOfLE_refl, op_id]
  rw [CategoryTheory.Functor.map_id]
  simp only [CommRingCat.hom_id, Ideal.map_id]
  ext z
  change (Spec.map (CommRingCat.ofHom f)).appTop.hom
    ((Scheme.ΓSpecIso (.of A)).inv.hom z) = 0 ↔ f z = 0
  have he := congrArg (fun k ↦ k.hom z)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  change (Scheme.ΓSpecIso (.of B)).inv.hom (f z) =
    (Spec.map (CommRingCat.ofHom f)).appTop.hom
      ((Scheme.ΓSpecIso (.of A)).inv.hom z) at he
  rw [← he]
  exact map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (.of B)).inv).injective

/-- The outgoing section's ideal sheaf has the exact coordinate equation x-a. -/
theorem markedSection_ideal_coordinate :
    ((markedSection t a).ker.ideal ⟨⊤, isAffineOpen_top (Spec (.of (ChartRing t)))⟩).comap
      (Scheme.ΓSpecIso (.of (ChartRing t))).inv.hom = markedCoordinateIdeal t a := by
  rw [markedSection, specMap_kernel_coordinate, markedEvaluation_ker_eq]

/-- The incoming section's ideal sheaf has the exact coordinate equation y-a⁻¹. -/
theorem incomingMarkedSection_ideal_coordinate :
    ((incomingMarkedSection t a).ker.ideal ⟨⊤, isAffineOpen_top (Spec (.of (ChartRing t)))⟩).comap
      (Scheme.ΓSpecIso (.of (ChartRing t))).inv.hom =
        Ideal.span {rightCoordinate t - algebraMap R (ChartRing t) (a⁻¹ : Rˣ)} := by
  rw [incomingMarkedSection, specMap_kernel_coordinate, incomingMarkedEvaluation_ker]

/-- The full outgoing unit-one section ideal is (x-1). -/
theorem markedSection_one_ideal_coordinate :
    ((markedSection t 1).ker.ideal ⟨⊤, isAffineOpen_top (Spec (.of (ChartRing t)))⟩).comap
      (Scheme.ΓSpecIso (.of (ChartRing t))).inv.hom =
        Ideal.span {leftCoordinate t - 1} := by
  rw [markedSection, specMap_kernel_coordinate, markedEvaluation_one_ker]

/-- The full incoming unit-one section ideal is (y-1). -/
theorem incomingMarkedSection_one_ideal_coordinate :
    ((incomingMarkedSection t 1).ker.ideal ⟨⊤, isAffineOpen_top (Spec (.of (ChartRing t)))⟩).comap
      (Scheme.ΓSpecIso (.of (ChartRing t))).inv.hom =
        Ideal.span {rightCoordinate t - 1} := by
  rw [incomingMarkedSection, specMap_kernel_coordinate, incomingMarkedEvaluation_one_ker]

end FLT.Mazur.PolygonSmoothing
