/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SpecGenericFlatOpen
public import FLT.Mazur.QuasiFiniteGenericFiniteFree
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Finite whole-source projection over the constructed dense principal open

For a quasi-finite algebra, the generic-free coefficient already makes the
entire Cartesian source finite. This upgrades generic flatness without a
second denominator and without selecting or deleting source branches.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
namespace FLT.Mazur.SpecGenericFlatOpen
set_option backward.isDefEq.respectTransparency false
variable (R A : Type) [CommRing R] [IsDomain R] [CommRing A] [Algebra R A]
  [Algebra.FiniteType R A] [Algebra.QuasiFinite R A]
local notation "S" => Localization.Away (coefficient R A)

/-- The previously constructed free scalar extension has finite rank. -/
theorem scalarExtension_finite : Module.Finite S (S ⊗[R] A) := by
  let _ : Module.Free S (S ⊗[R] A) :=
    (FiniteTypeGenericFreeness.exists_free_baseChange (R := R) (A := A)).choose_spec.2
  let _ := IsLocalization.isDomain_of_le_nonZeroDivisors S
    (powers_le_nonZeroDivisors_of_noZeroDivisors (coefficient_ne_zero R A))
  exact QuasiFiniteGenericFiniteFree.finite_of_free

/-- The FULL original source is finite above the constructed dense coefficient open. -/
instance projection_isFinite : IsFinite (projection R A) := by
  let _ := scalarExtension_finite R A
  let _ : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] A)))) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have he : projection R A = (pullbackSpecIso R S A).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] A))) := by
    rw [← pullbackSpecIso_inv_fst', Iso.hom_inv_id_assoc]
    rfl
  rw [he]
  infer_instance

end FLT.Mazur.SpecGenericFlatOpen
