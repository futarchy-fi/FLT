/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteTypeGenericFreeness
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# A constructed dense principal open with flat affine source projection

For a finite type algebra over a domain, generic freeness constructs the
coefficient denominator. The entire original source is pulled back to its
principal open, and the resulting projection is flat. Existing surjectivity
and local finite presentation survive this actual scheme pullback.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
namespace FLT.Mazur.SpecGenericFlatOpen
set_option backward.isDefEq.respectTransparency false
variable (R A : Type) [CommRing R] [IsDomain R] [CommRing A] [Algebra R A]
  [Algebra.FiniteType R A]

/-- The coefficient is selected from the proved generic-freeness construction. -/
def coefficient : R := (FiniteTypeGenericFreeness.exists_free_baseChange (R := R) (A := A)).choose

theorem coefficient_ne_zero : coefficient R A ≠ 0 :=
  (FiniteTypeGenericFreeness.exists_free_baseChange (R := R) (A := A)).choose_spec.1

local notation "S" => Localization.Away (coefficient R A)

/-- The principal target open retains the original coefficient map. -/
def targetMap : Spec (.of S) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R S))

instance targetMap_isOpenImmersion : IsOpenImmersion (targetMap R A) :=
  inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R S))))

/-- The constructed principal open is dense in the original integral affine target. -/
instance targetMap_isDominant : IsDominant (targetMap R A) := by
  constructor
  apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
  change RingHom.ker (algebraMap R S) ≤ nilradical R
  rw [(RingHom.injective_iff_ker_eq_bot _).mp (IsLocalization.injective S
    (powers_le_nonZeroDivisors_of_noZeroDivisors (coefficient_ne_zero R A)))]
  exact bot_le

/-- The entire source above that open, without discarding any source branch. -/
def projection : pullback (targetMap R A)
    (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶ Spec (.of S) :=
  pullback.fst _ _

/-- Flatness follows from the proved basis of the actual scalar extension. -/
instance projection_flat : Flat (projection R A) := by
  let _ : Module.Free S (S ⊗[R] A) :=
    (FiniteTypeGenericFreeness.exists_free_baseChange (R := R) (A := A)).choose_spec.2
  let _ : Module.Flat S (S ⊗[R] A) := Module.Flat.of_free
  let _ : Flat (Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] A)))) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have he : projection R A = (pullbackSpecIso R S A).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] A))) := by
    rw [← pullbackSpecIso_inv_fst', Iso.hom_inv_id_assoc]
    rfl
  rw [he]
  let _ : Flat (pullbackSpecIso R S A).hom := inferInstance
  exact Flat.comp _ _

/-- Surjectivity of the original source survives over the entire constructed open. -/
instance projection_surjective
    [Surjective (Spec.map (CommRingCat.ofHom (algebraMap R A)))] :
    Surjective (projection R A) := inferInstanceAs (Surjective (pullback.fst _ _))

/-- Local finite presentation is retained whenever it holds for the original map. -/
instance projection_locallyOfFinitePresentation
    [LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap R A)))] :
    LocallyOfFinitePresentation (projection R A) :=
  inferInstanceAs (LocallyOfFinitePresentation (pullback.fst _ _))

/-- Both source and target are affine, so the whole flat projection is quasi-compact. -/
instance projection_quasiCompact : QuasiCompact (projection R A) :=
  inferInstanceAs (QuasiCompact (pullback.fst _ _))

end FLT.Mazur.SpecGenericFlatOpen
