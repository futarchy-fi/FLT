/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineBasisModuleMorphism
public import FLT.Mazur.PrincipalIdealScalarImage

/-!
# Principal scalar cokernels from affine annihilator calculations

An affine annihilator identity identifies an actual ideal quotient with an
actual principal ideal image. The comparison retains scalar multiplication.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Scheme.Modules

universe u

namespace FLT.Mazur.PrincipalScalarCokernel

open GlobalIdealPower IdealPowerScalarLift PrincipalIdealScalarImage
open FCurve.CoherentDevissage

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
  (I J : X.IdealSheafData) (M : X.Modules) [M.IsFinitePresentation]
  (r : Γ(X, ⊤))
  (hJ : ∀ U : X.affineOpens, J.ideal U =
    Ideal.span {X.presheaf.map U.1.leTop.op r})
  (hI : ∀ (U : X.affineOpens) (s : Γ(M, U.1)),
    X.presheaf.map U.1.leTop.op r • s = 0 ↔
      s ∈ I.ideal U • (⊤ : Submodule Γ(X, U.1) Γ(M, U.1)))

include hI in
/-- The scalar image map annihilates the actual ideal inclusion. -/
theorem inclusion_ontoPrincipal_zero : inclusion I M ≫ ontoPrincipal J M r hJ = 0 := by
  apply (cancel_mono (inclusion J M)).mp
  rw [Category.assoc, ontoPrincipal_inclusion, zero_comp]
  apply AffineBasisModuleMorphism.hom_ext
  intro U
  ext s
  change X.presheaf.map U.1.leTop.op r • (inclusion I M).app U.1 s = 0
  apply (hI U _).mpr
  rw [← inclusion_range I M U]
  exact ⟨s, rfl⟩

/-- The original scalar map descends through the ideal quotient. -/
def comparison : cokernel (inclusion I M) ⟶ multiple J M :=
  cokernel.desc (inclusion I M) (ontoPrincipal J M r hJ)
    (inclusion_ontoPrincipal_zero I J M r hJ hI)

/-- Quotient projection followed by the comparison is the original scalar lift. -/
@[reassoc (attr := simp)] theorem projection_comparison :
    cokernel.π (inclusion I M) ≫ comparison I J M r hJ hI = ontoPrincipal J M r hJ :=
  cokernel.π_desc _ _ _

/-- The comparison is bijective on every affine open. -/
theorem comparison_bijective (U : X.affineOpens) :
    Function.Bijective ((comparison I J M r hJ hI).app U.1) := by
  have := coherent_cokernel (inclusion I M)
  have hp := affine_epi_surjective (cokernel.π (inclusion I M)) U
  have hc (s : Γ(M, U.1)) :
      (comparison I J M r hJ hI).app U.1 ((cokernel.π (inclusion I M)).app U.1 s) =
        (ontoPrincipal J M r hJ).app U.1 s :=
    congr($(projection_comparison I J M r hJ hI).app U.1 s)
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro s hs
    obtain ⟨t, rfl⟩ := hp s
    have ht : X.presheaf.map U.1.leTop.op r • t = 0 := by
      have hz := congrArg ((inclusion J M).app U.1) hs
      rw [hc, map_zero] at hz
      exact (congr($(ontoPrincipal_inclusion J M r hJ).app U.1 t)).symm.trans hz
    have hi : t ∈ LinearMap.range ((inclusion I M).val.app (op U.1)).hom := by
      rw [inclusion_range]
      exact (hI U t).mp ht
    obtain ⟨a, rfl⟩ := hi
    exact congr($(cokernel.condition (inclusion I M)).app U.1 a)
  · intro s
    obtain ⟨t, ht⟩ := ontoPrincipal_surjective J M r hJ U s
    exact ⟨(cokernel.π (inclusion I M)).app U.1 t, (hc t).trans ht⟩

/-- Affine bijectivity makes the original quotient comparison invertible globally. -/
instance comparison_isIso : IsIso (comparison I J M r hJ hI) := by
  let F := SheafOfModules.toSheaf X.ringCatSheaf
  have : IsIso (F.map (comparison I J M r hJ hI)) := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis (B := fun U : X.affineOpens ↦ U.1)
      (by simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using X.isBasis_affineOpens)
    intro U
    exact (ConcreteCategory.isIso_iff_bijective _).mpr (comparison_bijective I J M r hJ hI U)
  apply Hom.isIso_iff_isIso_app.mpr
  intro U
  exact inferInstanceAs (IsIso ((F.map (comparison I J M r hJ hI)).hom.app (op U)))

/-- The actual ideal quotient is the actual scalar image. -/
def quotientImageIso : cokernel (inclusion I M) ≅ multiple J M :=
  asIso (comparison I J M r hJ hI)

/-- The global isomorphism sends the quotient class to its specified scalar multiple. -/
@[reassoc] theorem quotientImageIso_inclusion :
    cokernel.π (inclusion I M) ≫ (quotientImageIso I J M r hJ hI).hom ≫
      inclusion J M = scalarEnd M r := by
  rw [← Category.assoc, show (quotientImageIso I J M r hJ hI).hom =
    comparison I J M r hJ hI from rfl, projection_comparison, ontoPrincipal_inclusion]

end FLT.Mazur.PrincipalScalarCokernel
