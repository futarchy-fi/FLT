/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineModuleEpimorphisms
public import FLT.Mazur.IdealPowerScalarLift

/-!
# Principal ideal images and their original scalar maps

If an ideal sheaf is generated on every affine open by a fixed global
section, multiplication by that section surjects onto its actual image sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules

universe u

namespace FLT.Mazur.PrincipalIdealScalarImage

open GlobalIdealPower IdealPowerScalarLift

set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
  (I : X.IdealSheafData) (M : X.Modules) [M.IsFinitePresentation]
  (r : Γ(X, ⊤))
  (hI : ∀ U : X.affineOpens, I.ideal U =
    Ideal.span {X.presheaf.map U.1.leTop.op r})

include hI

/-- Sections of a principal ideal multiple are exactly scalar multiples. -/
theorem inclusion_range_principal (U : X.affineOpens) (s : Γ(M, U.1)) :
    s ∈ LinearMap.range ((inclusion I M).val.app (op U.1)).hom ↔
      ∃ t, X.presheaf.map U.1.leTop.op r • t = s := by
  rw [inclusion_range, hI U, Submodule.ideal_span_singleton_smul]
  simpa only [Submodule.mem_top, true_and] using
    (Submodule.mem_smul_pointwise_iff_exists s
      (X.presheaf.map U.1.leTop.op r) (⊤ : Submodule Γ(X, U.1) Γ(M, U.1)))

omit [IsLocallyNoetherian X] in
/-- The actual principal generator lies in the ideal on every affine open. -/
theorem generator_mem (U : X.affineOpens) :
    X.presheaf.map U.1.leTop.op r ∈ I.ideal U := by
  rw [hI U]
  exact Ideal.subset_span (Set.mem_singleton _)

/-- Multiplication with codomain the actual principal image. -/
def ontoPrincipal : M ⟶ multiple I M :=
  scalarLift I M r (generator_mem I r hI)

/-- The principal lift retains the original scalar endomorphism. -/
@[reassoc (attr := simp)] theorem ontoPrincipal_inclusion :
    ontoPrincipal I M r hI ≫ inclusion I M = scalarEnd M r :=
  scalarLift_inclusion I M r _

/-- Every affine section of the principal image is a multiple of a section. -/
theorem ontoPrincipal_surjective (U : X.affineOpens) :
    Function.Surjective ((ontoPrincipal I M r hI).app U.1) := by
  intro s
  obtain ⟨t, ht⟩ := (inclusion_range_principal I M r hI U
    ((inclusion I M).app U.1 s)).mp ⟨s, rfl⟩
  refine ⟨t, ModuleSubobjectCoverEquality.app_injective (inclusion I M) U.1 ?_⟩
  exact (congr($(ontoPrincipal_inclusion I M r hI).app U.1 t)).trans ht

instance ontoPrincipal_epi : Epi (ontoPrincipal I M r hI) :=
  AffineModuleEpimorphisms.epi_of_affineOpen_surjective _
    (fun U hU ↦ ontoPrincipal_surjective I M r hI ⟨U, hU⟩)

end FLT.Mazur.PrincipalIdealScalarImage
