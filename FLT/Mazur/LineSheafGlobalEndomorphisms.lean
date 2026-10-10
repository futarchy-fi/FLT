/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineSheafEndomorphismSheaf
public import FLT.Mazur.PowerCohomologyScalarMaps

/-!
# Global scalar endomorphisms of a line

Every actual endomorphism of a line sheaf is multiplication by a unique global
function. The classification uses no hypothesis on the underlying scheme.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve.ModuleSheafScalarEndomorphisms
open ModuleSheafInternalHom IdealPowerScalarLift
variable {X : Scheme.{u}} {M : X.Modules}

/-- The internal scalar action on the whole space is the existing scalar endomorphism. -/
lemma scalarMap_top (r : Γ(X, ⊤)) :
    (scalarMap M).app ⊤ r = (scalarEnd M r).over ⊤ := by
  apply sections_ext
  intro V s
  rfl

/-- Scalar multiplication is a bijection onto actual line-sheaf endomorphisms. -/
theorem scalarEnd_bijective (hM : LocallyFreeRankOne M) :
    Function.Bijective (scalarEnd M) := by
  constructor
  · intro r s h
    apply (scalarMap_app_bijective hM ⊤).injective
    rw [scalarMap_top, scalarMap_top, h]
  · intro φ
    obtain ⟨r, hr⟩ := (scalarMap_app_bijective hM ⊤).surjective (φ.over ⊤)
    refine ⟨r, ?_⟩
    apply Scheme.Modules.hom_ext
    intro U
    ext s : 2
    exact congrArg (fun k ↦ app M M k (Over.mk U.leTop) s) hr

/-- The coefficient of a line-sheaf endomorphism is globally unique. -/
theorem existsUnique_scalarEnd (hM : LocallyFreeRankOne M) (φ : M ⟶ M) :
    ∃! r : Γ(X, ⊤), scalarEnd M r = φ := by
  obtain ⟨r, hr⟩ := (scalarEnd_bijective hM).surjective φ
  exact ⟨r, hr, fun s hs ↦ (scalarEnd_bijective hM).injective (hs.trans hr.symm)⟩

/-- The canonical global scalar classification. -/
def scalarEndEquiv (hM : LocallyFreeRankOne M) : Γ(X, ⊤) ≃ (M ⟶ M) :=
  Equiv.ofBijective (scalarEnd M) (scalarEnd_bijective hM)

/-- The scalar classification retains the original multiplication morphism. -/
lemma scalarEndEquiv_apply (hM : LocallyFreeRankOne M) (r : Γ(X, ⊤)) :
    scalarEndEquiv hM r = scalarEnd M r := rfl

end FLT.Mazur.FCurve.ModuleSheafScalarEndomorphisms
