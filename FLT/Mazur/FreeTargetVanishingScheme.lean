/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FreeTargetVanishingIdeal
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The affine scheme representing vanishing in a free target

The coefficient quotient is an actual closed subscheme. Every affine test
factors through it uniquely exactly when the base-changed linear map is zero.
The coefficient ideal is independent of the chosen target basis.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FreeTargetVanishing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R M N ι : Type} [CommRing R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N] (b : Module.Basis ι R N) (f : M →ₗ[R] N)

/-- Changing the frame changes no scheme-theoretic equation. -/
theorem ideal_basis_independent {κ : Type} (c : Module.Basis κ R N) : ideal b f = ideal c f := by
  have h (b : Module.Basis ι R N) (c : Module.Basis κ R N) : ideal b f ≤ ideal c f := by
    have hz := (baseChange_eq_zero_iff b f (R ⧸ ideal c f)).mp
      (quotient_baseChange_eq_zero c f)
    simpa only [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker] using hz
  exact le_antisymm (h b c) (by
    have hz := (baseChange_eq_zero_iff c f (R ⧸ ideal b f)).mp
      (quotient_baseChange_eq_zero b f)
    simpa only [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker] using hz)

/-- The actual coefficient-vanishing scheme. -/
def scheme : Scheme := Spec (.of (R ⧸ ideal b f))

/-- Its original closed immersion into the coefficient base. -/
def inclusion : scheme b f ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (ideal b f)))

instance inclusion_closed : IsClosedImmersion (inclusion b f) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

variable (A : Type) [CommRing A] [Algebra R A]

/-- The canonical factorization of a test that kills the entire map. -/
def lift (h : f.baseChange A = 0) : Spec (.of A) ⟶ scheme b f :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift (ideal b f) (algebraMap R A)
    ((baseChange_eq_zero_iff b f A).mp h)))

/-- The lift lies over the exact original coefficient map. -/
@[reassoc (attr := simp)] theorem lift_inclusion (h : f.baseChange A = 0) :
    lift b f A h ≫ inclusion b f = Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  rw [lift, inclusion, ← Spec.map_comp]
  congr 1

/-- Arbitrary affine tests factor through the scheme precisely on vanishing. -/
theorem factorization_iff :
    (∃ g : Spec (.of A) ⟶ scheme b f,
      g ≫ inclusion b f = Spec.map (CommRingCat.ofHom (algebraMap R A))) ↔
        f.baseChange A = 0 := by
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨k, rfl⟩ := Spec.map_surjective g
    rw [inclusion, ← Spec.map_comp] at hg
    have hk := congrArg CommRingCat.Hom.hom (Spec.map_injective hg)
    change k.hom.comp (Ideal.Quotient.mk (ideal b f)) = algebraMap R A at hk
    apply (baseChange_eq_zero_iff b f A).mpr
    intro x hx
    change algebraMap R A x = 0
    rw [← hk]
    change k.hom (Ideal.Quotient.mk (ideal b f) x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
  · intro h
    exact ⟨lift b f A h, lift_inclusion b f A h⟩

/-- Closed immersion cancellation makes the factorization unique. -/
theorem lift_unique (h : f.baseChange A = 0) (g : Spec (.of A) ⟶ scheme b f)
    (hg : g ≫ inclusion b f = Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    g = lift b f A h := by
  apply (cancel_mono (inclusion b f)).mp
  rw [hg, lift_inclusion]

end FLT.Mazur.FreeTargetVanishing
