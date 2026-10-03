/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudStrictHenselian

/-!
# The explicit unramified union's prescribed fraction embedding

Construct the completion-field algebra and fraction lift on the specific
union used by the original-factor theorems, retaining its original inclusion.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace RaynaudParameters
open NumberField

variable {R K Ω : Type*} [CommRing R] [Field K] [Field Ω]
  [Algebra R K] [IsFractionRing R K] [Algebra R Ω] [Algebra K Ω]
  [IsScalarTower R K Ω] [FaithfulSMul R Ω]

/-- Retain the canonical base algebra while introducing the fraction-field algebra. -/
local instance prescribedFractionBaseAlgebra (A : Subalgebra R Ω) :
    Algebra R (FractionRing A) := inferInstance

/-- A prescribed integral subalgebra has a compatible fraction-field embedding. -/
theorem exists_subalgebra_fraction_embedding (A : Subalgebra R Ω) :
    ∃ (_ : Algebra K (FractionRing A)) (_ : IsScalarTower R K (FractionRing A))
      (e : FractionRing A →ₐ[K] Ω),
      ∀ a : A, e (algebraMap A (FractionRing A) a) = (a : Ω) := by
  let L := FractionRing A
  let : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).mpr
    (fun _ _ h ↦ FaithfulSMul.algebraMap_injective R Ω (congrArg Subtype.val h))
  have hinj : Function.Injective (algebraMap R L) :=
    (IsFractionRing.injective A L).comp (FaithfulSMul.algebraMap_injective R A)
  let hKL : Algebra K L := (IsFractionRing.lift hinj : K →+* L).toAlgebra
  let hT : IsScalarTower R K L := .of_algebraMap_eq fun r ↦
    (IsFractionRing.lift_algebraMap hinj r).symm
  let eR : L →ₐ[R] Ω := IsFractionRing.liftAlgHom (g := A.val) Subtype.val_injective
  have hcomm : eR.toRingHom.comp (algebraMap K L) = algebraMap K Ω := by
    apply IsFractionRing.ringHom_ext (A := R)
    intro r
    simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply R K L,
      ← IsScalarTower.algebraMap_apply R K Ω]
    exact eR.commutes r
  let e : L →ₐ[K] Ω := { eR.toRingHom with commutes' := RingHom.congr_fun hcomm }
  exact ⟨hKL, hT, e,
    fun a ↦ IsFractionRing.lift_algebraMap (g := A.val.toRingHom) Subtype.val_injective a⟩

end RaynaudParameters
