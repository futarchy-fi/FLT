/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mathlib.RingTheory.Smooth.LocalFiber

/-!
# Localizing a fibre

The local ring of an algebraic fibre at a prime is the fibre of the
corresponding local ring. The comparison retains the residue-field scalars,
so it transports formal smoothness and gives the pointwise fibre criterion.
-/

public noncomputable section

open Algebra TensorProduct

namespace Ideal.Fiber

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable (p : Ideal R) [p.IsPrime] (q : Ideal (p.Fiber S)) [q.IsPrime]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The local ring of a fibre is the fibre of the corresponding local ring,
as an algebra over the residue field of the base point. -/
def localizationEquivLocalFiber :
    Localization.AtPrime q ≃ₐ[p.ResidueField]
      p.Fiber (Localization.AtPrime (q.comap TensorProduct.includeRight)) := by
  let r := q.comap TensorProduct.includeRight
  let Rp := Localization.AtPrime p
  let Sr := Localization.AtPrime r
  letI : Algebra S (p.Fiber S) := TensorProduct.rightAlgebra
  have : r.LiesOver p := inferInstanceAs ((q.under S).LiesOver p)
  letI := Localization.AtPrime.algebraOfLiesOver p r
  let e₁ := localizationAlgEquivQuotient p q
  have h : p.map (algebraMap R Sr) =
      (IsLocalRing.maximalIdeal Rp).map (algebraMap Rp Sr) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p Rp, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq]
  let e₂ := (Ideal.quotientEquivAlgOfEq Rp h).trans
    ((TensorProduct.quotIdealMapEquivQuotTensor Sr
      (IsLocalRing.maximalIdeal Rp)).restrictScalars Rp)
  let e₃ : (IsLocalRing.ResidueField Rp ⊗[Rp] Sr) ≃ₐ[p.ResidueField] p.Fiber Sr :=
    Algebra.TensorProduct.equivOfCompatibleSMul R Rp p.ResidueField p.ResidueField Sr
  let e : Localization.AtPrime q ≃ₐ[R] p.Fiber Sr :=
    ((e₁.trans e₂).restrictScalars R).trans (e₃.restrictScalars R)
  refine { __ := e, commutes' := ?_ }
  intro x
  have he : e.toRingHom.comp (algebraMap p.ResidueField (Localization.AtPrime q)) =
      algebraMap p.ResidueField (p.Fiber Sr) := by
    apply Ideal.ResidueField.ringHom_ext
    rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq,
      ← IsScalarTower.algebraMap_eq]
    exact e.toAlgHom.comp_algebraMap
  exact congr($he x)

/-- Smoothness at a point of a fibre is equivalent to formal smoothness of
the fibre of the local ring. -/
theorem isSmoothAt_iff_localFiber :
    IsSmoothAt p.ResidueField q ↔
      FormallySmooth p.ResidueField
        (p.Fiber (Localization.AtPrime (q.comap TensorProduct.includeRight))) :=
  FormallySmooth.iff_of_equiv (localizationEquivLocalFiber p q)

end Ideal.Fiber

namespace Algebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The pointwise fibre criterion for a flat finitely presented algebra. -/
theorem isSmoothAt_iff_isSmoothAt_fiber [Module.Flat R S] [FinitePresentation R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal (p.Fiber S)) [q.IsPrime] :
    IsSmoothAt R (q.comap TensorProduct.includeRight) ↔ IsSmoothAt p.ResidueField q := by
  let : Algebra S (p.Fiber S) := TensorProduct.rightAlgebra
  have : (q.comap TensorProduct.includeRight).LiesOver p :=
    inferInstanceAs ((q.under S).LiesOver p)
  rw [isSmoothAt_iff_formallySmooth_localFiber p, Ideal.Fiber.isSmoothAt_iff_localFiber]

end Algebra
