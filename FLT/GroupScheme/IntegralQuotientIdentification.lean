/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.GroupScheme.FaithfullyFlatRetraction
public import FLT.GroupScheme.FiniteFlatExtensionQuotientIso
public import FLT.GroupScheme.IntegralClosedImmersion

/-!
# Identification of faithfully flat integral quotients

A faithfully flat quotient over a principal ideal domain is already the
contraction of its generic quotient coordinates. The comparison preserves the
specified map, so exact integral maps assemble into the full torsor extension.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace ThreeAdicPlan

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
    [PerfectField K] [IsDedekindDomain R] [IsFractionRing R K]
    [IsPrincipalIdealRing R] {X Y : FF R K}

/-- A faithfully flat integral quotient contains every integral coordinate in
its generic image. -/
theorem ModelHom.memRangeOfGenericQuotient (f : ModelHom X Y)
    (hf : let _quotientAlgebra := f.toAlgHom.toRingHom.toAlgebra;
      Module.FaithfullyFlat Y.CoordinateRing X.CoordinateRing)
    (x : (genericHom f).quotientCoordinates) : ∃ y, f y = x.val := by
  let quotientAlgebra := f.toAlgHom.toRingHom.toAlgebra
  let quotientTower : IsScalarTower R Y.CoordinateRing X.CoordinateRing :=
    IsScalarTower.of_algebraMap_eq' f.toAlgHom.comp_algebraMap.symm
  let quotientFlat : Module.FaithfullyFlat Y.CoordinateRing X.CoordinateRing := hf
  obtain ⟨s, hs⟩ := Algebra.faithfullyFlatLinearRetraction
    (R := R) (A := Y.CoordinateRing) (B := X.CoordinateRing)
  change s.comp f.toLinearMap = LinearMap.id at hs
  obtain ⟨y, hy⟩ := x.property
  change (genericHom f).toBialgHom y = 1 ⊗ₜ[R] x.val at hy
  rw [ModelHom.toBialgHom_genericHom] at hy
  have hsK : s.lTensor K (f.toLinearMap.lTensor K y) = y := by
    change ((s.lTensor K).comp (f.toLinearMap.lTensor K)) y = y
    rw [← LinearMap.lTensor_comp, hs, LinearMap.lTensor_id]
    rfl
  change s.lTensor K (f.baseChange y) = y at hsK
  rw [hy] at hsK
  refine ⟨s x.val, ?_⟩
  apply Algebra.TensorProduct.includeRight_injective (A := K) (IsFractionRing.injective R K)
  change f.baseChange (1 ⊗ₜ[R] s x.val) = 1 ⊗ₜ[R] x.val
  rw [show 1 ⊗ₜ[R] s x.val = y from hsK, hy]

/-- The natural comparison from a contracted quotient to its prescribed integral model. -/
def ModelHom.quotientComparison (f : ModelHom X Y)
    (hq : Function.Surjective (genericHom f)) :
    ModelHom ((genericHom f).flatQuotient hq) Y := by
  let q := genericHom f
  let a := f.toAlgHom.codRestrict q.quotientCoordinates (fun y ↦ by
    refine ⟨1 ⊗ₜ[R] y, ?_⟩
    change q.toBialgHom (1 ⊗ₜ[R] y) = 1 ⊗ₜ[R] f y
    rw [ModelHom.toBialgHom_genericHom]
    rfl)
  exact BialgHom.factorOfInjectiveOfFlat q.quotientInclusion Subtype.val_injective f a
    (by ext; rfl)

omit [IsPrincipalIdealRing R] in
/-- The contracted quotient comparison retains the original quotient map. -/
theorem ModelHom.quotientComparisonComp (f : ModelHom X Y)
    (hq : Function.Surjective (genericHom f)) :
    ((genericHom f).toFlatQuotient hq).comp (f.quotientComparison hq) = f := by
  ext y
  rfl

/-- A faithfully flat quotient is isomorphic to its contracted generic quotient. -/
def ModelHom.quotientIso (f : ModelHom X Y)
    (hq : Function.Surjective (genericHom f))
    (hf : let _quotientAlgebra := f.toAlgHom.toRingHom.toAlgebra;
      Module.FaithfullyFlat Y.CoordinateRing X.CoordinateRing) :
    ((genericHom f).flatQuotient hq).Iso Y := by
  apply BialgEquiv.ofBijective (f.quotientComparison hq)
  constructor
  · intro a b hab
    let quotientAlgebra := f.toAlgHom.toRingHom.toAlgebra
    let quotientFlat : Module.FaithfullyFlat Y.CoordinateRing X.CoordinateRing := hf
    apply FaithfulSMul.algebraMap_injective Y.CoordinateRing X.CoordinateRing
    exact congrArg Subtype.val hab
  · intro x
    obtain ⟨y, hy⟩ := f.memRangeOfGenericQuotient hf x
    exact ⟨y, Subtype.ext hy⟩

variable [Algebra R ℚ] [IsFractionRing R ℚ]

/-- Closed kernel and faithfully flat quotient maps that are generically exact
form an integral extension with the prescribed maps and torsor formula. -/
def FiniteFlatObject.extensionOfExactMaps {A H Q : FiniteFlatObject R}
    (i : A.Hom H) (q : H.Hom Q)
    (hi : Function.Injective (FiniteFlatObject.pointMap i)) (hiO : Function.Surjective i)
    (hq : Function.Surjective (FiniteFlatObject.pointMap q))
    (hexact : ∀ h, FiniteFlatObject.pointMap q h = 0 ↔
      ∃ a, FiniteFlatObject.pointMap i a = h)
    (hqO : let _quotientAlgebra := q.toAlgHom.toRingHom.toAlgebra;
      Module.FaithfullyFlat Q.model.CoordinateRing H.model.CoordinateRing) :
    FiniteFlatExtension A H Q :=
  (FiniteFlatObject.extensionOfClosedImmersion i hi hiO
    (genericHom (X := H.toFF) (Y := Q.toFF) q) hq hexact).transportQuotient
      (ModelHom.quotientIso (X := H.toFF) (Y := Q.toFF) q hq hqO)

/-- Assembly from exact maps leaves the kernel inclusion unchanged. -/
theorem FiniteFlatObject.extensionOfExactMapsInclusion {A H Q : FiniteFlatObject R}
    (i : A.Hom H) (q : H.Hom Q)
    (hi : Function.Injective (FiniteFlatObject.pointMap i)) (hiO : Function.Surjective i)
    (hq : Function.Surjective (FiniteFlatObject.pointMap q))
    (hexact : ∀ h, FiniteFlatObject.pointMap q h = 0 ↔
      ∃ a, FiniteFlatObject.pointMap i a = h)
    (hqO : let _quotientAlgebra := q.toAlgHom.toRingHom.toAlgebra;
      Module.FaithfullyFlat Q.model.CoordinateRing H.model.CoordinateRing) :
    (FiniteFlatObject.extensionOfExactMaps i q hi hiO hq hexact hqO).inclusion = i := by
  ext a
  rfl

/-- Assembly from exact maps leaves the quotient morphism unchanged. -/
theorem FiniteFlatObject.extensionOfExactMapsQuotient {A H Q : FiniteFlatObject R}
    (i : A.Hom H) (q : H.Hom Q)
    (hi : Function.Injective (FiniteFlatObject.pointMap i)) (hiO : Function.Surjective i)
    (hq : Function.Surjective (FiniteFlatObject.pointMap q))
    (hexact : ∀ h, FiniteFlatObject.pointMap q h = 0 ↔
      ∃ a, FiniteFlatObject.pointMap i a = h)
    (hqO : let _quotientAlgebra := q.toAlgHom.toRingHom.toAlgebra;
      Module.FaithfullyFlat Q.model.CoordinateRing H.model.CoordinateRing) :
    (FiniteFlatObject.extensionOfExactMaps i q hi hiO hq hexact hqO).quotient = q := by
  ext a
  rfl

end ThreeAdicPlan
