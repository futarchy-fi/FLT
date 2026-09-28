/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.GroupScheme.HopfTorsor
public import FLT.GroupScheme.IntegralQuotientFaithfullyFlat
public import FLT.GroupScheme.LocalFiniteFlatExtension

/-!
# Integral extensions from exact generic subquotients

Over a principal ideal domain the flat closure of a generic subgroup and the
contracted generic quotient form an integral extension of the chosen middle
model. The torsor comparison uses the equality between the closure ideal and
the scheme-theoretic kernel ideal, so its second coordinate is the prescribed
kernel coaction.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace HopfAlgebra

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [HopfAlgebra R A] [HopfAlgebra R B] [Algebra B A] [IsScalarTower R B A]

/-- The Hopf torsor comparison with any specified presentation of the kernel ideal. -/
def torsorEquivOfIdealEq (f : B →ₐc[R] A)
    (hf : f.toAlgHom = IsScalarTower.toAlgHom R B A)
    (I : Ideal A) (hI : augmentationIdeal f = I) :
    A ⊗[B] A ≃ₐ[A] A ⊗[R] (A ⧸ I) :=
  (torsorEquiv f hf).trans
    (Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[A] A)
      (Ideal.quotientEquivAlgOfEq R hI))

/-- The comparison for a specified kernel ideal retains the canonical second coordinate. -/
theorem torsorEquivOfIdealEqSecond (f : B →ₐc[R] A)
    (hf : f.toAlgHom = IsScalarTower.toAlgHom R B A)
    (I : Ideal A) (hI : augmentationIdeal f = I) (a : A) :
    torsorEquivOfIdealEq f hf I hI (1 ⊗ₜ[B] a) =
      Algebra.TensorProduct.map (AlgHom.id R A) (Ideal.Quotient.mkₐ R I)
        (Coalgebra.comul (R := R) a) := by
  subst I
  have he : Ideal.quotientEquivAlgOfEq R (rfl : augmentationIdeal f = augmentationIdeal f) =
      AlgEquiv.refl := by
    ext x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  simp [torsorEquivOfIdealEq, he, torsorEquiv, torsorHom, torsorCoactionOverBase,
    torsorCoaction, ← Algebra.TensorProduct.one_def]

end HopfAlgebra

namespace ThreeAdicPlan

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
    [PerfectField K] [IsDedekindDomain R] [IsFractionRing R K]
    [IsPrincipalIdealRing R] {S X Y : FF R K}

/-- Flat closure and contraction assemble an exact generic sequence into an integral
extension of the original middle model, including its faithfully flat torsor. -/
def GenericGaloisHom.integralModelExtension
    (i : GenericGaloisHom S X) (q : GenericGaloisHom X Y)
    (hi : Function.Injective i) (hq : Function.Surjective q)
    (hexact : ∀ x, q x = 0 ↔ ∃ s, i s = x) :
    ModelExtension (i.closure hi) X (q.flatQuotient hq) where
  inclusion := i.closureInclusion hi
  quotient := q.toFlatQuotient hq
  compositionZero := by
    change (Ideal.Quotient.mkₐ R i.closureIdeal).comp q.quotientInclusion.toAlgHom =
      (Algebra.ofId R (X.CoordinateRing ⧸ i.closureIdeal)).comp
        (Bialgebra.counitAlgHom R q.quotientCoordinates)
    have he := i.quotientKernelIdealEqClosureIdeal q hq hexact
    change HopfAlgebra.augmentationIdeal q.quotientInclusion = i.closureIdeal at he
    rw [← he]
    exact HopfAlgebra.quotient_comp_bialgHom q.quotientInclusion
  pointsInjective := by
    intro a b hab
    exact hi (by simpa only [GenericGaloisHom.genericHom_closureInclusion] using hab)
  pointsSurjective := by
    intro y
    obtain ⟨x, hx⟩ := hq y
    exact ⟨x, (q.genericHom_toFlatQuotient hq x).trans hx⟩
  pointsExact := by
    intro x
    rw [q.genericHom_toFlatQuotient]
    constructor
    · intro hx
      obtain ⟨s, hs⟩ := (hexact x).mp hx
      exact ⟨s, (i.genericHom_closureInclusion hi s).trans hs⟩
    · rintro ⟨s, hs⟩
      exact (hexact x).mpr ⟨s, (i.genericHom_closureInclusion hi s).symm.trans hs⟩
  quotientFaithfullyFlat := q.quotientCoordinatesFaithfullyFlat
  torsorEquiv := HopfAlgebra.torsorEquivOfIdealEq q.quotientInclusion (by ext; rfl)
    i.closureIdeal (i.quotientKernelIdealEqClosureIdeal q hq hexact)
  torsorEquivSecond := HopfAlgebra.torsorEquivOfIdealEqSecond q.quotientInclusion
    (by ext; rfl) i.closureIdeal (i.quotientKernelIdealEqClosureIdeal q hq hexact)

end ThreeAdicPlan
