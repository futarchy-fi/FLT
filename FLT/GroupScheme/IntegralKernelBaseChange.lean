/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.GroupScheme.FaithfullyFlatQuotient
public import FLT.GroupScheme.IntegralExtensionKernel
public import FLT.GroupScheme.IntegralQuotientIdentification

/-!
# Faithfully flat base change between integral kernels

A compatible morphism of extensions over the same quotient induces the
base change of its middle map on their actual kernels. Kernel coordinate
presentations make faithful flatness of this map explicit.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

variable {R : Type} [CommRing R] [Algebra R ℚ] [IsDomain R] [IsPrincipalIdealRing R]

/-- A faithfully flat middle map over a common quotient induces a faithfully flat
map of the actual integral kernels. -/
theorem kernelMapFaithfullyFlat
    {K H A T Q : FiniteFlatObject R}
    (E : FiniteFlatExtension K H Q) (F : FiniteFlatExtension A T Q)
    (p : H.Hom T) (i : K.Hom A)
    (hq : p.comp F.quotient = E.quotient)
    (hi : i.comp F.inclusion = E.inclusion.comp p)
    (hp : p.toAlgHom.toRingHom.FaithfullyFlat) : i.toAlgHom.toRingHom.FaithfullyFlat := by
  let f := p.toAlgHom.toRingHom
  let I := HopfAlgebra.augmentationIdeal F.quotient
  let J := HopfAlgebra.augmentationIdeal E.quotient
  have hJ : J = I.map f := by
    dsimp [I, J, HopfAlgebra.augmentationIdeal]
    rw [← hq, Ideal.map_map]
    rfl
  have hIJ : I ≤ J.comap f := by rw [hJ]; exact Ideal.le_comap_map
  let j := Ideal.quotientMap J f hIJ
  have hj : j.FaithfullyFlat := RingHom.FaithfullyFlat.quotientMap f hp I J hJ hIJ
  have he : i.toAlgHom.toRingHom = E.kernelEquiv.toRingEquiv.toRingHom.comp
      (j.comp F.kernelEquiv.symm.toRingEquiv.toRingHom) := by
    ext a
    obtain ⟨z, rfl⟩ := F.kernelEquiv.surjective a
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective z
    change i (F.kernelEquiv _) =
      E.kernelEquiv (j (F.kernelEquiv.symm (F.kernelEquiv _)))
    rw [AlgEquiv.symm_apply_apply]
    exact DFunLike.congr_fun hi t
  rw [he]
  exact RingHom.FaithfullyFlat.stableUnderComposition _ _
    (RingHom.FaithfullyFlat.stableUnderComposition _ _
      (RingHom.FaithfullyFlat.of_bijective F.kernelEquiv.symm.bijective) hj)
    (RingHom.FaithfullyFlat.of_bijective E.kernelEquiv.bijective)

variable [IsDedekindDomain R] [IsFractionRing R ℚ]

omit [IsDomain R] in
/-- A faithfully flat integral quotient admits its actual finite-flat kernel,
with the specified quotient map and the full integral torsor comparison. -/
theorem FiniteFlatObject.existsExtensionOfQuotient {H Q : FiniteFlatObject R}
    (q : H.Hom Q) (hq : Function.Surjective (FiniteFlatObject.pointMap q))
    (hqO : q.toAlgHom.toRingHom.FaithfullyFlat) :
    ∃ A : FiniteFlatObject R, ∃ E : FiniteFlatExtension A H Q, E.quotient = q := by
  let P := (FiniteFlatObject.pointMap q).toAddMonoidHom.ker
  have hP : GaloisStable H.points P := by
    intro σ h hh
    change FiniteFlatObject.pointMap q (σ • h) = 0
    rw [map_smul, show FiniteFlatObject.pointMap q h = 0 from hh, smul_zero]
  obtain ⟨A, T, E, hE⟩ := H.existsExtensionOfGaloisStable P hP
  have hexact : ∀ h, FiniteFlatObject.pointMap q h = 0 ↔
      ∃ a, FiniteFlatObject.pointMap E.inclusion a = h := by
    intro h
    change h ∈ P ↔ h ∈ (FiniteFlatObject.pointMap E.inclusion).toAddMonoidHom.range
    rw [hE]
  refine ⟨A, FiniteFlatObject.extensionOfExactMaps E.inclusion q
    E.pointsInjective E.inclusion_surjective hq hexact hqO, ?_⟩
  exact FiniteFlatObject.extensionOfExactMapsQuotient _ _ _ _ _ _ _

end ThreeAdicPlan
