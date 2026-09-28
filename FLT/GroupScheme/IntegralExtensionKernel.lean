/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.GroupScheme.CartierDualKernelInclusion
public import FLT.GroupScheme.HopfTorsor
public import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Scheme-theoretic kernels of integral extensions

The prescribed torsor identifies the quotient by the augmentation ideal with
the given kernel coordinates. Faithful flatness over the original base descends
this identification from the torsor comparison.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace BialgHom

variable {R A B C : Type} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Bialgebra R A] [Bialgebra R B] [Bialgebra R C]

/-- An algebra factorization through a surjective bialgebra map is a bialgebra map. -/
def factorOfSurjective (p : A →ₐc[R] B) (hp : Function.Surjective p)
    (f : A →ₐc[R] C) (g : B →ₐ[R] C) (hg : g.comp p.toAlgHom = f.toAlgHom) : B →ₐc[R] C := by
  apply BialgHom.ofAlgHom g
  · ext b
    obtain ⟨a, rfl⟩ := hp b
    change Coalgebra.counit (g (p a)) = Coalgebra.counit (p a)
    rw [show g (p a) = f a from AlgHom.congr_fun hg a,
      CoalgHomClass.counit_comp_apply, CoalgHomClass.counit_comp_apply]
  · ext b
    obtain ⟨a, rfl⟩ := hp b
    change TensorProduct.map g.toLinearMap g.toLinearMap (Coalgebra.comul (p a)) =
      Coalgebra.comul (g (p a))
    rw [← CoalgHomClass.map_comp_comul_apply p, TensorProduct.map_map]
    have hl : g.toLinearMap.comp (p : A →ₗ[R] B) = (f : A →ₗ[R] C) :=
      congrArg AlgHom.toLinearMap hg
    rw [hl, show g (p a) = f a from AlgHom.congr_fun hg a]
    exact CoalgHomClass.map_comp_comul_apply f a

end BialgHom

namespace ThreeAdicPlan.FiniteFlatExtension

variable {R : Type} [CommRing R] [Algebra R ℚ] [IsDomain R] [IsPrincipalIdealRing R]
    {A H Q : FiniteFlatObject R}

omit [IsDomain R] [IsPrincipalIdealRing R] in
/-- The augmentation ideal of the quotient vanishes on the prescribed kernel. -/
theorem augmentationIdealLeKernel (E : FiniteFlatExtension A H Q) :
    HopfAlgebra.augmentationIdeal E.quotient ≤ RingHom.ker E.inclusion.toAlgHom.toRingHom := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro q hq
  change E.inclusion.toAlgHom (E.quotient.toAlgHom q) = 0
  have he := AlgHom.congr_fun E.compositionZero q
  change Bialgebra.counitAlgHom R Q.model.CoordinateRing q = 0 at hq
  simpa only [AlgHom.comp_apply, Algebra.ofId_apply, hq, map_zero] using he

/-- The prescribed inclusion descends to the augmentation quotient. -/
def kernelMap (E : FiniteFlatExtension A H Q) :
    (H.model.CoordinateRing ⧸ HopfAlgebra.augmentationIdeal E.quotient) →ₐ[R]
      A.model.CoordinateRing :=
  Ideal.Quotient.liftₐ _ E.inclusion.toAlgHom E.augmentationIdealLeKernel

/-- The augmentation quotient is canonically the specified kernel algebra. -/
def kernelEquiv (E : FiniteFlatExtension A H Q) :
    (H.model.CoordinateRing ⧸ HopfAlgebra.augmentationIdeal E.quotient) ≃ₐ[R]
      A.model.CoordinateRing := by
  let quotientAlgebra := E.quotient.toAlgHom.toRingHom.toAlgebra
  let quotientTower : IsScalarTower R Q.model.CoordinateRing H.model.CoordinateRing :=
    IsScalarTower.of_algebraMap_eq' E.quotient.toAlgHom.comp_algebraMap.symm
  let middleNontrivial : Nontrivial H.model.CoordinateRing :=
    (Bialgebra.counitAlgHom R H.model.CoordinateRing).toRingHom.domain_nontrivial
  let middleFree : Module.Free R H.model.CoordinateRing := inferInstance
  let middleFaithfullyFlat : Module.FaithfullyFlat R H.model.CoordinateRing := inferInstance
  let t := HopfAlgebra.torsorEquiv E.quotient (by ext; rfl)
  let m := Algebra.TensorProduct.map (AlgHom.id R H.model.CoordinateRing) E.kernelMap
  have hm (z : H.model.CoordinateRing ⊗[Q.model.CoordinateRing] H.model.CoordinateRing) :
      m (t z) = E.torsorEquiv z := by
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      rw [E.torsorEquiv_tmul]
      change m ((x ⊗ₜ[R] 1) * HopfAlgebra.torsorCoaction E.quotient y) = _
      rw [map_mul]
      have he : m (HopfAlgebra.torsorCoaction E.quotient y) =
          Algebra.TensorProduct.map (AlgHom.id R H.model.CoordinateRing)
            E.inclusion.toAlgHom (Coalgebra.comul y) := by
        change m (Algebra.TensorProduct.map (AlgHom.id R H.model.CoordinateRing)
          (Ideal.Quotient.mkₐ R _) (Coalgebra.comul y)) = _
        generalize Coalgebra.comul (R := R) y = c
        induction c using TensorProduct.inductionOn with
        | tmul a b => rfl
        | add a b ha hb => simp only [map_add, ha, hb]
      rw [he]
      simp [m]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hb : Function.Bijective m := by
    have he : (m : _ → _) = E.torsorEquiv ∘ t.symm := by
      funext z
      simpa only [Function.comp_apply, AlgEquiv.apply_symm_apply] using hm (t.symm z)
    rw [he]
    exact E.torsorEquiv.bijective.comp t.symm.bijective
  apply AlgEquiv.ofBijective E.kernelMap
  exact (Module.FaithfullyFlat.lTensor_bijective_iff_bijective R H.model.CoordinateRing
    E.kernelMap.toLinearMap).mp hb

/-- Kernel identification evaluates a quotient representative by the given inclusion. -/
@[simp] theorem kernelEquivMk (E : FiniteFlatExtension A H Q) (h : H.model.CoordinateRing) :
    E.kernelEquiv (Ideal.Quotient.mk (HopfAlgebra.augmentationIdeal E.quotient) h) =
      E.inclusion h := rfl

/-- The inclusion's ideal is exactly the augmentation ideal of the quotient. -/
theorem kernelIdealEqAugmentation (E : FiniteFlatExtension A H Q) :
    RingHom.ker E.inclusion.toAlgHom.toRingHom = HopfAlgebra.augmentationIdeal E.quotient := by
  ext h
  change E.inclusion h = 0 ↔ h ∈ HopfAlgebra.augmentationIdeal E.quotient
  rw [← E.kernelEquivMk h, EmbeddingLike.map_eq_zero_iff,
    Ideal.Quotient.eq_zero_iff_mem]

/-- Equations of the kernel vanish on every map annihilated by the quotient. -/
theorem kernelLeOfCompositionZero (E : FiniteFlatExtension A H Q) {J : FiniteFlatObject R}
    (f : J.Hom H)
    (hf : f.toAlgHom.comp E.quotient.toAlgHom =
      (Algebra.ofId R J.model.CoordinateRing).comp
        (Bialgebra.counitAlgHom R Q.model.CoordinateRing)) :
    RingHom.ker E.inclusion.toAlgHom.toRingHom ≤ RingHom.ker f.toAlgHom.toRingHom := by
  rw [E.kernelIdealEqAugmentation]
  apply Ideal.map_le_iff_le_comap.mpr
  intro q hq
  change f.toAlgHom (E.quotient.toAlgHom q) = 0
  have he := AlgHom.congr_fun hf q
  change Bialgebra.counitAlgHom R Q.model.CoordinateRing q = 0 at hq
  simpa only [AlgHom.comp_apply, Algebra.ofId_apply, hq, map_zero] using he

/-- A group map annihilated by the quotient factors through the actual integral kernel. -/
def liftKernel (E : FiniteFlatExtension A H Q) {J : FiniteFlatObject R}
    (f : J.Hom H)
    (hf : f.toAlgHom.comp E.quotient.toAlgHom =
      (Algebra.ofId R J.model.CoordinateRing).comp
        (Bialgebra.counitAlgHom R Q.model.CoordinateRing)) : J.Hom A := by
  let g := AlgHom.liftOfSurjective E.inclusion.toAlgHom E.inclusion_surjective
    f.toAlgHom (E.kernelLeOfCompositionZero f hf)
  exact BialgHom.factorOfSurjective E.inclusion E.inclusion_surjective f g
    (AlgHom.liftOfSurjective_comp _ _ _ _)

/-- Kernel factorization retains the prescribed map into the middle model. -/
theorem liftKernelComp (E : FiniteFlatExtension A H Q) {J : FiniteFlatObject R}
    (f : J.Hom H)
    (hf : f.toAlgHom.comp E.quotient.toAlgHom =
      (Algebra.ofId R J.model.CoordinateRing).comp
        (Bialgebra.counitAlgHom R Q.model.CoordinateRing)) :
    (E.liftKernel f hf).comp E.inclusion = f := by
  ext h
  change (AlgHom.liftOfSurjective E.inclusion.toAlgHom E.inclusion_surjective
    f.toAlgHom (E.kernelLeOfCompositionZero f hf)) (E.inclusion.toAlgHom h) = f.toAlgHom h
  exact AlgHom.liftOfSurjective_apply _ _ _ _ h

end ThreeAdicPlan.FiniteFlatExtension
