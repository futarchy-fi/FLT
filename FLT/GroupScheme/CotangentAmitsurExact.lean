/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.CotangentAmitsurComparison
public import FLT.GroupScheme.AmitsurFaithfullyFlatExact

/-! # Correcting cochains for actual cotangent-valued Amitsur cocycles -/

@[expose] public noncomputable section
open TensorProduct Algebra.Amitsur
namespace AlgHom
variable {R A B S M : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing S]
  [Algebra R A] [Algebra R B] [Algebra R S] [Algebra B S] [IsScalarTower R B S]
  [Module.Free R A] [Module.Finite R A]
  [Module.FaithfullyFlat B S] [AddCommGroup M] [Module R M] [Module B M]
  [IsScalarTower R B M] (ε : A →ₐ[R] R)

/-- A cotangent cocycle has a cotangent cochain, without projectivity of the cotangent quotient. -/
theorem exists_cotangent_cocycle_correction
    (z : (RingHom.ker ε).Cotangent →ₗ[R] S ⊗[B] (S ⊗[B] M))
    (hz : ∀ a, d₁ B S M (z a) = 0) :
    ∃ w : (RingHom.ker ε).Cotangent →ₗ[R] S ⊗[B] M,
      ∀ a, d₀ B S M (w a) = z a := by
  let v := ε.cotangentDoubleTensorEquiv.symm z
  have hv : d₁ B S _ v = 0 := by
    apply ε.cotangentTripleTensorEquiv.injective
    ext a
    rw [cotangentTripleTensorEquiv_d₁, map_zero, LinearMap.zero_apply]
    change d₁ B S M ((ε.cotangentDoubleTensorEquiv
      (ε.cotangentDoubleTensorEquiv.symm z)) a) = 0
    rw [LinearEquiv.apply_symm_apply]
    exact hz a
  obtain ⟨u, hu⟩ := exists_cocycle_correction B S _ v hv
  refine ⟨ε.relativeFlatCotangentHomEquiv u, fun a ↦ ?_⟩
  rw [← cotangentDoubleTensorEquiv_d₀, hu]
  exact LinearMap.congr_fun (ε.cotangentDoubleTensorEquiv.apply_symm_apply z) a

end AlgHom
