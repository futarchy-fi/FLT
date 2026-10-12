/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianMorphismLocalQuotient
public import FLT.Mazur.GrassmannianNumeratorTransport

/-!
# Clearing denominators between recovered original chart relations

Compatibility is used on an actual iterated principal localization. A numerator
in one recovered relation belongs to every other one after multiplication by a
power of the first coefficient. No reducedness or flatness of the base is needed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R A M κ : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Fintype κ] {d : ℕ}
variable (f : Spec (.of A) ⟶ ambientGrassmannianScheme R M κ d)
  (hf : f ≫ ambientGrassmannianStructure R M κ d = Spec.algebraMap R A)

/-- The global numerators satisfying one recovered original chart relation. -/
def ambientMorphismContraction (q : AmbientMorphismCoverIndex f) :
    Submodule A (A ⊗[R] M) :=
  Submodule.comap
    (AlgebraTensorModule.rTensor R M (Algebra.linearMap A (Localization.Away q.2.val)))
    ((ambientMorphismLocalPoint f hf q).val.toSubmodule.restrictScalars A)

/-- Overlap compatibility clears a power of the first coefficient in the second relation. -/
theorem ambientMorphismContraction_clear (p q : AmbientMorphismCoverIndex f)
    (x : A ⊗[R] M) (hx : x ∈ ambientMorphismContraction f hf p) :
    ∃ n : ℕ, p.2.val ^ n • x ∈ ambientMorphismContraction f hf q := by
  let B := Localization.Away q.2.val
  let r : B := algebraMap A B p.2.val
  let C := Localization.Away r
  have hu : IsUnit (algebraMap A C p.2.val) := by
    rw [IsScalarTower.algebraMap_apply A B C]
    exact IsLocalization.Away.algebraMap_isUnit r
  let s : Localization.Away p.2.val →ₐ[R] C :=
    IsLocalization.Away.liftAlgHom (A := R) p.2.val
      (f := IsScalarTower.toAlgHom R A C) hu
  let t := IsScalarTower.toAlgHom R B C
  have hs (a : A) : s (algebraMap A (Localization.Away p.2.val) a) =
      algebraMap A C a := IsLocalization.Away.lift_eq p.2.val hu a
  have hc := ambientMorphismLocalPoint_compatible f hf p q s t (by
    apply AlgHom.ext
    intro a
    exact (hs a).trans (IsScalarTower.algebraMap_apply A B C a))
  have he (y : A ⊗[R] M) :
      s.toLinearMap.rTensor M
        (AlgebraTensorModule.rTensor R M
          (Algebra.linearMap A (Localization.Away p.2.val)) y) =
      AlgebraTensorModule.rTensor R M (Algebra.linearMap B C)
        (AlgebraTensorModule.rTensor R M (Algebra.linearMap A B) y) := by
    induction y using TensorProduct.inductionOn with
    | tmul a m =>
      simp only [AlgebraTensorModule.rTensor_tmul, Algebra.linearMap_apply,
        LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, hs,
        IsScalarTower.algebraMap_apply A B C]
    | add y z hy hz => simp only [map_add, hy, hz]
  have hxC := grassmannian_map_numerator_mem s (ambientMorphismLocalPoint f hf p).val
    (AlgebraTensorModule.rTensor R M
      (Algebra.linearMap A (Localization.Away p.2.val)) x) hx
  rw [hc, he] at hxC
  obtain ⟨n, hn⟩ := (grassmannian_localized_numerator_iff
    (ambientMorphismLocalPoint f hf q).val r
    (AlgebraTensorModule.rTensor R M (Algebra.linearMap A B) x)).mp hxC
  refine ⟨n, ?_⟩
  change AlgebraTensorModule.rTensor R M (Algebra.linearMap A B)
    (p.2.val ^ n • x) ∈ (ambientMorphismLocalPoint f hf q).val.toSubmodule
  rw [map_smul, ← algebraMap_smul B, map_pow]
  exact hn

end FLT.Mazur.GrassmannianChart
