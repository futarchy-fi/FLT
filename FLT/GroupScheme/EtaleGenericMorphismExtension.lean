/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PadicBialgebraDescent
public import FLT.GroupScheme.RaynaudEtaleExtension

/-!
# Generic morphisms from étale integral models

Over an integrally closed base, a generic Hopf map whose target coordinate
algebra is étale extends uniquely to the integral coordinates. Geometrically
this extends every generic morphism from an étale finite-flat group scheme.
The result applies to any fraction field, not only to the three-adic base.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace ThreeAdicPlan

variable {R K : Type} [CommRing R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K]

/-- An integral generic coordinate map into an étale algebra extends uniquely
as a Hopf morphism. No rank or prime-power restriction is needed. -/
theorem existsUnique_bialgHom_of_etale
    (A B : Type) [CommRing A] [CommRing B] [Bialgebra R A] [Bialgebra R B]
    [Algebra.IsIntegral R A] [Algebra.Etale R B]
    (fK : K ⊗[R] A →ₐc[K] K ⊗[R] B) :
    ∃! f : A →ₐc[R] B, ∀ a, (1 : K) ⊗ₜ[R] f a = fK (1 ⊗ₜ[R] a) := by
  let j : B →ₐ[R] K ⊗[R] B := Algebra.TensorProduct.includeRight
  have hj : Function.Injective j :=
    Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective R K)
  let e := AlgEquiv.ofInjective j hj
  let g : A →ₐ[R] K ⊗[R] B :=
    (fK.toAlgHom.restrictScalars R).comp Algebra.TensorProduct.includeRight
  have hg (a : A) : g a ∈ j.range :=
    Algebra.TensorProduct.exists_includeRight_eq_of_isIntegral (g a)
      ((Algebra.IsIntegral.isIntegral a).map g)
  let g' : A →ₐ[R] j.range := g.codRestrict j.range hg
  let f : A →ₐ[R] B := e.symm.toAlgHom.comp g'
  have hf (a : A) : (1 : K) ⊗ₜ[R] f a = fK (1 ⊗ₜ[R] a) :=
    congrArg Subtype.val (e.apply_symm_apply (g' a))
  let F := bialgHomOfScalarExtension R K A B (IsFractionRing.injective R K) f fK hf
  refine ⟨F, hf, fun f' hf' ↦ ?_⟩
  ext a
  exact hj ((hf' a).trans (hf a).symm)

/-- Every generic Galois-equivariant morphism from an étale finite-flat model
over an integrally closed base extends uniquely to its specified integral model. -/
theorem extend_generic_morphism_of_etale [PerfectField K]
    (X Y : FF R K) [Algebra.Etale R X.CoordinateRing] (f : GenericGaloisHom X Y) :
    ∃! fO : ModelHom X Y, genericHom fO = f := by
  obtain ⟨fO, hfO, _⟩ := existsUnique_bialgHom_of_etale
    Y.CoordinateRing X.CoordinateRing f.toBialgHom
  have hbase : ModelHom.baseChange (X := X) (Y := Y) fO = f.toBialgHom := by
    ext z
    induction z using TensorProduct.inductionOn with
    | tmul k a =>
      change k ⊗ₜ[R] fO a = f.toBialgHom (k ⊗ₜ[R] a)
      rw [show k ⊗ₜ[R] a = k • ((1 : K) ⊗ₜ[R] a) by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul, ← hfO]
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy
  have hpoints : genericHom fO = f := by
    ext x
    obtain ⟨p, rfl⟩ := X.points_bijective.2 x
    rw [genericHom_points]
    rw [hbase]
    exact f.toBialgHom_points p
  exact ⟨fO, hpoints, fun g hg ↦ genericHom_injective X Y (hg.trans hpoints.symm)⟩

end ThreeAdicPlan
