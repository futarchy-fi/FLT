/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.BialgebraBaseChange
public import FLT.GroupScheme.FiniteFlatSubobject
public import FLT.GroupScheme.KummerPoints

/-!
# Finite-flat subquotients after changing the integral base

Use a common algebraic closure throughout. Scalar extension retains the underlying
point group, and schematic closure followed by quotient constructs its subquotients.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace GaloisModule

variable {R S K L Ω X : Type} [CommRing R] [CommRing S] [Field K] [Field L] [Field Ω]
  [Algebra R K] [Algebra R S] [Algebra K L] [Algebra S L] [Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R S L]
  [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
  [AddCommGroup X] [DistribMulAction (Ω ≃ₐ[K] Ω) X]

/-- Restriction changes only the acting Galois group, using the same closure. -/
def RestrictedPoints (_K _L _Ω X : Type) := X

instance : AddCommGroup (RestrictedPoints K L Ω X) := inferInstanceAs (AddCommGroup X)
instance : DistribMulAction (Ω ≃ₐ[L] Ω) (RestrictedPoints K L Ω X) :=
  DistribMulAction.compHom X (AlgEquiv.restrictScalarsHom K)

instance {k : Type} [Semiring k] [Module k X] :
    Module k (RestrictedPoints K L Ω X) := inferInstanceAs (Module k X)

/-- Restriction does not extend the coefficient field or change the dimension. -/
theorem finrank_restrictedPoints {K L Ω X : Type} [AddCommGroup X]
    (k : Type) [DivisionRing k] [Module k X] :
    Module.finrank k (RestrictedPoints K L Ω X) = Module.finrank k X := rfl

/-- Tensoring the original integral model supplies a model after base change;
the point comparison restricts to the original coordinates. -/
theorem IsFiniteFlat.baseChange_sameClosure (hX : IsFiniteFlat R K Ω X) :
    IsFiniteFlat S L Ω (RestrictedPoints K L Ω X) := by
  let : Algebra R Ω := (algebraMap K Ω).comp (algebraMap R K) |>.toAlgebra
  let : IsScalarTower R K Ω := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  let : IsScalarTower R L Ω := IsScalarTower.to₁₃₄ R K L Ω
  rcases hX with ⟨H, _, _, _, _, f, hf⟩
  let A := S ⊗[R] H
  let : HopfAlgebra.IsFiniteFlat S A := ⟨⟩
  let e : L ⊗[S] A ≃ₐc[L] L ⊗[K] (K ⊗[R] H) :=
    (ThreeAdicPlan.bialgebraCancelBaseChange R S L H).trans
      (ThreeAdicPlan.bialgebraCancelBaseChange R K L H).symm
  let : Algebra.Etale L (L ⊗[S] A) := Algebra.Etale.of_equiv e.symm.toAlgEquiv
  let a : Additive (L ⊗[S] A →ₐ[L] Ω) ≃ Additive (K ⊗[R] H →ₐ[K] Ω) :=
    (show (L ⊗[S] A →ₐ[L] Ω) ≃ (L ⊗[K] (K ⊗[R] H) →ₐ[L] Ω) from
      { toFun := fun p ↦ p.comp e.symm.toAlgEquiv.toAlgHom
        invFun := fun p ↦ p.comp e.toAlgEquiv.toAlgHom
        left_inv := fun p ↦ by ext; simp
        right_inv := fun p ↦ by ext; simp }).trans
      (Bialgebra.restrictPoints K L Ω (K ⊗[R] H))
  let g : Additive (L ⊗[S] A →ₐ[L] Ω) →+[Ω ≃ₐ[L] Ω]
      RestrictedPoints K L Ω X :=
    { toFun := fun p ↦ f (a p)
      map_zero' := by
        change f (a 0) = 0
        have hz : a 0 = 0 := by
          apply Additive.toMul.injective
          apply AlgHom.ext
          intro x
          change algebraMap L Ω (Coalgebra.counit (R := L) (e.symm (1 ⊗ₜ[K] x))) = _
          rw [CoalgHomClass.counit_comp_apply]
          simp only [TensorProduct.counit_tmul, Algebra.smul_def, Bialgebra.counit_one, mul_one]
          exact (IsScalarTower.algebraMap_apply K L Ω _).symm
        rw [hz, map_zero]
      map_add' := by
        intro p q
        have ha : a (p + q) = a p + a q := by
          change Bialgebra.restrictPoints K L Ω (K ⊗[R] H)
            ((BialgHom.precompPoints e.symm.toBialgHom) (p + q)).toMul = _
          rw [map_add]
          exact Bialgebra.restrictPoints_mul K L Ω (K ⊗[R] H) _ _
        exact (congrArg f ha).trans (f.map_add _ _)
      map_smul' := fun σ p ↦ by
        change f (a (σ • p)) = (σ.restrictScalars K) • f (a p)
        exact f.map_smul (σ.restrictScalars K) (a p) }
  exact ⟨A, inferInstance, inferInstance, inferInstance, inferInstance,
    g, hf.comp a.bijective⟩

/-- An embedded submodule followed by an equivariant quotient has an actual
finite-flat model over the extended integral base. -/
theorem IsFiniteFlat.subquotient_baseChange [IsDedekindDomain S] [IsFractionRing S L]
    [IsGalois L Ω] [IsSepClosed Ω]
    {U W : Type} [AddCommGroup U] [AddCommGroup W]
    [DistribMulAction (Ω ≃ₐ[L] Ω) U] [DistribMulAction (Ω ≃ₐ[L] Ω) W]
    (hX : IsFiniteFlat R K Ω X)
    (i : U →+[Ω ≃ₐ[L] Ω] RestrictedPoints K L Ω X)
    (q : U →+[Ω ≃ₐ[L] Ω] W) (hi : Function.Injective i) (hq : Function.Surjective q) :
    IsFiniteFlat S L Ω W :=
  ((hX.baseChange_sameClosure (S := S) (L := L)).subobject S L Ω _ i hi).quotient
    S L Ω U q hq

end GaloisModule
