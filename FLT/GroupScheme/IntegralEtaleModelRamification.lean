/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.Unramified
public import FLT.GroupScheme.IntegralCoordinateAlgebra
public import Mathlib.NumberTheory.RamificationInertia.Unramified

/-!
# The unramified splitting field of a finite Galois module

The kernel of the action defines a finite Galois extension. The local inertia
condition on the module implies arithmetic unramifiedness of this extension.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ThreeAdicPlan.FiniteContinuousGaloisModule

variable (W : FiniteContinuousGaloisModule)

/-- The subgroup acting trivially on the entire finite module. -/
def actionKernel : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
  (MulAction.toPermHom (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) W).ker

/-- Membership in the action kernel is pointwise triviality. -/
@[simp] theorem mem_actionKernel (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    σ ∈ W.actionKernel ↔ ∀ w : W, σ • w = w := by
  change MulAction.toPermHom _ W σ = 1 ↔ _
  exact Equiv.ext_iff

instance actionKernelNormal : W.actionKernel.Normal := MonoidHom.normal_ker _

/-- Continuity and finiteness make the kernel open. -/
theorem actionKernel_isOpen :
    IsOpen (W.actionKernel : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) := by
  have he : (W.actionKernel : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) =
      ⋂ w : W, {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ | σ • w = w} := by
    ext σ
    simp
  rw [he]
  exact isOpen_iInter_of_finite fun w ↦ ContinuousSMulDiscrete.isOpen_smul_eq _ w w

/-- The finite Galois extension cut out by the action. -/
def actionField : IntermediateField ℚ (AlgebraicClosure ℚ) :=
  IntermediateField.fixedField W.actionKernel

/-- The action kernel is exactly the subgroup fixing the action field. -/
theorem actionField_fixingSubgroup : W.actionField.fixingSubgroup = W.actionKernel :=
  InfiniteGalois.fixingSubgroup_fixedField
    ⟨W.actionKernel, W.actionKernel.isClosed_of_isOpen W.actionKernel_isOpen⟩

instance actionFieldFinite : FiniteDimensional ℚ W.actionField := by
  apply (InfiniteGalois.isOpen_iff_finite W.actionField).mp
  rw [W.actionField_fixingSubgroup]
  exact W.actionKernel_isOpen

instance actionFieldGalois : IsGalois ℚ W.actionField := by
  apply (InfiniteGalois.normal_iff_isGalois W.actionField).mp
  rw [W.actionField_fixingSubgroup]
  infer_instance

/-- Every value of an equivariant generic coordinate lies in the action field. -/
theorem genericCoordinate_mem_actionField (a : W.GenericCoordinateAlgebra) (w : W) :
    a w ∈ W.actionField := by
  rw [actionField, IntermediateField.mem_fixedField_iff]
  intro σ hσ
  change σ • a w = a w
  rw [← map_smul, (W.mem_actionKernel σ).mp hσ w]

/-- Each field quotient of the generic coordinate algebra embeds in the action field. -/
def fieldFactorEmbedding (F : Type) [Field F] [Algebra ℚ F]
    (f : W.GenericCoordinateAlgebra →ₐ[ℚ] F) (hf : Function.Surjective f) :
    F →ₐ[ℚ] W.actionField := by
  letI : Module.Finite ℚ F := Module.Finite.of_surjective f.toLinearMap hf
  let e : F →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  refine e.codRestrict W.actionField.toSubalgebra ?_
  intro x
  obtain ⟨a, rfl⟩ := hf x
  obtain ⟨w, hw⟩ :=
    (InfiniteGalois.evalAlgHom_bijective ℚ (AlgebraicClosure ℚ) W).2 (e.comp f)
  have he : e (f a) = a w := (AlgHom.congr_fun hw a).symm
  rw [he]
  exact W.genericCoordinate_mem_actionField a w

/-- Outside the exceptional set, local inertia restricts trivially to the action field. -/
theorem localInertia_le_actionFieldKer {S : Finset ℕ} (h : UnramifiedOutside S W)
    (p : ℕ) (hp : p.Prime) (hpS : p ∉ S) :
    localInertiaGroup hp.toHeightOneSpectrumRingOfIntegersRat ≤
      (NumberField.InertiaComparison.localRestriction
        hp.toHeightOneSpectrumRingOfIntegersRat W.actionField).ker := by
  intro σ hσ
  rw [MonoidHom.mem_ker, NumberField.InertiaComparison.localRestriction, MonoidHom.comp_apply]
  rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker,
    W.actionField_fixingSubgroup, W.mem_actionKernel]
  intro w
  convert h.inertia_trivial p hp hpS σ hσ w using 1
  congr 4
  exact Subsingleton.elim _ _

/-- The action field is arithmetically unramified at each prime outside the exceptional set. -/
theorem actionField_isUnramifiedIn {S : Finset ℕ} (h : UnramifiedOutside S W)
    (p : ℕ) (hp : p.Prime) (hpS : p ∉ S) :
    Algebra.IsUnramifiedIn (NumberField.RingOfIntegers W.actionField)
      hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal :=
  NumberField.InertiaComparison.isUnramifiedIn_of_localInertia_le_ker
    hp.toHeightOneSpectrumRingOfIntegersRat W.actionField
    (W.localInertia_le_actionFieldKer h p hp hpS)

/-- Each field factor has unramified ring of integers away from the exceptional primes. -/
theorem fieldFactor_isUnramifiedIn (F : Type) [Field F] [Algebra ℚ F]
    (f : W.GenericCoordinateAlgebra →ₐ[ℚ] F) (hf : Function.Surjective f)
    {S : Finset ℕ} (h : UnramifiedOutside S W) (p : ℕ) (hp : p.Prime) (hpS : p ∉ S) :
    Algebra.IsUnramifiedIn (NumberField.RingOfIntegers F)
      hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal := by
  let : Module.Finite ℚ F := Module.Finite.of_surjective f.toLinearMap hf
  let : NumberField F := NumberField.of_module_finite ℚ F
  let e := W.fieldFactorEmbedding F f hf
  let : Algebra F W.actionField := e.toAlgebra
  let : IsScalarTower ℚ F W.actionField :=
    IsScalarTower.of_algebraMap_eq' e.comp_algebraMap.symm
  intro P hP hPv
  obtain ⟨Q, hQ⟩ := (inferInstance : Nonempty
    (Ideal.primesOver P (NumberField.RingOfIntegers W.actionField)))
  let : Q.IsPrime := hQ.1
  let : Q.LiesOver P := hQ.2
  let : Q.LiesOver hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal :=
    Ideal.LiesOver.trans Q P _
  let : Algebra.IsUnramifiedAt (NumberField.RingOfIntegers ℚ) Q :=
    W.actionField_isUnramifiedIn h p hp hpS Q inferInstance inferInstance
  exact Algebra.IsUnramifiedAt.of_liesOver (NumberField.RingOfIntegers ℚ) P Q

end ThreeAdicPlan.FiniteContinuousGaloisModule
