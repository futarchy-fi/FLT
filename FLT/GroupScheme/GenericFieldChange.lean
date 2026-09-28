/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.GlobalModel

/-!
# Changing the field of a generic coordinate algebra

Restriction of a finite continuous Galois module uses the chosen embedding of
algebraic closures. Applying that same embedding to equivariant functions
constructs the comparison with scalar extension of its coordinate algebra.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct

namespace ThreeAdicPlan.FiniteContinuousGaloisModule

variable {K L : Type} [Field K] [Field L] [PerfectField K] [PerfectField L]
    [Algebra K L] (W : FiniteContinuousGaloisModule K)

/-- Apply the chosen closure embedding to an equivariant function. Its equivariance
uses exactly the absolute-Galois restriction defining `W.restrict`. -/
def genericRestrictionAlgHom : W.GenericCoordinateAlgebra →ₐ[K]
    (W.restrict (algebraMap K L)).GenericCoordinateAlgebra where
  toFun f :=
    { toFun := fun w ↦ AlgebraicClosure.map (algebraMap K L) (f w)
      map_smul' := by
        intro σ w
        change AlgebraicClosure.map (algebraMap K L)
          (f ((show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from
            Field.absoluteGaloisGroup.map (algebraMap K L) σ) • (show W from w))) = _
        rw [f.map_smul]
        exact Field.absoluteGaloisGroup.lift_map _ σ (f w) }
  map_one' := by ext; exact map_one (AlgebraicClosure.map (algebraMap K L))
  map_mul' f g := by ext w; exact map_mul (AlgebraicClosure.map (algebraMap K L)) (f w) (g w)
  map_zero' := by ext; exact map_zero (AlgebraicClosure.map (algebraMap K L))
  map_add' f g := by ext w; exact map_add (AlgebraicClosure.map (algebraMap K L)) (f w) (g w)
  commutes' r := by
    ext w
    exact AlgebraicClosure.map_algebraMap (algebraMap K L) r

instance : IsScalarTower K L (W.restrict (algebraMap K L)).GenericCoordinateAlgebra := by
  apply IsScalarTower.of_algebraMap_eq
  intro r
  ext w
  exact IsScalarTower.algebraMap_apply K L (AlgebraicClosure L) r

/-- The natural scalar-extension comparison for generic coordinate algebras. -/
def genericFieldChangeAlgHom : L ⊗[K] W.GenericCoordinateAlgebra →ₐ[L]
    (W.restrict (algebraMap K L)).GenericCoordinateAlgebra :=
  Algebra.TensorProduct.liftEquivRight K L _ _ (W.genericRestrictionAlgHom (L := L))

omit [PerfectField K] [PerfectField L] in
@[simp] theorem genericFieldChangeAlgHom_tmul (r : L) (f : W.GenericCoordinateAlgebra)
    (w : W) :
    W.genericFieldChangeAlgHom (r ⊗ₜ[K] f) w =
      algebraMap L (AlgebraicClosure L) r * AlgebraicClosure.map (algebraMap K L) (f w) := rfl

omit [PerfectField L] in
/-- Evaluation after field change still separates the original finite Galois module. -/
theorem genericFieldChange_eval_injective : Function.Injective
    (fun w : W ↦ (MulActionHom.evalAlgHom (AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L)
      L (W.restrict (algebraMap K L)) (AlgebraicClosure L) w).comp
        (W.genericFieldChangeAlgHom (L := L))) := by
  intro x y h
  apply (InfiniteGalois.evalAlgHom_bijective K (AlgebraicClosure K) W).1
  ext f
  change f x = f y
  apply (AlgebraicClosure.map (algebraMap K L)).injective
  have hh := AlgHom.congr_fun h (1 ⊗ₜ[K] f)
  change W.genericFieldChangeAlgHom ((1 : L) ⊗ₜ[K] f) x =
    W.genericFieldChangeAlgHom ((1 : L) ⊗ₜ[K] f) y at hh
  simpa only [genericFieldChangeAlgHom_tmul, map_one, one_mul] using hh

omit [PerfectField L] in
/-- Every geometric point of the scalar extension is evaluation at a unique element. -/
theorem genericFieldChange_eval_bijective : Function.Bijective
    (fun w : W ↦ (MulActionHom.evalAlgHom (AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L)
      L (W.restrict (algebraMap K L)) (AlgebraicClosure L) w).comp
        (W.genericFieldChangeAlgHom (L := L))) := by
  apply Function.Injective.bijective_of_nat_card_le (W.genericFieldChange_eval_injective)
  rw [← GaloisModule.finrank_eq_natCard_algHom L (AlgebraicClosure L),
    Module.finrank_baseChange,
    GaloisModule.finrank_equivariantFunctions K (AlgebraicClosure K) W]

/-- The natural comparison is bijective: geometric points detect injectivity, and
both coordinate algebras have dimension equal to the cardinality of `W`. -/
theorem genericFieldChangeAlgHom_bijective :
    Function.Bijective (W.genericFieldChangeAlgHom (L := L)) := by
  have hinj : Function.Injective (W.genericFieldChangeAlgHom (L := L)) := by
    intro a b h
    apply (InfiniteGalois.evalMulActionHom_bijective_of_isSepClosed
      L (AlgebraicClosure L) (L ⊗[K] W.GenericCoordinateAlgebra)).1
    ext p
    obtain ⟨w, rfl⟩ := W.genericFieldChange_eval_bijective.2 p
    exact congrArg (fun f ↦ f w) h
  have hrank : Module.finrank L (L ⊗[K] W.GenericCoordinateAlgebra) =
      Module.finrank L (W.restrict (algebraMap K L)).GenericCoordinateAlgebra := by
    rw [Module.finrank_baseChange,
      GaloisModule.finrank_equivariantFunctions K (AlgebraicClosure K) W,
      GaloisModule.finrank_equivariantFunctions L (AlgebraicClosure L)]
    rfl
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank
    (f := (W.genericFieldChangeAlgHom (L := L)).toLinearMap)).mp hinj⟩

/-- Scalar extension of the generic coordinate algebra agrees with restriction of
its Galois module, using the specified embedding of algebraic closures. -/
def genericFieldChangeAlgEquiv : L ⊗[K] W.GenericCoordinateAlgebra ≃ₐ[L]
    (W.restrict (algebraMap K L)).GenericCoordinateAlgebra :=
  AlgEquiv.ofBijective W.genericFieldChangeAlgHom W.genericFieldChangeAlgHom_bijective


/-- Tensoring the comparison twice applies the same closure embedding to the
function of two variables. -/
theorem genericFieldChange_tensor_eval
    (z : W.GenericCoordinateAlgebra ⊗[K] W.GenericCoordinateAlgebra) (x y : W) :
    GaloisModule.tensorEquiv L (AlgebraicClosure L)
      (W.restrict (algebraMap K L)) (W.restrict (algebraMap K L))
      (Algebra.TensorProduct.map W.genericFieldChangeAlgHom W.genericFieldChangeAlgHom
        ((HopfAlgebra.IntegralClosure.baseChangeTensorEquiv K L
          W.GenericCoordinateAlgebra W.GenericCoordinateAlgebra).symm (1 ⊗ₜ[K] z))) (x, y) =
    AlgebraicClosure.map (algebraMap K L)
      (GaloisModule.tensorEquiv K (AlgebraicClosure K) W W z (x, y)) := by
  induction z using TensorProduct.inductionOn with
  | tmul f g =>
    simp [HopfAlgebra.IntegralClosure.baseChangeTensorEquiv,
      genericFieldChangeAlgHom_tmul]
  | add a b ha hb =>
    simp only [TensorProduct.tmul_add, map_add]
    change _ + _ = AlgebraicClosure.map (algebraMap K L) (_ + _)
    rw [map_add]
    exact congrArg₂ (· + ·) ha hb

set_option maxHeartbeats 800000 in
-- Comparing comultiplications unfolds the two generic Hopf structures.
/-- Restriction of Galois modules commutes with scalar extension as bialgebras. -/
def genericFieldChangeBialgEquiv : L ⊗[K] W.GenericCoordinateAlgebra ≃ₐc[L]
    (W.restrict (algebraMap K L)).GenericCoordinateAlgebra := by
  refine BialgEquiv.ofAlgEquiv W.genericFieldChangeAlgEquiv ?_ ?_
  · apply Algebra.TensorProduct.ext_ring
    ext f
    change Bialgebra.counitAlgHom L _ (W.genericFieldChangeAlgHom ((1 : L) ⊗ₜ[K] f)) =
      Coalgebra.counit (R := L) (1 ⊗ₜ[K] f : L ⊗[K] W.GenericCoordinateAlgebra)
    apply (algebraMap L (AlgebraicClosure L)).injective
    rw [TensorProduct.counit_tmul, CommSemiring.counit_apply]
    change algebraMap L (AlgebraicClosure L)
        (GaloisModule.GenericFiber.counitAlgHom L (AlgebraicClosure L)
          (W.restrict (algebraMap K L)) (W.genericFieldChangeAlgHom ((1 : L) ⊗ₜ[K] f))) = _
    rw [GaloisModule.GenericFiber.algebraMap_counitAlgHom, genericFieldChangeAlgHom_tmul,
      map_one, one_mul, Algebra.smul_def, mul_one]
    rw [← AlgebraicClosure.map_algebraMap]
    congr 1
    exact (GaloisModule.GenericFiber.algebraMap_counitAlgHom K (AlgebraicClosure K) W f).symm
  · apply Algebra.TensorProduct.ext_ring
    ext f
    change Algebra.TensorProduct.map W.genericFieldChangeAlgHom W.genericFieldChangeAlgHom
      (Coalgebra.comul (R := L) (1 ⊗ₜ[K] f : L ⊗[K] W.GenericCoordinateAlgebra)) =
      Coalgebra.comul (R := L) (W.genericFieldChangeAlgHom ((1 : L) ⊗ₜ[K] f))
    have he := HopfAlgebra.IntegralClosure.baseChange_comul_includeRight K L
      W.GenericCoordinateAlgebra f
    simp only [Algebra.TensorProduct.includeRight_apply] at he
    rw [← (HopfAlgebra.IntegralClosure.baseChangeTensorEquiv K L
      W.GenericCoordinateAlgebra W.GenericCoordinateAlgebra).symm_apply_apply
        (Coalgebra.comul (R := L) (1 ⊗ₜ[K] f : L ⊗[K] W.GenericCoordinateAlgebra)), he]
    apply (GaloisModule.tensorEquiv L (AlgebraicClosure L)
      (W.restrict (algebraMap K L)) (W.restrict (algebraMap K L))).injective
    ext ⟨x, y⟩
    rw [W.genericFieldChange_tensor_eval (L := L)]
    change AlgebraicClosure.map (algebraMap K L)
      (GaloisModule.tensorEquiv K (AlgebraicClosure K) W W
        (GaloisModule.GenericFiber.comulAlgHom K (AlgebraicClosure K) W f) (x, y)) =
      GaloisModule.tensorEquiv L (AlgebraicClosure L)
        (W.restrict (algebraMap K L)) (W.restrict (algebraMap K L))
        (GaloisModule.GenericFiber.comulAlgHom L (AlgebraicClosure L)
          (W.restrict (algebraMap K L)) (W.genericFieldChangeAlgHom ((1 : L) ⊗ₜ[K] f))) (x, y)
    rw [GaloisModule.GenericFiber.comulAlgHom_eval,
      GaloisModule.GenericFiber.comulAlgHom_eval, genericFieldChangeAlgHom_tmul,
      map_one, one_mul]

@[simp] theorem genericFieldChangeBialgEquiv_tmul (r : L)
    (f : W.GenericCoordinateAlgebra) (w : W) :
    W.genericFieldChangeBialgEquiv (L := L) (r ⊗ₜ[K] f) w =
      algebraMap L (AlgebraicClosure L) r * AlgebraicClosure.map (algebraMap K L) (f w) :=
  W.genericFieldChangeAlgHom_tmul r f w

/-- The comparison over `ℚ₃` required to put the global and local models in a
common generic bialgebra. -/
def localAtThreeGenericBialgEquiv (W : FiniteContinuousGaloisModule) :
    ℚ_[3] ⊗[ℚ] W.GenericCoordinateAlgebra ≃ₐc[ℚ_[3]]
      W.localAtThree.GenericCoordinateAlgebra := W.genericFieldChangeBialgEquiv

/-- Evaluation of the local comparison uses precisely the closure embedding
chosen for the absolute-Galois restriction. -/
@[simp] theorem localAtThreeGenericBialgEquiv_tmul (W : FiniteContinuousGaloisModule)
    (r : ℚ_[3]) (f : W.GenericCoordinateAlgebra) (w : W) :
    W.localAtThreeGenericBialgEquiv (r ⊗ₜ[ℚ] f) w =
      algebraMap ℚ_[3] (AlgebraicClosure ℚ_[3]) r *
        AlgebraicClosure.map (algebraMap ℚ ℚ_[3]) (f w) :=
  W.genericFieldChangeBialgEquiv_tmul r f w

/-- The global generic algebra and any chosen finite-flat model at three have
explicitly identified local generic fibres. -/
def localModelGenericBialgEquiv (W : FiniteContinuousGaloisModule)
    (M : HasFiniteFlatModel ℤ_[3] W.localAtThree) :
    ℚ_[3] ⊗[ℚ] W.GenericCoordinateAlgebra ≃ₐc[ℚ_[3]] ℚ_[3] ⊗[ℤ_[3]] M.CoordinateRing :=
  W.localAtThreeGenericBialgEquiv.trans M.genericBialgEquiv

end ThreeAdicPlan.FiniteContinuousGaloisModule

