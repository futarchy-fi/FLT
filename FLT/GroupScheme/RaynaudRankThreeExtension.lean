/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.GlobalModel
public import FLT.GroupScheme.RaynaudRigidity

/-!
# Extension of generic morphisms in Oort–Tate coordinates

Generic morphisms between three-adic models equipped with `OortTateThreeBasis`
extend uniquely. Integrality of the generic coordinate map makes the first
graph projection surjective, so its bialgebra inverse and the second projection
give the extension. No presentation of the graph closure is assumed.

This is a theorem about explicitly presented rank-three models. It does not
prove the existence of presentations for arbitrary rank-three models, or the
full Raynaud extension theorem for models killed by powers of three.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u
namespace ThreeAdicPlan

variable {R K : Type u} [CommRing R] [Field K] [Algebra R K] [PerfectField K]
  [IsDedekindDomain R] [IsFractionRing R K]

omit [PerfectField K] [IsDedekindDomain R] [IsFractionRing R K] in
/-- The identity integral morphism induces the identity on generic points. -/
@[simp] theorem genericHom_id (X : FF R K) (x : X.Points) :
    genericHom (BialgHom.id R X.CoordinateRing) x = x := by
  obtain ⟨p, rfl⟩ := X.points_bijective.2 x
  rw [genericHom_points]
  congr 1
  apply Additive.toMul.injective
  ext a
  rfl

/-- The two graph projections obey the original morphism on generic coordinate rings. -/
theorem GenericGaloisHom.graphSnd_baseChange {X Y : FF R K} (f : GenericGaloisHom X Y) :
    f.graphSnd.baseChange = f.graphFst.baseChange.comp f.toBialgHom := by
  ext a
  apply (GaloisModule.GenericFiber.genericEvalAlgEquiv K (AlgebraicClosure K)
    (K ⊗[R] f.graphClosure.CoordinateRing)).injective
  ext p
  have hs := genericHom_points f.graphSnd (Additive.ofMul p)
  have ht := f.toBialgHom_points
    (BialgHom.precompPoints f.graphFst.baseChange (Additive.ofMul p))
  have hf := genericHom_points f.graphFst (Additive.ofMul p)
  rw [f.genericHom_graphFst] at hf
  rw [f.genericHom_graphSnd] at hs
  rw [← hf] at ht
  exact AlgHom.congr_fun (congrArg Additive.toMul
    (Y.points_bijective.1 (hs.symm.trans ht.symm))) a

/-- If a generic coordinate has an integral preimage in the source, its second
graph projection lies in the image of the first projection. -/
theorem GenericGaloisHom.graphSnd_eq_graphFst {X Y : FF R K}
    (f : GenericGaloisHom X Y) (y : Y.CoordinateRing) (x : X.CoordinateRing)
    (h : f.toBialgHom (1 ⊗ₜ[R] y) = 1 ⊗ₜ[R] x) : f.graphSnd y = f.graphFst x := by
  apply Algebra.TensorProduct.includeRight_injective (A := K)
    (IsFractionRing.injective R K)
  change f.graphSnd.baseChange (1 ⊗ₜ[R] y) = f.graphFst.baseChange (1 ⊗ₜ[R] x)
  rw [f.graphSnd_baseChange, BialgHom.comp_apply, h]

/-- Integral values of every generic coordinate imply surjectivity of the first
graph projection. This is the purely algebraic end of the graph argument. -/
theorem GenericGaloisHom.graphFst_surjective_of_integral {X Y : FF R K}
    (f : GenericGaloisHom X Y)
    (hf : ∀ y : Y.CoordinateRing, ∃ x : X.CoordinateRing,
      f.toBialgHom (1 ⊗ₜ[R] y) = 1 ⊗ₜ[R] x) : Function.Surjective f.graphFst := by
  intro z
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective (I := f.graph.closureIdeal) z
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
    obtain ⟨w, hw⟩ := hf y
    refine ⟨x * w, ?_⟩
    rw [map_mul, ← f.graphSnd_eq_graphFst y w hw]
    simp only [GenericGaloisHom.graphFst, GenericGaloisHom.graphSnd, BialgHom.comp_apply,
      FF.fst, FF.snd, GaloisModule.tensorIncludeLeft, GaloisModule.tensorIncludeRight,
      BialgEquiv.toBialgHom_eq_coe, BialgEquiv.coe_coe]
    simp only [Bialgebra.TensorProduct.rid_symm_apply,
      Bialgebra.TensorProduct.lid_symm_apply, Bialgebra.TensorProduct.map_tmul,
      BialgHom.id_apply, map_one]
    change ((f.graph.closureInclusion f.graph_injective) (x ⊗ₜ[R] 1)) *
      ((f.graph.closureInclusion f.graph_injective) (1 ⊗ₜ[R] y)) = _
    rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rfl
  | add a b ha hb =>
    obtain ⟨x, hx⟩ := ha
    obtain ⟨y, hy⟩ := hb
    exact ⟨x + y, by simp only [map_add, hx, hy]⟩

/-- The first graph projection is surjective for models with Oort–Tate power bases. -/
theorem GenericGaloisHom.graphFst_surjective_of_oortTateThreeBasis
    {X Y : FF ℤ_[3] ℚ_[3]} (f : GenericGaloisHom X Y)
    (P : OortTateThreeBasis ℤ_[3] X.CoordinateRing)
    (Q : OortTateThreeBasis ℤ_[3] Y.CoordinateRing) : Function.Surjective f.graphFst :=
  f.graphFst_surjective_of_integral (Q.generic_map_integral P f.toBialgHom)

/-- Generic morphisms between explicitly presented rank-three three-adic models
extend uniquely. The unrestricted Raynaud theorem still requires classification
and higher-rank rigidity. -/
theorem raynaud_extend_generic_morphism_of_oortTateThreeBasis
    (X Y : FF ℤ_[3] ℚ_[3])
    (P : OortTateThreeBasis ℤ_[3] X.CoordinateRing)
    (Q : OortTateThreeBasis ℤ_[3] Y.CoordinateRing) (f : GenericGaloisHom X Y) :
    ∃! fO : ModelHom X Y, genericHom fO = f := by
  let e := BialgEquiv.ofBijective f.graphFst
    ⟨f.graphFst_injective, f.graphFst_surjective_of_oortTateThreeBasis P Q⟩
  let g : ModelHom X f.graphClosure := e.symm.toBialgHom
  have hg : ∀ x : X.Points, genericHom g x = x := by
    have he : g.comp f.graphFst = BialgHom.id ℤ_[3] X.CoordinateRing := by
      ext a
      exact e.symm_apply_apply a
    intro x
    have h := congrArg (fun a : ModelHom X X ↦ genericHom a x) he
    rw [genericHom_comp] at h
    simpa using h
  let fO : ModelHom X Y := g.comp f.graphSnd
  have hO : genericHom fO = f := by
    ext x
    change genericHom (g.comp f.graphSnd) x = f x
    rw [genericHom_comp, f.genericHom_graphSnd, hg]
  exact ⟨fO, hO, fun gO hgO ↦
    raynaud_extend_generic_morphism_unique X Y f gO fO hgO hO⟩

/-- It suffices to find odd power bases for the two models. The cubic equation,
the comultiplication formula, and the parameter relation follow from the Hopf laws. -/
theorem raynaud_extend_generic_morphism_of_odd_power_basis
    (X Y : FF ℤ_[3] ℚ_[3])
    (x : X.CoordinateRing) (y : Y.CoordinateRing)
    (bX : Module.Basis (Fin 3) ℤ_[3] X.CoordinateRing)
    (bY : Module.Basis (Fin 3) ℤ_[3] Y.CoordinateRing)
    (hX0 : bX 0 = 1) (hX1 : bX 1 = x) (hX2 : bX 2 = x ^ 2)
    (hY0 : bY 0 = 1) (hY1 : bY 1 = y) (hY2 : bY 2 = y ^ 2)
    (hSX : HopfAlgebra.antipode ℤ_[3] x = -x)
    (hSY : HopfAlgebra.antipode ℤ_[3] y = -y) (f : GenericGaloisHom X Y) :
    ∃! fO : ModelHom X Y, genericHom fO = f := by
  let : Coalgebra.IsCocomm ℤ_[3] X.CoordinateRing :=
    cocomm_of_injective_points X.points.toAddMonoidHom X.points_bijective.1
  let : Coalgebra.IsCocomm ℤ_[3] Y.CoordinateRing :=
    cocomm_of_injective_points Y.points.toAddMonoidHom Y.points_bijective.1
  exact raynaud_extend_generic_morphism_of_oortTateThreeBasis X Y
    (OortTateThreeBasis.ofOddPowerBasis x bX hX0 hX1 hX2 hSX)
    (OortTateThreeBasis.ofOddPowerBasis y bY hY0 hY1 hY2 hSY) f

end ThreeAdicPlan
