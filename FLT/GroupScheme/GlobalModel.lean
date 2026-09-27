/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup
public import FLT.GroupScheme.EtaleOrder
public import FLT.GroupScheme.FiniteFlat
public import FLT.GroupScheme.KummerPoints
public import FLT.Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Global finite-flat model data

The records in this file retain a coordinate Hopf algebra and the comparison with its
geometric generic fibre. They do not include global existence or classification assertions.
The finite étale algebra of equivariant functions is constructed over the fraction field;
extending it over a ring of integers is a separate arithmetic problem.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace ThreeAdicPlan

/-- A finite abelian group with continuous discrete action of the absolute Galois group of
`K`. The default field is `ℚ`; allowing another field also describes local restrictions. -/
structure FiniteContinuousGaloisModule (K : Type := ℚ) [Field K] where
  /-- The underlying finite abelian group. -/
  Carrier : Type
  [addCommGroup : AddCommGroup Carrier]
  [finite : Finite Carrier]
  [action : DistribMulAction (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) Carrier]
  [continuous : ContinuousSMulDiscrete
    (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) Carrier]

attribute [instance] FiniteContinuousGaloisModule.addCommGroup
  FiniteContinuousGaloisModule.finite FiniteContinuousGaloisModule.action
  FiniteContinuousGaloisModule.continuous

instance {K : Type} [Field K] : CoeSort (FiniteContinuousGaloisModule K) Type :=
  ⟨FiniteContinuousGaloisModule.Carrier⟩

namespace FiniteContinuousGaloisModule

/-- Restriction along the continuous absolute-Galois map induced by a field embedding.
The underlying abelian group is unchanged. -/
def restrict {K L : Type} [Field K] [Field L]
    (W : FiniteContinuousGaloisModule K) (f : K →+* L) :
    FiniteContinuousGaloisModule L := by
  let φ : (AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L) →ₜ*
      (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) := Field.absoluteGaloisGroup.map f
  letI := DistribMulAction.compHom W φ.toMonoidHom
  refine { Carrier := W, continuous := ⟨fun x y ↦ ?_⟩ }
  exact (ContinuousSMulDiscrete.isOpen_smul_eq
    (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) x y).preimage φ.continuous

/-- The restriction to `G_{ℚ₃}`, using the embedding of algebraic closures chosen by
`Field.absoluteGaloisGroup.map`. -/
def localAtThree (W : FiniteContinuousGaloisModule) :
    FiniteContinuousGaloisModule ℚ_[3] := W.restrict (algebraMap ℚ ℚ_[3])

end FiniteContinuousGaloisModule

/-- Outside `S`, every element of local inertia acts trivially on `W`. The local groups
and their maps to `G_ℚ` are the ones used by `GaloisRep.IsUnramifiedAt`. -/
structure UnramifiedOutside (S : Finset ℕ) (W : FiniteContinuousGaloisModule) : Prop where
  inertia_trivial : ∀ (p : ℕ) (hp : p.Prime), p ∉ S →
    ∀ σ ∈ localInertiaGroup hp.toHeightOneSpectrumRingOfIntegersRat,
    ∀ w : W,
      (Field.absoluteGaloisGroup.map
        (algebraMap ℚ (hp.toHeightOneSpectrumRingOfIntegersRat.adicCompletion ℚ)) σ) • w = w

/-- Allowing more excluded primes preserves the unramified-outside condition. -/
theorem UnramifiedOutside.mono {S T : Finset ℕ} {W : FiniteContinuousGaloisModule}
    (h : UnramifiedOutside S W) (hST : S ⊆ T) : UnramifiedOutside T W :=
  ⟨fun p hp hpT ↦ h.inertia_trivial p hp (fun hpS ↦ hpT (hST hpS))⟩

/-- A finite flat commutative group scheme over `R` with geometric generic fibre `W`.
It is stored contravariantly as a commutative, cocommutative Hopf algebra. The bijective
equivariant additive map is the same point-comparison format as `GaloisModule.IsFiniteFlat`.
Unlike that predicate, this record lets subsequent constructions access the chosen model. -/
structure HasFiniteFlatModel (R : Type) [CommRing R] {K : Type} [Field K]
    [Algebra R K] (W : FiniteContinuousGaloisModule K) where
  /-- The finite-flat Hopf algebra representing the chosen integral model. -/
  CoordinateRing : Type
  [commRing : CommRing CoordinateRing]
  [hopfAlgebra : HopfAlgebra R CoordinateRing]
  [finiteFlat : HopfAlgebra.IsFiniteFlat R CoordinateRing]
  [cocomm : Coalgebra.IsCocomm R CoordinateRing]
  [genericEtale : Algebra.Etale K (K ⊗[R] CoordinateRing)]
  /-- The additive Galois-equivariant identification of geometric generic points with `W`. -/
  points : Additive (K ⊗[R] CoordinateRing →ₐ[K] AlgebraicClosure K) →+[AlgebraicClosure K ≃ₐ[K]
    AlgebraicClosure K] W
  points_bijective : Function.Bijective points

attribute [instance] HasFiniteFlatModel.commRing HasFiniteFlatModel.hopfAlgebra
  HasFiniteFlatModel.finiteFlat HasFiniteFlatModel.cocomm HasFiniteFlatModel.genericEtale

/-- A chosen model which is finite étale over its coefficient ring, not just on the generic
fibre. This is the integral datum needed on the complement of the exceptional primes. -/
structure FiniteEtaleModel (R : Type) [CommRing R] {K : Type} [Field K]
    [Algebra R K] (W : FiniteContinuousGaloisModule K) extends HasFiniteFlatModel R W where
  [etale : Algebra.Etale R CoordinateRing]

attribute [instance] FiniteEtaleModel.etale

/-- Forgetting the chosen model recovers the existing finite-flat predicate. -/
theorem HasFiniteFlatModel.isFiniteFlat {R K : Type} [CommRing R] [Field K]
    [Algebra R K] {W : FiniteContinuousGaloisModule K} (M : HasFiniteFlatModel R W) :
    GaloisModule.IsFiniteFlat R K (AlgebraicClosure K) W :=
  ⟨M.CoordinateRing, inferInstance, inferInstance, inferInstance, inferInstance,
    M.points, M.points_bijective⟩

/-- For a flat Hopf algebra with étale generic fibre, an injective additive comparison of
its geometric points with an abelian group forces cocommutativity over the base ring.
This supplies the commutativity field when unpacking the existing finite-flat predicate. -/
theorem cocomm_of_injective_points {R K L H X : Type} [CommRing R] [Field K] [Field L]
    [CommRing H] [Algebra R K] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [IsFractionRing R K] [IsGalois K L] [IsSepClosed L]
    [HopfAlgebra R H] [Module.Flat R H] [Algebra.Etale K (K ⊗[R] H)]
    [AddCommGroup X] (f : Additive (K ⊗[R] H →ₐ[K] L) →+ X)
    (hf : Function.Injective f) : Coalgebra.IsCocomm R H := by
  have hcomm (p q : K ⊗[R] H →ₐ[K] L) : p * q = q * p := by
    apply Additive.ofMul.injective
    apply hf
    change f (Additive.ofMul p + Additive.ofMul q) =
      f (Additive.ofMul q + Additive.ofMul p)
    rw [map_add, map_add, add_comm]
  let : Algebra.Etale K (K ⊗[R] (H ⊗[R] H)) :=
    Algebra.etale_genericFiber_tensorSquare R K H
  constructor
  apply LinearMap.ext
  intro x
  apply Algebra.eq_of_generic_points_eq R K L (H ⊗[R] H)
  intro t
  let p : H →ₐ[R] L := t.comp Algebra.TensorProduct.includeLeft
  let q : H →ₐ[R] L := t.comp Algebra.TensorProduct.includeRight
  have hpq : Algebra.TensorProduct.lift p q (fun _ _ ↦ Commute.all _ _) = t := by
    ext a <;> simp [p, q]
  have hswap (z : H ⊗[R] H) :
      t (TensorProduct.comm R H H z) =
        Algebra.TensorProduct.lift q p (fun _ _ ↦ Commute.all _ _) z := by
    induction z using TensorProduct.inductionOn with
    | tmul a b => simp [p, q, ← map_mul]
    | add a b ha hb => simp only [map_add, ha, hb]
  obtain ⟨p', hp'⟩ := (Bialgebra.restrictPoints R K L H).surjective p
  obtain ⟨q', hq'⟩ := (Bialgebra.restrictPoints R K L H).surjective q
  have he := congrArg (fun a ↦ Bialgebra.restrictPoints R K L H a x) (hcomm q' p')
  rw [Bialgebra.restrictPoints_mul, Bialgebra.restrictPoints_mul, hp', hq'] at he
  change t (TensorProduct.comm R H H (Coalgebra.comul x)) = t (Coalgebra.comul x)
  rw [hswap, ← hpq]
  exact he

/-- Over a fraction-field base, the data-carrying model and the existing finite-flat
predicate express the same existence assertion. Cocommutativity is recovered from the
abelian point group rather than imposed as an additional arithmetic hypothesis. -/
theorem nonempty_hasFiniteFlatModel_iff {R K : Type} [CommRing R] [Field K]
    [PerfectField K] [Algebra R K] [IsFractionRing R K]
    (W : FiniteContinuousGaloisModule K) :
    Nonempty (HasFiniteFlatModel R W) ↔
      GaloisModule.IsFiniteFlat R K (AlgebraicClosure K) W := by
  refine ⟨fun ⟨M⟩ ↦ M.isFiniteFlat, ?_⟩
  rintro ⟨H, _, _, hH, hEtale, f, hf⟩
  let : Coalgebra.IsCocomm R H := cocomm_of_injective_points f.toAddMonoidHom hf.1
  exact ⟨{ CoordinateRing := H, points := f, points_bijective := hf }⟩

/-- The ring `ℤ[1/2]`, realized as the localization at powers of `2`. -/
abbrev ZInvTwo := Localization.Away (2 : ℤ)

/-- The canonical inclusion of `ℤ[1/2]` in `ℚ`. -/
def zInvTwoToRat : ZInvTwo →+* ℚ :=
  IsLocalization.Away.lift (2 : ℤ)
    (show IsUnit ((algebraMap ℤ ℚ) 2) by norm_num)

instance : Algebra ZInvTwo ℚ := zInvTwoToRat.toAlgebra

instance : IsDomain ZInvTwo := Localization.Away.isDomain (by norm_num)

section ZInvTwoScalarTower

attribute [local instance 100000] Algebra.toSMul

instance : IsScalarTower ℤ ZInvTwo ℚ := by
  apply IsScalarTower.of_algebraMap_eq (R := ℤ) (S := ZInvTwo) (A := ℚ)
  intro x
  exact (IsLocalization.Away.lift_eq (2 : ℤ)
    (show IsUnit ((algebraMap ℤ ℚ) 2) by norm_num) x).symm

instance : IsFractionRing ZInvTwo ℚ :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Submonoid.powers (2 : ℤ)) ZInvTwo ℚ

end ZInvTwoScalarTower

/-- A chosen finite-flat model over `ℤ[1/2]`, including its Galois-equivariant point
comparison. No existence or morphism-extension theorem is part of this data. -/
structure ModelOverZInvTwo (W : FiniteContinuousGaloisModule)
    extends HasFiniteFlatModel ZInvTwo W

/-- A chosen finite-flat model over `ℤ`, including its Galois-equivariant point comparison. -/
structure ModelOverInt (W : FiniteContinuousGaloisModule)
    extends HasFiniteFlatModel ℤ W

namespace FiniteContinuousGaloisModule

variable {K : Type} [Field K] [PerfectField K] (W : FiniteContinuousGaloisModule K)

/-- The finite étale generic coordinate algebra: equivariant functions from `W` to `K̄`. -/
abbrev GenericCoordinateAlgebra :=
  W →[AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K] AlgebraicClosure K

instance : HopfAlgebra K W.GenericCoordinateAlgebra :=
  GaloisModule.GenericFiber.hopfAlgebra K (AlgebraicClosure K) W

/-- Swapping tensor factors swaps the two arguments of an equivariant function. -/
theorem generic_tensor_comm (z : W.GenericCoordinateAlgebra ⊗[K] W.GenericCoordinateAlgebra)
    (x y : W) :
    GaloisModule.tensorEquiv K (AlgebraicClosure K) W W
      (TensorProduct.comm K _ _ z) (x, y) =
    GaloisModule.tensorEquiv K (AlgebraicClosure K) W W z (y, x) := by
  induction z using TensorProduct.inductionOn with
  | tmul a b => exact mul_comm _ _
  | add a b ha hb =>
    simp only [map_add]
    exact congrArg₂ (· + ·) ha hb

/-- The generic Hopf algebra is cocommutative because addition on `W` is commutative. -/
instance genericCoordinateAlgebra_isCocomm : Coalgebra.IsCocomm K W.GenericCoordinateAlgebra where
  comm_comp_comul := by
    apply LinearMap.ext
    intro a
    apply (GaloisModule.tensorEquiv K (AlgebraicClosure K) W W).injective
    ext ⟨x, y⟩
    change GaloisModule.tensorEquiv K (AlgebraicClosure K) W W
        (TensorProduct.comm K _ _ (GaloisModule.GenericFiber.comulAlgHom K
          (AlgebraicClosure K) W a)) (x, y) =
      GaloisModule.tensorEquiv K (AlgebraicClosure K) W W
        (GaloisModule.GenericFiber.comulAlgHom K (AlgebraicClosure K) W a) (x, y)
    rw [generic_tensor_comm, GaloisModule.GenericFiber.comulAlgHom_eval,
      GaloisModule.GenericFiber.comulAlgHom_eval, add_comm]

/-- Evaluation identifies the geometric points of the generic coordinate algebra with `W`. -/
def genericPoints : Additive (W.GenericCoordinateAlgebra →ₐ[K] AlgebraicClosure K) →+[
    AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K] W :=
  GaloisModule.GenericFiber.pointsEquivariantAddEquiv K (AlgebraicClosure K) W

/-- The generic point comparison is bijective. -/
theorem genericPoints_bijective : Function.Bijective W.genericPoints :=
  GaloisModule.GenericFiber.pointsEquivariantAddEquiv_bijective K (AlgebraicClosure K) W

end FiniteContinuousGaloisModule

namespace HasFiniteFlatModel

/-- The generic fibre of a chosen model is the canonical equivariant function Hopf algebra.
The comparison is determined by the model's point identification, so different integral
models of the same `W` have an explicit common generic fibre. -/
def genericBialgEquiv {R K : Type} [CommRing R] [Field K] [PerfectField K]
    [Algebra R K] {W : FiniteContinuousGaloisModule K} (M : HasFiniteFlatModel R W) :
    W.GenericCoordinateAlgebra ≃ₐc[K] K ⊗[R] M.CoordinateRing := by
  let G := K ⊗[R] M.CoordinateRing
  let L := AlgebraicClosure K
  let e : Additive (G →ₐ[K] L) ≃ W := Equiv.ofBijective M.points M.points_bijective
  let i : W →[L ≃ₐ[K] L] (G →ₐ[K] L) :=
    { toFun := fun w ↦ (e.symm w).toMul
      map_smul' := by
        intro σ w
        change (e.symm (σ • w)).toMul = (σ • e.symm w).toMul
        congr 1
        apply e.injective
        change e (e.symm (σ • w)) = M.points (σ • e.symm w)
        rw [e.apply_symm_apply, map_smul]
        exact congrArg (σ • ·) (e.apply_symm_apply w).symm }
  let j := GaloisModule.GenericFiber.canonicalEmbeddingBialgHom K L G W M.points
  refine BialgEquiv.ofBijective j ⟨?_, ?_⟩
  · exact GaloisModule.GenericFiber.canonicalEmbeddingAlgHom_injective
      K L G W M.points M.points_bijective.2
  · intro a
    let b : W →[L ≃ₐ[K] L] L :=
      (GaloisModule.GenericFiber.genericEvalAlgEquiv K L G a).comp i
    refine ⟨b, ?_⟩
    apply (GaloisModule.GenericFiber.genericEvalAlgEquiv K L G).injective
    ext p
    change p (GaloisModule.GenericFiber.canonicalEmbeddingAlgHom K L G W M.points b) = p a
    rw [GaloisModule.GenericFiber.eval_canonicalEmbeddingAlgHom]
    change (e.symm (e (Additive.ofMul p))).toMul a = p a
    rw [e.symm_apply_apply]
    rfl

/-- A finite-flat integral Hopf algebra whose generic fibre is identified with the
equivariant function algebra gives a model with the required point comparison.
This is the assembly step after constructing an integral Hopf order. -/
def ofGenericBialgEquiv {R K : Type} [CommRing R] [Field K] [PerfectField K]
    [Algebra R K] (W : FiniteContinuousGaloisModule K)
    (H : Type) [CommRing H] [HopfAlgebra R H]
    [HopfAlgebra.IsFiniteFlat R H] [Coalgebra.IsCocomm R H]
    (e : K ⊗[R] H ≃ₐc[K] W.GenericCoordinateAlgebra) : HasFiniteFlatModel R W := by
  letI : Algebra.Etale K (K ⊗[R] H) := Algebra.Etale.of_equiv e.symm.toAlgEquiv
  let p := BialgHom.precompPoints (L := AlgebraicClosure K) e.symm.toBialgHom
  have hp : Function.Bijective p := by
    constructor
    · intro a b hab
      apply Additive.toMul.injective
      apply AlgHom.ext
      intro x
      obtain ⟨y, rfl⟩ := e.symm.surjective x
      exact AlgHom.congr_fun (congrArg Additive.toMul hab) y
    · intro a
      refine ⟨Additive.ofMul (a.toMul.comp e.toAlgEquiv.toAlgHom), ?_⟩
      apply Additive.toMul.injective
      apply AlgHom.ext
      intro x
      exact congrArg a.toMul (e.apply_symm_apply x)
  exact { CoordinateRing := H
          points := W.genericPoints.comp p
          points_bijective := W.genericPoints_bijective.comp hp }

end HasFiniteFlatModel

namespace FiniteContinuousGaloisModule

variable {K : Type} [Field K] [PerfectField K] (W : FiniteContinuousGaloisModule K)

/-- The equivariant function algebra, viewed as a finite-flat model over the field itself.
This constructs the generic fibre only, not an integral model. -/
def genericModel : HasFiniteFlatModel K W := by
  letI : HopfAlgebra.IsFiniteFlat K W.GenericCoordinateAlgebra := ⟨⟩
  exact HasFiniteFlatModel.ofGenericBialgEquiv W W.GenericCoordinateAlgebra
    (Bialgebra.TensorProduct.lid K W.GenericCoordinateAlgebra)

/-- Every finite continuous Galois module has the constructed finite-flat generic model. -/
theorem isFiniteFlat_over_field : GaloisModule.IsFiniteFlat K K (AlgebraicClosure K) W :=
  W.genericModel.isFiniteFlat

/-- The canonical generic model is finite étale over `K`. Integral étaleness over a
localization of the ring of integers is not asserted here. -/
def genericEtaleModel : FiniteEtaleModel K W where
  toHasFiniteFlatModel := W.genericModel
  etale := inferInstanceAs (Algebra.Etale K W.GenericCoordinateAlgebra)

end FiniteContinuousGaloisModule

end ThreeAdicPlan
