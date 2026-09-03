/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Deformations.RepresentationTheory.Etale
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.HopfAlgebra.Quotient
public import Mathlib.RingTheory.HopfAlgebra.TensorProduct
public import Mathlib.RingTheory.LocalRing.Module

/-!
# Finite flat group schemes and their generic-fibre Galois modules

This file provides the algebraic interface used for finite flat deformation conditions.
A finite flat affine commutative group scheme over `R` is represented contravariantly by a
commutative Hopf `R`-algebra which is finite and flat as an `R`-module. Its geometric generic
fibre is the additive Galois module of algebra homomorphisms into a separably closed field.

The subsequent results in this file establish the closure properties needed by the flat
deformation functor: finite products, Galois-stable subobjects, and quotients.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Ideal.Quotient

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]

/-- Contracting an ideal from an algebra with torsion-free quotient gives a torsion-free quotient.
This is the saturation property used when taking schematic closure inside a generic fibre. -/
lemma isTorsionFree_comap (f : A →ₐ[R] B) (J : Ideal B)
    [Module.IsTorsionFree R (B ⧸ J)] : Module.IsTorsionFree R (A ⧸ J.comap f) := by
  let q : A ⧸ J.comap f →ₐ[R] B ⧸ J := Ideal.quotientMapₐ J f le_rfl
  have hq : Function.Injective q :=
    Ideal.quotientMap_injective (I := J) (f := f.toRingHom)
  exact Function.Injective.moduleIsTorsionFree q hq
    (fun r x ↦ q.toLinearMap.map_smul r x)

end Ideal.Quotient

namespace Ideal

open Coalgebra HopfAlgebra LinearMap

/-- An explicit name for a module quotient, used to distinguish it from an ideal quotient when
the ambient module is itself a ring. -/
abbrev ModuleQuotient {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (p : Submodule R M) := M ⧸ p

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
variable [HopfAlgebra R A] [HopfAlgebra R B]

/-- The linear map between module quotients induced by a bialgebra map and contraction of an
ideal. -/
def comapQuotientLinearMap (f : A →ₐc[R] B) (J : Ideal B) :
    ModuleQuotient ((J.comap f.toAlgHom).restrictScalars R) →ₗ[R]
      ModuleQuotient (J.restrictScalars R) :=
  ((J.comap f.toAlgHom).restrictScalars R).mapQ (J.restrictScalars R)
    (f : A →ₗ[R] B) (by intro x hx; change f x ∈ J; exact hx)

lemma comapQuotientLinearMap_injective (f : A →ₐc[R] B) (J : Ideal B) :
    Function.Injective (comapQuotientLinearMap f J) := by
  rw [← LinearMap.ker_eq_bot]
  rw [comapQuotientLinearMap, Submodule.ker_mapQ]
  change Submodule.map ((J.comap f.toAlgHom).restrictScalars R).mkQ
    ((J.comap f.toAlgHom).restrictScalars R) = ⊥
  exact Submodule.mkQ_map_self ((J.comap f.toAlgHom).restrictScalars R)

/-- A Hopf ideal contracts along a Hopf-compatible bialgebra map when the induced map on the
tensor squares of the quotients is injective. -/
lemma IsHopfIdeal.comap_of_tensor_quotientMap_injective (f : A →ₐc[R] B) (J : Ideal B)
    [J.IsHopfIdeal R]
    (hS : antipode R ∘ₗ f.toLinearMap = f.toLinearMap ∘ₗ antipode R)
    (hq : Function.Injective (TensorProduct.map
      (comapQuotientLinearMap f J) (comapQuotientLinearMap f J))) :
    (J.comap f.toAlgHom).IsHopfIdeal R := by
  let I := J.comap f.toAlgHom
  let q := comapQuotientLinearMap f J
  let _ : (I.restrictScalars R).IsCoideal := by
    constructor
    · intro x hx
      exact (CoalgHomClass.counit_comp_apply f x).symm.trans
        (Submodule.IsCoideal.counit_eq_zero (I := J.restrictScalars R) hx)
    · intro x hx
      apply hq
      change TensorProduct.map q q
        (TensorProduct.map (I.restrictScalars R).mkQ (I.restrictScalars R).mkQ (comul x)) = 0
      rw [TensorProduct.map_map]
      have hqmk : q.comp (I.restrictScalars R).mkQ =
          (J.restrictScalars R).mkQ.comp (f : A →ₗ[R] B) := by
        dsimp [q, I, comapQuotientLinearMap]
        apply Submodule.mapQ_mkQ
      rw [hqmk]
      rw [← TensorProduct.map_map]
      have hfcomul := CoalgHomClass.map_comp_comul_apply f x
      rw [hfcomul]
      exact Submodule.IsCoideal.map_mkQ_comul_eq_zero hx
  constructor
  intro x hx
  change f (antipode R x) ∈ J
  have hsx : antipode R (f x) = f (antipode R x) := LinearMap.congr_fun hS x
  rw [← hsx]
  exact IsHopfIdeal.antipode_mem hx

/-- Over a Dedekind domain, contraction preserves Hopf ideals when the generic quotient is
torsion-free and the bialgebra map respects antipodes. -/
lemma IsHopfIdeal.comap [IsDedekindDomain R] (f : A →ₐc[R] B) (J : Ideal B)
    [J.IsHopfIdeal R]
    [Module.IsTorsionFree R (ModuleQuotient (J.restrictScalars R))]
    (hS : antipode R ∘ₗ f.toLinearMap = f.toLinearMap ∘ₗ antipode R) :
    (J.comap f.toAlgHom).IsHopfIdeal R := by
  let q := comapQuotientLinearMap f J
  have hq : Function.Injective q := comapQuotientLinearMap_injective f J
  let _ : Module.IsTorsionFree R
      (ModuleQuotient ((J.comap f.toAlgHom).restrictScalars R)) :=
    Function.Injective.moduleIsTorsionFree q hq (fun r x ↦ q.map_smul r x)
  let _ : Module.Flat R (ModuleQuotient ((J.comap f.toAlgHom).restrictScalars R)) :=
    inferInstance
  let _ : Module.Flat R (ModuleQuotient (J.restrictScalars R)) := inferInstance
  exact IsHopfIdeal.comap_of_tensor_quotientMap_injective f J hS
    (TensorProduct.map_injective_of_flat_flat q q hq hq)

end Ideal

namespace HopfAlgebra

/-- A Hopf algebra representing a finite flat affine group scheme. -/
class IsFiniteFlat (R H : Type u) [CommRing R] [CommRing H] [Algebra R H] : Prop extends
    Module.Finite R H, Module.Flat R H

section Image

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]

/-- A surjective image of a finite module is finite; over a Dedekind domain it is flat as soon
as it is torsion-free. -/
lemma IsFiniteFlat.of_surjective [IsDedekindDomain R] [Module.IsTorsionFree R B]
    (hA : IsFiniteFlat R A) (f : A →ₐ[R] B) (hf : Function.Surjective f) :
    IsFiniteFlat R B := by
  let _ : Module.Finite R A := hA.toFinite
  let _ : Module.Finite R B := Module.Finite.of_surjective f.toLinearMap hf
  exact ⟨⟩

/-- The algebraic image of a finite algebra in a torsion-free algebra is finite flat over a
Dedekind domain. This is the module-theoretic core of schematic closure over a DVR. -/
lemma IsFiniteFlat.range [IsDedekindDomain R] [Module.IsTorsionFree R B]
    (hA : IsFiniteFlat R A) (f : A →ₐ[R] B) : IsFiniteFlat R f.range := by
  exact hA.of_surjective f.rangeRestrict f.rangeRestrict_surjective

end Image

section Quotient

variable {R A : Type u} [CommRing R] [CommRing A] [HopfAlgebra R A]

/-- A torsion-free quotient by a Hopf ideal remains finite flat over a Dedekind domain. -/
lemma IsFiniteFlat.quotient [IsDedekindDomain R] (hA : IsFiniteFlat R A)
    (I : Ideal A) [I.IsTwoSided] [I.IsHopfIdeal R]
    [Module.IsTorsionFree R (A ⧸ I)] : IsFiniteFlat R (A ⧸ I) := by
  exact hA.of_surjective (Ideal.Quotient.mkₐ R I) Ideal.Quotient.mk_surjective

/-- Contracting a generic-fibre ideal gives a finite-flat quotient whenever the contraction is a
Hopf ideal and the generic quotient is torsion-free. -/
lemma IsFiniteFlat.quotient_comap [IsDedekindDomain R] (hA : IsFiniteFlat R A)
    {B : Type u} [CommRing B] [Algebra R B] (f : A →ₐ[R] B) (J : Ideal B)
    [(J.comap f).IsHopfIdeal R] [Module.IsTorsionFree R (B ⧸ J)] :
    IsFiniteFlat R (A ⧸ J.comap f) := by
  let _ : Module.IsTorsionFree R (A ⧸ J.comap f) :=
    Ideal.Quotient.isTorsionFree_comap f J
  exact hA.quotient (J.comap f)

end Quotient

end HopfAlgebra

namespace Additive

/-- A multiplicative action which preserves multiplication becomes an additive action on the
additive type synonym. -/
instance {G M : Type*} [Monoid G] [Monoid M] [MulDistribMulAction G M] :
    DistribMulAction G (Additive M) where
  smul g x := Additive.ofMul (g • x.toMul)
  one_smul x := congrArg Additive.ofMul (one_smul G x.toMul)
  mul_smul g h x := congrArg Additive.ofMul (mul_smul g h x.toMul)
  smul_zero g := congrArg Additive.ofMul (smul_one g)
  smul_add g x y := congrArg Additive.ofMul (smul_mul' g x.toMul y.toMul)

instance {G M : Type*} [TopologicalSpace G] [Monoid G] [Monoid M]
    [MulDistribMulAction G M] [ContinuousSMulDiscrete G M] :
    ContinuousSMulDiscrete G (Additive M) where
  isOpen_smul_eq x y := by
    change IsOpen {g : G | Additive.ofMul (g • x.toMul) = y}
    convert ContinuousSMulDiscrete.isOpen_smul_eq G x.toMul y.toMul using 1
    ext g
    constructor
    · intro h
      simpa using congrArg Additive.toMul h
    · intro h
      simpa using congrArg Additive.ofMul h

end Additive

/-- A surjective equivariant additive map transports continuity of a discrete group action to its
target. -/
lemma ContinuousSMulDiscrete.of_surjective_map
    {G X Y : Type*} [TopologicalSpace G] [Group G] [ContinuousMul G]
    [AddMonoid X] [AddMonoid Y]
    [DistribMulAction G X] [DistribMulAction G Y] [ContinuousSMulDiscrete G X]
    (f : X →+[G] Y) (hf : Function.Surjective f) : ContinuousSMulDiscrete G Y := by
  rw [continuousSMulDiscrete_iff_isOpen_stabilizer]
  intro y
  obtain ⟨x, rfl⟩ := hf y
  apply Subgroup.isOpen_mono _ (ContinuousSMulDiscrete.isOpen_stabilizer G x)
  intro g hg
  change g • f x = f x
  rw [← map_smul f g x, hg]

namespace BialgHom

variable {K L A B : Type u} [Field K] [CommRing A] [CommRing B] [Field L]
variable [Bialgebra K A] [Bialgebra K B] [Algebra K L]

lemma algHom_mul_comp (f g : B →ₐ[K] L) (h : A →ₐc[K] B) :
    (f * g).comp (h : A →ₐ[K] B) =
      (f.comp (h : A →ₐ[K] B)) * (g.comp (h : A →ₐ[K] B)) := by
  change (AlgHom.comp (Algebra.TensorProduct.lift f g (fun _ _ ↦ .all _ _))
      (Bialgebra.comulAlgHom K B)).comp (h : A →ₐ[K] B) =
    AlgHom.comp (Algebra.TensorProduct.lift (f.comp (h : A →ₐ[K] B))
      (g.comp (h : A →ₐ[K] B)) (fun _ _ ↦ .all _ _)) (Bialgebra.comulAlgHom K A)
  rw [AlgHom.comp_assoc, ← BialgHom.map_comp_comulAlgHom, ← AlgHom.comp_assoc]
  congr 1
  ext <;> simp

lemma algHom_one_comp (h : A →ₐc[K] B) :
    (1 : B →ₐ[K] L).comp (h : A →ₐ[K] B) = 1 := by
  ext x
  change algebraMap K L (Coalgebra.counit (h x)) = algebraMap K L (Coalgebra.counit x)
  rw [CoalgHomClass.counit_comp_apply]

/-- Precomposition with a bialgebra morphism as an additive equivariant map on geometric
points, where addition on points is the Hopf-algebra convolution product. -/
noncomputable def precompPoints (h : A →ₐc[K] B) :
    Additive (B →ₐ[K] L) →+[L ≃ₐ[K] L] Additive (A →ₐ[K] L) where
  toFun f := Additive.ofMul (f.toMul.comp (h : A →ₐ[K] B))
  map_zero' := congrArg Additive.ofMul (algHom_one_comp h)
  map_add' f g := congrArg Additive.ofMul (algHom_mul_comp f.toMul g.toMul h)
  map_smul' σ f := by ext x; rfl

end BialgHom

namespace GaloisModule

section TensorProduct

variable (R K H₁ H₂ : Type u)
variable [CommRing R] [Field K] [Algebra R K]
variable [CommRing H₁] [CommRing H₂] [HopfAlgebra R H₁] [HopfAlgebra R H₂]

/-- Base change distributes over the tensor product of two algebras. -/
noncomputable def genericTensorEquiv :
    ((K ⊗[R] H₁) ⊗[K] (K ⊗[R] H₂)) ≃ₐ[K] K ⊗[R] (H₁ ⊗[R] H₂) :=
  (Algebra.TensorProduct.tensorTensorTensorComm R R K K K H₁ K H₂).trans
    (Algebra.TensorProduct.congr (Algebra.TensorProduct.lid K K)
      (AlgEquiv.refl : (H₁ ⊗[R] H₂) ≃ₐ[R] (H₁ ⊗[R] H₂)))

variable (L : Type u) [Field L] [Algebra K L]

def commutingPairEquiv :
    {fg : ((K ⊗[R] H₁ →ₐ[K] L) × (K ⊗[R] H₂ →ₐ[K] L)) //
      ∀ x y, Commute (fg.1 x) (fg.2 y)} ≃
      ((K ⊗[R] H₁ →ₐ[K] L) × (K ⊗[R] H₂ →ₐ[K] L)) where
  toFun fg := fg.1
  invFun fg := ⟨fg, fun _ _ ↦ mul_comm _ _⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Geometric points of the base-changed tensor product are pairs of geometric points. -/
noncomputable def genericTensorPointsEquiv :
    (K ⊗[R] (H₁ ⊗[R] H₂) →ₐ[K] L) ≃
      ((K ⊗[R] H₁ →ₐ[K] L) × (K ⊗[R] H₂ →ₐ[K] L)) :=
  ((genericTensorEquiv R K H₁ H₂).arrowCongr (AlgEquiv.refl : L ≃ₐ[K] L)).symm.trans <|
    (Algebra.TensorProduct.liftEquiv (R := K) (S := K)
      (A := K ⊗[R] H₁) (B := K ⊗[R] H₂) (C := L)).symm.trans <|
      commutingPairEquiv R K H₁ H₂ L

/-- The first factor inclusion of a tensor product, as a bialgebra morphism. -/
noncomputable def tensorIncludeLeft : H₁ →ₐc[R] H₁ ⊗[R] H₂ :=
  (Bialgebra.TensorProduct.map (BialgHom.id R H₁) (Bialgebra.unitBialgHom R H₂)).comp
    (Bialgebra.TensorProduct.rid R R H₁).symm.toBialgHom

/-- The second factor inclusion of a tensor product, as a bialgebra morphism. -/
noncomputable def tensorIncludeRight : H₂ →ₐc[R] H₁ ⊗[R] H₂ :=
  (Bialgebra.TensorProduct.map (Bialgebra.unitBialgHom R H₁) (BialgHom.id R H₂)).comp
    (Bialgebra.TensorProduct.lid R H₂).symm.toBialgHom

/-- The base change of `tensorIncludeLeft`. -/
noncomputable def genericTensorIncludeLeft :
    K ⊗[R] H₁ →ₐc[K] K ⊗[R] (H₁ ⊗[R] H₂) :=
  Bialgebra.TensorProduct.map (BialgHom.id K K) (tensorIncludeLeft R H₁ H₂)

/-- The base change of `tensorIncludeRight`. -/
noncomputable def genericTensorIncludeRight :
    K ⊗[R] H₂ →ₐc[K] K ⊗[R] (H₁ ⊗[R] H₂) :=
  Bialgebra.TensorProduct.map (BialgHom.id K K) (tensorIncludeRight R H₁ H₂)

@[simp] private lemma genericTensorPointsEquiv_apply_fst
    (f : K ⊗[R] (H₁ ⊗[R] H₂) →ₐ[K] L) :
    (genericTensorPointsEquiv R K H₁ H₂ L f).1 =
      f.comp (genericTensorIncludeLeft R K H₁ H₂ :
        K ⊗[R] H₁ →ₐ[K] K ⊗[R] (H₁ ⊗[R] H₂)) := by
  ext x
  induction x with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul k x =>
    simp [genericTensorPointsEquiv, genericTensorEquiv, commutingPairEquiv,
      genericTensorIncludeLeft, tensorIncludeLeft, Algebra.TensorProduct.one_def]

@[simp] private lemma genericTensorPointsEquiv_apply_snd
    (f : K ⊗[R] (H₁ ⊗[R] H₂) →ₐ[K] L) :
    (genericTensorPointsEquiv R K H₁ H₂ L f).2 =
      f.comp (genericTensorIncludeRight R K H₁ H₂ :
        K ⊗[R] H₂ →ₐ[K] K ⊗[R] (H₁ ⊗[R] H₂)) := by
  ext x
  induction x with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul k x =>
    simp [genericTensorPointsEquiv, genericTensorEquiv, commutingPairEquiv,
      genericTensorIncludeRight, tensorIncludeRight, Algebra.TensorProduct.one_def]

end TensorProduct

/-- The generic fibre of the trivial Hopf algebra has exactly one geometric point. -/
noncomputable def trivialPointsEquiv (R K L : Type u) [CommRing R] [Field K] [Field L]
    [Algebra R K] [Algebra K L] :
    (K ⊗[R] R →ₐ[K] L) ≃ (K →ₐ[K] L) :=
  (Algebra.TensorProduct.rid R K K).arrowCongr (AlgEquiv.refl : L ≃ₐ[K] L)

variable (R K L : Type u) (X : Type v)
variable [CommRing R] [Field K] [Field L] [Algebra R K] [Algebra K L]
variable [AddCommGroup X] [DistribMulAction (L ≃ₐ[K] L) X]

/-- A finite additive Galois module has a finite flat model over `R` if it is equivariantly
isomorphic to the geometric points of the generic fibre of a finite flat commutative Hopf
`R`-algebra.

The definition deliberately retains the Hopf algebra witness. This makes it strong enough to
construct products and schematic closures, rather than merely recording that the underlying
Galois set is finite. -/
def IsFiniteFlat (R K L : Type u) (X : Type v) [CommRing R] [Field K] [Field L] [Algebra R K]
    [Algebra K L] [AddCommGroup X] [DistribMulAction (L ≃ₐ[K] L) X] : Prop :=
  ∃ (H : Type u) (_ : CommRing H) (_ : HopfAlgebra R H)
    (_ : HopfAlgebra.IsFiniteFlat R H) (_ : Algebra.Etale K (K ⊗[R] H))
    (f : Additive (K ⊗[R] H →ₐ[K] L) →+[L ≃ₐ[K] L] X),
    Function.Bijective f

lemma isFiniteFlat_iff : GaloisModule.IsFiniteFlat R K L X ↔
    ∃ (H : Type u) (_ : CommRing H) (_ : HopfAlgebra R H)
      (_ : Module.Finite R H) (_ : Module.Flat R H) (_ : Algebra.Etale K (K ⊗[R] H))
      (f : Additive (K ⊗[R] H →ₐ[K] L) →+[L ≃ₐ[K] L] X),
      Function.Bijective f := by
  constructor
  · rintro ⟨H, _, _, hH, _, f, hf⟩
    exact ⟨H, inferInstance, inferInstance, hH.toFinite, hH.toFlat, inferInstance, f, hf⟩
  · rintro ⟨H, _, _, _, _, _, f, hf⟩
    let _ : HopfAlgebra.IsFiniteFlat R H := ⟨⟩
    exact ⟨H, inferInstance, inferInstance, inferInstance, inferInstance, f, hf⟩

/-- The Galois action on a module admitting a finite flat model is continuous for the discrete
topology. -/
lemma IsFiniteFlat.continuousSMulDiscrete
    (hX : GaloisModule.IsFiniteFlat R K L X) :
    ContinuousSMulDiscrete (L ≃ₐ[K] L) X := by
  rcases hX with ⟨H, _, _, _, _, f, hf⟩
  let P : Type u := (K ⊗[R] H →ₐ[K] L)
  let _ : ContinuousSMulDiscrete (L ≃ₐ[K] L) P := inferInstance
  let _ : ContinuousSMulDiscrete (L ≃ₐ[K] L) (Additive P) := inferInstance
  exact ContinuousSMulDiscrete.of_surjective_map
    (G := L ≃ₐ[K] L) (X := Additive P) (Y := X) f hf.2

/-- Every subsingleton additive Galois module is represented by the trivial finite flat group
scheme. In particular, this supplies the empty finite product. -/
lemma IsFiniteFlat.of_subsingleton [Subsingleton X] :
    GaloisModule.IsFiniteFlat R K L X := by
  let _ : HopfAlgebra.IsFiniteFlat R R := ⟨⟩
  let _ : Algebra.Etale K (K ⊗[R] R) :=
    Algebra.Etale.of_equiv (Algebra.TensorProduct.rid R K K).symm
  let _ : Subsingleton (K ⊗[R] R →ₐ[K] L) :=
    (trivialPointsEquiv R K L).injective.subsingleton
  let f : Additive (K ⊗[R] R →ₐ[K] L) →+[L ≃ₐ[K] L] X := 0
  refine ⟨R, inferInstance, inferInstance, inferInstance, inferInstance, f, ?_⟩
  constructor
  · exact fun _ _ _ ↦ Subsingleton.elim _ _
  · intro x
    let y : K ⊗[R] R →ₐ[K] L :=
      (Algebra.ofId K L).comp (Algebra.TensorProduct.rid R K K).toAlgHom
    exact ⟨Additive.ofMul y, Subsingleton.elim _ _⟩

/-- Having a finite flat model is invariant under an equivariant additive isomorphism. -/
lemma IsFiniteFlat.map {Y : Type w} [AddCommGroup Y]
    [DistribMulAction (L ≃ₐ[K] L) Y] (hX : GaloisModule.IsFiniteFlat R K L X)
    (f : X →+[L ≃ₐ[K] L] Y) (hf : Function.Bijective f) :
    GaloisModule.IsFiniteFlat R K L Y := by
  rcases hX with ⟨H, _, _, _, _, g, hg⟩
  exact ⟨H, inferInstance, inferInstance, inferInstance, inferInstance,
    f.comp g, hf.comp hg⟩

set_option maxHeartbeats 1000000 in
-- The mixed-universe tensor-product witness needs more elaboration time than the default budget.
/-- The product of two Galois modules with finite flat models has a finite flat model. The
coordinate Hopf algebra is the tensor product of the two coordinate Hopf algebras. -/
lemma IsFiniteFlat.prod {Y : Type w} [AddCommGroup Y]
    [DistribMulAction (L ≃ₐ[K] L) Y] (hX : GaloisModule.IsFiniteFlat R K L X)
    (hY : GaloisModule.IsFiniteFlat R K L Y) :
    GaloisModule.IsFiniteFlat R K L (X × Y) := by
  rcases hX with ⟨H₁, _, _, hH₁, _, f₁, hf₁⟩
  rcases hY with ⟨H₂, _, _, hH₂, _, f₂, hf₂⟩
  let _ : HopfAlgebra.IsFiniteFlat R (H₁ ⊗[R] H₂) := ⟨⟩
  let _ : Algebra (K ⊗[R] H₁) ((K ⊗[R] H₁) ⊗[K] (K ⊗[R] H₂)) :=
    Algebra.TensorProduct.leftAlgebra
  let _ : IsScalarTower K (K ⊗[R] H₁)
      ((K ⊗[R] H₁) ⊗[K] (K ⊗[R] H₂)) := by infer_instance
  let _ : Algebra.Etale K ((K ⊗[R] H₁) ⊗[K] (K ⊗[R] H₂)) :=
    Algebra.Etale.comp K (K ⊗[R] H₁)
      ((K ⊗[R] H₁) ⊗[K] (K ⊗[R] H₂))
  let genericBialgebra : Bialgebra K (K ⊗[R] (H₁ ⊗[R] H₂)) := inferInstance
  let _ : Bialgebra K (K ⊗[R] (H₁ ⊗[R] H₂)) := genericBialgebra
  let _ : Algebra K (K ⊗[R] (H₁ ⊗[R] H₂)) := genericBialgebra.toAlgebra
  let _ : Algebra.Etale K (K ⊗[R] (H₁ ⊗[R] H₂)) :=
    Algebra.Etale.of_equiv (genericTensorEquiv R K H₁ H₂)
  let p : Additive (K ⊗[R] (H₁ ⊗[R] H₂) →ₐ[K] L) →+[L ≃ₐ[K] L]
      Additive (K ⊗[R] H₁ →ₐ[K] L) × Additive (K ⊗[R] H₂ →ₐ[K] L) :=
    { toFun := fun f ↦
        (BialgHom.precompPoints (genericTensorIncludeLeft R K H₁ H₂) f,
          BialgHom.precompPoints (genericTensorIncludeRight R K H₁ H₂) f)
      map_zero' := by simp [BialgHom.precompPoints]
      map_add' := by intro f g; simp [BialgHom.precompPoints]
      map_smul' := by intro σ f; simp [BialgHom.precompPoints] }
  have hp : Function.Bijective p := by
    constructor
    · intro f g h
      change f.toMul = g.toMul
      apply (genericTensorPointsEquiv R K H₁ H₂ L).injective
      apply Prod.ext
      · have h₁ := congrArg Prod.fst h
        change Additive.ofMul ((f.toMul).comp
            (genericTensorIncludeLeft R K H₁ H₂ :
              K ⊗[R] H₁ →ₐ[K] K ⊗[R] (H₁ ⊗[R] H₂))) =
          Additive.ofMul ((g.toMul).comp
            (genericTensorIncludeLeft R K H₁ H₂ :
              K ⊗[R] H₁ →ₐ[K] K ⊗[R] (H₁ ⊗[R] H₂))) at h₁
        simpa [genericTensorPointsEquiv_apply_fst] using
          congrArg (fun z : Additive (K ⊗[R] H₁ →ₐ[K] L) ↦ z.toMul) h₁
      · have h₂ := congrArg Prod.snd h
        change Additive.ofMul ((f.toMul).comp
            (genericTensorIncludeRight R K H₁ H₂ :
              K ⊗[R] H₂ →ₐ[K] K ⊗[R] (H₁ ⊗[R] H₂))) =
          Additive.ofMul ((g.toMul).comp
            (genericTensorIncludeRight R K H₁ H₂ :
              K ⊗[R] H₂ →ₐ[K] K ⊗[R] (H₁ ⊗[R] H₂))) at h₂
        simpa [genericTensorPointsEquiv_apply_snd] using
          congrArg (fun z : Additive (K ⊗[R] H₂ →ₐ[K] L) ↦ z.toMul) h₂
    · intro y
      let x := Additive.ofMul ((genericTensorPointsEquiv R K H₁ H₂ L).symm
        (y.1.toMul, y.2.toMul))
      refine ⟨x, ?_⟩
      apply Prod.ext
      · have hy := congrArg Prod.fst
          ((genericTensorPointsEquiv R K H₁ H₂ L).apply_symm_apply
            (y.1.toMul, y.2.toMul))
        rw [genericTensorPointsEquiv_apply_fst] at hy
        change Additive.ofMul (((genericTensorPointsEquiv R K H₁ H₂ L).symm
            (y.1.toMul, y.2.toMul)).comp
              (genericTensorIncludeLeft R K H₁ H₂ :
                K ⊗[R] H₁ →ₐ[K] K ⊗[R] (H₁ ⊗[R] H₂))) = y.1
        exact congrArg Additive.ofMul hy
      · have hy := congrArg Prod.snd
          ((genericTensorPointsEquiv R K H₁ H₂ L).apply_symm_apply
            (y.1.toMul, y.2.toMul))
        rw [genericTensorPointsEquiv_apply_snd] at hy
        change Additive.ofMul (((genericTensorPointsEquiv R K H₁ H₂ L).symm
            (y.1.toMul, y.2.toMul)).comp
              (genericTensorIncludeRight R K H₁ H₂ :
                K ⊗[R] H₂ →ₐ[K] K ⊗[R] (H₁ ⊗[R] H₂))) = y.2
        exact congrArg Additive.ofMul hy
  let q : (Additive (K ⊗[R] H₁ →ₐ[K] L) × Additive (K ⊗[R] H₂ →ₐ[K] L))
      →+[L ≃ₐ[K] L] (X × Y) :=
    { toFun := fun z ↦ (f₁ z.1, f₂ z.2)
      map_zero' := by simp
      map_add' := by intro x y; simp
      map_smul' := by intro σ x; simp }
  exact ⟨H₁ ⊗[R] H₂, inferInstance, inferInstance, inferInstance, inferInstance,
    q.comp p, (hf₁.prodMap hf₂).comp hp⟩

/-- Every finite power of a Galois module with a finite flat model has a finite flat model. -/
lemma IsFiniteFlat.finPow (hX : GaloisModule.IsFiniteFlat R K L X) :
    ∀ n : ℕ, GaloisModule.IsFiniteFlat R K L (Fin n → X) := by
  intro n
  induction n with
  | zero => exact IsFiniteFlat.of_subsingleton R K L (Fin 0 → X)
  | succ n ih =>
      let f : (X × (Fin n → X)) →+[L ≃ₐ[K] L] (Fin (n + 1) → X) :=
        { toFun := fun x ↦ Fin.cons x.1 x.2
          map_zero' := by ext i; exact Fin.cases rfl (fun _ ↦ rfl) i
          map_add' := by intro x y; ext i; exact Fin.cases rfl (fun _ ↦ rfl) i
          map_smul' := by intro σ x; ext i; exact Fin.cases rfl (fun _ ↦ rfl) i }
      have hf : Function.Bijective f := by
        have h := (Fin.consEquiv (fun _ : Fin (n + 1) ↦ X)).bijective
        constructor
        · intro x y hxy
          exact h.1 hxy
        · intro y
          rcases h.2 y with ⟨x, hx⟩
          exact ⟨x, hx⟩
      exact IsFiniteFlat.map R K L (X × (Fin n → X))
        (IsFiniteFlat.prod R K L X hX ih) f hf
end GaloisModule
