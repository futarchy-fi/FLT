/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Deformations.RepresentationTheory.Etale
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Etale.Finite
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
    (I : Ideal A) [I.IsTwoSided]
    [Module.IsTorsionFree R (A ⧸ I)] : IsFiniteFlat R (A ⧸ I) := by
  exact hA.of_surjective (Ideal.Quotient.mkₐ R I) Ideal.Quotient.mk_surjective

/-- Contracting a generic-fibre ideal gives a finite-flat quotient whenever the contraction is a
Hopf ideal and the generic quotient is torsion-free. -/
lemma IsFiniteFlat.quotient_comap [IsDedekindDomain R] (hA : IsFiniteFlat R A)
    {B : Type u} [CommRing B] [Algebra R B] (f : A →ₐ[R] B) (J : Ideal B)
    [Module.IsTorsionFree R (B ⧸ J)] :
    IsFiniteFlat R (A ⧸ J.comap f) := by
  let _ : Module.IsTorsionFree R (A ⧸ J.comap f) :=
    Ideal.Quotient.isTorsionFree_comap f J
  exact hA.quotient (J.comap f)

end Quotient

end HopfAlgebra

namespace Additive

/-- A multiplicative action which preserves multiplication becomes an additive action on the
additive type synonym. -/
instance instDistribMulActionAdditiveOfMulDistribMulActionFLT
    {G M : Type*} [Monoid G] [Monoid M] [MulDistribMulAction G M] :
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

/-- Over a commutative target, pairs of algebra maps automatically commute. -/
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

/-! ## The canonical generic fibre of a finite continuous Galois module -/

instance continuousSMulDiscrete_prod {G X Y : Type*} [TopologicalSpace G]
    [SMul G X] [SMul G Y] [ContinuousSMulDiscrete G X]
    [ContinuousSMulDiscrete G Y] : ContinuousSMulDiscrete G (X × Y) where
  isOpen_smul_eq x y := by
    convert (ContinuousSMulDiscrete.isOpen_smul_eq G x.1 y.1).inter
      (ContinuousSMulDiscrete.isOpen_smul_eq G x.2 y.2) using 1
    ext g
    simp [Prod.ext_iff]
lemma finrank_eq_natCard_algHom (K L A : Type u) [Field K] [Field L]
    [Algebra K L] [IsSepClosed L] [CommRing A] [Algebra K A]
    [Algebra.Etale K A] :
    Module.finrank K A = Nat.card (A →ₐ[K] L) := by
  let B := L ⊗[K] A
  let _ : CommRing B := inferInstance
  let _ : Algebra L B := inferInstance
  let _ : Algebra.Etale L B := inferInstance
  calc
    Module.finrank K A = Module.finrank L B := by
      exact (Module.finrank_baseChange (R := L) (S := K) (M' := A)).symm
    _ = Nat.card (PrimeSpectrum B) := by
      classical
      let _ : IsArtinianRing B := isArtinian_of_tower L inferInstance
      let _ := Fintype.ofFinite (PrimeSpectrum B)
      rw [(Algebra.FormallyEtale.equivPiOfIsSepClosed L B).toLinearEquiv.finrank_eq]
      rw [Module.finrank_pi, Fintype.card_eq_nat_card]
    _ = Nat.card (B →ₐ[L] L) := Nat.card_congr
      (Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum L B).symm
    _ = Nat.card (A →ₐ[K] L) := Nat.card_congr
      (Algebra.TensorProduct.liftEquivRight K L A L).symm

section

variable (K L X Y : Type u) [Field K] [Field L] [Algebra K L]
variable [MulAction (L ≃ₐ[K] L) X] [MulAction (L ≃ₐ[K] L) Y]

/-- The algebra map sending a pure tensor of equivariant functions to their product. -/
def tensorHom :
    ((X →[L ≃ₐ[K] L] L) ⊗[K] (Y →[L ≃ₐ[K] L] L)) →ₐ[K]
      ((X × Y) →[L ≃ₐ[K] L] L) :=
  Algebra.TensorProduct.lift
    (MulActionHom.compLeftAlgHom (L ≃ₐ[K] L) K L
      (MulActionHom.fst (L ≃ₐ[K] L) X Y))
    (MulActionHom.compLeftAlgHom (L ≃ₐ[K] L) K L
      (MulActionHom.snd (L ≃ₐ[K] L) X Y))
    (fun _ _ ↦ Commute.all _ _)

@[simp] lemma tensorHom_tmul
    (f : X →[L ≃ₐ[K] L] L) (g : Y →[L ≃ₐ[K] L] L) (x : X) (y : Y) :
    tensorHom K L X Y (f ⊗ₜ[K] g) (x, y) = f x * g y := by
  rfl

lemma finrank_equivariantFunctions (K L X : Type u) [Field K] [Field L]
    [Algebra K L] [IsGalois K L] [IsSepClosed L]
    [MulAction (L ≃ₐ[K] L) X] [Finite X]
    [ContinuousSMulDiscrete (L ≃ₐ[K] L) X] :
    Module.finrank K (X →[L ≃ₐ[K] L] L) = Nat.card X := by
  calc
    Module.finrank K (X →[L ≃ₐ[K] L] L) =
        Nat.card ((X →[L ≃ₐ[K] L] L) →ₐ[K] L) :=
      finrank_eq_natCard_algHom K L (X →[L ≃ₐ[K] L] L)
    _ = Nat.card X := Nat.card_congr
      (Equiv.ofBijective _ (InfiniteGalois.evalAlgHom_bijective K L X)).symm

lemma tensorHom_bijective (K L X Y : Type u) [Field K] [Field L]
    [Algebra K L] [IsGalois K L] [IsSepClosed L]
    [MulAction (L ≃ₐ[K] L) X] [MulAction (L ≃ₐ[K] L) Y]
    [Finite X] [Finite Y]
    [ContinuousSMulDiscrete (L ≃ₐ[K] L) X]
    [ContinuousSMulDiscrete (L ≃ₐ[K] L) Y] :
    Function.Bijective (tensorHom K L X Y) := by
  let BX := X →[L ≃ₐ[K] L] L
  let BY := Y →[L ≃ₐ[K] L] L
  let BXY := (X × Y) →[L ≃ₐ[K] L] L
  let _ : Module.Free K BX := Module.Free.of_divisionRing K BX
  let _ : Module.Free K BY := Module.Free.of_divisionRing K BY
  let _ : Module.Free K BXY := Module.Free.of_divisionRing K BXY
  let _ : Module.Finite K BX := Algebra.FormallyUnramified.finite_of_free K BX
  let _ : Module.Finite K BY := Algebra.FormallyUnramified.finite_of_free K BY
  let _ : Module.Finite K BXY := Algebra.FormallyUnramified.finite_of_free K BXY
  let _ : Algebra BX (BX ⊗[K] BY) := Algebra.TensorProduct.leftAlgebra
  let _ : IsScalarTower K BX (BX ⊗[K] BY) := by infer_instance
  let _ : Algebra.Etale K (BX ⊗[K] BY) :=
    Algebra.Etale.comp K BX (BX ⊗[K] BY)
  let _ : Module.Free K (BX ⊗[K] BY) :=
    Module.Free.of_divisionRing K (BX ⊗[K] BY)
  let _ : Module.Finite K (BX ⊗[K] BY) :=
    Algebra.FormallyUnramified.finite_of_free K (BX ⊗[K] BY)
  let _ : ContinuousSMulDiscrete (L ≃ₐ[K] L) (X × Y) :=
    continuousSMulDiscrete_prod
  have hinj : Function.Injective (tensorHom K L X Y) := by
    intro z₁ z₂ hz
    apply (InfiniteGalois.evalMulActionHom_bijective_of_isSepClosed
      K L (BX ⊗[K] BY)).1
    ext h
    let fg := (Algebra.TensorProduct.liftEquiv (R := K) (S := K)
      (A := BX) (B := BY) (C := L)).symm h
    obtain ⟨x, hx⟩ := (InfiniteGalois.evalAlgHom_bijective K L X).2 fg.1.1
    obtain ⟨y, hy⟩ := (InfiniteGalois.evalAlgHom_bijective K L Y).2 fg.1.2
    have hh : h = (MulActionHom.evalAlgHom (L ≃ₐ[K] L) K (X × Y) L (x, y)).comp
        (tensorHom K L X Y) := by
      apply (Algebra.TensorProduct.liftEquiv (R := K) (S := K)
        (A := BX) (B := BY) (C := L)).symm.injective
      apply Subtype.ext
      apply Prod.ext
      · exact hx.symm.trans (by
          ext f
          simp [Algebra.TensorProduct.liftEquiv, tensorHom,
            MulActionHom.compLeftAlgHom, MulActionHom.fst]
          rfl)
      · exact hy.symm.trans (by
          ext f
          simp [Algebra.TensorProduct.liftEquiv, tensorHom,
            MulActionHom.compLeftAlgHom, MulActionHom.snd]
          rfl)
    change h z₁ = h z₂
    rw [hh, AlgHom.comp_apply, AlgHom.comp_apply, hz]
  have hrank : Module.finrank K (BX ⊗[K] BY) = Module.finrank K BXY := by
    rw [Module.finrank_tensorProduct,
      finrank_equivariantFunctions K L X,
      finrank_equivariantFunctions K L Y,
      finrank_equivariantFunctions K L (X × Y), Nat.card_prod]
  exact ⟨hinj,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp hinj⟩

/-- Equivariant functions on a product as a tensor product of function algebras. -/
noncomputable def tensorEquiv (K L X Y : Type u) [Field K] [Field L]
    [Algebra K L] [IsGalois K L] [IsSepClosed L]
    [MulAction (L ≃ₐ[K] L) X] [MulAction (L ≃ₐ[K] L) Y]
    [Finite X] [Finite Y]
    [ContinuousSMulDiscrete (L ≃ₐ[K] L) X]
    [ContinuousSMulDiscrete (L ≃ₐ[K] L) Y] :
    ((X →[L ≃ₐ[K] L] L) ⊗[K] (Y →[L ≃ₐ[K] L] L)) ≃ₐ[K]
      ((X × Y) →[L ≃ₐ[K] L] L) :=
  AlgEquiv.ofBijective (tensorHom K L X Y)
    (tensorHom_bijective K L X Y)

@[simp] lemma tensorEquiv_tmul [IsGalois K L] [IsSepClosed L]
    [Finite X] [Finite Y]
    [ContinuousSMulDiscrete (L ≃ₐ[K] L) X]
    [ContinuousSMulDiscrete (L ≃ₐ[K] L) Y]
    (f : X →[L ≃ₐ[K] L] L) (g : Y →[L ≃ₐ[K] L] L)
    (x : X) (y : Y) :
    tensorEquiv K L X Y (f ⊗ₜ[K] g) (x, y) = f x * g y := by
  rfl



namespace GenericFiber

variable (K L A : Type u) [Field K] [Field L] [Algebra K L]
variable [IsGalois K L] [IsSepClosed L]
variable [AddCommGroup A] [DistribMulAction (L ≃ₐ[K] L) A]

/-- Addition as an equivariant map. -/
def addHom : A × A →[L ≃ₐ[K] L] A where
  toFun z := z.1 + z.2
  map_smul' g z := by simp

/-- Negation as an equivariant map. -/
def negHom : A →[L ≃ₐ[K] L] A where
  toFun x := -x
  map_smul' g x := by simp

variable [Finite A] [ContinuousSMulDiscrete (L ≃ₐ[K] L) A]

/-- Comultiplication on the algebra of equivariant functions, induced by addition. -/
noncomputable def comulAlgHom :
    (A →[L ≃ₐ[K] L] L) →ₐ[K]
      (A →[L ≃ₐ[K] L] L) ⊗[K] (A →[L ≃ₐ[K] L] L) :=
  (tensorEquiv K L A A).symm.toAlgHom.comp
    (MulActionHom.compLeftAlgHom (L ≃ₐ[K] L) K L (addHom K L A))

/-- Antipode on the algebra of equivariant functions, induced by negation. -/
noncomputable def antipodeAlgHom :
    (A →[L ≃ₐ[K] L] L) →ₐ[K] (A →[L ≃ₐ[K] L] L) :=
  MulActionHom.compLeftAlgHom (L ≃ₐ[K] L) K L (negHom K L A)

/-- Evaluation at zero, with values in the splitting field. -/
noncomputable def counitToL : (A →[L ≃ₐ[K] L] L) →ₐ[K] L :=
  MulActionHom.evalAlgHom (L ≃ₐ[K] L) K A L 0

omit [IsGalois K L] [IsSepClosed L] [Finite A]
  [ContinuousSMulDiscrete (L ≃ₐ[K] L) A] in
lemma counitToL_fixed (f : A →[L ≃ₐ[K] L] L) (g : L ≃ₐ[K] L) :
    g (counitToL K L A f) = counitToL K L A f := by
  change g (f 0) = f 0
  simpa using (map_smul f g (0 : A)).symm

/-- Evaluation at zero, restricted to the fixed field. -/
noncomputable def counitToBot :
    (A →[L ≃ₐ[K] L] L) →ₐ[K] (⊥ : IntermediateField K L) :=
  (counitToL K L A).codRestrict (⊥ : IntermediateField K L).toSubalgebra
    (fun f ↦ (InfiniteGalois.mem_bot_iff_fixed (counitToL K L A f)).mpr
      (counitToL_fixed K L A f))

/-- The counit on the algebra of equivariant functions. -/
noncomputable def counitAlgHom :
    (A →[L ≃ₐ[K] L] L) →ₐ[K] K :=
  (IntermediateField.botEquiv K L).toAlgHom.comp (counitToBot K L A)

@[simp] lemma comulAlgHom_eval (f : A →[L ≃ₐ[K] L] L) (x y : A) :
    tensorEquiv K L A A (comulAlgHom K L A f) (x, y) = f (x + y) := by
  change (tensorEquiv K L A A
    ((tensorEquiv K L A A).symm
      (MulActionHom.compLeftAlgHom (L ≃ₐ[K] L) K L (addHom K L A) f))) (x, y) = _
  rw [AlgEquiv.apply_symm_apply]
  rfl

omit [IsGalois K L] [IsSepClosed L] [Finite A]
  [ContinuousSMulDiscrete (L ≃ₐ[K] L) A] in
@[simp] lemma antipodeAlgHom_eval (f : A →[L ≃ₐ[K] L] L) (x : A) :
    antipodeAlgHom K L A f x = f (-x) := by
  rfl

omit [IsSepClosed L] [Finite A]
  [ContinuousSMulDiscrete (L ≃ₐ[K] L) A] in
@[simp] lemma algebraMap_counitAlgHom (f : A →[L ≃ₐ[K] L] L) :
    algebraMap K L (counitAlgHom K L A f) = f 0 := by
  have hbot (z : (⊥ : IntermediateField K L)) :
      algebraMap K L ((IntermediateField.botEquiv K L) z) = (z : L) := by
    obtain ⟨k, rfl⟩ := (IntermediateField.botEquiv K L).symm.surjective z
    simp
  change algebraMap K L ((IntermediateField.botEquiv K L)
    (counitToBot K L A f)) = f 0
  exact (hbot (counitToBot K L A f)).trans rfl

end GenericFiber
end

namespace GenericFiber

variable (K L A : Type u) [Field K] [Field L] [Algebra K L]
variable [IsGalois K L] [IsSepClosed L]
variable [AddCommGroup A] [DistribMulAction (L ≃ₐ[K] L) A]
variable [Finite A] [ContinuousSMulDiscrete (L ≃ₐ[K] L) A]


/-- The commutative ring structure on the inner tensor product. -/
local instance innerCommRing :
    CommRing ((A →[L ≃ₐ[K] L] L) ⊗[K] (A →[L ≃ₐ[K] L] L)) :=
  Algebra.TensorProduct.instCommRing
/-- The scalar algebra structure on the inner tensor product. -/
local instance innerAlgebra :
    Algebra K ((A →[L ≃ₐ[K] L] L) ⊗[K] (A →[L ≃ₐ[K] L] L)) :=
  Algebra.TensorProduct.instAlgebra
/-- The right-associated equivalence for three equivariant-function factors. -/
noncomputable def tripleEquivRight :
    ((A →[L ≃ₐ[K] L] L) ⊗[K]
      ((A →[L ≃ₐ[K] L] L) ⊗[K] (A →[L ≃ₐ[K] L] L))) ≃ₐ[K]
      ((A × (A × A)) →[L ≃ₐ[K] L] L) :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl)
    (tensorEquiv K L A A)).trans
      (tensorEquiv K L A (A × A))

@[simp] lemma tripleEquivRight_tmul (f : A →[L ≃ₐ[K] L] L)
    (z : (A →[L ≃ₐ[K] L] L) ⊗[K] (A →[L ≃ₐ[K] L] L))
    (x y w : A) :
    tripleEquivRight K L A (f ⊗ₜ[K] z) (x, (y, w)) =
      f x * tensorEquiv K L A A z (y, w) := by
  simp [tripleEquivRight, tensorEquiv, tensorHom,
    Algebra.TensorProduct.congr]
  rfl


lemma tripleEquivRight_map_id_comul
    (z : (A →[L ≃ₐ[K] L] L) ⊗[K] (A →[L ≃ₐ[K] L] L))
    (x y w : A) :
    tripleEquivRight K L A
      (Algebra.TensorProduct.map (AlgHom.id K _)
        (comulAlgHom K L A) z) (x, (y, w)) =
      tensorEquiv K L A A z (x, y + w) := by
  induction z with
  | zero => simp
  | add z₁ z₂ hz₁ hz₂ => simpa using congrArg₂ (· + ·) hz₁ hz₂
  | tmul f g =>
      simp [tripleEquivRight_tmul, comulAlgHom_eval, tensorEquiv_tmul]

lemma tripleEquivRight_assoc_tmul
    (z : (A →[L ≃ₐ[K] L] L) ⊗[K] (A →[L ≃ₐ[K] L] L))
    (f : A →[L ≃ₐ[K] L] L) (x y w : A) :
    tripleEquivRight K L A
      ((Algebra.TensorProduct.assoc K K K _ _ _).toAlgHom (z ⊗ₜ[K] f))
        (x, (y, w)) =
      tensorEquiv K L A A z (x, y) * f w := by
  induction z with
  | zero => simp
  | add z₁ z₂ hz₁ hz₂ =>
      rw [TensorProduct.add_tmul, map_add, map_add]
      change
        tripleEquivRight K L A
            ((Algebra.TensorProduct.assoc K K K _ _ _).toAlgHom (z₁ ⊗ₜ[K] f))
              (x, (y, w)) +
          tripleEquivRight K L A
            ((Algebra.TensorProduct.assoc K K K _ _ _).toAlgHom (z₂ ⊗ₜ[K] f))
              (x, (y, w)) = _
      rw [hz₁, hz₂, map_add]
      change _ * f w + _ * f w = (_ + _) * f w
      exact (add_mul _ _ _).symm
  | tmul f₁ f₂ =>
      change f₁ x * (f₂ y * f w) = (f₁ x * f₂ y) * f w
      exact (mul_assoc _ _ _).symm

lemma tripleEquivRight_assoc_map_comul_id
    (z : (A →[L ≃ₐ[K] L] L) ⊗[K] (A →[L ≃ₐ[K] L] L))
    (x y w : A) :
    tripleEquivRight K L A
      ((Algebra.TensorProduct.assoc K K K _ _ _).toAlgHom
        (Algebra.TensorProduct.map (comulAlgHom K L A)
          (AlgHom.id K _) z)) (x, (y, w)) =
      tensorEquiv K L A A z (x + y, w) := by
  induction z with
  | zero => simp
  | add z₁ z₂ hz₁ hz₂ => simpa using congrArg₂ (· + ·) hz₁ hz₂
  | tmul f g =>
      simp only [Algebra.TensorProduct.map_tmul]
      change tripleEquivRight K L A
        ((Algebra.TensorProduct.assoc K K K _ _ _).toAlgHom
          (comulAlgHom K L A f ⊗ₜ[K] g)) (x, (y, w)) =
        f (x + y) * g w
      rw [tripleEquivRight_assoc_tmul, comulAlgHom_eval]

lemma coassocAlgHom :
    (Algebra.TensorProduct.assoc K K K
      (A →[L ≃ₐ[K] L] L) (A →[L ≃ₐ[K] L] L)
      (A →[L ≃ₐ[K] L] L)).toAlgHom.comp
      ((Algebra.TensorProduct.map (comulAlgHom K L A)
        (AlgHom.id K _)).comp (comulAlgHom K L A)) =
    (Algebra.TensorProduct.map (AlgHom.id K _)
      (comulAlgHom K L A)).comp (comulAlgHom K L A) := by
  apply AlgHom.ext
  intro f
  apply (tripleEquivRight K L A).injective
  ext z
  rcases z with ⟨x, y, w⟩
  simp only [AlgHom.comp_apply]
  rw [tripleEquivRight_assoc_map_comul_id,
    tripleEquivRight_map_id_comul, comulAlgHom_eval, comulAlgHom_eval]
  rw [add_assoc]

lemma lid_map_counit_id_eval
    (z : (A →[L ≃ₐ[K] L] L) ⊗[K] (A →[L ≃ₐ[K] L] L))
    (y : A) :
    (Algebra.TensorProduct.lid K (A →[L ≃ₐ[K] L] L))
      (Algebra.TensorProduct.map (counitAlgHom K L A) (AlgHom.id K _) z) y =
      tensorEquiv K L A A z (0, y) := by
  induction z with
  | zero => simp
  | add z₁ z₂ hz₁ hz₂ =>
      simp only [map_add]
      change
        (Algebra.TensorProduct.lid K (A →[L ≃ₐ[K] L] L)
          (Algebra.TensorProduct.map (counitAlgHom K L A) (AlgHom.id K _) z₁)) y +
        (Algebra.TensorProduct.lid K (A →[L ≃ₐ[K] L] L)
          (Algebra.TensorProduct.map (counitAlgHom K L A) (AlgHom.id K _) z₂)) y =
        tensorEquiv K L A A z₁ (0, y) + tensorEquiv K L A A z₂ (0, y)
      exact congrArg₂ (· + ·) hz₁ hz₂
  | tmul f g =>
      simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lid_tmul,
        tensorEquiv_tmul]
      change counitAlgHom K L A f • g y = f 0 * g y
      rw [Algebra.smul_def, algebraMap_counitAlgHom]

lemma rid_map_id_counit_eval
    (z : (A →[L ≃ₐ[K] L] L) ⊗[K] (A →[L ≃ₐ[K] L] L))
    (x : A) :
    (Algebra.TensorProduct.rid K K (A →[L ≃ₐ[K] L] L))
      (Algebra.TensorProduct.map (AlgHom.id K _)
        (counitAlgHom K L A) z) x =
      tensorEquiv K L A A z (x, 0) := by
  induction z with
  | zero => simp
  | add z₁ z₂ hz₁ hz₂ =>
      simp only [map_add]
      change
        (Algebra.TensorProduct.rid K K (A →[L ≃ₐ[K] L] L)
          (Algebra.TensorProduct.map (AlgHom.id K _) (counitAlgHom K L A) z₁)) x +
        (Algebra.TensorProduct.rid K K (A →[L ≃ₐ[K] L] L)
          (Algebra.TensorProduct.map (AlgHom.id K _) (counitAlgHom K L A) z₂)) x =
        tensorEquiv K L A A z₁ (x, 0) + tensorEquiv K L A A z₂ (x, 0)
      exact congrArg₂ (· + ·) hz₁ hz₂
  | tmul f g =>
      simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.rid_tmul,
        tensorEquiv_tmul]
      change counitAlgHom K L A g • f x = f x * g 0
      rw [Algebra.smul_def, algebraMap_counitAlgHom, mul_comm]

lemma rTensorCounitAlgHom :
    (Algebra.TensorProduct.map (counitAlgHom K L A)
      (AlgHom.id K _)).comp (comulAlgHom K L A) =
      (Algebra.TensorProduct.lid K (A →[L ≃ₐ[K] L] L)).symm.toAlgHom := by
  apply AlgHom.ext
  intro f
  apply (Algebra.TensorProduct.lid K (A →[L ≃ₐ[K] L] L)).injective
  ext y
  simp only [AlgHom.comp_apply]
  rw [lid_map_counit_id_eval, comulAlgHom_eval, zero_add]
  exact congrArg (fun g : A →[L ≃ₐ[K] L] L ↦ g y)
    ((Algebra.TensorProduct.lid K (A →[L ≃ₐ[K] L] L)).apply_symm_apply f).symm

lemma lTensorCounitAlgHom :
    (Algebra.TensorProduct.map (AlgHom.id K _)
      (counitAlgHom K L A)).comp (comulAlgHom K L A) =
      (Algebra.TensorProduct.rid K K (A →[L ≃ₐ[K] L] L)).symm.toAlgHom := by
  apply AlgHom.ext
  intro f
  apply (Algebra.TensorProduct.rid K K (A →[L ≃ₐ[K] L] L)).injective
  ext x
  simp only [AlgHom.comp_apply]
  rw [rid_map_id_counit_eval, comulAlgHom_eval, add_zero]
  exact congrArg (fun g : A →[L ≃ₐ[K] L] L ↦ g x)
    ((Algebra.TensorProduct.rid K K (A →[L ≃ₐ[K] L] L)).apply_symm_apply f).symm

/-- The canonical bialgebra of equivariant functions on a finite Galois module. -/
@[instance_reducible]
noncomputable def bialgebra :
    Bialgebra K (A →[L ≃ₐ[K] L] L) :=
  Bialgebra.ofAlgHom (comulAlgHom K L A) (counitAlgHom K L A)
    (coassocAlgHom K L A) (rTensorCounitAlgHom K L A)
      (lTensorCounitAlgHom K L A)



/-- The local canonical bialgebra instance on equivariant functions. -/
noncomputable local instance genericBialgebra :
    Bialgebra K (A →[L ≃ₐ[K] L] L) :=
  bialgebra K L A

lemma lift_antipode_id_eval
    (z : (A →[L ≃ₐ[K] L] L) ⊗[K] (A →[L ≃ₐ[K] L] L))
    (x : A) :
    Algebra.TensorProduct.lift (antipodeAlgHom K L A) (AlgHom.id K _)
      (fun _ _ ↦ Commute.all _ _) z x =
      tensorEquiv K L A A z (-x, x) := by
  induction z with
  | zero => simp
  | add z₁ z₂ hz₁ hz₂ =>
      simp only [map_add]
      change
        Algebra.TensorProduct.lift (antipodeAlgHom K L A) (AlgHom.id K _)
            (fun _ _ ↦ Commute.all _ _) z₁ x +
          Algebra.TensorProduct.lift (antipodeAlgHom K L A) (AlgHom.id K _)
            (fun _ _ ↦ Commute.all _ _) z₂ x =
        tensorEquiv K L A A z₁ (-x, x) +
          tensorEquiv K L A A z₂ (-x, x)
      exact congrArg₂ (· + ·) hz₁ hz₂
  | tmul f g =>
      simp only [Algebra.TensorProduct.lift_tmul, tensorEquiv_tmul]
      change f (-x) * g x = f (-x) * g x
      rfl

lemma lift_id_antipode_eval
    (z : (A →[L ≃ₐ[K] L] L) ⊗[K] (A →[L ≃ₐ[K] L] L))
    (x : A) :
    Algebra.TensorProduct.lift (AlgHom.id K _) (antipodeAlgHom K L A)
      (fun _ _ ↦ Commute.all _ _) z x =
      tensorEquiv K L A A z (x, -x) := by
  induction z with
  | zero => simp
  | add z₁ z₂ hz₁ hz₂ =>
      simp only [map_add]
      change
        Algebra.TensorProduct.lift (AlgHom.id K _) (antipodeAlgHom K L A)
            (fun _ _ ↦ Commute.all _ _) z₁ x +
          Algebra.TensorProduct.lift (AlgHom.id K _) (antipodeAlgHom K L A)
            (fun _ _ ↦ Commute.all _ _) z₂ x =
        tensorEquiv K L A A z₁ (x, -x) +
          tensorEquiv K L A A z₂ (x, -x)
      exact congrArg₂ (· + ·) hz₁ hz₂
  | tmul f g =>
      simp only [Algebra.TensorProduct.lift_tmul, tensorEquiv_tmul]
      change f x * g (-x) = f x * g (-x)
      rfl

lemma antipode_mul_id :
    (Algebra.TensorProduct.lift (antipodeAlgHom K L A) (AlgHom.id K _)
      (fun _ _ ↦ Commute.all _ _)).comp (Bialgebra.comulAlgHom K _) =
    (Algebra.ofId K _).comp (Bialgebra.counitAlgHom K _) := by
  apply AlgHom.ext
  intro f
  ext x
  change Algebra.TensorProduct.lift (antipodeAlgHom K L A) (AlgHom.id K _)
      (fun _ _ ↦ Commute.all _ _) (comulAlgHom K L A f) x =
    algebraMap K (A →[L ≃ₐ[K] L] L) (counitAlgHom K L A f) x
  rw [lift_antipode_id_eval, comulAlgHom_eval, neg_add_cancel]
  change f 0 = algebraMap K L (counitAlgHom K L A f)
  exact (algebraMap_counitAlgHom K L A f).symm

lemma id_mul_antipode :
    (Algebra.TensorProduct.lift (AlgHom.id K _) (antipodeAlgHom K L A)
      (fun _ _ ↦ Commute.all _ _)).comp (Bialgebra.comulAlgHom K _) =
    (Algebra.ofId K _).comp (Bialgebra.counitAlgHom K _) := by
  apply AlgHom.ext
  intro f
  ext x
  change Algebra.TensorProduct.lift (AlgHom.id K _) (antipodeAlgHom K L A)
      (fun _ _ ↦ Commute.all _ _) (comulAlgHom K L A f) x =
    algebraMap K (A →[L ≃ₐ[K] L] L) (counitAlgHom K L A f) x
  rw [lift_id_antipode_eval, comulAlgHom_eval, add_neg_cancel]
  change f 0 = algebraMap K L (counitAlgHom K L A f)
  exact (algebraMap_counitAlgHom K L A f).symm

/-- The canonical Hopf algebra of equivariant functions on a finite Galois module. -/
@[instance_reducible]
noncomputable def hopfAlgebra :
    HopfAlgebra K (A →[L ≃ₐ[K] L] L) :=
  HopfAlgebra.ofAlgHom (antipodeAlgHom K L A)
    (antipode_mul_id K L A) (id_mul_antipode K L A)




/-- The local convolution monoid on geometric points. -/
noncomputable local instance pointsMonoid :
    Monoid ((A →[L ≃ₐ[K] L] L) →ₐ[K] L) :=
  instMonoidAlgHom_fLT K L

/-- The Galois action on geometric points, compatible with convolution. -/
noncomputable local instance pointsMulDistribMulAction :
    MulDistribMulAction (L ≃ₐ[K] L)
      ((A →[L ≃ₐ[K] L] L) →ₐ[K] L) :=
  instMulDistribMulActionAlgEquivAlgHom_fLT K L


lemma tensorEquiv_eq_lift_eval
    (z : (A →[L ≃ₐ[K] L] L) ⊗[K] (A →[L ≃ₐ[K] L] L))
    (x y : A) :
    tensorEquiv K L A A z (x, y) =
      Algebra.TensorProduct.lift
        (MulActionHom.evalAlgHom (L ≃ₐ[K] L) K A L x)
        (MulActionHom.evalAlgHom (L ≃ₐ[K] L) K A L y)
        (fun _ _ ↦ Commute.all _ _) z := by
  induction z with
  | zero => simp
  | add z₁ z₂ hz₁ hz₂ =>
      simp only [map_add]
      change tensorEquiv K L A A z₁ (x, y) +
          tensorEquiv K L A A z₂ (x, y) = _
      exact congrArg₂ (· + ·) hz₁ hz₂
  | tmul f g =>
      simp only [tensorEquiv_tmul, Algebra.TensorProduct.lift_tmul,
        MulActionHom.evalAlgHom_apply]

/-- Evaluation identifies group elements with geometric points additively. -/
noncomputable def evalAddHom :
    A →+[L ≃ₐ[K] L] Additive ((A →[L ≃ₐ[K] L] L) →ₐ[K] L) where
  toFun x := Additive.ofMul (MulActionHom.evalAlgHom (L ≃ₐ[K] L) K A L x)
  map_zero' := by
    change MulActionHom.evalAlgHom (L ≃ₐ[K] L) K A L 0 =
      (1 : (A →[L ≃ₐ[K] L] L) →ₐ[K] L)
    ext f
    change f 0 = algebraMap K L (counitAlgHom K L A f)
    exact (algebraMap_counitAlgHom K L A f).symm
  map_add' x y := by
    change MulActionHom.evalAlgHom (L ≃ₐ[K] L) K A L (x + y) =
      MulActionHom.evalAlgHom (L ≃ₐ[K] L) K A L x * MulActionHom.evalAlgHom (L ≃ₐ[K] L) K A L y
    ext f
    change f (x + y) =
      Algebra.TensorProduct.lift
        (MulActionHom.evalAlgHom (L ≃ₐ[K] L) K A L x)
        (MulActionHom.evalAlgHom (L ≃ₐ[K] L) K A L y)
        (fun _ _ ↦ Commute.all _ _) (comulAlgHom K L A f)
    rw [← tensorEquiv_eq_lift_eval, comulAlgHom_eval]
  map_smul' g x := by
    change MulActionHom.evalAlgHom (L ≃ₐ[K] L) K A L (g • x) =
      g • MulActionHom.evalAlgHom (L ≃ₐ[K] L) K A L x
    exact (MulActionHom.evalAlgHom (L ≃ₐ[K] L) K A L).map_smul g x

lemma evalAddHom_bijective :
    Function.Bijective (evalAddHom K L A) := by
  constructor
  · intro x y h
    apply (InfiniteGalois.evalAlgHom_bijective K L A).1
    exact congrArg Additive.toMul h
  · intro y
    obtain ⟨x, hx⟩ :=
      (InfiniteGalois.evalAlgHom_bijective K L A).2 y.toMul
    exact ⟨x, congrArg Additive.ofMul hx⟩

/-- The equivalence between a finite Galois module and its geometric points. -/
noncomputable def pointsEquiv :
    Additive ((A →[L ≃ₐ[K] L] L) →ₐ[K] L) ≃+ A :=
  (AddEquiv.ofBijective (evalAddHom K L A).toAddMonoidHom
    (evalAddHom_bijective K L A)).symm

/-- The equivariant additive equivalence with the geometric points of the generic fibre. -/
noncomputable def pointsEquivariantAddEquiv :
    Additive ((A →[L ≃ₐ[K] L] L) →ₐ[K] L) →+[L ≃ₐ[K] L] A where
  toFun := pointsEquiv K L A
  map_zero' := (pointsEquiv K L A).map_zero
  map_add' := (pointsEquiv K L A).map_add
  map_smul' g x := by
    have hinv (z : Additive ((A →[L ≃ₐ[K] L] L) →ₐ[K] L)) :
        evalAddHom K L A (pointsEquiv K L A z) = z := by
      change
        (AddEquiv.ofBijective (evalAddHom K L A).toAddMonoidHom
          (evalAddHom_bijective K L A))
            ((AddEquiv.ofBijective (evalAddHom K L A).toAddMonoidHom
              (evalAddHom_bijective K L A)).symm z) = z
      exact AddEquiv.apply_symm_apply _ z
    apply (evalAddHom_bijective K L A).1
    calc
      evalAddHom K L A (pointsEquiv K L A (g • x)) = g • x := hinv (g • x)
      _ = g • evalAddHom K L A (pointsEquiv K L A x) := by rw [hinv x]
      _ = evalAddHom K L A (g • pointsEquiv K L A x) :=
        ((evalAddHom K L A).map_smul g (pointsEquiv K L A x)).symm

lemma pointsEquivariantAddEquiv_bijective :
    Function.Bijective (pointsEquivariantAddEquiv K L A) :=
  (pointsEquiv K L A).bijective


end GenericFiber

namespace GenericFiber

/-- The canonical coalgebra structure on the equivariant function algebra. -/
noncomputable instance canonicalCoalgebraStruct (K L A : Type u)
    [Field K] [Field L] [Algebra K L] [IsGalois K L] [IsSepClosed L]
    [AddCommGroup A] [DistribMulAction (L ≃ₐ[K] L) A] [Finite A]
    [ContinuousSMulDiscrete (L ≃ₐ[K] L) A] :
    CoalgebraStruct K (A →[L ≃ₐ[K] L] L) :=
  (bialgebra K L A).toCoalgebra.toCoalgebraStruct

variable (K L X Y : Type u) [Field K] [Field L] [Algebra K L]
variable [IsGalois K L] [IsSepClosed L]
variable [AddCommGroup X] [DistribMulAction (L ≃ₐ[K] L) X]
variable [AddCommGroup Y] [DistribMulAction (L ≃ₐ[K] L) Y]
variable [Finite X] [Finite Y]
variable [ContinuousSMulDiscrete (L ≃ₐ[K] L) X]
variable [ContinuousSMulDiscrete (L ≃ₐ[K] L) Y]


/-- Pullback of equivariant functions along an equivariant additive map. -/
def pullbackAlgHom (q : X →+[L ≃ₐ[K] L] Y) :
    (Y →[L ≃ₐ[K] L] L) →ₐ[K] (X →[L ≃ₐ[K] L] L) :=
  MulActionHom.compLeftAlgHom (L ≃ₐ[K] L) K L q.toMulActionHom

omit [IsGalois K L] [IsSepClosed L] [Finite X] [Finite Y]
  [ContinuousSMulDiscrete (L ≃ₐ[K] L) X]
  [ContinuousSMulDiscrete (L ≃ₐ[K] L) Y] in
@[simp] lemma pullbackAlgHom_apply (q : X →+[L ≃ₐ[K] L] Y)
    (f : Y →[L ≃ₐ[K] L] L) (x : X) :
    pullbackAlgHom K L X Y q f x = f (q x) := rfl

omit [IsGalois K L] [IsSepClosed L] [Finite X] [Finite Y]
  [ContinuousSMulDiscrete (L ≃ₐ[K] L) X]
  [ContinuousSMulDiscrete (L ≃ₐ[K] L) Y] in
lemma pullbackAlgHom_injective (q : X →+[L ≃ₐ[K] L] Y)
    (hq : Function.Surjective q) :
    Function.Injective (pullbackAlgHom K L X Y q) := by
  intro f g h
  ext y
  obtain ⟨x, rfl⟩ := hq y
  exact congrFun (congrArg DFunLike.coe h) x

omit [IsGalois K L] [IsSepClosed L] [Finite X] [Finite Y]
  [ContinuousSMulDiscrete (L ≃ₐ[K] L) X]
  [ContinuousSMulDiscrete (L ≃ₐ[K] L) Y] in
lemma antipodeAlgHom_comp_pullbackAlgHom (q : X →+[L ≃ₐ[K] L] Y) :
    (antipodeAlgHom K L X).comp (pullbackAlgHom K L X Y q) =
      (pullbackAlgHom K L X Y q).comp (antipodeAlgHom K L Y) := by
  ext f x
  change f (q (-x)) = f (-(q x))
  rw [map_neg]

lemma tensorEquiv_map_pullbackAlgHom (q : X →+[L ≃ₐ[K] L] Y)
    (z : (Y →[L ≃ₐ[K] L] L) ⊗[K] (Y →[L ≃ₐ[K] L] L)) (x x' : X) :
    tensorEquiv K L X X
        (TensorProduct.map (pullbackAlgHom K L X Y q).toLinearMap
          (pullbackAlgHom K L X Y q).toLinearMap z) (x, x') =
      tensorEquiv K L Y Y z (q x, q x') := by
  induction z with
  | zero => simp
  | add z₁ z₂ hz₁ hz₂ => simpa using congrArg₂ (· + ·) hz₁ hz₂
  | tmul f₁ f₂ => simp [tensorEquiv_tmul, pullbackAlgHom_apply]

/-- Pullback along an equivariant additive map as a coalgebra homomorphism. -/
noncomputable def pullbackCoalgHom (q : X →+[L ≃ₐ[K] L] Y) :
    (Y →[L ≃ₐ[K] L] L) →ₗc[K] (X →[L ≃ₐ[K] L] L) where
  __ := (pullbackAlgHom K L X Y q).toLinearMap
  counit_comp := by
    apply LinearMap.ext
    intro f
    apply (algebraMap K L).injective
    change algebraMap K L (counitAlgHom K L X (pullbackAlgHom K L X Y q f)) =
      algebraMap K L (counitAlgHom K L Y f)
    rw [algebraMap_counitAlgHom, algebraMap_counitAlgHom]
    exact congrArg f q.map_zero
  map_comp_comul := by
    apply LinearMap.ext
    intro f
    apply (tensorEquiv K L X X).injective
    ext z
    rcases z with ⟨x, x'⟩
    change tensorEquiv K L X X
        (TensorProduct.map (pullbackAlgHom K L X Y q).toLinearMap
          (pullbackAlgHom K L X Y q).toLinearMap (comulAlgHom K L Y f)) (x, x') =
      tensorEquiv K L X X (comulAlgHom K L X (pullbackAlgHom K L X Y q f)) (x, x')
    rw [tensorEquiv_map_pullbackAlgHom, comulAlgHom_eval, comulAlgHom_eval]
    change f (q x + q x') = f (q (x + x'))
    rw [q.map_add]

/-- Pullback along an equivariant additive map as a bialgebra homomorphism. -/
noncomputable def pullbackBialgHom (q : X →+[L ≃ₐ[K] L] Y) :
    (Y →[L ≃ₐ[K] L] L) →ₐc[K] (X →[L ≃ₐ[K] L] L) where
  __ := pullbackAlgHom K L X Y q
  __ := pullbackCoalgHom K L X Y q



end GenericFiber


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

/-- A Galois module admitting a finite flat model has finite underlying type. -/
lemma IsFiniteFlat.finite (hX : GaloisModule.IsFiniteFlat R K L X) : Finite X := by
  rcases hX with ⟨H, _, _, _, _, f, hf⟩
  let _ : Module.Finite K (K ⊗[R] H) :=
    Algebra.FormallyUnramified.finite_of_free K (K ⊗[R] H)
  let _ : Module.Free K (K ⊗[R] H) := Module.Free.of_divisionRing K (K ⊗[R] H)
  let _ : Finite (K ⊗[R] H →ₐ[K] L) := inferInstance
  let _ : Finite (Additive (K ⊗[R] H →ₐ[K] L)) := inferInstance
  exact Finite.of_surjective f hf.2

/-- A surjective equivariant image of a finite-flat Galois module is finite and has continuous
discrete Galois action. These are the two generic-fibre inputs for the quotient construction. -/
lemma IsFiniteFlat.quotient_finite_continuous {Y : Type w} [AddCommGroup Y]
    [DistribMulAction (L ≃ₐ[K] L) Y]
    (hX : GaloisModule.IsFiniteFlat R K L X)
    (q : X →+[L ≃ₐ[K] L] Y) (hq : Function.Surjective q) :
    Finite Y ∧ ContinuousSMulDiscrete (L ≃ₐ[K] L) Y := by
  let _ : Finite X := hX.finite R K L X
  let _ : ContinuousSMulDiscrete (L ≃ₐ[K] L) X := hX.continuousSMulDiscrete R K L X
  exact ⟨Finite.of_surjective q hq,
    ContinuousSMulDiscrete.of_surjective_map q hq⟩


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
open scoped TensorProduct

namespace HopfAlgebra.IntegralClosure

variable (R K H : Type u) [CommRing R] [Field K] [Algebra R K]
variable [CommRing H] [Algebra R H] [IsFractionRing R K]

/-- The integral contraction of a subalgebra of the generic fibre. -/
def contraction (C : Subalgebra K (K ⊗[R] H)) : Subalgebra R H :=
  (C.restrictScalars R).comap Algebra.TensorProduct.includeRight

omit [IsFractionRing R K] in
lemma contraction_toSubmodule (C : Subalgebra K (K ⊗[R] H)) :
    (contraction R K H C).toSubmodule =
      (C.toSubmodule.restrictScalars R).comap
        (TensorProduct.mk R K H 1) := by
  rfl

lemma localized_contraction (C : Subalgebra K (K ⊗[R] H)) :
    (contraction R K H C).toSubmodule.localized' K (nonZeroDivisors R)
      (TensorProduct.mk R K H 1) = C.toSubmodule := by
  rw [contraction_toSubmodule]
  exact (Submodule.localized'gi K (nonZeroDivisors R)
    (TensorProduct.mk R K H 1)).l_u_eq C.toSubmodule

/-- The canonical algebra map from a contraction into its generic-fibre subalgebra. -/
def contractionMap (C : Subalgebra K (K ⊗[R] H)) :
    contraction R K H C →ₐ[R] C :=
  (Algebra.TensorProduct.includeRight : H →ₐ[R] K ⊗[R] H).comp
      (contraction R K H C).val |>.codRestrict (C.restrictScalars R) fun x ↦ x.property

/-- Localization identifies a contraction with the original generic-fibre submodule. -/
noncomputable def localizedContractionEquiv (C : Subalgebra K (K ⊗[R] H)) :
    (contraction R K H C).toSubmodule.localized' K (nonZeroDivisors R)
        (TensorProduct.mk R K H 1) ≃ₗ[K] C.toSubmodule :=
  LinearEquiv.ofEq _ _ (localized_contraction R K H C)

noncomputable instance contractionMap_isLocalized
    (C : Subalgebra K (K ⊗[R] H)) :
    IsLocalizedModule (nonZeroDivisors R) (contractionMap R K H C).toLinearMap := by
  let e := localizedContractionEquiv R K H C
  let g := (contraction R K H C).toSubmodule.toLocalized' K
    (nonZeroDivisors R) (TensorProduct.mk R K H 1)
  have hg : (contractionMap R K H C).toLinearMap =
      e.toLinearMap.restrictScalars R ∘ₗ g := by
    ext x
    rfl
  rw [hg]
  exact IsLocalizedModule.of_linearEquiv (nonZeroDivisors R) g
    (e.restrictScalars R)

/-- The canonical base-change map from a contraction to its generic fibre. -/
noncomputable def baseChangeMap (C : Subalgebra K (K ⊗[R] H)) :
    K ⊗[R] contraction R K H C →ₐ[K] C :=
  Algebra.TensorProduct.liftEquivRight R K (contraction R K H C) C
    (contractionMap R K H C)

lemma baseChangeMap_bijective (C : Subalgebra K (K ⊗[R] H)) :
    Function.Bijective (baseChangeMap R K H C) := by
  let D := contraction R K H C
  let f : D →ₗ[R] K ⊗[R] D := TensorProduct.mk R K D 1
  let g : D →ₗ[R] C := (contractionMap R K H C).toLinearMap
  let e := IsLocalizedModule.linearEquiv (nonZeroDivisors R) f g
  have he : (baseChangeMap R K H C).toLinearMap.restrictScalars R = e.toLinearMap := by
    apply IsLocalizedModule.linearMap_ext (nonZeroDivisors R) f g
    ext x
    simp only [LinearMap.comp_apply, LinearMap.coe_restrictScalars]
    dsimp only [e]
    have hx := IsLocalizedModule.linearEquiv_apply
      (nonZeroDivisors R) f g x
    exact congrArg Subtype.val <| calc
      (baseChangeMap R K H C).toLinearMap (f x) = g x := by
        simp [f, g, baseChangeMap, Algebra.TensorProduct.liftEquivRight]
      _ = (IsLocalizedModule.linearEquiv (nonZeroDivisors R) f g) (f x) := hx.symm
  have he' (x : K ⊗[R] D) : baseChangeMap R K H C x = e x :=
    LinearMap.congr_fun he x
  constructor
  · intro x y hxy
    apply e.injective
    rw [← he' x, ← he' y, hxy]
  · intro y
    obtain ⟨x, hx⟩ := e.surjective y
    exact ⟨x, (he' x).trans hx⟩

/-- Base change of a contraction is algebra-equivalent to the original subalgebra. -/
noncomputable def baseChangeEquiv (C : Subalgebra K (K ⊗[R] H)) :
    K ⊗[R] contraction R K H C ≃ₐ[K] C :=
  AlgEquiv.ofBijective (baseChangeMap R K H C) (baseChangeMap_bijective R K H C)

omit [IsFractionRing R K] in
lemma contraction_finite [IsNoetherianRing R] [Module.Finite R H]
    (C : Subalgebra K (K ⊗[R] H)) :
    Module.Finite R (contraction R K H C) := by
  let D := contraction R K H C
  change Module.Finite R D.toSubmodule
  rw [Module.Finite.iff_fg]
  exact Submodule.FG.of_le Module.Finite.fg_top le_top

/-- The map from the quotient by a contraction to the corresponding generic quotient. -/
def contractionQuotientMap (C : Subalgebra K (K ⊗[R] H)) :
    Ideal.ModuleQuotient (contraction R K H C).toSubmodule →ₗ[R]
      Ideal.ModuleQuotient C.toSubmodule :=
  (contraction R K H C).toSubmodule.liftQ
    ((C.toSubmodule.mkQ.restrictScalars R).comp (TensorProduct.mk R K H 1))
    (by
      intro x hx
      rw [LinearMap.mem_ker]
      rw [LinearMap.comp_apply]
      change Submodule.Quotient.mk ((TensorProduct.mk R K H 1) x) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact hx)

omit [IsFractionRing R K] in
lemma contractionQuotientMap_injective (C : Subalgebra K (K ⊗[R] H)) :
    Function.Injective (contractionQuotientMap R K H C) := by
  intro x y hxy
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
  apply (Submodule.Quotient.eq (contraction R K H C).toSubmodule).2
  change TensorProduct.mk R K H 1 (x - y) ∈ C
  have hmem : TensorProduct.mk R K H 1 x - TensorProduct.mk R K H 1 y ∈ C := by
    apply (Submodule.Quotient.eq C.toSubmodule).1
    exact hxy
  rw [(TensorProduct.mk R K H 1).map_sub]
  exact hmem

lemma contraction_quotient_isTorsionFree [IsDomain R]
    (C : Subalgebra K (K ⊗[R] H)) :
    Module.IsTorsionFree R
      (Ideal.ModuleQuotient (contraction R K H C).toSubmodule) := by
  let _ : Module.IsTorsionFree R (Ideal.ModuleQuotient C.toSubmodule) :=
    Module.IsTorsionFree.trans_faithfulSMul R K _
  exact Function.Injective.moduleIsTorsionFree
    (contractionQuotientMap R K H C)
    (contractionQuotientMap_injective R K H C)
    (fun r x ↦ (contractionQuotientMap R K H C).map_smul r x)

omit [IsFractionRing R K] in
lemma contraction_flat [Module.IsTorsionFree R H]
    [IsDedekindDomain R] (C : Subalgebra K (K ⊗[R] H)) :
    Module.Flat R (contraction R K H C) := by
  infer_instance

end HopfAlgebra.IntegralClosure

namespace HopfAlgebra.IntegralClosure

variable (R K H : Type u) [CommRing R] [Field K] [Algebra R K]
variable [CommRing H] [Algebra R H] [IsFractionRing R K]

/-- A linear section of the quotient by a finite projective contraction. -/
noncomputable def quotientSection (C : Subalgebra K (K ⊗[R] H))
    [Module.Projective R H]
    [Module.Projective R
      (Ideal.ModuleQuotient (contraction R K H C).toSubmodule)] :
    Ideal.ModuleQuotient (contraction R K H C).toSubmodule →ₗ[R] H :=
  Classical.choose <| (Module.Projective.iff_split_of_projective
    (contraction R K H C).toSubmodule.mkQ
    (Submodule.mkQ_surjective _)).mp inferInstance

omit [IsFractionRing R K] in
lemma quotientSection_spec (C : Subalgebra K (K ⊗[R] H))
    [Module.Projective R H]
    [Module.Projective R
      (Ideal.ModuleQuotient (contraction R K H C).toSubmodule)] :
    (contraction R K H C).toSubmodule.mkQ ∘ₗ quotientSection R K H C =
      LinearMap.id :=
  Classical.choose_spec <| (Module.Projective.iff_split_of_projective
    (contraction R K H C).toSubmodule.mkQ
    (Submodule.mkQ_surjective _)).mp inferInstance

/-- A linear retraction from the ambient algebra onto a projective contraction. -/
noncomputable def retraction (C : Subalgebra K (K ⊗[R] H))
    [Module.Projective R H]
    [Module.Projective R
      (Ideal.ModuleQuotient (contraction R K H C).toSubmodule)] :
    H →ₗ[R] contraction R K H C where
  toFun h :=
    ⟨h - quotientSection R K H C
      ((contraction R K H C).toSubmodule.mkQ h), by
      have hs := LinearMap.congr_fun (quotientSection_spec R K H C)
        ((contraction R K H C).toSubmodule.mkQ h)
      rw [LinearMap.comp_apply, LinearMap.id_apply] at hs
      have hd : h - quotientSection R K H C
          ((contraction R K H C).toSubmodule.mkQ h) ∈
          (contraction R K H C).toSubmodule :=
        (Submodule.Quotient.eq (contraction R K H C).toSubmodule).1 hs.symm
      exact hd⟩
  map_add' x y := by
    apply Subtype.ext
    change x + y - quotientSection R K H C
        ((contraction R K H C).toSubmodule.mkQ (x + y)) =
      (x - quotientSection R K H C ((contraction R K H C).toSubmodule.mkQ x)) +
      (y - quotientSection R K H C ((contraction R K H C).toSubmodule.mkQ y))
    rw [map_add, map_add]
    abel
  map_smul' r x := by
    apply Subtype.ext
    change r • x - quotientSection R K H C
        ((contraction R K H C).toSubmodule.mkQ (r • x)) =
      r • (x - quotientSection R K H C
        ((contraction R K H C).toSubmodule.mkQ x))
    rw [map_smul, map_smul, smul_sub]

omit [IsFractionRing R K] in
lemma retraction_comp_val (C : Subalgebra K (K ⊗[R] H))
    [Module.Projective R H]
    [Module.Projective R
      (Ideal.ModuleQuotient (contraction R K H C).toSubmodule)] :
    (retraction R K H C).comp
      (contraction R K H C).val.toLinearMap = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change x - quotientSection R K H C
      ((contraction R K H C).toSubmodule.mkQ x) = x
  have hx : (contraction R K H C).toSubmodule.mkQ x = 0 :=
    (Submodule.Quotient.mk_eq_zero (contraction R K H C).toSubmodule).2 x.property
  rw [hx, map_zero, sub_zero]

omit [IsFractionRing R K] in
lemma tensor_val_injective (C : Subalgebra K (K ⊗[R] H))
    [Module.Projective R H]
    [Module.Projective R
      (Ideal.ModuleQuotient (contraction R K H C).toSubmodule)] :
    Function.Injective (TensorProduct.map
      (contraction R K H C).val.toLinearMap
      (contraction R K H C).val.toLinearMap) := by
  apply Function.LeftInverse.injective
    (g := TensorProduct.map (retraction R K H C) (retraction R K H C))
  intro z
  rw [TensorProduct.map_map]
  simp only [retraction_comp_val, TensorProduct.map_id]
  rfl

end HopfAlgebra.IntegralClosure

namespace HopfAlgebra.IntegralClosure

variable (R K H : Type u) [CommRing R] [Field K] [Algebra R K]
variable [CommRing H] [Algebra R H] [IsFractionRing R K]

/-- The base change of the linear retraction onto a contraction. -/
noncomputable def localizedRetraction (C : Subalgebra K (K ⊗[R] H))
    [Module.Projective R H]
    [Module.Projective R
      (Ideal.ModuleQuotient (contraction R K H C).toSubmodule)] :
    K ⊗[R] H →ₗ[K] K ⊗[R] contraction R K H C :=
  TensorProduct.AlgebraTensorModule.lTensor K K (retraction R K H C)

lemma baseChangeMap_localizedRetraction_val
    (C : Subalgebra K (K ⊗[R] H))
    [Module.Projective R H]
    [Module.Projective R
      (Ideal.ModuleQuotient (contraction R K H C).toSubmodule)]
    (c : C) :
    baseChangeMap R K H C (localizedRetraction R K H C c.1) = c := by
  let D := contraction R K H C
  let g : D →ₗ[R] C := (contractionMap R K H C).toLinearMap
  have heq :
      ((baseChangeMap R K H C).toLinearMap.comp
        ((localizedRetraction R K H C).comp C.val.toLinearMap)).restrictScalars R =
      (LinearMap.id (R := K) (M := C)).restrictScalars R := by
    apply IsLocalizedModule.linearMap_ext (nonZeroDivisors R) g g
    apply LinearMap.ext
    intro d
    have hd : retraction R K H C d.1 = d :=
      LinearMap.congr_fun (retraction_comp_val R K H C) d
    have hC : baseChangeMap R K H C
        (1 ⊗ₜ[R] retraction R K H C d.1) = contractionMap R K H C d := by
      rw [hd]
      change (Algebra.TensorProduct.lift (Algebra.ofId K C)
        (contractionMap R K H C) (fun _ _ ↦ Commute.all _ _) (1 ⊗ₜ[R] d)) =
          contractionMap R K H C d
      rw [Algebra.TensorProduct.lift_tmul]
      simp
    change baseChangeMap R K H C
      (localizedRetraction R K H C (contractionMap R K H C d).1) =
        contractionMap R K H C d
    rw [show (contractionMap R K H C d).1 =
      Algebra.TensorProduct.includeRight d.1 from rfl]
    change baseChangeMap R K H C (1 ⊗ₜ[R] retraction R K H C d.1) =
      contractionMap R K H C d
    exact hC
  exact LinearMap.congr_fun heq c

/-- The base-changed inclusion of a contraction into the ambient algebra. -/
noncomputable def localizedInclusion (C : Subalgebra K (K ⊗[R] H)) :
    K ⊗[R] contraction R K H C →ₗ[K] K ⊗[R] H :=
  TensorProduct.AlgebraTensorModule.lTensor K K
    (contraction R K H C).val.toLinearMap

omit [IsFractionRing R K] in
lemma localizedInclusion_eq_val_baseChangeMap
    (C : Subalgebra K (K ⊗[R] H))
    (x : K ⊗[R] contraction R K H C) :
    localizedInclusion R K H C x = (baseChangeMap R K H C x).1 := by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro k d
    change k ⊗ₜ[R] d.1 =
      algebraMap K (K ⊗[R] H) k * (contractionMap R K H C d).1
    rw [show (contractionMap R K H C d).1 =
      (1 ⊗ₜ[R] d.1 : K ⊗[R] H) from rfl]
    simp [Algebra.TensorProduct.algebraMap_apply]
  · intro x y hx hy
    rw [map_add, map_add]
    exact congrArg₂ (· + ·) hx hy

lemma localizedInclusion_localizedRetraction_val
    (C : Subalgebra K (K ⊗[R] H))
    [Module.Projective R H]
    [Module.Projective R
      (Ideal.ModuleQuotient (contraction R K H C).toSubmodule)]
    (c : C) :
    localizedInclusion R K H C (localizedRetraction R K H C c.1) = c.1 := by
  rw [localizedInclusion_eq_val_baseChangeMap]
  exact congrArg Subtype.val (baseChangeMap_localizedRetraction_val R K H C c)

/-- Base change commutes with tensor products of algebras. -/
noncomputable def baseChangeTensorEquiv
    (R K A B : Type u) [CommRing R] [Field K] [Algebra R K]
    [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] :
    ((K ⊗[R] A) ⊗[K] (K ⊗[R] B)) ≃ₐ[K] K ⊗[R] (A ⊗[R] B) :=
  (Algebra.TensorProduct.tensorTensorTensorComm R R K K K A K B).trans
    (Algebra.TensorProduct.congr (Algebra.TensorProduct.lid K K)
      (AlgEquiv.refl : (A ⊗[R] B) ≃ₐ[R] (A ⊗[R] B)))

lemma baseChangeTensorEquiv_naturality
    (R K A B A' B' : Type u) [CommRing R] [Field K] [Algebra R K]
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra R A] [Algebra R B] [Algebra R A'] [Algebra R B']
    (f : A →ₗ[R] A') (g : B →ₗ[R] B')
    (z : (K ⊗[R] A) ⊗[K] (K ⊗[R] B)) :
    baseChangeTensorEquiv R K A' B'
        (TensorProduct.map
          (TensorProduct.AlgebraTensorModule.lTensor K K f)
          (TensorProduct.AlgebraTensorModule.lTensor K K g) z) =
      TensorProduct.AlgebraTensorModule.lTensor K K
        (TensorProduct.map f g) (baseChangeTensorEquiv R K A B z) := by
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro x y
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp
    · intro k a
      refine TensorProduct.induction_on y ?_ ?_ ?_
      · simp
      · intro l b
        simp [baseChangeTensorEquiv]
      · intro y₁ y₂ hy₁ hy₂
        simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hy₁ hy₂
    · intro x₁ x₂ hx₁ hx₂
      simp only [TensorProduct.add_tmul, map_add, hx₁, hx₂]
  · intro z₁ z₂ hz₁ hz₂
    simpa only [map_add] using congrArg₂ (· + ·) hz₁ hz₂

/-- A generic-fibre subalgebra closed under comultiplication and antipode. -/
structure IsGenericHopfSubalgebra
    (R K H : Type u) [CommRing R] [Field K] [Algebra R K]
    [CommRing H] [HopfAlgebra R H]
    (C : Subalgebra K (K ⊗[R] H)) : Prop where
  comul_mem : ∀ c : C, ∃ z : C ⊗[K] C,
    TensorProduct.map C.val.toLinearMap C.val.toLinearMap z =
      Coalgebra.comul (R := K) c.1
  antipode_mem : ∀ c : C, HopfAlgebra.antipode K c.1 ∈ C

lemma baseChange_comul_includeRight
    (R K H : Type u) [CommRing R] [Field K] [Algebra R K]
    [CommRing H] [HopfAlgebra R H] (h : H) :
    baseChangeTensorEquiv R K H H
      (Coalgebra.comul (R := K) (A := K ⊗[R] H)
        (Algebra.TensorProduct.includeRight h)) =
      Algebra.TensorProduct.includeRight (Coalgebra.comul (R := R) h) := by
  simp only [Algebra.TensorProduct.includeRight_apply,
    TensorProduct.comul_tmul, CommSemiring.comul_apply]
  generalize Coalgebra.comul (R := R) h = z
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro x y
    simp [baseChangeTensorEquiv]
  · intro x y hx hy
    simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hx hy

lemma contraction_comul_mem
    (R K H : Type u) [CommRing R] [Field K] [Algebra R K]
    [CommRing H] [HopfAlgebra R H] [IsFractionRing R K]
    [IsDedekindDomain R] [Module.Finite R H] [Module.Flat R H]
    (C : Subalgebra K (K ⊗[R] H)) (hC : IsGenericHopfSubalgebra R K H C)
    (d : contraction R K H C) :
    ∃ z : contraction R K H C ⊗[R] contraction R K H C,
      TensorProduct.map (contraction R K H C).val.toLinearMap
        (contraction R K H C).val.toLinearMap z = Coalgebra.comul (R := R) d.1 := by
  let D := contraction R K H C
  let _ : Module.IsTorsionFree R (Ideal.ModuleQuotient D.toSubmodule) :=
    contraction_quotient_isTorsionFree R K H C
  let _ : Module.Finite R (Ideal.ModuleQuotient D.toSubmodule) := inferInstance
  let _ : Module.Flat R (Ideal.ModuleQuotient D.toSubmodule) := inferInstance
  let _ : Module.FinitePresentation R H :=
    Module.finitePresentation_of_finite R H
  let _ : Module.FinitePresentation R (Ideal.ModuleQuotient D.toSubmodule) :=
    Module.finitePresentation_of_finite R _
  let _ : Module.Projective R H :=
    Module.Flat.projective_of_finitePresentation
  let _ : Module.Projective R (Ideal.ModuleQuotient D.toSubmodule) :=
    Module.Flat.projective_of_finitePresentation
  let i : D →ₗ[R] H := D.val.toLinearMap
  let r : H →ₗ[R] D := retraction R K H C
  let it : D ⊗[R] D →ₗ[R] H ⊗[R] H := TensorProduct.map i i
  let rt : H ⊗[R] H →ₗ[R] D ⊗[R] D := TensorProduct.map r r
  refine ⟨rt (Coalgebra.comul (R := R) d.1), ?_⟩
  apply Algebra.TensorProduct.includeRight_injective (A := K) (B := H ⊗[R] H)
    (IsFractionRing.injective R K)
  let c : C := contractionMap R K H C d
  obtain ⟨z, hz⟩ := hC.comul_mem c
  let zi : (K ⊗[R] H) ⊗[K] (K ⊗[R] H) :=
    TensorProduct.map C.val.toLinearMap C.val.toLinearMap z
  let zr : (K ⊗[R] D) ⊗[K] (K ⊗[R] D) :=
    TensorProduct.map (localizedRetraction R K H C)
      (localizedRetraction R K H C) zi
  have hri : (localizedInclusion R K H C).comp
        ((localizedRetraction R K H C).comp C.val.toLinearMap) =
      C.val.toLinearMap := by
    apply LinearMap.ext
    intro x
    exact localizedInclusion_localizedRetraction_val R K H C x
  have hzri : TensorProduct.map (localizedInclusion R K H C)
      (localizedInclusion R K H C) zr = zi := by
    simp only [zr, zi, TensorProduct.map_map, hri]
  have hEzi : baseChangeTensorEquiv R K H H zi =
      Algebra.TensorProduct.includeRight (Coalgebra.comul (R := R) d.1) := by
    change baseChangeTensorEquiv R K H H
      (TensorProduct.map C.val.toLinearMap C.val.toLinearMap z) = _
    rw [hz]
    change baseChangeTensorEquiv R K H H
      (Coalgebra.comul (R := K) (Algebra.TensorProduct.includeRight d.1)) = _
    exact baseChange_comul_includeRight R K H d.1
  have hEr : baseChangeTensorEquiv R K D D zr =
      TensorProduct.AlgebraTensorModule.lTensor K K rt
        (baseChangeTensorEquiv R K H H zi) := by
    exact baseChangeTensorEquiv_naturality R K H H D D r r zi
  have hEi : baseChangeTensorEquiv R K H H
        (TensorProduct.map (localizedInclusion R K H C)
          (localizedInclusion R K H C) zr) =
      TensorProduct.AlgebraTensorModule.lTensor K K it
        (baseChangeTensorEquiv R K D D zr) := by
    exact baseChangeTensorEquiv_naturality R K D D H H i i zr
  change Algebra.TensorProduct.includeRight
      (it (rt (Coalgebra.comul (R := R) d.1))) =
    Algebra.TensorProduct.includeRight (Coalgebra.comul (R := R) d.1)
  calc
    Algebra.TensorProduct.includeRight (it (rt (Coalgebra.comul (R := R) d.1))) =
        TensorProduct.AlgebraTensorModule.lTensor K K it
          (Algebra.TensorProduct.includeRight
            (rt (Coalgebra.comul (R := R) d.1))) := by simp
    _ = TensorProduct.AlgebraTensorModule.lTensor K K it
          (baseChangeTensorEquiv R K D D zr) := by rw [hEr, hEzi]; simp
    _ = baseChangeTensorEquiv R K H H
          (TensorProduct.map (localizedInclusion R K H C)
            (localizedInclusion R K H C) zr) := hEi.symm
    _ = baseChangeTensorEquiv R K H H zi := by rw [hzri]
    _ = Algebra.TensorProduct.includeRight
          (Coalgebra.comul (R := R) d.1) := hEzi

lemma baseChange_antipode_includeRight
    (R K H : Type u) [CommRing R] [Field K] [Algebra R K]
    [CommRing H] [HopfAlgebra R H] (h : H) :
    HopfAlgebra.antipode K
        (Algebra.TensorProduct.includeRight h : K ⊗[R] H) =
      Algebra.TensorProduct.includeRight (HopfAlgebra.antipode R h) := by
  simp [TensorProduct.antipode_def, Algebra.TensorProduct.includeRight]

lemma contraction_antipode_mem
    (R K H : Type u) [CommRing R] [Field K] [Algebra R K]
    [CommRing H] [HopfAlgebra R H]
    (C : Subalgebra K (K ⊗[R] H)) (hC : IsGenericHopfSubalgebra R K H C)
    (d : contraction R K H C) :
    HopfAlgebra.antipode R d.1 ∈ contraction R K H C := by
  change Algebra.TensorProduct.includeRight (HopfAlgebra.antipode R d.1) ∈ C
  rw [← baseChange_antipode_includeRight R K H d.1]
  exact hC.antipode_mem (contractionMap R K H C d)

/-- Comultiplication on a generic Hopf subalgebra's integral contraction. -/
noncomputable def contractionComul
    (R K H : Type u) [CommRing R] [Field K] [Algebra R K]
    [CommRing H] [HopfAlgebra R H] [IsFractionRing R K]
    [IsDedekindDomain R] [Module.Finite R H] [Module.Flat R H]
    (C : Subalgebra K (K ⊗[R] H)) :
    contraction R K H C →ₗ[R]
      contraction R K H C ⊗[R] contraction R K H C := by
  let D := contraction R K H C
  let _ : Module.IsTorsionFree R (Ideal.ModuleQuotient D.toSubmodule) :=
    contraction_quotient_isTorsionFree R K H C
  let _ : Module.Finite R (Ideal.ModuleQuotient D.toSubmodule) := inferInstance
  let _ : Module.Flat R (Ideal.ModuleQuotient D.toSubmodule) := inferInstance
  let _ : Module.FinitePresentation R H := Module.finitePresentation_of_finite R H
  let _ : Module.FinitePresentation R (Ideal.ModuleQuotient D.toSubmodule) :=
    Module.finitePresentation_of_finite R _
  let _ : Module.Projective R H := Module.Flat.projective_of_finitePresentation
  let _ : Module.Projective R (Ideal.ModuleQuotient D.toSubmodule) :=
    Module.Flat.projective_of_finitePresentation
  exact (TensorProduct.map (retraction R K H C) (retraction R K H C)).comp
    ((Coalgebra.comul (R := R)).comp D.val.toLinearMap)

lemma contractionComul_compat
    (R K H : Type u) [CommRing R] [Field K] [Algebra R K]
    [CommRing H] [HopfAlgebra R H] [IsFractionRing R K]
    [IsDedekindDomain R] [Module.Finite R H] [Module.Flat R H]
    (C : Subalgebra K (K ⊗[R] H)) (hC : IsGenericHopfSubalgebra R K H C)
    (d : contraction R K H C) :
    TensorProduct.map (contraction R K H C).val.toLinearMap
        (contraction R K H C).val.toLinearMap (contractionComul R K H C d) =
      Coalgebra.comul (R := R) d.1 := by
  obtain ⟨z, hz⟩ := contraction_comul_mem R K H C hC d
  let D := contraction R K H C
  let _ : Module.IsTorsionFree R (Ideal.ModuleQuotient D.toSubmodule) :=
    contraction_quotient_isTorsionFree R K H C
  let _ : Module.Finite R (Ideal.ModuleQuotient D.toSubmodule) := inferInstance
  let _ : Module.Flat R (Ideal.ModuleQuotient D.toSubmodule) := inferInstance
  let _ : Module.FinitePresentation R H := Module.finitePresentation_of_finite R H
  let _ : Module.FinitePresentation R (Ideal.ModuleQuotient D.toSubmodule) :=
    Module.finitePresentation_of_finite R _
  let _ : Module.Projective R H := Module.Flat.projective_of_finitePresentation
  let _ : Module.Projective R (Ideal.ModuleQuotient D.toSubmodule) :=
    Module.Flat.projective_of_finitePresentation
  have hz' : TensorProduct.map D.val.toLinearMap D.val.toLinearMap z =
      Coalgebra.comul (R := R) (D.val.toLinearMap d) := hz
  simp only [contractionComul, LinearMap.comp_apply]
  change TensorProduct.map D.val.toLinearMap D.val.toLinearMap
      (TensorProduct.map (retraction R K H C) (retraction R K H C)
        (Coalgebra.comul (R := R) (D.val.toLinearMap d))) =
    Coalgebra.comul (R := R) (D.val.toLinearMap d)
  rw [← hz', TensorProduct.map_map]
  rw [TensorProduct.map_map]
  have hiri : (D.val.toLinearMap.comp (retraction R K H C)).comp
      D.val.toLinearMap = D.val.toLinearMap := by
    rw [LinearMap.comp_assoc, retraction_comp_val]
    rfl
  rw [hiri]

/-- Antipode on a generic Hopf subalgebra's integral contraction. -/
noncomputable def contractionAntipode
    (R K H : Type u) [CommRing R] [Field K] [Algebra R K]
    [CommRing H] [HopfAlgebra R H]
    (C : Subalgebra K (K ⊗[R] H)) (hC : IsGenericHopfSubalgebra R K H C) :
    contraction R K H C →ₗ[R] contraction R K H C :=
  { toFun := fun d ↦ ⟨HopfAlgebra.antipode R d.1,
        contraction_antipode_mem R K H C hC d⟩
    map_add' := fun _ _ ↦ Subtype.ext (map_add (HopfAlgebra.antipode R) _ _)
    map_smul' := fun _ _ ↦ Subtype.ext (map_smul (HopfAlgebra.antipode R) _ _) }

namespace Coalgebra

/-- Transport a coalgebra structure across a split injective linear map. -/
@[instance_reducible]
noncomputable def ofInjective
    (R M N : Type u) [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Coalgebra R N]
    (i : M →ₗ[R] N) (r : N →ₗ[R] M) (hri : r.comp i = LinearMap.id)
    (comulM : M →ₗ[R] M ⊗[R] M) (counitM : M →ₗ[R] R)
    (hcomul : (TensorProduct.map i i).comp comulM =
      (Coalgebra.comul (R := R)).comp i)
    (hcounit : counitM = (Coalgebra.counit (R := R)).comp i) :
    Coalgebra R M where
  comul := comulM
  counit := counitM
  coassoc := by
    apply LinearMap.ext
    intro x
    have hinj : Function.Injective
        (TensorProduct.map i (TensorProduct.map i i)) := by
      apply Function.LeftInverse.injective
        (g := TensorProduct.map r (TensorProduct.map r r))
      intro z
      rw [TensorProduct.map_map]
      rw [← TensorProduct.map_comp]
      rw [hri]
      simp only [TensorProduct.map_id]
      rfl
    apply hinj
    simp only [LinearMap.comp_apply]
    change TensorProduct.map i (TensorProduct.map i i)
        (TensorProduct.assoc R M M M (comulM.rTensor M (comulM x))) =
      TensorProduct.map i (TensorProduct.map i i)
        (comulM.lTensor M (comulM x))
    rw [TensorProduct.map_map_assoc i i i]
    simp only [LinearMap.rTensor_def, LinearMap.lTensor_def]
    rw [TensorProduct.map_map, TensorProduct.map_map]
    simp only [LinearMap.comp_id]
    have hcx : TensorProduct.map i i (comulM x) =
        Coalgebra.comul (R := R) (i x) := LinearMap.congr_fun hcomul x
    have hamb := Coalgebra.coassoc_apply (R := R) (i x)
    rw [← hcx] at hamb
    simp only [LinearMap.rTensor_def, LinearMap.lTensor_def] at hamb
    rw [TensorProduct.map_map, TensorProduct.map_map] at hamb
    rw [← hcomul] at hamb
    simpa only [LinearMap.id_comp, LinearMap.comp_id] using hamb
  rTensor_counit_comp_comul := by
    apply LinearMap.ext
    intro x
    have hinj : Function.Injective
        (TensorProduct.map (LinearMap.id (R := R) (M := R)) i) := by
      apply Function.LeftInverse.injective
        (g := TensorProduct.map (LinearMap.id (R := R) (M := R)) r)
      intro z
      rw [TensorProduct.map_map, hri]
      simp only [LinearMap.id_comp, TensorProduct.map_id]
      rfl
    apply hinj
    simp only [LinearMap.comp_apply, LinearMap.rTensor_def]
    rw [TensorProduct.map_map]
    rw [show counitM = (Coalgebra.counit (R := R)).comp i from hcounit]
    simp only [LinearMap.id_comp, LinearMap.comp_id]
    have hcx : TensorProduct.map i i (comulM x) =
        Coalgebra.comul (R := R) (i x) := LinearMap.congr_fun hcomul x
    have hamb := Coalgebra.rTensor_counit_comul (R := R) (i x)
    rw [← hcx] at hamb
    simp only [LinearMap.rTensor_def] at hamb
    rw [TensorProduct.map_map] at hamb
    change TensorProduct.map ((Coalgebra.counit (R := R)).comp i) i (comulM x) =
      1 ⊗ₜ[R] i x
    exact hamb
  lTensor_counit_comp_comul := by
    apply LinearMap.ext
    intro x
    have hinj : Function.Injective
        (TensorProduct.map i (LinearMap.id (R := R) (M := R))) := by
      apply Function.LeftInverse.injective
        (g := TensorProduct.map r (LinearMap.id (R := R) (M := R)))
      intro z
      rw [TensorProduct.map_map, hri]
      simp only [LinearMap.id_comp, TensorProduct.map_id]
      rfl
    apply hinj
    simp only [LinearMap.comp_apply, LinearMap.lTensor_def]
    rw [TensorProduct.map_map]
    rw [show counitM = (Coalgebra.counit (R := R)).comp i from hcounit]
    simp only [LinearMap.id_comp, LinearMap.comp_id]
    have hcx : TensorProduct.map i i (comulM x) =
        Coalgebra.comul (R := R) (i x) := LinearMap.congr_fun hcomul x
    have hamb := Coalgebra.lTensor_counit_comul (R := R) (i x)
    rw [← hcx] at hamb
    simp only [LinearMap.lTensor_def] at hamb
    rw [TensorProduct.map_map] at hamb
    change TensorProduct.map i ((Coalgebra.counit (R := R)).comp i) (comulM x) =
      i x ⊗ₜ[R] 1
    exact hamb

end Coalgebra

/-- The coalgebra structure inherited by a generic Hopf subalgebra's contraction. -/
@[instance_reducible]
noncomputable def contractionCoalgebra
    (R K H : Type u) [CommRing R] [Field K] [Algebra R K]
    [CommRing H] [HopfAlgebra R H] [IsFractionRing R K]
    [IsDedekindDomain R] [Module.Finite R H] [Module.Flat R H]
    (C : Subalgebra K (K ⊗[R] H)) (hC : IsGenericHopfSubalgebra R K H C) :
    Coalgebra R (contraction R K H C) := by
  let D := contraction R K H C
  let _ : Module.IsTorsionFree R (Ideal.ModuleQuotient D.toSubmodule) :=
    contraction_quotient_isTorsionFree R K H C
  let _ : Module.Finite R (Ideal.ModuleQuotient D.toSubmodule) := inferInstance
  let _ : Module.Flat R (Ideal.ModuleQuotient D.toSubmodule) := inferInstance
  let _ : Module.FinitePresentation R H := Module.finitePresentation_of_finite R H
  let _ : Module.FinitePresentation R (Ideal.ModuleQuotient D.toSubmodule) :=
    Module.finitePresentation_of_finite R _
  let _ : Module.Projective R H := Module.Flat.projective_of_finitePresentation
  let _ : Module.Projective R (Ideal.ModuleQuotient D.toSubmodule) :=
    Module.Flat.projective_of_finitePresentation
  apply Coalgebra.ofInjective R D H D.val.toLinearMap (retraction R K H C)
    (retraction_comp_val R K H C) (contractionComul R K H C)
    ((Coalgebra.counit (R := R)).comp D.val.toLinearMap)
  · apply LinearMap.ext
    intro d
    exact contractionComul_compat R K H C hC d
  · rfl

/-- The bialgebra structure inherited by a generic Hopf subalgebra's contraction. -/
@[instance_reducible]
noncomputable def contractionBialgebra
    (R K H : Type u) [CommRing R] [Field K] [Algebra R K]
    [CommRing H] [HopfAlgebra R H] [IsFractionRing R K]
    [IsDedekindDomain R] [Module.Finite R H] [Module.Flat R H]
    (C : Subalgebra K (K ⊗[R] H)) (hC : IsGenericHopfSubalgebra R K H C) :
    Bialgebra R (contraction R K H C) := by
  let D := contraction R K H C
  let _ : Module.IsTorsionFree R (Ideal.ModuleQuotient D.toSubmodule) :=
    contraction_quotient_isTorsionFree R K H C
  let _ : Module.Finite R (Ideal.ModuleQuotient D.toSubmodule) := inferInstance
  let _ : Module.Flat R (Ideal.ModuleQuotient D.toSubmodule) := inferInstance
  let _ : Module.FinitePresentation R H := Module.finitePresentation_of_finite R H
  let _ : Module.FinitePresentation R (Ideal.ModuleQuotient D.toSubmodule) :=
    Module.finitePresentation_of_finite R _
  let _ : Module.Projective R H := Module.Flat.projective_of_finitePresentation
  let _ : Module.Projective R (Ideal.ModuleQuotient D.toSubmodule) :=
    Module.Flat.projective_of_finitePresentation
  letI : Coalgebra R D := contractionCoalgebra R K H C hC
  have hcompat (d : D) : TensorProduct.map D.val.toLinearMap D.val.toLinearMap
      (Coalgebra.comul (R := R) d) = Coalgebra.comul (R := R) d.1 := by
    change TensorProduct.map D.val.toLinearMap D.val.toLinearMap
      (contractionComul R K H C d) = Coalgebra.comul (R := R) d.1
    exact contractionComul_compat R K H C hC d
  have hmap_one : TensorProduct.map D.val.toLinearMap D.val.toLinearMap
      (1 : D ⊗[R] D) = 1 := by
    change Algebra.TensorProduct.map D.val D.val 1 = 1
    exact map_one (Algebra.TensorProduct.map D.val D.val)
  have hmap_mul (x y : D ⊗[R] D) :
      TensorProduct.map D.val.toLinearMap D.val.toLinearMap (x * y) =
        TensorProduct.map D.val.toLinearMap D.val.toLinearMap x *
          TensorProduct.map D.val.toLinearMap D.val.toLinearMap y := by
    change Algebra.TensorProduct.map D.val D.val (x * y) =
      Algebra.TensorProduct.map D.val D.val x * Algebra.TensorProduct.map D.val D.val y
    exact map_mul (Algebra.TensorProduct.map D.val D.val) x y
  apply Bialgebra.mk' R D
  · exact Bialgebra.counit_one (R := R) (A := H)
  · intro a b
    exact Bialgebra.counit_mul (R := R) (A := H) a.1 b.1
  · apply (tensor_val_injective R K H C)
    rw [hcompat]
    change Coalgebra.comul (R := R) (1 : H) = _
    rw [Bialgebra.comul_one, hmap_one]
  · intro a b
    apply (tensor_val_injective R K H C)
    rw [hcompat]
    change Coalgebra.comul (R := R) (a.1 * b.1) = _
    rw [Bialgebra.comul_mul, hmap_mul, hcompat, hcompat]

lemma val_mul_contractionAntipode_rTensor
    (R K H : Type u) [CommRing R] [Field K] [Algebra R K]
    [CommRing H] [HopfAlgebra R H]
    (C : Subalgebra K (K ⊗[R] H)) (hC : IsGenericHopfSubalgebra R K H C)
    (z : contraction R K H C ⊗[R] contraction R K H C) :
    ((LinearMap.mul' R (contraction R K H C))
      ((contractionAntipode R K H C hC).rTensor (contraction R K H C) z)).1 =
      LinearMap.mul' R H ((HopfAlgebra.antipode R).rTensor H
        (TensorProduct.map
          (contraction R K H C).val.toLinearMap
          (contraction R K H C).val.toLinearMap z)) := by
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro x y
    rfl
  · intro x y hx hy
    rw [map_add, map_add, map_add, map_add]
    change (contraction R K H C).val (_ + _) = _
    rw [map_add, map_add]
    exact congrArg₂ (· + ·) hx hy

lemma val_mul_contractionAntipode_lTensor
    (R K H : Type u) [CommRing R] [Field K] [Algebra R K]
    [CommRing H] [HopfAlgebra R H]
    (C : Subalgebra K (K ⊗[R] H)) (hC : IsGenericHopfSubalgebra R K H C)
    (z : contraction R K H C ⊗[R] contraction R K H C) :
    ((LinearMap.mul' R (contraction R K H C))
      ((contractionAntipode R K H C hC).lTensor (contraction R K H C) z)).1 =
      LinearMap.mul' R H ((HopfAlgebra.antipode R).lTensor H
        (TensorProduct.map
          (contraction R K H C).val.toLinearMap
          (contraction R K H C).val.toLinearMap z)) := by
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro x y
    rfl
  · intro x y hx hy
    rw [map_add, map_add, map_add, map_add]
    change (contraction R K H C).val (_ + _) = _
    rw [map_add, map_add]
    exact congrArg₂ (· + ·) hx hy

/-- The Hopf algebra structure inherited by a generic Hopf subalgebra's contraction. -/
@[instance_reducible]
noncomputable def contractionHopfAlgebra
    (R K H : Type u) [CommRing R] [Field K] [Algebra R K]
    [CommRing H] [HopfAlgebra R H] [IsFractionRing R K]
    [IsDedekindDomain R] [Module.Finite R H] [Module.Flat R H]
    (C : Subalgebra K (K ⊗[R] H)) (hC : IsGenericHopfSubalgebra R K H C) :
    HopfAlgebra R (contraction R K H C) := by
  let D := contraction R K H C
  let _ : Module.IsTorsionFree R (Ideal.ModuleQuotient D.toSubmodule) :=
    contraction_quotient_isTorsionFree R K H C
  let _ : Module.Finite R (Ideal.ModuleQuotient D.toSubmodule) := inferInstance
  let _ : Module.Flat R (Ideal.ModuleQuotient D.toSubmodule) := inferInstance
  let _ : Module.FinitePresentation R H := Module.finitePresentation_of_finite R H
  let _ : Module.FinitePresentation R (Ideal.ModuleQuotient D.toSubmodule) :=
    Module.finitePresentation_of_finite R _
  let _ : Module.Projective R H := Module.Flat.projective_of_finitePresentation
  let _ : Module.Projective R (Ideal.ModuleQuotient D.toSubmodule) :=
    Module.Flat.projective_of_finitePresentation
  letI : Bialgebra R D := contractionBialgebra R K H C hC
  have hcompat (d : D) : TensorProduct.map D.val.toLinearMap D.val.toLinearMap
      (Coalgebra.comul (R := R) d) = Coalgebra.comul (R := R) d.1 := by
    change TensorProduct.map D.val.toLinearMap D.val.toLinearMap
      (contractionComul R K H C d) = Coalgebra.comul (R := R) d.1
    exact contractionComul_compat R K H C hC d
  refine
    { contractionBialgebra R K H C hC with
      antipode := contractionAntipode R K H C hC
      mul_antipode_rTensor_comul := ?_
      mul_antipode_lTensor_comul := ?_ }
  · apply LinearMap.ext
    intro d
    apply Subtype.ext
    change
      ((LinearMap.mul' R D)
        ((contractionAntipode R K H C hC).rTensor D
          (Coalgebra.comul (R := R) d))).1 =
        (algebraMap R D (Coalgebra.counit (R := R) d)).1
    rw [val_mul_contractionAntipode_rTensor, hcompat]
    exact HopfAlgebra.mul_antipode_rTensor_comul_apply (R := R) d.1
  · apply LinearMap.ext
    intro d
    apply Subtype.ext
    change
      ((LinearMap.mul' R D)
        ((contractionAntipode R K H C hC).lTensor D
          (Coalgebra.comul (R := R) d))).1 =
        (algebraMap R D (Coalgebra.counit (R := R) d)).1
    rw [val_mul_contractionAntipode_lTensor, hcompat]
    exact HopfAlgebra.mul_antipode_lTensor_comul_apply (R := R) d.1

end HopfAlgebra.IntegralClosure
namespace BialgHom

open LinearMap WithConv

lemma antipode_comp {R A B : Type u} [CommSemiring R]
    [Semiring A] [Semiring B] [HopfAlgebra R A] [HopfAlgebra R B]
    (f : A →ₐc[R] B) :
    (HopfAlgebra.antipode R).comp f.toLinearMap =
      f.toLinearMap.comp (HopfAlgebra.antipode R) := by
  let u : WithConv (A →ₗ[R] B) :=
    toConv ((HopfAlgebra.antipode R).comp f.toLinearMap)
  let v : WithConv (A →ₗ[R] B) := toConv f.toLinearMap
  let w : WithConv (A →ₗ[R] B) :=
    toConv (f.toLinearMap.comp (HopfAlgebra.antipode R))
  have huv : u * v = 1 := by
    apply ofConv_injective
    change (toConv ((HopfAlgebra.antipode R).comp f.toLinearMap) *
      toConv f.toLinearMap).ofConv = _
    calc
      _ = (toConv (HopfAlgebra.antipode R (A := B)) *
            toConv (LinearMap.id (R := R) (M := B))).ofConv.comp
          f.toLinearMap := by
            rw [convMul_comp_coalgHom_distrib]
            rfl
      _ = (1 : WithConv (B →ₗ[R] B)).ofConv.comp f.toLinearMap := by
        rw [antipode_mul_id]
      _ = (1 : WithConv (A →ₗ[R] B)).ofConv :=
        convOne_comp_coalgHom f.toCoalgHom
  have hvw : v * w = 1 := by
    apply ofConv_injective
    change (toConv f.toLinearMap *
      toConv (f.toLinearMap.comp (HopfAlgebra.antipode R))).ofConv = _
    calc
      _ = f.toLinearMap.comp
          (toConv (LinearMap.id (R := R) (M := A)) *
            toConv (HopfAlgebra.antipode R (A := A))).ofConv := by
            symm
            convert algHom_comp_convMul_distrib f.toAlgHom
              (toConv (LinearMap.id (R := R) (M := A)))
              (toConv (HopfAlgebra.antipode R (A := A))) using 1 <;> rfl
      _ = f.toLinearMap.comp (1 : WithConv (A →ₗ[R] A)).ofConv := by
        rw [id_mul_antipode]
      _ = (1 : WithConv (A →ₗ[R] B)).ofConv :=
        algHom_comp_convOne f.toAlgHom
  exact congrArg ofConv (left_inv_eq_right_inv huv hvw)

/-- Lift an algebra factorization to a bialgebra homomorphism through an injective target map. -/
noncomputable def factorOfInjective {K A B C : Type u} [Field K]
    [CommRing A] [CommRing B] [CommRing C]
    [Bialgebra K A] [Bialgebra K B] [Bialgebra K C]
    (k : B →ₐc[K] C) (hk : Function.Injective k)
    (i : A →ₐc[K] C) (f : A →ₐ[K] B)
    (hcomp : k.toAlgHom.comp f = i.toAlgHom) : A →ₐc[K] B := by
  let cf : A →ₗc[K] B :=
    { __ := f.toLinearMap
      counit_comp := by
        apply LinearMap.ext
        intro a
        calc
          Coalgebra.counit (R := K) (f a) =
              Coalgebra.counit (R := K) (k (f a)) :=
            (CoalgHomClass.counit_comp_apply k (f a)).symm
          _ = Coalgebra.counit (R := K) (i a) := by
            rw [show k (f a) = i a from AlgHom.congr_fun hcomp a]
          _ = Coalgebra.counit (R := K) a :=
            CoalgHomClass.counit_comp_apply i a
      map_comp_comul := by
        apply LinearMap.ext
        intro a
        apply TensorProduct.map_injective_of_flat_flat
          k.toLinearMap k.toLinearMap hk hk
        change TensorProduct.map k.toLinearMap k.toLinearMap
          (TensorProduct.map f.toLinearMap f.toLinearMap
            (Coalgebra.comul (R := K) a)) =
          TensorProduct.map k.toLinearMap k.toLinearMap
            (Coalgebra.comul (R := K) (f a))
        rw [TensorProduct.map_map]
        have hlin : k.toLinearMap.comp f.toLinearMap = i.toLinearMap := by
          exact congrArg AlgHom.toLinearMap hcomp
        rw [hlin]
        calc
          TensorProduct.map i.toLinearMap i.toLinearMap
              (Coalgebra.comul (R := K) a) =
            Coalgebra.comul (R := K) (i a) :=
              CoalgHomClass.map_comp_comul_apply i a
          _ = Coalgebra.comul (R := K) (k (f a)) := by
            rw [show k (f a) = i a from AlgHom.congr_fun hcomp a]
          _ = TensorProduct.map k.toLinearMap k.toLinearMap
              (Coalgebra.comul (R := K) (f a)) :=
            (CoalgHomClass.map_comp_comul_apply k (f a)).symm }
  exact { __ := f, __ := cf }

end BialgHom

namespace HopfAlgebra.IntegralClosure

lemma isGenericHopfSubalgebra_range
    (R K H A : Type u) [CommRing R] [Field K] [Algebra R K]
    [CommRing H] [HopfAlgebra R H]
    [CommRing A] [HopfAlgebra K A]
    (f : A →ₐc[K] K ⊗[R] H) :
    IsGenericHopfSubalgebra R K H f.toAlgHom.range := by
  constructor
  · intro c
    obtain ⟨a, ha⟩ := c.property
    let fr : A →ₐ[K] f.toAlgHom.range := f.toAlgHom.rangeRestrict
    refine ⟨TensorProduct.map fr.toLinearMap fr.toLinearMap
      (Coalgebra.comul (R := K) a), ?_⟩
    rw [TensorProduct.map_map]
    have hcomp : f.toAlgHom.range.val.toLinearMap.comp fr.toLinearMap =
        f.toLinearMap := by
      rfl
    rw [hcomp]
    exact (CoalgHomClass.map_comp_comul_apply f a).trans
      (congrArg (Coalgebra.comul (R := K)) ha)
  · intro c
    obtain ⟨a, ha⟩ := c.property
    refine ⟨HopfAlgebra.antipode K a, ?_⟩
    have hs := LinearMap.congr_fun (BialgHom.antipode_comp f) a
    change f (HopfAlgebra.antipode K a) = HopfAlgebra.antipode K c.1
    rw [← ha]
    exact hs.symm
end HopfAlgebra.IntegralClosure

namespace GaloisModule.GenericFiber

variable (K L G X : Type u) [Field K] [Field L] [Algebra K L]
variable [IsGalois K L] [IsSepClosed L]
variable [CommRing G] [HopfAlgebra K G] [Algebra.Etale K G]
variable [AddCommGroup X] [DistribMulAction (L ≃ₐ[K] L) X]

/-- The local convolution monoid on the geometric points of a generic fibre. -/
noncomputable local instance genericPointsMonoid : Monoid (G →ₐ[K] L) :=
  instMonoidAlgHom_fLT K L

/-- The Galois action on generic-fibre points, compatible with convolution. -/
noncomputable local instance genericPointsMulDistribMulAction :
    MulDistribMulAction (L ≃ₐ[K] L) (G →ₐ[K] L) :=
  instMulDistribMulActionAlgEquivAlgHom_fLT K L

/-- Forget the additive synonym in an equivariant map from generic-fibre points. -/
noncomputable def forwardPointsMulActionHom
    (f : Additive (G →ₐ[K] L) →+[L ≃ₐ[K] L] X) :
    (G →ₐ[K] L) →[L ≃ₐ[K] L] X where
  toFun p := f (Additive.ofMul p)
  map_smul' σ p := f.map_smul σ (Additive.ofMul p)

/-- Evaluation realizes an etale Hopf algebra as functions on its geometric points. -/
noncomputable def genericEvalAlgEquiv :
    G ≃ₐ[K] ((G →ₐ[K] L) →[L ≃ₐ[K] L] L) :=
  AlgEquiv.ofBijective
    (AlgHom.evalMulActionHom (L ≃ₐ[K] L) K G L)
    (InfiniteGalois.evalMulActionHom_bijective_of_isSepClosed K L G)

/-- The function-algebra embedding induced by a map from generic-fibre points. -/
noncomputable def canonicalEmbeddingAlgHom
    (g : Additive (G →ₐ[K] L) →+[L ≃ₐ[K] L] X) :
    (X →[L ≃ₐ[K] L] L) →ₐ[K] G :=
  (genericEvalAlgEquiv K L G).symm.toAlgHom.comp
    (MulActionHom.compLeftAlgHom (L ≃ₐ[K] L) K L
      (forwardPointsMulActionHom K L G X g))

lemma eval_canonicalEmbeddingAlgHom
    (g : Additive (G →ₐ[K] L) →+[L ≃ₐ[K] L] X)
    (a : X →[L ≃ₐ[K] L] L) (p : G →ₐ[K] L) :
    p (canonicalEmbeddingAlgHom K L G X g a) =
      a (g (Additive.ofMul p)) := by
  change genericEvalAlgEquiv K L G
      ((genericEvalAlgEquiv K L G).symm
        (MulActionHom.compLeftAlgHom (L ≃ₐ[K] L) K L
          (forwardPointsMulActionHom K L G X g) a)) p = _
  rw [AlgEquiv.apply_symm_apply]
  rfl

lemma canonicalEmbeddingAlgHom_injective
    (g : Additive (G →ₐ[K] L) →+[L ≃ₐ[K] L] X)
    (hg : Function.Surjective g) :
    Function.Injective (canonicalEmbeddingAlgHom K L G X g) := by
  intro a b hab
  ext x
  obtain ⟨p, rfl⟩ := hg x
  have hp := congrArg (fun z : G ↦ p z) hab
  simpa [eval_canonicalEmbeddingAlgHom] using hp

lemma tensorEquiv_map_evalAlgEquiv
    [Module.Finite K G]
    (z : G ⊗[K] G) (p q : G →ₐ[K] L) :
    tensorEquiv K L (G →ₐ[K] L) (G →ₐ[K] L)
        (TensorProduct.map
          (genericEvalAlgEquiv K L G).toLinearMap
          (genericEvalAlgEquiv K L G).toLinearMap z) (p, q) =
      Algebra.TensorProduct.lift p q (fun _ _ ↦ Commute.all _ _) z := by
  induction z with
  | zero => simp
  | add z₁ z₂ hz₁ hz₂ => simpa using congrArg₂ (· + ·) hz₁ hz₂
  | tmul a b => rfl

omit [Algebra.Etale K G] in
lemma tensorEquiv_map_reindexPoints
    [Module.Finite K G] [Finite X] [ContinuousSMulDiscrete (L ≃ₐ[K] L) X]
    (g : Additive (G →ₐ[K] L) →+[L ≃ₐ[K] L] X)
    (z : (X →[L ≃ₐ[K] L] L) ⊗[K] (X →[L ≃ₐ[K] L] L))
    (p q : G →ₐ[K] L) :
    tensorEquiv K L (G →ₐ[K] L) (G →ₐ[K] L)
        (TensorProduct.map
          (MulActionHom.compLeftAlgHom (L ≃ₐ[K] L) K L
            (forwardPointsMulActionHom K L G X g)).toLinearMap
          (MulActionHom.compLeftAlgHom (L ≃ₐ[K] L) K L
            (forwardPointsMulActionHom K L G X g)).toLinearMap z) (p, q) =
      tensorEquiv K L X X z
        (g (Additive.ofMul p), g (Additive.ofMul q)) := by
  induction z with
  | zero => simp
  | add z₁ z₂ hz₁ hz₂ => simpa using congrArg₂ (· + ·) hz₁ hz₂
  | tmul a b => rfl

/-- The canonical function-algebra embedding as a coalgebra homomorphism. -/
noncomputable def canonicalEmbeddingCoalgHom
    [Module.Finite K G] [Finite X]
    [ContinuousSMulDiscrete (L ≃ₐ[K] L) X]
    (g : Additive (G →ₐ[K] L) →+[L ≃ₐ[K] L] X) :
    (X →[L ≃ₐ[K] L] L) →ₗc[K] G := by
  let P := G →ₐ[K] L
  let BX := X →[L ≃ₐ[K] L] L
  letI : Bialgebra K BX := bialgebra K L X
  refine
    { __ := (canonicalEmbeddingAlgHom K L G X g).toLinearMap
      counit_comp := ?_
      map_comp_comul := ?_ }
  · apply LinearMap.ext
    intro a
    apply (algebraMap K L).injective
    change algebraMap K L (Coalgebra.counit (R := K)
      (canonicalEmbeddingAlgHom K L G X g a)) =
        algebraMap K L (counitAlgHom K L X a)
    rw [algebraMap_counitAlgHom]
    change (1 : G →ₐ[K] L) (canonicalEmbeddingAlgHom K L G X g a) = a 0
    rw [eval_canonicalEmbeddingAlgHom]
    rw [show g (Additive.ofMul (1 : G →ₐ[K] L)) = 0 from g.map_zero]
  · apply LinearMap.ext
    intro a
    let e := genericEvalAlgEquiv K L G
    have hinj : Function.Injective
        (TensorProduct.map e.toLinearMap e.toLinearMap) := by
      apply Function.LeftInverse.injective
        (g := TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap)
      intro z
      rw [TensorProduct.map_map]
      have hcomp : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by
        apply LinearMap.ext
        intro x
        exact e.symm_apply_apply x
      rw [hcomp]
      simp only [TensorProduct.map_id]
      rfl
    apply hinj
    apply (tensorEquiv K L P P).injective
    ext pq
    rcases pq with ⟨p, q⟩
    change tensorEquiv K L P P
        (TensorProduct.map e.toLinearMap e.toLinearMap
          (TensorProduct.map
            (canonicalEmbeddingAlgHom K L G X g).toLinearMap
            (canonicalEmbeddingAlgHom K L G X g).toLinearMap
            (comulAlgHom K L X a))) (p, q) =
      tensorEquiv K L P P
        (TensorProduct.map e.toLinearMap e.toLinearMap
          (Coalgebra.comul (R := K)
            (canonicalEmbeddingAlgHom K L G X g a))) (p, q)
    rw [TensorProduct.map_map]
    have hcomp : e.toLinearMap.comp
        (canonicalEmbeddingAlgHom K L G X g).toLinearMap =
      (MulActionHom.compLeftAlgHom (L ≃ₐ[K] L) K L
        (forwardPointsMulActionHom K L G X g)).toLinearMap := by
      apply LinearMap.ext
      intro b
      exact e.apply_symm_apply _
    rw [hcomp]
    rw [tensorEquiv_map_reindexPoints, comulAlgHom_eval]
    rw [tensorEquiv_map_evalAlgEquiv]
    change a (g (Additive.ofMul p) + g (Additive.ofMul q)) =
      (p * q) (canonicalEmbeddingAlgHom K L G X g a)
    rw [eval_canonicalEmbeddingAlgHom]
    rw [show Additive.ofMul (p * q) =
      Additive.ofMul p + Additive.ofMul q from rfl, g.map_add]

/-- The canonical function-algebra embedding as a bialgebra homomorphism. -/
noncomputable def canonicalEmbeddingBialgHom
    [Module.Finite K G] [Finite X]
    [ContinuousSMulDiscrete (L ≃ₐ[K] L) X]
    (g : Additive (G →ₐ[K] L) →+[L ≃ₐ[K] L] X) :
    (X →[L ≃ₐ[K] L] L) →ₐc[K] G := by
  letI : Bialgebra K (X →[L ≃ₐ[K] L] L) := bialgebra K L X
  exact
    { __ := canonicalEmbeddingAlgHom K L G X g
      __ := canonicalEmbeddingCoalgHom K L G X g }

end GaloisModule.GenericFiber
namespace GaloisModule

open HopfAlgebra.IntegralClosure

variable (R K L X : Type u) [CommRing R] [Field K] [Field L]
variable [Algebra R K] [Algebra K L]
variable [IsDedekindDomain R] [IsFractionRing R K]
variable [IsGalois K L] [IsSepClosed L]
variable [AddCommGroup X] [DistribMulAction (L ≃ₐ[K] L) X]

lemma IsFiniteFlat.quotient {Y : Type u} [AddCommGroup Y]
    [DistribMulAction (L ≃ₐ[K] L) Y]
    (hX : IsFiniteFlat R K L X)
    (q : X →+[L ≃ₐ[K] L] Y) (hq : Function.Surjective q) :
    IsFiniteFlat R K L Y := by
  have hY := hX.quotient_finite_continuous R K L X q hq
  let _ : Finite Y := hY.1
  let _ : ContinuousSMulDiscrete (L ≃ₐ[K] L) Y := hY.2
  rcases hX with ⟨H, _, _, hH, hEtale, f, hf⟩
  let _ : Algebra.Etale K (K ⊗[R] H) := hEtale
  let G := K ⊗[R] H
  let _ : Module.Free K G := Module.Free.of_divisionRing K G
  let _ : Module.Finite K G :=
    Algebra.FormallyUnramified.finite_of_free K G
  let g : Additive (G →ₐ[K] L) →+[L ≃ₐ[K] L] Y := q.comp f
  have hg : Function.Surjective g := hq.comp hf.2
  let BY := Y →[L ≃ₐ[K] L] L
  let _ : HopfAlgebra K BY := GenericFiber.hopfAlgebra K L Y
  let i : BY →ₐc[K] G := GenericFiber.canonicalEmbeddingBialgHom K L G Y g
  have hi : Function.Injective i :=
    GenericFiber.canonicalEmbeddingAlgHom_injective K L G Y g hg
  let C : Subalgebra K G := i.toAlgHom.range
  have hC : IsGenericHopfSubalgebra R K H C :=
    isGenericHopfSubalgebra_range R K H BY i
  let D := contraction R K H C
  let _ : HopfAlgebra R D := contractionHopfAlgebra R K H C hC
  let _ : Module.Finite R D := contraction_finite R K H C
  let _ : Module.Flat R D := contraction_flat R K H C
  let _ : HopfAlgebra.IsFiniteFlat R D := ⟨⟩
  let dvalCoalg : D →ₗc[R] H :=
    { __ := D.val.toLinearMap
      counit_comp := by rfl
      map_comp_comul := by
        apply LinearMap.ext
        intro d
        exact contractionComul_compat R K H C hC d }
  let dval : D →ₐc[R] H := { __ := D.val, __ := dvalCoalg }
  let k : K ⊗[R] D →ₐc[K] G :=
    Bialgebra.TensorProduct.map (BialgHom.id K K) dval
  have hk_apply (x : K ⊗[R] D) :
      k x = localizedInclusion R K H C x := by
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · rfl
    · intro a d
      rfl
    · intro x y hx hy
      simpa only [map_add] using congrArg₂ (· + ·) hx hy
  have hk : Function.Injective k := by
    intro x y hxy
    apply (baseChangeMap_bijective R K H C).1
    apply Subtype.ext
    rw [← localizedInclusion_eq_val_baseChangeMap,
      ← localizedInclusion_eq_val_baseChangeMap]
    rw [← hk_apply, ← hk_apply]
    exact hxy
  let jAlg : BY →ₐ[K] K ⊗[R] D :=
    (baseChangeEquiv R K H C).symm.toAlgHom.comp i.toAlgHom.rangeRestrict
  have hcomp : k.toAlgHom.comp jAlg = i.toAlgHom := by
    apply AlgHom.ext
    intro a
    change k (jAlg a) = i a
    rw [hk_apply, localizedInclusion_eq_val_baseChangeMap]
    change ((baseChangeEquiv R K H C)
      ((baseChangeEquiv R K H C).symm (i.toAlgHom.rangeRestrict a))).1 = i a
    rw [AlgEquiv.apply_symm_apply]
    rfl
  let j : BY →ₐc[K] K ⊗[R] D :=
    BialgHom.factorOfInjective k hk i jAlg hcomp
  have hj_inj : Function.Injective j := by
    intro a b hab
    apply hi
    have ha : k (j a) = i a := AlgHom.congr_fun hcomp a
    have hb : k (j b) = i b := AlgHom.congr_fun hcomp b
    exact ha.symm.trans ((congrArg k hab).trans hb)
  have hj_surj : Function.Surjective j := by
    intro x
    let c : C := baseChangeEquiv R K H C x
    obtain ⟨a, ha⟩ := c.property
    refine ⟨a, ?_⟩
    apply hk
    calc
      k (j a) = i a := AlgHom.congr_fun hcomp a
      _ = c.1 := ha
      _ = localizedInclusion R K H C x := by
        rw [localizedInclusion_eq_val_baseChangeMap]
        rfl
      _ = k x := (hk_apply x).symm
  let je : BY ≃ₐc[K] K ⊗[R] D :=
    BialgEquiv.ofBijective j ⟨hj_inj, hj_surj⟩
  let _ : Algebra.Etale K (K ⊗[R] D) :=
    Algebra.Etale.of_equiv je.toAlgEquiv
  let p : Additive (K ⊗[R] D →ₐ[K] L) →+[L ≃ₐ[K] L]
      Additive (BY →ₐ[K] L) := BialgHom.precompPoints j
  have hp : Function.Bijective p := by
    constructor
    · intro a b hab
      change a.toMul = b.toMul
      ext x
      obtain ⟨y, rfl⟩ := hj_surj x
      have hy := congrArg Additive.toMul hab
      exact AlgHom.congr_fun hy y
    · intro a
      let b : K ⊗[R] D →ₐ[K] L :=
        a.toMul.comp je.symm.toAlgEquiv.toAlgHom
      refine ⟨Additive.ofMul b, ?_⟩
      change Additive.ofMul (b.comp j.toAlgHom) = a
      apply Additive.toMul.injective
      apply AlgHom.ext
      intro x
      exact congrArg a.toMul (je.symm_apply_apply x)
  let result : Additive (K ⊗[R] D →ₐ[K] L) →+[L ≃ₐ[K] L] Y :=
    (GenericFiber.pointsEquivariantAddEquiv K L Y).comp p
  refine ⟨D, inferInstance, inferInstance, inferInstance, inferInstance,
    result, ?_⟩
  exact (GenericFiber.pointsEquivariantAddEquiv_bijective K L Y).comp hp

end GaloisModule
