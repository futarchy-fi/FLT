/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.GroupScheme.FiniteFlat

/-!
# Finite-flat subobjects

Schematic closure of a generic subgroup is a finite-flat Hopf quotient over a
Dedekind domain. Its generic points recover the original subgroup equivariantly.
-/

@[expose] public section

open scoped TensorProduct nonZeroDivisors

universe u

namespace GaloisModule

variable (R K L X : Type u) [CommRing R] [Field K] [Field L]
variable [Algebra R K] [Algebra K L]
variable [AddCommGroup X] [DistribMulAction (L ≃ₐ[K] L) X]

/-- An equivariantly embedded subgroup of finite-flat points is finite and continuous. -/
lemma IsFiniteFlat.subobject_finite_continuous {Y : Type u} [AddCommGroup Y]
    [DistribMulAction (L ≃ₐ[K] L) Y]
    (hX : IsFiniteFlat R K L X)
    (i : Y →+[L ≃ₐ[K] L] X) (hi : Function.Injective i) :
    Finite Y ∧ ContinuousSMulDiscrete (L ≃ₐ[K] L) Y := by
  let _ : Finite X := hX.finite R K L X
  let _ : ContinuousSMulDiscrete (L ≃ₐ[K] L) X := hX.continuousSMulDiscrete R K L X
  refine ⟨Finite.of_injective i hi, ⟨fun y z ↦ ?_⟩⟩
  convert ContinuousSMulDiscrete.isOpen_smul_eq (L ≃ₐ[K] L) (i y) (i z) using 1
  ext σ
  change (σ • y = z) ↔ (σ • i y = i z)
  rw [← map_smul, hi.eq_iff]

end GaloisModule

namespace HopfAlgebra.SchematicClosure

open HopfAlgebra.IntegralClosure

variable (R K H B : Type u) [CommRing R] [Field K] [Algebra R K]
variable [IsDedekindDomain R] [IsFractionRing R K]
variable [CommRing H] [HopfAlgebra R H] [CommRing B] [HopfAlgebra K B]
variable [Algebra R B] [IsScalarTower R K B]

/-- Restrict a morphism out of the generic fibre to the integral coordinate ring. -/
noncomputable def integralMap (p : K ⊗[R] H →ₐc[K] B) : H →ₐ[R] B :=
  (p.toAlgHom.restrictScalars R).comp Algebra.TensorProduct.includeRight

/-- The equations defining schematic closure are the integral kernel. -/
noncomputable def ideal (p : K ⊗[R] H →ₐc[K] B) : Ideal H :=
  RingHom.ker (integralMap R K H B p).toRingHom

/-- The quotient coordinate ring embeds in the generic quotient. -/
noncomputable def quotientMap (p : K ⊗[R] H →ₐc[K] B) : (H ⧸ ideal R K H B p) →ₐ[R] B :=
  Ideal.Quotient.liftₐ _ (integralMap R K H B p) (by intro x hx; exact hx)

omit [IsDedekindDomain R] [IsFractionRing R K] in
lemma quotientMap_injective (p : K ⊗[R] H →ₐc[K] B) :
    Function.Injective (quotientMap R K H B p) := by
  exact RingHom.kerLift_injective (integralMap R K H B p).toRingHom

omit [IsDedekindDomain R] in
/-- The tensor comparison for a generic morphism agrees with restriction to integral tensors. -/
lemma tensor_integralMap (p : K ⊗[R] H →ₐc[K] B) (z : H ⊗[R] H) :
    (IsLocalization.moduleTensorEquiv R⁰ K B B).symm
      (TensorProduct.map (integralMap R K H B p).toLinearMap
        (integralMap R K H B p).toLinearMap z) =
    TensorProduct.map p.toLinearMap p.toLinearMap
      ((baseChangeTensorEquiv R K H H).symm (1 ⊗ₜ[R] z)) := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    simp [integralMap, baseChangeTensorEquiv, IsLocalization.moduleTensorEquiv,
      TensorProduct.equivOfCompatibleSMul, BialgHom.toCoalgHom_apply]
  | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy]

/-- Schematic closure of a generic Hopf quotient is again a Hopf quotient. -/
lemma isHopfIdeal (p : K ⊗[R] H →ₐc[K] B) :
    (ideal R K H B p).IsHopfIdeal R := by
  let I := ideal R K H B p
  let q : Ideal.ModuleQuotient (I.restrictScalars R) →ₗ[R] B :=
    (I.restrictScalars R).liftQ (integralMap R K H B p).toLinearMap
      (by intro x hx; exact hx)
  have hq : Function.Injective q := quotientMap_injective R K H B p
  let _ : Module.IsTorsionFree R B := Module.IsTorsionFree.trans K
  let _ : Module.IsTorsionFree R (Ideal.ModuleQuotient (I.restrictScalars R)) :=
    Function.Injective.moduleIsTorsionFree q hq (fun r x ↦ q.map_smul r x)
  let _ : Module.Flat R (Ideal.ModuleQuotient (I.restrictScalars R)) := inferInstance
  let _ : Module.Flat R B := inferInstance
  have ht := TensorProduct.map_injective_of_flat_flat q q hq hq
  let _ : (I.restrictScalars R).IsCoideal := by
    constructor
    · intro x hx
      apply IsFractionRing.injective R K
      have hp : p (Algebra.TensorProduct.includeRight x) = 0 := hx
      have hc := CoalgHomClass.counit_comp_apply p (Algebra.TensorProduct.includeRight x)
      rw [hp, map_zero] at hc
      simpa using hc.symm
    · intro x hx
      apply ht
      rw [map_zero, TensorProduct.map_map]
      change TensorProduct.map (integralMap R K H B p).toLinearMap
        (integralMap R K H B p).toLinearMap (Coalgebra.comul x) = 0
      apply (IsLocalization.moduleTensorEquiv R⁰ K B B).symm.injective
      rw [map_zero, tensor_integralMap]
      change TensorProduct.map p.toLinearMap p.toLinearMap
        ((baseChangeTensorEquiv R K H H).symm
          (Algebra.TensorProduct.includeRight (Coalgebra.comul x))) = 0
      rw [← baseChange_comul_includeRight R K H x, AlgEquiv.symm_apply_apply]
      have hp : p (Algebra.TensorProduct.includeRight x) = 0 := hx
      exact (CoalgHomClass.map_comp_comul_apply p
        (Algebra.TensorProduct.includeRight x)).trans (by rw [hp, map_zero])
  constructor
  intro x hx
  change p (Algebra.TensorProduct.includeRight (antipode R x)) = 0
  rw [← baseChange_antipode_includeRight R K H x]
  have hp : p (Algebra.TensorProduct.includeRight x) = 0 := hx
  have hs := LinearMap.congr_fun (BialgHom.antipode_comp p)
    (Algebra.TensorProduct.includeRight x)
  change antipode K (p (Algebra.TensorProduct.includeRight x)) =
    p (antipode K (Algebra.TensorProduct.includeRight x)) at hs
  rw [← hs, hp, map_zero]

end HopfAlgebra.SchematicClosure

namespace MulActionHom

/-- Extend equivariant functions by zero outside an invariant embedded subset. -/
lemma compLeftAlgHom_surjective_of_injective
    {G X Y S T : Type*} [Group G] [MulAction G X] [MulAction G Y]
    [CommSemiring S] [Semiring T] [Algebra S T] [MulSemiringAction G T]
    [SMulCommClass G S T] (i : Y →[G] X) (hi : Function.Injective i) :
    Function.Surjective (compLeftAlgHom G S T i) := by
  classical
  intro f
  let g : X → T := fun x ↦ if h : ∃ y, i y = x then f h.choose else 0
  have hg (y : Y) : g (i y) = f y := by
    dsimp [g]
    split
    · rename_i h
      exact congrArg f (hi h.choose_spec)
    · rename_i h
      exact (h ⟨y, rfl⟩).elim
  have hz (x : X) (h : ¬ ∃ y, i y = x) : g x = 0 := by simp [g, h]
  refine ⟨⟨g, ?_⟩, ?_⟩
  · intro σ x
    by_cases hx : ∃ y, i y = x
    · obtain ⟨y, rfl⟩ := hx
      rw [← map_smul, hg, hg, map_smul]
      rfl
    · have hs : ¬ ∃ y, i y = σ • x := by
        rintro ⟨y, hy⟩
        exact hx ⟨σ⁻¹ • y, by rw [map_smul, hy, inv_smul_smul]⟩
      rw [hz _ hs, hz _ hx, smul_zero]
  · ext y
    exact hg y

end MulActionHom

namespace GaloisModule.GenericFiber

variable (K L G X : Type u) [Field K] [Field L] [Algebra K L]
variable [IsGalois K L] [IsSepClosed L]
variable [CommRing G] [HopfAlgebra K G] [Algebra.Etale K G]
variable [AddCommGroup X] [DistribMulAction (L ≃ₐ[K] L) X]

/-- A bijective identification of points makes the canonical embedding an isomorphism. -/
lemma canonicalEmbeddingAlgHom_bijective
    (g : Additive (G →ₐ[K] L) →+[L ≃ₐ[K] L] X) (hg : Function.Bijective g) :
    Function.Bijective (canonicalEmbeddingAlgHom K L G X g) := by
  refine ⟨canonicalEmbeddingAlgHom_injective K L G X g hg.2, ?_⟩
  apply (genericEvalAlgEquiv K L G).symm.surjective.comp
  apply MulActionHom.compLeftAlgHom_surjective_of_injective (S := K)
  intro p q hpq
  exact hg.1 hpq

end GaloisModule.GenericFiber

namespace HopfAlgebra.SchematicClosure

variable (R K H B : Type u) [CommRing R] [Field K] [Algebra R K]
variable [IsDedekindDomain R] [IsFractionRing R K]
variable [CommRing H] [HopfAlgebra R H] [CommRing B] [HopfAlgebra K B]
variable [Algebra R B] [IsScalarTower R K B]

/-- A schematic closure in a finite-flat model is finite flat. -/
lemma isFiniteFlat (p : K ⊗[R] H →ₐc[K] B) (hH : HopfAlgebra.IsFiniteFlat R H) :
    HopfAlgebra.IsFiniteFlat R (H ⧸ ideal R K H B p) := by
  let q := quotientMap R K H B p
  let _ : Module.IsTorsionFree R B := Module.IsTorsionFree.trans K
  let _ : Module.IsTorsionFree R (H ⧸ ideal R K H B p) :=
    Function.Injective.moduleIsTorsionFree q (quotientMap_injective R K H B p)
      (fun r x ↦ q.toLinearMap.map_smul r x)
  exact hH.quotient (ideal R K H B p)

/-- The generic fibre of the schematic closure maps to the prescribed generic quotient. -/
noncomputable def genericMap (p : K ⊗[R] H →ₐc[K] B) :
    K ⊗[R] (H ⧸ ideal R K H B p) →ₐ[K] B :=
  AlgHom.liftEquiv R K _ B (quotientMap R K H B p)

omit [IsDedekindDomain R] in
lemma genericMap_injective (p : K ⊗[R] H →ₐc[K] B) :
    Function.Injective (genericMap R K H B p) := by
  apply IsLocalizedModule.injective_of_map_eq R⁰
    (TensorProduct.mk R K (H ⧸ ideal R K H B p) 1)
    (g := (genericMap R K H B p).toLinearMap.restrictScalars R)
  intro x y hxy
  have hq : quotientMap R K H B p x = quotientMap R K H B p y := by
    simpa [genericMap] using hxy
  exact congrArg (fun z ↦ 1 ⊗ₜ[R] z) (quotientMap_injective R K H B p hq)

/-- Base change of the quotient map on coordinate rings. -/
noncomputable def genericProjection (p : K ⊗[R] H →ₐc[K] B) :
    K ⊗[R] H →ₐ[K] K ⊗[R] (H ⧸ ideal R K H B p) :=
  Algebra.TensorProduct.map (AlgHom.id K K) (Ideal.Quotient.mkₐ R _)

omit [IsDedekindDomain R] [IsFractionRing R K] in
lemma genericMap_comp_projection (p : K ⊗[R] H →ₐc[K] B) :
    (genericMap R K H B p).comp (genericProjection R K H B p) = p.toAlgHom := by
  ext h
  simp [genericMap, genericProjection, quotientMap, integralMap]
  rfl

omit [IsDedekindDomain R] [IsFractionRing R K] in
lemma genericProjection_surjective (p : K ⊗[R] H →ₐc[K] B) :
    Function.Surjective (genericProjection R K H B p) :=
  Algebra.TensorProduct.map_surjective _ _ Function.surjective_id Ideal.Quotient.mk_surjective

omit [IsDedekindDomain R] [IsFractionRing R K] in
lemma genericMap_surjective (p : K ⊗[R] H →ₐc[K] B) (hp : Function.Surjective p) :
    Function.Surjective (genericMap R K H B p) := by
  intro b
  obtain ⟨x, rfl⟩ := hp b
  exact ⟨genericProjection R K H B p x,
    AlgHom.congr_fun (genericMap_comp_projection R K H B p) x⟩

attribute [local instance] isHopfIdeal

/-- The generic comparison preserves the Hopf operations. -/
noncomputable def genericBialgHom (p : K ⊗[R] H →ₐc[K] B) :
    K ⊗[R] (H ⧸ ideal R K H B p) →ₐc[K] B := by
  let π : K ⊗[R] H →ₐc[K] K ⊗[R] (H ⧸ ideal R K H B p) :=
    Bialgebra.TensorProduct.map (BialgHom.id K K) (Bialgebra.Quotient.mkBialgHom _)
  have hπ : Function.Surjective π := genericProjection_surjective R K H B p
  let e := genericMap R K H B p
  have he : e.comp π.toAlgHom = p.toAlgHom := genericMap_comp_projection R K H B p
  have hey (y : K ⊗[R] H) : e (π y) = p y := AlgHom.congr_fun he y
  apply BialgHom.ofAlgHom e
  · apply AlgHom.ext
    intro x
    obtain ⟨y, rfl⟩ := hπ x
    change Coalgebra.counit (e (π y)) = Coalgebra.counit (π y)
    rw [hey y, CoalgHomClass.counit_comp_apply,
      CoalgHomClass.counit_comp_apply]
  · apply AlgHom.ext
    intro x
    obtain ⟨y, rfl⟩ := hπ x
    change TensorProduct.map e.toLinearMap e.toLinearMap (Coalgebra.comul (π y)) =
      Coalgebra.comul (e (π y))
    rw [← CoalgHomClass.map_comp_comul_apply π, TensorProduct.map_map]
    have hel : e.toLinearMap.comp
        (π : (K ⊗[R] H) →ₗ[K] K ⊗[R] (H ⧸ ideal R K H B p)) =
        (p : (K ⊗[R] H) →ₗ[K] B) := by
      apply LinearMap.ext
      exact hey
    rw [hel, hey y]
    exact CoalgHomClass.map_comp_comul_apply p y

end HopfAlgebra.SchematicClosure

namespace GaloisModule

variable (R K L X : Type u) [CommRing R] [Field K] [Field L]
variable [Algebra R K] [Algebra K L]
variable [IsDedekindDomain R] [IsFractionRing R K]
variable [IsGalois K L] [IsSepClosed L]
variable [AddCommGroup X] [DistribMulAction (L ≃ₐ[K] L) X]

/-- A Galois-stable subgroup of a finite-flat Galois module has a finite-flat model,
obtained by schematic closure in any finite-flat model of the ambient module. -/
theorem IsFiniteFlat.subobject {Y : Type u} [AddCommGroup Y]
    [DistribMulAction (L ≃ₐ[K] L) Y]
    (hX : IsFiniteFlat R K L X)
    (i : Y →+[L ≃ₐ[K] L] X) (hi : Function.Injective i) :
    IsFiniteFlat R K L Y := by
  let _ : Finite X := hX.finite R K L X
  let _ : ContinuousSMulDiscrete (L ≃ₐ[K] L) X := hX.continuousSMulDiscrete R K L X
  have hY := hX.subobject_finite_continuous R K L X i hi
  let _ : Finite Y := hY.1
  let _ : ContinuousSMulDiscrete (L ≃ₐ[K] L) Y := hY.2
  rcases hX with ⟨H, _, _, hH, hEtale, f, hf⟩
  let G := K ⊗[R] H
  let _ : Module.Finite K G := Algebra.FormallyUnramified.finite_of_free K G
  let BX := X →[L ≃ₐ[K] L] L
  let BY := Y →[L ≃ₐ[K] L] L
  let _ : HopfAlgebra K BX := GenericFiber.hopfAlgebra K L X
  let _ : HopfAlgebra K BY := GenericFiber.hopfAlgebra K L Y
  let e : BX ≃ₐc[K] G := BialgEquiv.ofBijective
    (GenericFiber.canonicalEmbeddingBialgHom K L G X f)
    (GenericFiber.canonicalEmbeddingAlgHom_bijective K L G X f hf)
  let p : G →ₐc[K] BY :=
    (GenericFiber.pullbackBialgHom K L Y X i).comp e.symm.toBialgHom
  have hp : Function.Surjective p :=
    (MulActionHom.compLeftAlgHom_surjective_of_injective (S := K) (T := L)
      i.toMulActionHom hi).comp e.symm.surjective
  let _ : Algebra R BY := Algebra.compHom BY (algebraMap R K)
  let _ : IsScalarTower R K BY := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  let I := HopfAlgebra.SchematicClosure.ideal R K H BY p
  let _ : I.IsHopfIdeal R := HopfAlgebra.SchematicClosure.isHopfIdeal R K H BY p
  let D := H ⧸ I
  let _ : HopfAlgebra.IsFiniteFlat R D :=
    HopfAlgebra.SchematicClosure.isFiniteFlat R K H BY p hH
  let j : K ⊗[R] D →ₐc[K] BY := HopfAlgebra.SchematicClosure.genericBialgHom R K H BY p
  have hj : Function.Bijective j :=
    ⟨HopfAlgebra.SchematicClosure.genericMap_injective R K H BY p,
      HopfAlgebra.SchematicClosure.genericMap_surjective R K H BY p hp⟩
  let je : K ⊗[R] D ≃ₐc[K] BY := BialgEquiv.ofBijective j hj
  let _ : Algebra.Etale K (K ⊗[R] D) := Algebra.Etale.of_equiv je.symm.toAlgEquiv
  let a : Additive (K ⊗[R] D →ₐ[K] L) →+[L ≃ₐ[K] L]
      Additive (BY →ₐ[K] L) := BialgHom.precompPoints je.symm.toBialgHom
  have ha : Function.Bijective a := by
    constructor
    · intro b c hbc
      change b.toMul = c.toMul
      ext x
      obtain ⟨y, rfl⟩ := je.symm.surjective x
      exact AlgHom.congr_fun (congrArg Additive.toMul hbc) y
    · intro b
      refine ⟨Additive.ofMul (b.toMul.comp je.toAlgEquiv.toAlgHom), ?_⟩
      apply Additive.toMul.injective
      apply AlgHom.ext
      intro x
      exact congrArg b.toMul (je.apply_symm_apply x)
  refine ⟨D, inferInstance, inferInstance, inferInstance, inferInstance,
    (GenericFiber.pointsEquivariantAddEquiv K L Y).comp a, ?_⟩
  exact (GenericFiber.pointsEquivariantAddEquiv_bijective K L Y).comp ha

end GaloisModule
