/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.ContinuousTangent
public import FLT.Deformations.FiniteParameterQuotient

/-!
# Continuous tangents stabilize at one finite quotient

Pullback is linear over the original residue field. If the continuous tangent
space is finite, a single proper open quotient has exactly that tangent space.
This does not replace the continuous tangent by an algebraic cotangent of the
original ring.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory IsLocalRing
namespace Deformation.ProartinianCat

variable {O : Type} [CommRing O] [IsLocalRing O] [Finite (ResidueField O)]
  {A B : ProartinianCat O}
local notation "k" => residueField (𝓞 := O)

omit [Finite (ResidueField O)] in
/-- Every coefficient morphism respects the specified residue map. -/
theorem residue_comp_apply (f : A ⟶ B) (a : A) :
    (toResidueField B).hom (f.hom a) = (toResidueField A).hom a :=
  congrArg (fun g : A ⟶ k ↦ g.hom a) (Subsingleton.elim
    (f ≫ toResidueField B) (toResidueField A))

/-- Pullback of continuous tangent functionals along a coefficient morphism. -/
def continuousTangentPullback (f : A ⟶ B) :
    continuousTangent O B →ₗ[k] continuousTangent O A where
  toFun d := ⟨d.1.comp f.hom.toContinuousLinearMap, by
    constructor
    · change d.1 (f.hom 1) = 0
      rw [map_one]
      exact d.2.1
    · intro a b
      change d.1 (f.hom (a * b)) = _
      rw [map_mul, d.2.2, residue_comp_apply, residue_comp_apply]
      rfl⟩
  map_add' d e := by apply Subtype.ext; ext; rfl
  map_smul' c d := by apply Subtype.ext; ext; rfl

/-- Pullback agrees with precomposition of the corresponding dual-number map. -/
theorem tangentToDualNumber_pullback (f : A ⟶ B) (d : continuousTangent O B) :
    tangentToDualNumber O A (continuousTangentPullback f d) =
      f ≫ tangentToDualNumber O B d := by
  apply hom_ext
  apply ContinuousAlgHom.ext
  intro a
  apply TrivSqZeroExt.ext
  · exact (residue_comp_apply f a).symm
  · rfl

omit [Finite (ResidueField O)] in
/-- A surjective coefficient morphism is injective on continuous tangent pullback. -/
theorem continuousTangentPullback_injective (f : A ⟶ B)
    (hf : Function.Surjective f.hom) : Function.Injective (continuousTangentPullback f) := by
  intro d e h
  apply Subtype.ext
  ext b
  obtain ⟨a, rfl⟩ := hf b
  exact congrArg (fun t : continuousTangent O A ↦ t.1 a) h

variable (A)

/-- Finite continuous tangents give finitely many dual-number parameters. -/
theorem finite_dualNumberHom [Finite (continuousTangent O A)] :
    Finite (A ⟶ dualNumberTest O) :=
  Finite.of_equiv _ (continuousTangentEquiv O A)

/-- A proper open quotient retaining all continuous tangents. -/
def tangentOpenIdeal [Finite (continuousTangent O A)] : OpenIdeal A := by
  let := finite_dualNumberHom A
  exact parameterOpenIdeal A (dualNumberTest O)

/-- Tangents of this finite quotient pull back bijectively. -/
theorem tangentOpenIdeal_pullback_bijective [Finite (continuousTangent O A)] :
    Function.Bijective (continuousTangentPullback
      (openIdealQuotientHom A (tangentOpenIdeal A))) := by
  let := finite_dualNumberHom A
  refine ⟨continuousTangentPullback_injective _ Ideal.Quotient.mk_surjective, ?_⟩
  intro d
  let e := parameterQuotientEquiv A (dualNumberTest O)
  let g := e.symm (tangentToDualNumber O A d)
  refine ⟨dualNumberToTangent O _ g, ?_⟩
  apply tangentToDualNumber_injective O A
  rw [tangentToDualNumber_pullback]
  change e (continuousTangentEquiv O _ ((continuousTangentEquiv O _).symm g)) = _
  rw [Equiv.apply_symm_apply]
  exact e.apply_symm_apply _

/-- Every finer open quotient retains the full continuous tangent space as well. -/
theorem tangentOpenIdeal_finer_pullback_bijective [Finite (continuousTangent O A)]
    (J : OpenIdeal A) (hJ : tangentOpenIdeal A ≤ J) :
    Function.Bijective (continuousTangentPullback (openIdealQuotientHom A J)) := by
  let := finite_dualNumberHom A
  refine ⟨continuousTangentPullback_injective _ Ideal.Quotient.mk_surjective, ?_⟩
  intro d
  let f := tangentToDualNumber O A d
  have hker : OpenIdeal.ideal J ≤ RingHom.ker f.hom.toRingHom :=
    (OpenIdeal.ideal_le_ideal hJ).trans (parameterOpenIdeal_le_ker A _ f)
  let g := descendOpenIdeal A (dualNumberTest O) J f hker
  refine ⟨dualNumberToTangent O _ g, ?_⟩
  apply tangentToDualNumber_injective O A
  rw [tangentToDualNumber_pullback]
  change openIdealQuotientHom A J ≫
    (continuousTangentEquiv O _ ((continuousTangentEquiv O _).symm g)) = f
  rw [Equiv.apply_symm_apply]
  exact quotient_descendOpenIdeal A _ J f hker

/-- Linear stabilization over the original residue field at one finite quotient. -/
def tangentQuotientLinearEquiv [Finite (continuousTangent O A)] :
    continuousTangent O (openIdealQuotient A (tangentOpenIdeal A)) ≃ₗ[k]
      continuousTangent O A :=
  LinearEquiv.ofBijective _ (tangentOpenIdeal_pullback_bijective A)

end Deformation.ProartinianCat
