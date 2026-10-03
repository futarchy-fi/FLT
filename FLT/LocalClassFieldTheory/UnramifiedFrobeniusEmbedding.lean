/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.IntegralFrobeniusBaseChange
public import FLT.LocalClassFieldTheory.UnramifiedIntegralModel

/-!
# Frobenius under embeddings of finite unramified stages

The field embedding induces a local embedding of canonical integral closures.
The integral comparison then gives the residue-degree Frobenius power.
-/

@[expose] public noncomputable section

universe u

namespace LocalClassFieldTheory

open IsLocalRing

variable (R S K L E F : Type u)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra S L] [IsFractionRing S L]
  [Field E] [Algebra K E] [Algebra R E] [IsScalarTower R K E]
  [Field F] [Algebra L F] [Algebra S F] [IsScalarTower S L F]
  [Algebra K F] [Algebra R F] [IsScalarTower R K F] [IsScalarTower R S F]
  [Finite (ResidueField R)] [Finite (ResidueField S)]
  [FiniteDimensional K E] [IsGalois K E] [FiniteDimensional L F] [IsGalois L F]
  [IsDiscreteValuationRing (integralClosure R E)]
  [IsDiscreteValuationRing (integralClosure S F)]
  [Algebra.FormallyUnramified R (integralClosure R E)]
  [Algebra.FormallyUnramified S (integralClosure S F)]

local notation "A" => integralClosure R E
local notation "B" => integralClosure S F

variable [IsFractionRing (integralClosure R E) E] [IsFractionRing (integralClosure S F) F]
  [Module.Finite R (integralClosure R E)] [Module.Finite S (integralClosure S F)]
  [IsLocalHom (algebraMap R (integralClosure R E))]
  [IsLocalHom (algebraMap S (integralClosure S F))]

/-- A finite-stage field embedding carries integral elements into the new integral closure. -/
def unramifiedIntegralEmbedding (i : E →ₐ[K] F) : A →+* B where
  toFun x := ⟨i x, (x.property.map (i.restrictScalars R)).tower_top⟩
  map_zero' := Subtype.ext (map_zero i)
  map_one' := Subtype.ext (map_one i)
  map_add' x y := Subtype.ext (map_add i x.val y.val)
  map_mul' x y := Subtype.ext (map_mul i x.val y.val)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsDomain S] [IsDiscreteValuationRing S]
  [FaithfulSMul R S] [IsFractionRing R K] [Finite (ResidueField R)] [Finite (ResidueField S)]
  [FiniteDimensional K E] [IsGalois K E] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
  [Algebra.FormallyUnramified R A] [Algebra.FormallyUnramified S B]
  [IsFractionRing A E] [IsFractionRing B F] [Module.Finite R A]
  [IsLocalHom (algebraMap R A)] [IsLocalHom (algebraMap S B)] in
/-- The integral embedding is local, even when the base extension is ramified. -/
theorem unramifiedIntegralEmbedding_isLocal (i : E →ₐ[K] F) :
    IsLocalHom (unramifiedIntegralEmbedding R S K E F i) := by
  let j := unramifiedIntegralEmbedding R S K E F i
  let : Algebra A B := j.toAlgebra
  let : Algebra R B := ((algebraMap S B).comp (algebraMap R S)).toAlgebra
  let : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun r => by
    apply Subtype.ext
    change algebraMap S F (algebraMap R S r) = i (algebraMap R E r)
    rw [← IsScalarTower.algebraMap_apply]
    exact (i.restrictScalars R).commutes r |>.symm
  let : Module.Finite R B := Module.Finite.trans S B
  let : Algebra.IsIntegral A B :=
    ⟨fun x => (Algebra.IsIntegral.isIntegral (R := R) x).tower_top⟩
  exact (algebraMap_isIntegral_iff.mpr inferInstance).isLocalHom
    (fun x y h => Subtype.ext (i.injective (congrArg Subtype.val h)))

omit [Module.Finite R A] in
/-- A field action commuting with the new-base Frobenius is the residue-degree
power of the old-base Frobenius. -/
theorem unramifiedFrobenius_embedding (i : E →ₐ[K] F) (σ : Gal(E/K))
    (hi : ∀ x : E, i (σ x) = arithmeticFrobenius S B L F (i x)) :
    σ = arithmeticFrobenius R A K E ^
      Module.finrank (ResidueField R) (ResidueField S) := by
  let : IsLocalHom (algebraMap R S) :=
    (algebraMap_isIntegral_iff.mpr inferInstance).isLocalHom
      (FaithfulSMul.algebraMap_injective R S)
  let j := unramifiedIntegralEmbedding R S K E F i
  let : IsLocalHom j := unramifiedIntegralEmbedding_isLocal R S K E F i
  apply integralFrobenius_baseChange R S A B K L E F j σ
  intro x
  apply Subtype.ext
  change i (algebraMap A E (galRestrict R K E A σ x)) =
    algebraMap B F (galRestrict S L F B (arithmeticFrobenius S B L F) (j x))
  rw [algebraMap_galRestrict_apply, algebraMap_galRestrict_apply]
  exact hi x

end LocalClassFieldTheory
