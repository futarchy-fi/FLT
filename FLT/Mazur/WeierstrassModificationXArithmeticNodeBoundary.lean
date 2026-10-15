/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXLaurentNodeRestriction
public import FLT.Mazur.WeierstrassModificationXArithmeticTensorNodes
public import FLT.Mazur.WeierstrassModificationXTensorLaurentEvaluation

/-!
# Original arithmetic tensor boundaries restrict the full initial nodes

The tensor comparison retains both original Laurent maps on all functions.
Their source is the same constructed node restriction, with its corrected parameter.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (π : R) (m : ℕ)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (ha : IsUnit W.a₁) (h2 : π ∣ W.a₂) (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6)
  (hs : π ∣ s)
local notation "Q" => Quotient R π m
local notation "q" => algebraMap R Q
local notation "J" => ideal Q (parameter R π m)
local notation "r₀" => polynomialSlopeRoot (W.map q) (q b3) (q b4) (q b6) J
  (arithmeticParameterIdeal_nilpotent π m) (ha.map q)
  (arithmeticCoefficient_mem π m h2) (arithmeticCoefficient_mem π m h3)
  (arithmeticCoefficient_mem π m h4) (arithmeticCoefficient_mem π m h6)
local notation "hr₀" => polynomialSlopeRoot_equation (W.map q) (q b3) (q b4) (q b6) J
  (arithmeticParameterIdeal_nilpotent π m) (ha.map q)
  (arithmeticCoefficient_mem π m h2) (arithmeticCoefficient_mem π m h3)
  (arithmeticCoefficient_mem π m h4) (arithmeticCoefficient_mem π m h6)
local notation "hm₀" => polynomialSlopeRoot_mem (W.map q) (q b3) (q b4) (q b6) J
  (arithmeticParameterIdeal_nilpotent π m) (ha.map q)
  (arithmeticCoefficient_mem π m h2) (arithmeticCoefficient_mem π m h3)
  (arithmeticCoefficient_mem π m h4) (arithmeticCoefficient_mem π m h6)
local notation "L" => PolynomialNodeOpen (W.map q) (q s)
local notation "G" => laurentNodeRestriction (W.map q) (q s) (q b3) (q b4) (q b6) J
  (arithmeticParameterIdeal_nilpotent π m) (ha.map q) (arithmeticCoefficient_mem π m hs)
  (arithmeticCoefficient_mem π m h2) (arithmeticCoefficient_mem π m h3)
  (arithmeticCoefficient_mem π m h4) (arithmeticCoefficient_mem π m h6)
local notation "v₀" => laurentBranchSlope (W.map q) (q s) (q b3) (q b4) (q b6) J
  (arithmeticParameterIdeal_nilpotent π m) (ha.map q) (arithmeticCoefficient_mem π m hs)
  (arithmeticCoefficient_mem π m h2) (arithmeticCoefficient_mem π m h3)
  (arithmeticCoefficient_mem π m h4) (arithmeticCoefficient_mem π m h6)
local notation "hv₀" => laurentBranchSlope_equation (W.map q) (q s) (q b3) (q b4) (q b6) J
  (arithmeticParameterIdeal_nilpotent π m) (ha.map q) (arithmeticCoefficient_mem π m hs)
  (arithmeticCoefficient_mem π m h2) (arithmeticCoefficient_mem π m h3)
  (arithmeticCoefficient_mem π m h4) (arithmeticCoefficient_mem π m h6)

/-- The constructed full-node restriction on the original arithmetic Laurent parameter. -/
def arithmeticInitialNodeRestriction : Spec (.of Q[T;T⁻¹]) ⟶ Spec (.of L) :=
  Spec.map (CommRingCat.ofHom (G).toRingHom)

/-- The first tensor node restriction is exactly the original small Laurent tensor map. -/
@[reassoc] theorem arithmeticInitialTensorNode_boundary :
    arithmeticInitialNodeRestriction π m W s b3 b4 b6 ha h2 h3 h4 h6 hs ≫
      arithmeticInitialTensorNodeChart π m W s b3 b4 b6 ha h2 h3 h4 h6 =
        Spec.map (CommRingCat.ofHom
          (tensorLaurentSlopeEvaluation W s b3 b4 b6 Q (v₀ false) (hv₀ false)).toRingHom) := by
  rw [arithmeticInitialTensorNodeChart, ← Category.assoc]
  change (Spec.map (CommRingCat.ofHom (G).toRingHom) ≫
    polynomialNodeChart (W.map q) (q s) (q b3) (q b4) (q b6) r₀ hr₀ J
      (arithmeticParameterIdeal_nilpotent π m) hm₀ (arithmeticCoefficient_mem π m h3)) ≫ _ = _
  rw [laurentNodeRestriction_first_spec]
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  rfl

/-- The opposite tensor restriction is exactly the original opposite Laurent tensor map. -/
@[reassoc] theorem arithmeticOppositeInitialTensorNode_boundary :
    arithmeticInitialNodeRestriction π m W s b3 b4 b6 ha h2 h3 h4 h6 hs ≫
      arithmeticOppositeInitialTensorNodeChart π m W s b3 b4 b6 ha h2 h3 h4 h6 =
        Spec.map (CommRingCat.ofHom
          (tensorLaurentSlopeEvaluation W s b3 b4 b6 Q (v₀ true) (hv₀ true)).toRingHom) := by
  rw [arithmeticOppositeInitialTensorNodeChart, ← Category.assoc]
  change (Spec.map (CommRingCat.ofHom (G).toRingHom) ≫
    polynomialOppositeNodeChart (W.map q) (q s) (q b3) (q b4) (q b6) r₀ hr₀ J
      (arithmeticParameterIdeal_nilpotent π m) hm₀ (arithmeticCoefficient_mem π m h3)) ≫ _ = _
  rw [laurentNodeRestriction_opposite_spec]
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  rfl

end FLT.Mazur.WeierstrassModificationX
