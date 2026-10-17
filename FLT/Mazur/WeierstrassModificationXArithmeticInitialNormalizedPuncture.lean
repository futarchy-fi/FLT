/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXArithmeticPuncture
public import FLT.Mazur.WeierstrassModificationXArithmeticInitialMobius
public import FLT.Mazur.WeierstrassModificationXInitialMobiusLaurentEquiv

/-!
# The complete initial puncture in the normalized smoothing coordinate

The original initial Laurent map carries a nonconstant Mobius parameter.
Its full isomorphism identifies the original D(p) with the normalized puncture.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassModificationX
open PolygonArithmeticStages PolygonSmoothing WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (π : R) (m : ℕ)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (ha : IsUnit W.a₁) (hs : π ∣ s) (h2 : π ∣ W.a₂)
  (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6)
local notation "Q" => Quotient R π m
local notation "q" => algebraMap R Q
local notation "J" => ideal Q (parameter R π m)
local notation "τ" => arithmeticInitialMobiusSmoothing W ha s π m
local notation "P" => arithmeticInitialPunctureInclusion π m W s ha hs
local notation "E" => arithmeticInitialPunctureIso π m W s b3 b4 b6 ha hs h2 h3 h4 h6
local notation "M" => arithmeticInitialMobiusChart W ha s π m

/-- The whole original Laurent parameter in the normalized initial coordinate. -/
def arithmeticInitialMobiusParameter : branchTorus Q ≅ branchTorus Q :=
  initialMobiusLaurentIso (W.map q) (ha.map q) (q s) τ
    (initialTangentSmoothing_factor (W.map q) (ha.map q) (q s))
    (q b3) (q b4) (q b6) J (arithmeticParameterIdeal_nilpotent π m)
    (arithmeticCoefficient_mem π m hs) (arithmeticCoefficient_mem π m h2)
    (arithmeticCoefficient_mem π m h3) (arithmeticCoefficient_mem π m h4)
    (arithmeticCoefficient_mem π m h6)

local notation "B" => arithmeticInitialMobiusParameter π m W s b3 b4 b6 ha hs h2 h3 h4 h6

/-- The complete original initial restriction uses this actual Mobius parameter. -/
@[reassoc] theorem arithmeticInitialMobiusParameter_boundary :
    arithmeticInitialNodeRestriction π m W s b3 b4 b6 ha h2 h3 h4 h6 hs ≫ M =
      (B).hom ≫ leftBranchOpen Q τ :=
  initialMobiusLaurentIso_boundary ..

attribute [local irreducible] arithmeticInitialPunctureIso arithmeticInitialMobiusParameter

/-- The original D(p) is identified with the normalized full left puncture. -/
def arithmeticInitialNormalizedPunctureIso :
    Spec (.of (Localization.Away (NodalFiber.p (q s)))) ≅ branchTorus Q :=
  (E).symm ≪≫ B

local notation "N" => arithmeticInitialNormalizedPunctureIso
  π m W s b3 b4 b6 ha hs h2 h3 h4 h6

/-- The normalized puncture comparison retains the entire original initial diagram. -/
@[reassoc] theorem arithmeticInitialNormalizedPunctureIso_boundary :
    P ≫ M = (N).hom ≫ leftBranchOpen Q τ := by
  simp only [arithmeticInitialNormalizedPunctureIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc]
  rw [← arithmeticInitialPunctureIso_inv_boundary π m W s b3 b4 b6 ha hs h2 h3 h4 h6,
    Category.assoc, arithmeticInitialMobiusParameter_boundary]

/-- Its inverse realizes the standard full puncture inside the actual initial chart. -/
@[reassoc] theorem arithmeticInitialNormalizedPunctureIso_inv_boundary :
    (N).inv ≫ P ≫ M = leftBranchOpen Q τ := by
  rw [arithmeticInitialNormalizedPunctureIso_boundary
    π m W s b3 b4 b6 ha hs h2 h3 h4 h6, Iso.inv_hom_id_assoc]

/-- The two original puncture comparisons retain precisely the full Mobius parameter. -/
@[reassoc] theorem arithmeticInitialNormalizedPunctureIso_inv_comp :
    (N).inv ≫ (E).inv = (B).inv := by
  simp only [arithmeticInitialNormalizedPunctureIso, Iso.trans_inv, Iso.symm_inv,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

end FLT.Mazur.WeierstrassModificationX
