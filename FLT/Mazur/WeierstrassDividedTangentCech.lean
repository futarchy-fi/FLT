/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodeTangentOverlapScheme
public import FLT.Mazur.WeierstrassDividedTangentConjugation

/-!
# The actual finite model on the quadratic Cech overlap

Both coefficient projections of the original overlap induce maps to the
original tangent-cover model. On the identity branch they agree; on the
conjugate branch they are the identity and the constructed model involution.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j ≤ n)
local notation "S" => AdjoinRoot (nodeTangentPolynomial W)
local notation "q" => nodeTangentCover W
local notation "p₁" => pullback.fst q q
local notation "p₂" => pullback.snd q q
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "Y" => finiteGlobalTensorModel hπ data S j hj
local notation "Z" => pullback (p₁ ≫ q) base
local notation "zs" => pullback.fst (p₁ ≫ q) base
local notation "zx" => pullback.snd (p₁ ≫ q) base
local notation "ys" => pullback.fst q base
local notation "yx" => pullback.snd q base

/-- The first original overlap projection on the whole finite model. -/
def finiteGlobalTangentCechFirst : Z ⟶ Y :=
  pullback.lift (zs ≫ p₁) zx (by
    rw [Category.assoc]
    exact pullback.condition)

/-- The second original overlap projection on the whole finite model. -/
def finiteGlobalTangentCechSecond : Z ⟶ Y :=
  pullback.lift (zs ≫ p₂) zx (by
    change (zs ≫ p₂) ≫ q = zx ≫ base
    rw [Category.assoc, ← pullback.condition (f := q) (g := q)]
    exact pullback.condition)

@[reassoc] theorem finiteGlobalTangentCechFirst_structure :
    finiteGlobalTangentCechFirst hπ data j hj ≫ ys = zs ≫ p₁ :=
  pullback.lift_fst _ _ _

@[reassoc] theorem finiteGlobalTangentCechSecond_structure :
    finiteGlobalTangentCechSecond hπ data j hj ≫ ys = zs ≫ p₂ :=
  pullback.lift_fst _ _ _

/-- Both overlap projections retain precisely the original integral finite model. -/
@[reassoc] theorem finiteGlobalTangentCechFirst_projection :
    finiteGlobalTangentCechFirst hπ data j hj ≫ yx = zx := pullback.lift_snd _ _ _

@[reassoc] theorem finiteGlobalTangentCechSecond_projection :
    finiteGlobalTangentCechSecond hπ data j hj ≫ yx = zx := pullback.lift_snd _ _ _

/-- The identity coefficient branch lifted through the whole original finite model. -/
def finiteGlobalTangentCechIdentity : Y ⟶ Z :=
  pullback.lift (ys ≫ nodeTangentCechIdentity W) yx (by
    rw [Category.assoc, nodeTangentCechIdentity_fst_assoc]
    exact pullback.condition)

/-- The conjugate coefficient branch lifted through the whole original finite model. -/
def finiteGlobalTangentCechConjugate : Y ⟶ Z :=
  pullback.lift (ys ≫ nodeTangentCechConjugate W) yx (by
    rw [Category.assoc, nodeTangentCechConjugate_fst_assoc]
    exact pullback.condition)

/-- The identity branch's first map is the identity on the entire actual model. -/
@[reassoc] theorem finiteGlobalTangentCechIdentity_first :
    finiteGlobalTangentCechIdentity hπ data j hj ≫
      finiteGlobalTangentCechFirst hπ data j hj = 𝟙 Y := by
  apply (IsPullback.of_hasPullback q base).hom_ext
  · simp only [Category.assoc, finiteGlobalTangentCechFirst_structure,
      finiteGlobalTangentCechIdentity, pullback.lift_fst_assoc,
      nodeTangentCechIdentity_fst, Category.comp_id, Category.id_comp]
  · simp only [Category.assoc, finiteGlobalTangentCechFirst_projection,
      finiteGlobalTangentCechIdentity, pullback.lift_snd, Category.id_comp]

/-- The identity branch's second map is likewise the identity, including all nodes. -/
@[reassoc] theorem finiteGlobalTangentCechIdentity_second :
    finiteGlobalTangentCechIdentity hπ data j hj ≫
      finiteGlobalTangentCechSecond hπ data j hj = 𝟙 Y := by
  apply (IsPullback.of_hasPullback q base).hom_ext
  · simp only [Category.assoc, finiteGlobalTangentCechSecond_structure,
      finiteGlobalTangentCechIdentity, pullback.lift_fst_assoc,
      nodeTangentCechIdentity_snd, Category.comp_id, Category.id_comp]
  · simp only [Category.assoc, finiteGlobalTangentCechSecond_projection,
      finiteGlobalTangentCechIdentity, pullback.lift_snd, Category.id_comp]

/-- The conjugate branch's first projection is the original model itself. -/
@[reassoc] theorem finiteGlobalTangentCechConjugate_first :
    finiteGlobalTangentCechConjugate hπ data j hj ≫
      finiteGlobalTangentCechFirst hπ data j hj = 𝟙 Y := by
  apply (IsPullback.of_hasPullback q base).hom_ext
  · simp only [Category.assoc, finiteGlobalTangentCechFirst_structure,
      finiteGlobalTangentCechConjugate, pullback.lift_fst_assoc,
      nodeTangentCechConjugate_fst, Category.comp_id, Category.id_comp]
  · simp only [Category.assoc, finiteGlobalTangentCechFirst_projection,
      finiteGlobalTangentCechConjugate, pullback.lift_snd, Category.id_comp]

/-- The conjugate branch's second projection is exactly the actual model involution. -/
@[reassoc] theorem finiteGlobalTangentCechConjugate_second :
    finiteGlobalTangentCechConjugate hπ data j hj ≫
        finiteGlobalTangentCechSecond hπ data j hj =
      finiteGlobalTangentConjugation hπ data j hj := by
  apply (IsPullback.of_hasPullback q base).hom_ext
  · simp only [Category.assoc, finiteGlobalTangentCechSecond_structure,
      finiteGlobalTangentCechConjugate, pullback.lift_fst_assoc,
      nodeTangentCechConjugate_snd, finiteGlobalTangentConjugation_structure]
  · simp only [Category.assoc, finiteGlobalTangentCechSecond_projection,
      finiteGlobalTangentCechConjugate, pullback.lift_snd,
      finiteGlobalTangentConjugation_projection]

end FLT.Mazur.WeierstrassDividedDepth
