/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedResidueFiniteNormalization
public import FLT.Mazur.WeierstrassDividedTangentConjugation
public import FLT.Mazur.NodeTangentProjectiveMarkings

/-!
# Complete residue components in the actual tangent-coefficient model

Use the specialization of the original integral root algebra, and prove that
the complete component morphism intertwines the actual finite-model conjugation.
Both original slope markings are exchanged with their coefficient maps retained.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart ProjectiveLine
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
  {k : ℕ} (d : Data W π k) (hk : 0 < k) (hres : residue R π = 0)
local notation "V" => W.map (residue R)
local notation "S" => AdjoinRoot (nodeTangentPolynomial W)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
variable [hirr : Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "r" => Spec.map (CommRingCat.ofHom (nodeTangentCoefficientMap W (residue R)))
local notation "fst" => pullback.fst (nodeTangentCover W) base
local notation "snd" => pullback.snd (nodeTangentCover W) base
local notation "e" => originalResidueFiniteNormalization hπ data j hj d hk hres
local notation "σ" => nodeTangentCoverConjugation V

/-- The residue component uses the specialization of the actual integral tangent coefficient. -/
theorem originalResidueTangentNormalization_square :
    (toBase Q ≫ r) ≫ nodeTangentCover W = e ≫ base := by
  rw [Category.assoc, originalResidueFiniteNormalization_base]
  congr 1
  rw [nodeTangentCover, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext (nodeTangentCoefficientMap_coeff W (residue R)))

/-- The complete component morphism into the actual integral tangent base change. -/
def originalResidueTangentNormalization :
    scheme Q ⟶ finiteGlobalTensorModel hπ data S j hj :=
  pullback.lift (toBase Q ≫ r) e
    (originalResidueTangentNormalization_square hπ data j hj d hk hres)

/-- The tangent comparison retains every original integral finite-model point and function. -/
@[reassoc] theorem originalResidueTangentNormalization_projection :
    originalResidueTangentNormalization hπ data j hj d hk hres ≫ snd = e :=
  pullback.lift_snd _ _ _

/-- Its coefficient projection is the actual integral-root specialization. -/
@[reassoc] theorem originalResidueTangentNormalization_structure :
    originalResidueTangentNormalization hπ data j hj d hk hres ≫ fst = toBase Q ≫ r :=
  pullback.lift_fst _ _ _

/-- Complete normalization intertwines the original finite-model root conjugation. -/
@[reassoc] theorem originalResidueTangentNormalization_conjugation :
    nodeTangentLineConjugation V ≫ originalResidueTangentNormalization hπ data j hj d hk hres =
      originalResidueTangentNormalization hπ data j hj d hk hres ≫
        finiteGlobalTangentConjugation hπ data j hj := by
  apply pullback.hom_ext
  · change (nodeTangentLineConjugation V ≫
        originalResidueTangentNormalization hπ data j hj d hk hres) ≫ fst =
      (originalResidueTangentNormalization hπ data j hj d hk hres ≫
        finiteGlobalTangentConjugation hπ data j hj) ≫ fst
    simp only [Category.assoc, originalResidueTangentNormalization_structure,
      finiteGlobalTangentConjugation_structure]
    rw [nodeTangentLineConjugation_base_assoc,
      originalResidueTangentNormalization_structure_assoc]
    congr 1
    rw [nodeTangentCoverConjugation, ← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
      (nodeTangentCoefficientMap_conjugation W (residue R)).symm
  · change (nodeTangentLineConjugation V ≫
        originalResidueTangentNormalization hπ data j hj d hk hres) ≫ snd =
      (originalResidueTangentNormalization hπ data j hj d hk hres ≫
        finiteGlobalTangentConjugation hπ data j hj) ≫ snd
    simp only [Category.assoc, originalResidueTangentNormalization_projection,
      finiteGlobalTangentConjugation_projection, originalResidueFiniteNormalization_conjugation]

/-- The first actual slope marking maps to the companion marking under finite-model conjugation. -/
@[reassoc] theorem originalResidueTangentNormalization_first :
    infinitySlopeMark (0 : Q) ≫ originalResidueTangentNormalization hπ data j hj d hk hres ≫
        finiteGlobalTangentConjugation hπ data j hj =
      σ ≫ infinitySlopeMark (-(nodeTangentShear V).a₁) ≫
        originalResidueTangentNormalization hπ data j hj d hk hres := by
  rw [← originalResidueTangentNormalization_conjugation, nodeTangentLineConjugation_first_assoc]
  rfl

/-- The companion slope marking returns to the first over the same actual coefficient exchange. -/
@[reassoc] theorem originalResidueTangentNormalization_second :
    infinitySlopeMark (-(nodeTangentShear V).a₁) ≫
        originalResidueTangentNormalization hπ data j hj d hk hres ≫
          finiteGlobalTangentConjugation hπ data j hj =
      σ ≫ infinitySlopeMark (0 : Q) ≫
        originalResidueTangentNormalization hπ data j hj d hk hres := by
  rw [← originalResidueTangentNormalization_conjugation, nodeTangentLineConjugation_second_assoc]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
