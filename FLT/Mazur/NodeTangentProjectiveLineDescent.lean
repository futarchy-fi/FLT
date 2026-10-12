/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodeTangentProjectiveReflection
public import FLT.Mazur.NodeTangentFieldFixed
public import FLT.Mazur.ProjectiveLineSlopeNormalization

/-!
# Actual tangent conjugation on the glued complete projective line

For the nonsplit tangent field, transport the constructed projective map
to the original glued line. Ordered slope normalization gives exactly the
existing endpoint reversal together with the actual coefficient operation.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur
open ProjectiveSpace ProjectiveLine
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {F : Type u} [Field F] (W : WeierstrassCurve F)
variable [Fact (Irreducible (nodeTangentPolynomial W))]
local notation "S" => AdjoinRoot (nodeTangentPolynomial W)
local notation "σ" => RingEquiv.toRingHom (AlgEquiv.toRingEquiv (nodeTangentConjugation W))
local notation "a" => WeierstrassCurve.a₁ (nodeTangentShear W)

/-- The actual root-sheared operation on the original complete glued line. -/
def nodeTangentLineConjugation : scheme S ⟶ scheme S :=
  (homogeneousIso S).hom ≫ nodeTangentProjectiveConjugation W ≫ (homogeneousIso S).inv

/-- The actual coefficient conjugation on the complete glued line. -/
def nodeTangentLineCoefficients : scheme S ⟶ scheme S :=
  (homogeneousIso S).hom ≫ coefficientMap σ (ULift.{u} (Fin 2)) ≫ (homogeneousIso S).inv

/-- Root exchange remains involutive after comparison with the original glued scheme. -/
theorem nodeTangentLineConjugation_involutive :
    nodeTangentLineConjugation W ≫ nodeTangentLineConjugation W = 𝟙 _ := by
  simp only [nodeTangentLineConjugation, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc (nodeTangentProjectiveConjugation W),
    nodeTangentProjectiveConjugation_involutive, Category.id_comp, Iso.hom_inv_id]

/-- The whole-line operation has the original semilinear coefficient projection. -/
@[reassoc] theorem nodeTangentLineConjugation_base :
    nodeTangentLineConjugation W ≫ toBase S =
      toBase S ≫ Spec.map (CommRingCat.ofHom σ) := by
  simp only [nodeTangentLineConjugation, Category.assoc, homogeneousIso_inv_base,
    nodeTangentProjectiveConjugation_base, homogeneousIso_base_assoc]

/-- The coefficient operation retains its actual coefficient-spectrum map. -/
@[reassoc] theorem nodeTangentLineCoefficients_base :
    nodeTangentLineCoefficients W ≫ toBase S =
      toBase S ≫ Spec.map (CommRingCat.ofHom σ) := by
  simp only [nodeTangentLineCoefficients, Category.assoc, homogeneousIso_inv_base,
    coefficientMap_baseProjection, homogeneousIso_base_assoc]

/-- The existing ordered slope isomorphism converts root exchange into endpoint reversal. -/
@[reassoc] theorem nodeTangentLineConjugation_normalization (t : Sˣ) (ht : (t : S) = a) :
    nodeTangentLineConjugation W ≫ (slopeNormalizationIso t).hom =
      (slopeNormalizationIso t).hom ≫ nodeTangentLineCoefficients W ≫ endpointReversal S := by
  have hr : endpointReversal S =
      (homogeneousIso S).hom ≫ (reversalProjIso S).hom ≫ (homogeneousIso S).inv := by
    rw [← Category.assoc, homogeneousIso_reversal, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  simp only [nodeTangentLineConjugation, nodeTangentLineCoefficients,
    slopeNormalizationIso, Iso.trans_hom, Iso.symm_hom, hr, Category.assoc,
    Iso.inv_hom_id_assoc]
  rw [← Category.assoc (nodeTangentProjectiveConjugation W),
    nodeTangentProjectiveConjugation_normalization W t ht]
  simp only [Category.assoc]

/-- The normalization coordinate map is the original left chart, with all functions retained. -/
theorem nodeTangentProjectiveChart_glued :
    nodeTangentProjectiveChart W ≫ (homogeneousIso S).inv = left S := by
  have h := homogeneousPoint_left S (Polynomial.C : S →+* Polynomial S)
    (fun i => (![1, Polynomial.X] : Fin 2 → Polynomial S) i.down) 1 rfl
  have he : Polynomial.eval₂RingHom (Polynomial.C : S →+* Polynomial S) Polynomial.X =
      RingHom.id _ := by ext <;> simp
  simpa only [nodeTangentProjectiveChart, inv_one, Units.val_one, one_mul, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, he, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp] using h

/-- The full original affine normalization operation is retained in the complete comparison. -/
@[reassoc] theorem nodeTangentLineConjugation_left :
    left S ≫ nodeTangentLineConjugation W =
      Spec.map (CommRingCat.ofHom (nodeTangentNormalizationConjugation W).toRingHom) ≫
        left S := by
  rw [← nodeTangentProjectiveChart_glued W, nodeTangentLineConjugation]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, nodeTangentProjectiveConjugation_chart, Category.assoc]

end FLT.Mazur
