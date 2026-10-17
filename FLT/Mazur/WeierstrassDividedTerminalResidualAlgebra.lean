/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalChangedSmoothing

/-!
# The full residual terminal Laurent substitution

The residual transition is an explicit algebra equivalence. Its weighted
reduction is the identity, and its entire closed specialization is the identity.
The higher-order transition itself is not discarded.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
open LaurentPolynomial PolygonScaledReciprocal
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R} {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "L" => Q[T;T⁻¹]
local notation "a" => arithmeticTerminalTangentScale data H m j hj u hu
local notation "E" => arithmeticTerminalParameterEquiv data H m j hj u hu
local notation "B" => arithmeticRetainedClosingEquiv data H m (j + 1) hj
  (Fin.mk j (Nat.lt_succ_self j))
local notation "N" => arithmeticTerminalNormalizationEquiv data H m j hj u hu

/-- The exact residual substitution after the tangent scaling, including all inverse terms. -/
def arithmeticTerminalResidualEquiv (b : Bool) : L ≃ₐ[Q] L :=
  (scalingEquiv (a b)).trans (N b).symm

local notation "D" => arithmeticTerminalResidualEquiv data H m j hj u hu

/-- The residual substitution retains the full original terminal and retained parameters. -/
theorem arithmeticTerminalResidualEquiv_parameter (b : Bool) :
    (B).toAlgHom.comp (D b).toAlgHom = (E b).toAlgHom.comp (scaling (a b)) := by
  apply AlgHom.ext
  intro z
  exact (B).apply_symm_apply _

/-- Its spectrum is exactly the revised geometric closing transition. -/
theorem arithmeticTerminalResidualEquiv_spec (b : Bool) :
    Spec.map (CommRingCat.ofHom (D b).toAlgHom.toRingHom) =
      (arithmeticTerminalResidualTwist data H m j hj u hu b).hom := by
  let β := Spec.map (CommRingCat.ofHom (B).toAlgHom.toRingHom)
  have hb : IsIso β := by
    change IsIso (Scheme.Spec.mapIso (B).toRingEquiv.toCommRingCatIso.op).hom
    infer_instance
  apply (cancel_epi β).mp
  have he : β ≫ Spec.map (CommRingCat.ofHom (D b).toAlgHom.toRingHom) =
      Spec.map (CommRingCat.ofHom (E b).toAlgHom.toRingHom) ≫
        (edgeScalingIso (a b)).hom := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext
      (congrArg AlgHom.toRingHom (arithmeticTerminalResidualEquiv_parameter data H m j hj u hu b)))
  rw [he, arithmeticTerminalParameterEquiv_spec]
  simp only [arithmeticTerminalResidualTwist, arithmeticClosingTerminalTwist,
    Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv]
  change _ = β ≫ (inv β ≫ _) ≫ _
  rw [← Category.assoc, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]

/-- Every scalar annihilator of the original parameter sees the identity residual transition. -/
theorem arithmeticTerminalResidualEquiv_weighted (e : Q) (he : e * parameter R π m = 0)
    (b : Bool) (z : L) : C e * D b z = C e * z := by
  apply (scalingEquiv (a b)).injective
  have hn := arithmeticTerminalNormalization_weighted data H m j hj u hu e he b
    ((N b).symm (scaling (a b) z))
  simp only [AlgEquiv.apply_symm_apply] at hn
  simpa only [map_mul, AlgEquiv.commutes, C_eq_algebraMap,
    arithmeticTerminalResidualEquiv, AlgEquiv.trans_apply, scalingEquiv,
    AlgEquiv.ofAlgHom_apply] using hn.symm

/-- Both full residual transitions are the identity on the original closed Laurent scheme. -/
theorem arithmeticTerminalResidualTwist_closed (b : Bool) :
    (arithmeticTerminalResidualTwist data H 0 j hj u hu b).hom = 𝟙 _ := by
  simp only [arithmeticTerminalResidualTwist, arithmeticClosingTerminalTwist,
    Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom, Category.assoc]
  rw [arithmeticTerminalTangentScale_closed]
  rw [arithmeticClosedTerminalScale_parameter, IsIso.inv_hom_id]

/-- The changed closed terminal attachments therefore have precisely the standard punctures. -/
theorem arithmeticTerminalChangedBoundary_closed (b : Bool) :
    arithmeticTerminalChangedBoundary data H 0 j hj u hu b =
      (if b then leftBranchOpen (Quotient R π 0)
          (arithmeticTerminalChangedSmoothing data H 0 j hj u hu)
        else rightBranchOpen (Quotient R π 0)
          (arithmeticTerminalChangedSmoothing data H 0 j hj u hu)) := by
  rw [arithmeticTerminalChangedBoundary, arithmeticTerminalResidualTwist_closed, Category.id_comp]

end FLT.Mazur.WeierstrassDividedDepth
