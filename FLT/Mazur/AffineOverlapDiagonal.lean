/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineGeometricOverlap
public import FLT.Mazur.SchemeModulePullbackUnits

/-!
# Evaluating overlap coefficients along the geometric diagonal

The multiplication map of the tensor ring is the scheme diagonal in the
affine overlap chart. Its pullback, followed by the canonical retraction
comparison, evaluates both tensor coordinate systems by scalar multiplication.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineOverlapDiagonal
open AffineOverlapTensor AffineOverlapPullback SchemeModulePullbackUnits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- Ring map underlying the diagonal of the affine overlap. -/
abbrev diagonalRing : S ⊗[R] S →+* S := ↑(Algebra.TensorProduct.lmul' R (S := S))

/-- The diagonal is a section of the first projection. -/
theorem diagonal_first :
    Spec.map (CommRingCat.ofHom (diagonalRing R S)) ≫
      Spec.map (CommRingCat.ofHom (left R S)) = 𝟙 (Spec (.of S)) := by
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext s
  simp [diagonalRing, left]

/-- The diagonal is a section of the second projection. -/
theorem diagonal_second :
    Spec.map (CommRingCat.ofHom (diagonalRing R S)) ≫
      Spec.map (CommRingCat.ofHom (right R S)) = 𝟙 (Spec (.of S)) := by
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext s
  simp [diagonalRing, right]

/-- This multiplication morphism is the actual scheme diagonal in the tensor chart. -/
theorem diagonal_chart :
    Limits.pullback.diagonal (Spec.map (CommRingCat.ofHom (algebraMap R S))) ≫
      (pullbackSpecIso R S S).hom = Spec.map (CommRingCat.ofHom (diagonalRing R S)) := by
  rw [diagonal_SpecMap, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

variable (M : (Spec (.of S)).Modules) [M.IsQuasicoherent]
/-- Restrict coefficient scalars along the base algebra map. -/
local instance : Module R (coefficients S M) := Module.compHom _ (algebraMap R S)
local instance : IsScalarTower R S (coefficients S M) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)

/-- Evaluate a projection section by actual diagonal pullback and the retraction isomorphism. -/
def evaluate (i : S →+* S ⊗[R] S)
    (h : Spec.map (CommRingCat.ofHom (diagonalRing R S)) ≫
      Spec.map (CommRingCat.ofHom i) = 𝟙 (Spec (.of S))) :
    moduleSpecΓFunctor.obj ((pullback (Spec.map (CommRingCat.ofHom i))).obj M) →+
      coefficients S M where
  toFun x := (retractIso _ _ h M).hom.app ⊤
    (((pullbackPushforwardAdjunction (Spec.map (CommRingCat.ofHom (diagonalRing R S)))).unit.app
      ((pullback (Spec.map (CommRingCat.ofHom i))).obj M)).app ⊤ x)
  map_zero' := by simp only [map_zero]
  map_add' x y := by simp only [map_add]

/-- The first tensor coordinate system evaluates by the original module action. -/
theorem evaluate_first_tmul (n : coefficients S M) (s : S) :
    evaluate R S M (left R S) (diagonal_first R S) (firstSections R S M (n ⊗ₜ[R] s)) =
      s • n := by
  rw [firstSections_tmul]
  exact spec_retract_smul_unit (CommRingCat.ofHom (left R S)) M
    (CommRingCat.ofHom (diagonalRing R S)) (diagonal_first R S) (1 ⊗ₜ[R] s) n |>.trans
      (by simp [diagonalRing])

/-- The second tensor coordinate system evaluates by the original module action. -/
theorem evaluate_second_tmul (s : S) (n : coefficients S M) :
    evaluate R S M (right R S) (diagonal_second R S) (secondSections R S M (s ⊗ₜ[R] n)) =
      s • n := by
  rw [secondSections_tmul]
  exact spec_retract_smul_unit (CommRingCat.ofHom (right R S)) M
    (CommRingCat.ofHom (diagonalRing R S)) (diagonal_second R S) (s ⊗ₜ[R] 1) n |>.trans
      (by simp [diagonalRing])

/-- On all coefficients, the actual diagonal evaluation is tensor contraction. -/
theorem evaluate_second (x : S ⊗[R] coefficients S M) :
    evaluate R S M (right R S) (diagonal_second R S) (secondSections R S M x) =
      TensorProduct.lift (Algebra.lsmul R R (coefficients S M) (A := S)).toLinearMap x := by
  induction x using TensorProduct.inductionOn with
  | tmul s n => exact evaluate_second_tmul R S M s n
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The geometric diagonal equation, expressed using actual sheaf pullback comparisons. -/
def DiagonalCompatible (e : AffineGeometricOverlap.Overlap R S M) : Prop :=
  (pullback (Spec.map (CommRingCat.ofHom (diagonalRing R S)))).map e.hom ≫
    (retractIso _ _ (diagonal_second R S) M).hom =
      (retractIso _ _ (diagonal_first R S) M).hom

omit [M.IsQuasicoherent] in
/-- A geometric diagonal identity commutes with evaluation of arbitrary sections. -/
theorem evaluate_overlap (e : AffineGeometricOverlap.Overlap R S M)
    (h : DiagonalCompatible R S M e)
    (x : moduleSpecΓFunctor.obj
      ((pullback (Spec.map (CommRingCat.ofHom (left R S)))).obj M)) :
    evaluate R S M (right R S) (diagonal_second R S) (moduleSpecΓFunctor.map e.hom x) =
      evaluate R S M (left R S) (diagonal_first R S) x := by
  have hn := congrArg (fun k ↦ k.app ⊤ x)
    ((pullbackPushforwardAdjunction
      (Spec.map (CommRingCat.ofHom (diagonalRing R S)))).unit.naturality e.hom)
  have hd := congrArg (fun k ↦ k.app ⊤
    (((pullbackPushforwardAdjunction (Spec.map (CommRingCat.ofHom (diagonalRing R S)))).unit.app
      ((pullback (Spec.map (CommRingCat.ofHom (left R S)))).obj M)).app ⊤ x)) h
  exact (congrArg (fun y ↦ (retractIso _ _ (diagonal_second R S) M).hom.app ⊤ y) hn).trans hd

/-- The geometric diagonal equation implies the exact tensor datum diagonal equation. -/
theorem tensorEquiv_diagonal (e : AffineGeometricOverlap.Overlap R S M)
    (h : DiagonalCompatible R S M e) (n : coefficients S M) :
    TensorProduct.lift (Algebra.lsmul R R (coefficients S M) (A := S)).toLinearMap
      (AffineGeometricOverlap.tensorEquiv R S M e (n ⊗ₜ[R] (1 : S))) = n := by
  refine (evaluate_second R S M _).symm.trans ?_
  refine (congrArg (evaluate R S M (right R S) (diagonal_second R S))
    (AffineGeometricOverlap.tensorEquiv_sections R S M e (n ⊗ₜ[R] (1 : S)))).trans ?_
  exact (evaluate_overlap R S M e h _).trans
    ((evaluate_first_tmul R S M n 1).trans (one_smul S n))

end FLT.Mazur.AffineOverlapDiagonal
