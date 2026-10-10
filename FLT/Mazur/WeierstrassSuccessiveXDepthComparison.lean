/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationDepthComposition
public import FLT.Mazur.WeierstrassDilatationParameterCongruence
public import FLT.Mazur.WeierstrassSuccessiveXGluing

/-!
# Successive local modifications at the actual divided depths

The same original coefficient factorizations force the parameter identifications
for a successive step. Its divided chart contraction is exactly the existing
actual depth transition, rather than a separately assumed comparison map.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R]
  (π : R) (k : ℕ) (hπ : π ≠ 0) (W : WeierstrassCurve R)
  (b3 b4 b6 c3 c4 c6 : R)
  (h3 : W.a₃ = π ^ k * b3) (h4 : W.a₄ = π ^ k * b4)
  (h6 : W.a₆ = (π ^ k) ^ 2 * b6)
  (H3 : W.a₃ = π ^ (k + 1) * c3) (H4 : W.a₄ = π ^ (k + 1) * c4)
  (H6 : W.a₆ = (π ^ (k + 1)) ^ 2 * c6)

/-- Original coefficient factorizations identify the preceding divided chart parameters. -/
def previousDepthEquiv : WeierstrassDilatation.Coordinate W (π ^ k) b3 b4 b6 ≃ₐ[R]
    WeierstrassDilatation.Coordinate W (π ^ k) (π * c3) (π * c4) (π ^ 2 * c6) :=
  WeierstrassDilatation.parameterEquiv W (π ^ k) (π ^ k)
    b3 b4 b6 (π * c3) (π * c4) (π ^ 2 * c6) rfl
    (by simpa using WeierstrassDilatation.depth_coefficient_factor π k (k + 1)
          hπ (Nat.le_succ k) h3 H3)
    (by simpa using WeierstrassDilatation.depth_coefficient_factor π k (k + 1)
          hπ (Nat.le_succ k) h4 H4)
    (by simpa using WeierstrassDilatation.depth_constant_factor π k (k + 1)
          hπ (Nat.le_succ k) h6 H6)

/-- Multiplication by the uniformizer identifies the new chart with the next depth. -/
def nextDepthEquiv : WeierstrassDilatation.Coordinate W (π ^ k * π) c3 c4 c6 ≃ₐ[R]
    WeierstrassDilatation.Coordinate W (π ^ (k + 1)) c3 c4 c6 :=
  WeierstrassDilatation.parameterEquiv W (π ^ k * π) (π ^ (k + 1))
    c3 c4 c6 c3 c4 c6 (pow_succ π k).symm rfl rfl rfl

/-- The local step's coordinate contraction equals the already proved depth transition. -/
theorem refinement_eq_depthTransition :
    (nextDepthEquiv π k W c3 c4 c6).toAlgHom.comp
        ((WeierstrassDilatation.refinement W (π ^ k) π
          (π * c3) (π * c4) (π ^ 2 * c6) c3 c4 c6 rfl rfl rfl).comp
          (previousDepthEquiv π k hπ W b3 b4 b6 c3 c4 c6 h3 h4 h6 H3 H4 H6).toAlgHom) =
      WeierstrassDilatation.depthTransition π k (k + 1) hπ (Nat.le_succ k)
        W b3 b4 b6 c3 c4 c6 h3 h4 h6 H3 H4 H6 := by
  apply WeierstrassDilatation.hom_ext
  · simp [previousDepthEquiv, nextDepthEquiv]
  · simp [previousDepthEquiv, nextDepthEquiv]

/-- The actual local modification constructed at the next divided depth. -/
def depthStep : Scheme := modification W (π ^ k) π c3 c4 c6

/-- The contraction of the local step lands in the actual preceding depth chart. -/
def depthContraction : depthStep π k W c3 c4 c6 ⟶
    Spec (.of (WeierstrassDilatation.Coordinate W (π ^ k) b3 b4 b6)) :=
  contraction W (π ^ k) π c3 c4 c6 ≫ Spec.map (CommRingCat.ofHom
    (previousDepthEquiv π k hπ W b3 b4 b6 c3 c4 c6 h3 h4 h6 H3 H4 H6).toRingHom)

/-- The actual next depth chart is an open subscheme of the constructed local step. -/
def depthDividedChart : Spec (.of
    (WeierstrassDilatation.Coordinate W (π ^ (k + 1)) c3 c4 c6)) ⟶
      depthStep π k W c3 c4 c6 :=
  Spec.map (CommRingCat.ofHom (nextDepthEquiv π k W c3 c4 c6).toRingHom) ≫
    dividedChart W (π ^ k) π c3 c4 c6

instance depthDividedChart_isOpenImmersion :
    IsOpenImmersion (depthDividedChart π k W c3 c4 c6) := by
  change IsOpenImmersion
    ((Scheme.Spec.mapIso (nextDepthEquiv π k W c3 c4 c6).toRingEquiv.toCommRingCatIso.op).hom ≫
      dividedChart W (π ^ k) π c3 c4 c6)
  infer_instance

/-- Restricting the actual local contraction to its depth chart is the existing transition. -/
@[reassoc] theorem depthDividedChart_contraction :
    depthDividedChart π k W c3 c4 c6 ≫
        depthContraction π k hπ W b3 b4 b6 c3 c4 c6 h3 h4 h6 H3 H4 H6 =
      WeierstrassDilatation.depthTransitionMorphism π k (k + 1) hπ (Nat.le_succ k)
        W b3 b4 b6 c3 c4 c6 h3 h4 h6 H3 H4 H6 := by
  simp only [depthDividedChart, depthContraction, Category.assoc,
    dividedChart_contraction_assoc]
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = Spec.map _
  simp only [← Spec.map_comp]
  exact congrArg Spec.map (congrArg (fun f => CommRingCat.ofHom f.toRingHom)
    (refinement_eq_depthTransition π k hπ W b3 b4 b6 c3 c4 c6 h3 h4 h6 H3 H4 H6))

end FLT.Mazur.WeierstrassSuccessiveX
