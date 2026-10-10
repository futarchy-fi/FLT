/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineTensorInverseComparison

/-!
# Tensoring by a line is an equivalence

The inverse tensors by the intrinsic dual. Both cancellation isomorphisms
use the actual tensor evaluation, and their naturality is checked on local
pure tensors without assuming that global pure tensors generate.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
open ModuleSheafTensor ModuleSheafTensorAssociator ModuleSheafTensorCurrying
variable {X : Scheme.{u}}

/-- Cancel two successive tensor factors using a specified evaluation. -/
def tensorCancelIso (M : X.Modules) {N K : X.Modules}
    (e : tensor N K ≅ structureModule X) : tensor (tensor M N) K ≅ M :=
  associator M N K ≪≫ congr (Iso.refl M) e ≪≫ rightUnitor M

/-- Cancellation contracts the two line factors on every local pure tensor. -/
lemma tensorCancelIso_pure (M : X.Modules) {N K : X.Modules}
    (e : tensor N K ≅ structureModule X) (U : X.Opens)
    (m : Γ(M, U)) (n : Γ(N, U)) (k : Γ(K, U)) :
    (tensorCancelIso M e).hom.app U (pure (tensor M N) K U (pure M N U m n) k) =
      (show Γ(X, U) from e.hom.app U (pure N K U n k)) • m := by
  simp only [tensorCancelIso, Iso.trans_hom, Hom.comp_app, ConcreteCategory.comp_apply,
    associator_hom_pure, ModuleSheafTensor.congr, ModuleSheafTensor.map_pure,
    Iso.refl_hom, Hom.id_app, ConcreteCategory.id_apply]
  exact rightUnitor_pure M U _ m

/-- Cancellation is natural in the remaining, arbitrary coefficient sheaf. -/
def tensorCancelNatIso {N K : X.Modules} (e : tensor N K ≅ structureModule X) :
    tensoring N ⋙ tensoring K ≅ 𝟭 X.Modules :=
  NatIso.ofComponents (fun M ↦ tensorCancelIso M e) (fun f ↦ by
    apply left_hom_ext
    intro U m n k
    change (tensorCancelIso _ e).hom.app U
      ((map (map f (𝟙 N)) (𝟙 K)).app U _) =
        f.app U ((tensorCancelIso _ e).hom.app U _)
    simp only [ModuleSheafTensor.map_pure, Hom.id_app, ConcreteCategory.id_apply,
      tensorCancelIso_pure]
    exact (f.app_smul _ _).symm)

/-- The concrete right-tensor functor is an equivalence for any line sheaf. -/
def lineTensorEquivalence {N : X.Modules} (hN : LocallyFreeRankOne N) :
    X.Modules ≌ X.Modules :=
  CategoryTheory.Equivalence.mk (tensoring N) (tensoring (moduleSheafDual N))
    (tensorCancelNatIso (comm N (moduleSheafDual N) ≪≫
      lineSheafDualEvaluationIso hN)).symm
    (tensorCancelNatIso (lineSheafDualEvaluationIso hN))

/-- The equivalence acts on maps by the original concrete tensor map. -/
lemma lineTensorEquivalence_map {N M P : X.Modules} (hN : LocallyFreeRankOne N)
    (a : M ⟶ P) :
    (lineTensorEquivalence hN).functor.map a = map a (𝟙 N) := rfl

end FLT.Mazur.FCurve
