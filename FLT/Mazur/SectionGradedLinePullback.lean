/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedIsoRing
public import FLT.Mazur.SectionGradedPullbackRing

/-!
# Tensor-degree sections with a specified line pullback comparison

The actual pullback and line isomorphism define a sheaf morphism in each
exponent. Its formula on local pure tensors allows coherence to be checked
without assuming that arbitrary sections are pure tensors.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules

namespace FLT.Mazur.SectionGradedLinePullback

open FCurve ModuleLineBundleTensorPullback SectionGradedMultiplication

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] ModuleSheafTensor.tensor

variable {X Y : Scheme} (f : X ⟶ Y) {L : Y.Modules} {M : X.Modules}
    (e : (pullback f).obj L ≅ M)

/-- The actual line map, transposed through pullback and pushforward. -/
def lineMap : L ⟶ (pushforward f).obj M :=
  (pullbackPushforwardAdjunction f).homEquiv _ _ e.hom

/-- The actual tensor-power comparison followed by the specified line transport. -/
def powerMap (n : ℕ) : tensorPower L n ⟶ (pushforward f).obj (tensorPower M n) :=
  SectionGradedPullback.powerMap f L n ≫
    (pushforward f).map (tensorPowerCongr e n).hom

/-- Evaluation of the specified tensor-degree pullback on a local section. -/
def sectionMap (n : ℕ) (U : Y.Opens) (s : Piece L U n) : Piece M (f ⁻¹ᵁ U) n :=
  (powerMap f e n).app U s

/-- Section transport is the existing pullback followed by the existing line comparison. -/
theorem sectionMap_eq (n : ℕ) (U : Y.Opens) (s : Piece L U n) :
    sectionMap f e n U s =
      SectionGradedIso.pieceMap e n (f ⁻¹ᵁ U) (SectionGradedPullback.pull f L n U s) := rfl

/-- Degree zero is exactly the map of structure sheaves. -/
theorem sectionMap_zero (U : Y.Opens) (r : Γ(Y, U)) :
    sectionMap f e 0 U r = f.app U r :=
  SectionGradedPullback.pull_zero f L U r

/-- A prepended tensor factor is transported by the specified line map. -/
theorem sectionMap_cons (n : ℕ) (U : Y.Opens) (s : Γ(L, U)) (t : Piece L U n) :
    sectionMap f e (n + 1) U (cons L n U s t) =
      cons M n (f ⁻¹ᵁ U) ((lineMap f e).app U s) (sectionMap f e n U t) := by
  rw [sectionMap_eq, SectionGradedPullback.pull_cons, SectionGradedIso.pieceMap_cons]
  rfl

/-- The full section-ring map retaining the specified line comparison. -/
def ringHom : SectionGradedSum.Sections L ⊤ →+* SectionGradedSum.Sections M ⊤ :=
  (SectionGradedIso.ringHom e ⊤).comp (SectionGradedPullback.ringHom f L)

/-- Every homogeneous component of the ring map is the specified section map. -/
theorem ringHom_of (n : ℕ) (s : Piece L ⊤ n) :
    ringHom f e (SectionGradedSum.of L ⊤ n s) =
      SectionGradedSum.of M ⊤ n (sectionMap f e n ⊤ s) := by
  change SectionGradedIso.sumMap e ⊤
    (SectionGradedPullback.sumMap f L (SectionGradedSum.of L ⊤ n s)) = _
  rw [SectionGradedPullback.sumMap_of, SectionGradedIso.sumMap_of]
  rfl

end FLT.Mazur.SectionGradedLinePullback
