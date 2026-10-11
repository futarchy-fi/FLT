/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothNonspecialLineLift
public import FLT.Mazur.AmpleAcyclicNonzeroSection

/-!
# Relative nonspecial-line lifts from a fiberwise ample line

A high power of the original relative line supplies an acyclic positive-rank
starting fiber. The smooth point-condition construction then produces a genuine
relative line with nonspecial restriction, retaining both original fiber maps.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor

variable {k : Type} [Field k] [IsAlgClosed k]
  {X Y S : Scheme} [IsReduced Y] [Nonempty Y]
  (q : Y ⟶ Spec (.of k)) [IsProper q] [SmoothOfRelativeDimension 1 q]
  (f : X ⟶ S) [IsSeparated f] [SmoothOfRelativeDimension 1 f]
  {p : Y ⟶ X} {g : Spec (.of k) ⟶ S} (H : IsPullback p q f g)
  (B : X.Modules) (hB : LocallyFreeRankOne B)
  (hA : AmpleLineBundle ((Scheme.Modules.pullback p).obj B))

include H hB hA in
/-- An ample geometric restriction suffices to construct a smooth relative nonspecial lift. -/
theorem exists_smooth_nonspecial_line_lift_of_ample :
    ∃ (U Z : Scheme) (a : U ⟶ S) (b : Z ⟶ X) (r : Z ⟶ U)
      (u : Spec (.of k) ⟶ U) (v : Y ⟶ Z) (N : Z.Modules),
      Smooth a ∧ IsPullback b r f a ∧ IsPullback v q r u ∧
      u ≫ a = g ∧ v ≫ b = p ∧ LocallyFreeRankOne N ∧
      Subsingleton (ModuleScalarH q ((Scheme.Modules.pullback v).obj N) 1) ∧
      Module.finrank k (ModuleScalarH q ((Scheme.Modules.pullback v).obj N) 0) = 1 := by
  obtain ⟨n, _, hz, s, hs⟩ := exists_acyclic_power_nonzero_section q hA
  let M := tensorPower ((Scheme.Modules.pullback p).obj B) n
  have hM : LocallyFreeRankOne M := (hB.pullback p).tensorPower n
  let _ := hM.isFinitePresentation
  let _ : Module.Finite k (ModuleScalarH q M 0) := proper_coherent_hasFiniteCohomology q M 0
  let _ : Nontrivial (M.val.obj (Opposite.op ⊤)) := ⟨⟨s, 0, hs⟩⟩
  let _ : Nontrivial (ModuleScalarH q M 0) := (moduleScalarH0Equiv q M).toEquiv.nontrivial
  let e := ModuleLineBundleTensorPullback.tensorPowerIso p B n
  let _ : Subsingleton (ModuleH M 1) := hz
  let _ : Subsingleton (ModuleScalarH q ((Scheme.Modules.pullback p).obj
      (tensorPower B n)) 1) := moduleH_subsingleton_of_iso e 1
  have hr := ((moduleScalarHFunctor q 0).mapIso e).toLinearEquiv.finrank_eq
  exact exists_smooth_nonspecial_line_lift q f H (tensorPower B n) (hB.tensorPower n)
    (hr.symm ▸ Module.finrank_pos (R := k) (M := ModuleScalarH q M 0))

end FLT.Mazur.FCurve
