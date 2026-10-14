/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CurveStructureEuler
public import FLT.Mazur.CurveSurjectiveOpenComplement
public import FLT.Mazur.FiniteSupportEulerIso
public import FLT.Mazur.FinitePushforwardCoherent
public import FLT.Mazur.StructureDirectImageComparison

/-!
# Finite curve comparisons with equal arithmetic genus

For a finite surjection from a proper integral curve to a reduced proper target,
an unchanged nonempty open makes the structure cokernel finitely supported.
Equal structure Euler characteristics force this cokernel to vanish, recovering
the original scheme map everywhere, including at singular points.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open CoherentDevissage StructureDirectImage
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {k : Type} [Field k] {X Y : Scheme}
  (g : Y ⟶ Spec (.of k)) [IsProper g] (f : X ⟶ Y) [IsFinite f] [Surjective f]
  [IsIntegral X]

include g in
/-- The structure cokernel of a finite curve comparison is supported on finitely many points. -/
theorem finiteCurve_structure_cokernel_support (hd : topologicalKrullDim X ≤ 1)
    (U : Y.Opens) (hU : (U : Set Y).Nonempty) [IsIso (f ∣_ U)] :
    (support (cokernel (unitMap f))).Finite := by
  let _ := Chow.source_isNoetherian (f ≫ g)
  exact (finite_compl_open_of_curve_surjective hd f f.continuous
    (Surjective.surj (f := f)) U hU).subset (unitMap_cokernel_support_subset f U)

variable [IsReduced Y]

/-- An unchanged open and equal Euler characteristics recover the entire finite curve map. -/
theorem finiteCurve_isIso_of_euler_eq (hd : topologicalKrullDim X ≤ 1)
    (U : Y.Opens) (hU : (U : Set Y).Nonempty) [IsIso (f ∣_ U)]
    (he : curveEulerCharacteristic (f ≫ g) (structureModule X) =
      curveEulerCharacteristic g (structureModule Y)) : IsIso f := by
  let _ := Chow.source_isNoetherian g
  let _ : Y.IsSeparated := ⟨by rw [← terminal.comp_from g]; infer_instance⟩
  let _ : IsSchemeTheoreticallyDominant f := .of_isDominant f
  let _ := unitMap_mono f
  let _ : (structureModule X).IsFinitePresentation := unitSheaf_isFinitePresentation X
  let _ : (structureModule Y).IsFinitePresentation := unitSheaf_isFinitePresentation Y
  let _ : (image f).IsFinitePresentation :=
    finitePushforward_isFinitePresentation f (structureModule X)
  let _ : IsIso (unitMap f) := isIso_of_finiteSupport_euler_eq g (unitMap f)
    (finiteCurve_structure_cokernel_support g f hd U hU) (by
      change curveEulerCharacteristic g (structureModule Y) =
        curveEulerCharacteristic g ((pushforward f).obj (structureModule X))
      rw [curveEulerCharacteristic_affinePushforward, he])
  exact isIso_of_unitMap f

end FLT.Mazur.FCurve
