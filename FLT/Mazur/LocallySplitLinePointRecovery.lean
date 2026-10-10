/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineSplitLinePointRecovery

/-!
# Recovering a locally split affine line from its canonical point

Actual affine framed neighborhoods reduce the recovery theorem to the
framed case. The result retains a possibly nontrivial original source line.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.SplitLineAffinePresentation
open FCurve SplitLineAffineNeighborhood AffineFreeSheafCoordinates NormalizedSectionLine
open ProjectiveSpace
variable {X : Scheme.{u}} [IsAffine X] {ι : Type u} [Finite ι] {L : X.Modules}
variable (s : L ⟶ SheafOfModules.free ι) [Mono s]
variable (hL : LocallyFreeRankOne L) (hs : LocallySplit s)

/-- The actual canonical reverse point determines the original normalized ambient subobject. -/
lemma subobject_eq_sectionLine (j : ι) (N : Chart Γ(X, ⊤) ι j)
    (hp : morphism s hL hs = affineSectionLinePoint (.id _) j N) :
    Subobject.mk s = Subobject.mk (sectionLineInclusion X j N) := by
  classical
  choose U hx hU e r hr using exists_affine s hL hs
  have hcover : iSup U = ⊤ := by
    apply top_unique
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hx x⟩
  apply ModuleSubobjectCoverEquality.subobject_eq_of_openCover s _ U hcover
  intro x
  let _ : IsAffine (U x).toScheme := hU x
  let f := (U x).ι
  let t := SplitSheafLinePullback.inclusion f s
  let _ : IsSplitMono t := IsSplitMono.mk' ⟨r x, hr x⟩
  apply restriction_subobject_eq_of_pullback f s
  rw [canonicalSectionLinePullback_subobject]
  apply AffineSplitLineCoordinates.subobject_eq_sectionLine (e x).some t (r x) (hr x)
  apply (cancel_mono (coefficientMap f.appTop.hom ι)).mp
  rw [← morphism_affine_test s hL hs f (e x).some (r x) (hr x), hp,
    affineSectionLinePoint_pullback, affineSectionLinePoint_coefficientMap,
    RingHom.id_comp, RingHom.comp_id]

end FLT.Mazur.SplitLineAffinePresentation
