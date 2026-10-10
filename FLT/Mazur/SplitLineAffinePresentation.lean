/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SplitLineAffineNeighborhood
public import FLT.Mazur.LocallyFramedSplitLineCoverIndependence

/-!
# Constructing an affine framed split presentation

Actual local rank-one and local splitting hypotheses construct the affine
cover, source frames and retractions needed for the reverse projective map.
The resulting scheme morphism is independent of every presentation choice.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.SplitLineAffinePresentation
open FCurve SplitLineAffineNeighborhood
variable {X : Scheme.{u}} {ι : Type u} {L : X.Modules}
variable (s : L ⟶ SheafOfModules.free ι)

/-- Geometric affine local data for an actual split line inclusion. -/
structure Presentation where
  /-- An actual open cover, with no point compatibility fields. -/
  cover : X.OpenCover.{u}
  /-- Every member of this cover is affine. -/
  affine : ∀ i, IsAffine (cover.X i)
  /-- Trivializations of the pulled source line. -/
  frame : ∀ i, (pullback (cover.f i)).obj L ≅ structureModule (cover.X i)
  /-- Local retractions of the original inclusion. -/
  retraction : ∀ i, SheafOfModules.free ι ⟶ (pullback (cover.f i)).obj L
  /-- The local retractions actually split the pulled inclusion. -/
  split : ∀ i, SplitSheafLinePullback.inclusion (cover.f i) s ≫ retraction i = 𝟙 _

attribute [instance] Presentation.affine

/-- Construct every piece of local presentation data from the local sheaf properties. -/
def ofLocal (hL : LocallyFreeRankOne L) (hs : LocallySplit s) : Presentation s := by
  classical
  choose U hx hU e r hr using exists_affine s hL hs
  have hcover : iSup U = ⊤ := by
    apply top_unique
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hx x⟩
  exact ⟨X.openCoverOfIsOpenCover U hcover, hU, fun x ↦ (e x).some, r, hr⟩

variable [Finite ι]

/-- A local presentation constructs a morphism to the global-coefficient projective space. -/
def Presentation.morphism (P : Presentation s) : X ⟶ ProjectiveSpace.space Γ(X, ⊤) ι :=
  LocallyFramedSplitLineProjective.morphism s P.cover P.frame P.retraction P.split

/-- The construction is independent of the entire affine presentation. -/
lemma Presentation.morphism_eq (P Q : Presentation s) : P.morphism s = Q.morphism s :=
  LocallyFramedSplitLineProjective.morphism_cover_independent s
    P.cover P.frame P.retraction P.split Q.cover Q.frame Q.retraction Q.split

/-- Local line and splitting properties suffice to construct the global projective point. -/
def morphism (hL : LocallyFreeRankOne L) (hs : LocallySplit s) :
    X ⟶ ProjectiveSpace.space Γ(X, ⊤) ι := (ofLocal s hL hs).morphism s

/-- Every independently supplied affine presentation recovers the canonical construction. -/
lemma morphism_eq_presentation (hL : LocallyFreeRankOne L) (hs : LocallySplit s)
    (P : Presentation s) : morphism s hL hs = P.morphism s :=
  Presentation.morphism_eq s (ofLocal s hL hs) P

end FLT.Mazur.SplitLineAffinePresentation
