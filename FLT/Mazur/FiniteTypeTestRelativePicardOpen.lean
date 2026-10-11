/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteTypeTestAcyclicOpenRepresentation
public import FLT.Mazur.RelativeAcyclicPicardOpen

/-!
# Representing opens of independent relative Picard classes on all tests

The open is independent of the line representative and represents the
geometric acyclic condition on every further cartesian test. The original
finite-type model is only used to prove openness of the intrinsic locus.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.CartierAbel
open FCurve SchemePicard LineSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor

/-- Equal relative line classes define exactly the same pointwise acyclic rank-one locus. -/
theorem geometricAcyclicRankOneLocus_relativeClass {X S : Scheme.{0}} (f : X ⟶ S)
    {L M : X.Modules} (hL : LocallyFreeRankOne L) (hM : LocallyFreeRankOne M)
    (hc : relativeClass f (mk L hL) = relativeClass f (mk M hM)) :
    geometricAcyclicRankOneLocus f L = geometricAcyclicRankOneLocus f M := by
  obtain ⟨B, ⟨a⟩⟩ := (relativeClass_mk_eq_iff_twist_iso f hL hM).mp hc
  ext s
  obtain ⟨b⟩ := baseLineTwist_fiber_iso f L B.property s
  let c := (Scheme.Modules.pullback (f.fiberι s)).mapIso a ≪≫ b
  exact (and_congr (forall_congr' fun n ↦
    Equiv.subsingleton_congr (moduleHIsoOfIso c (n + 1)).toEquiv)
      (congrArg (· = 1) (fiberSectionRank_eq_of_iso f s c)).to_iff).symm

variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X Y S : Scheme.{0}} {a : X ⟶ Y} {f : X ⟶ S}
  {q : Y ⟶ Spec (.of R)} {g : S ⟶ Spec (.of R)}
  [IsProper q] [Flat q] [GeometricallyIntegral q] (h : IsPullback a f q g)

/-- The intrinsic open associated to any independently supplied test class. -/
def finiteTypeTestRelativePicardOpen (c : RelativePic f) : S.Opens :=
  let L := (relativePic_exists_line f c).choose
  finiteTypeTestAcyclicOpen h L.val L.property

/-- Every actual representative yields the same open, including independent choices of line. -/
theorem finiteTypeTestRelativePicardOpen_mk (L : X.Modules) (hL : LocallyFreeRankOne L) :
    finiteTypeTestRelativePicardOpen h (relativeClass f (mk L hL)) =
      finiteTypeTestAcyclicOpen h L hL :=
  SetLike.coe_injective (geometricAcyclicRankOneLocus_relativeClass f _ hL
    (relativePic_exists_line f (relativeClass f (mk L hL))).choose_spec)

/-- The open of a relative class represents the acyclic condition on all further tests. -/
theorem finiteTypeTestRelativePicardOpen_represents {P T : Scheme.{0}}
    {p : P ⟶ X} {r : P ⟶ T} {b : T ⟶ S} (H : IsPullback p r f b)
    (c : RelativePic f) :
    RelativeGeometricAcyclicRankOne r (relativeMap r f p b H.w.symm c) ↔
      ∃! k : T ⟶ (finiteTypeTestRelativePicardOpen h c).toScheme,
        k ≫ (finiteTypeTestRelativePicardOpen h c).ι = b := by
  obtain ⟨L, rfl⟩ := relativePic_exists_line f c
  rw [relativeMap_class, pullback_mk, relativeGeometricAcyclicRankOne_mk,
    finiteTypeTestRelativePicardOpen_mk]
  exact finiteTypeTestAcyclicOpen_represents h L.val L.property H

/-- Independently constructed class opens commute with arbitrary further base change. -/
theorem finiteTypeTestRelativePicardOpen_baseChange {P T : Scheme.{0}}
    {p : P ⟶ X} {r : P ⟶ T} {b : T ⟶ S} (H : IsPullback p r f b)
    (c : RelativePic f) :
    finiteTypeTestRelativePicardOpen (H.paste_horiz h) (relativeMap r f p b H.w.symm c) =
      b ⁻¹ᵁ finiteTypeTestRelativePicardOpen h c := by
  obtain ⟨L, rfl⟩ := relativePic_exists_line f c
  rw [relativeMap_class, pullback_mk, finiteTypeTestRelativePicardOpen_mk,
    finiteTypeTestRelativePicardOpen_mk]
  exact finiteTypeTestAcyclicOpen_baseChange h L.val L.property H

end FLT.Mazur.CartierAbel
