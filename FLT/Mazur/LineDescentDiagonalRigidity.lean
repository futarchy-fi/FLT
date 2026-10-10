/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RigidifiedLineIsomorphisms
public import FLT.Mazur.SchemeLineDescentCategory

/-!
# Diagonal rigidity forces compatibility of line isomorphisms

If functions on the double overlap come from its first projection, the
diagonal detects line isomorphisms. The diagonal laws of two descent data
then force every underlying line isomorphism to respect their overlaps.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.SchemeGeometricDescent
open FCurve SchemeModulePullbackUnits
variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The retraction comparison is natural in the original sheaf map. -/
lemma retractIso_naturality {Y Z : Scheme.{u}} (d : Y ⟶ Z) (p : Z ⟶ Y)
    (h : d ≫ p = 𝟙 Y) {M N : Y.Modules} (a : M ⟶ N) :
    (pullback d).map ((pullback p).map a) ≫ (retractIso d p h N).hom =
      (retractIso d p h M).hom ≫ a :=
  (pullbackComp d p ≪≫ pullbackCongr h ≪≫ pullbackId Y).hom.naturality a

/-- Both overlap paths agree after pullback to the actual diagonal. -/
lemma overlap_paths_diagonal (D E : LineData f) (e : D.obj ≅ E.obj) :
    (pullback (Limits.pullback.diagonal f)).map
        (D.datum.overlap.hom ≫ (pullback (Limits.pullback.snd f f)).map e.hom) =
      (pullback (Limits.pullback.diagonal f)).map
        ((pullback (Limits.pullback.fst f f)).map e.hom ≫ E.datum.overlap.hom) := by
  let d := Limits.pullback.diagonal f
  let l := Limits.pullback.fst f f
  let r := Limits.pullback.snd f f
  have hD := D.datum.diagonal
  have hE := E.datum.diagonal
  change (pullback d).map D.datum.overlap.hom ≫
    (retractIso d r (Limits.pullback.diagonal_snd f) D.obj).hom =
      (retractIso d l (Limits.pullback.diagonal_fst f) D.obj).hom at hD
  change (pullback d).map E.datum.overlap.hom ≫
    (retractIso d r (Limits.pullback.diagonal_snd f) E.obj).hom =
      (retractIso d l (Limits.pullback.diagonal_fst f) E.obj).hom at hE
  apply (cancel_mono (retractIso d r (Limits.pullback.diagonal_snd f) E.obj).hom).mp
  change (pullback d).map (D.datum.overlap.hom ≫ (pullback r).map e.hom) ≫ _ =
    (pullback d).map ((pullback l).map e.hom ≫ E.datum.overlap.hom) ≫ _
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
    retractIso_naturality, hE, retractIso_naturality, ← Category.assoc, hD]

/-- Diagonal rigidity forces an actual source isomorphism to respect the full descent datum. -/
theorem iso_mapCompatible
    (hf : Function.Surjective (Limits.pullback.fst f f).appTop)
    (D E : LineData f) (e : D.obj ≅ E.obj) : D.datum.MapCompatible f E.datum e.hom := by
  have h := LineSheafSectionRigidity.iso_eq_of_pullback_hom_eq
    (Limits.pullback.fst f f) (Limits.pullback.diagonal f)
    (Limits.pullback.diagonal_fst f) hf (D.rankOne.pullback (Limits.pullback.fst f f))
    (D.datum.overlap ≪≫ (pullback (Limits.pullback.snd f f)).mapIso e)
    ((pullback (Limits.pullback.fst f f)).mapIso e ≪≫ E.datum.overlap)
    (overlap_paths_diagonal f D E e)
  exact congrArg Iso.hom h

end FLT.Mazur.SchemeGeometricDescent
