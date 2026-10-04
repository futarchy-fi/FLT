/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineFpqcRefinement
public import FLT.Mazur.RelativeAmpleBaseChange
public import FLT.Mazur.RelativeAmplePresentationTransport

/-!
# Refining fpqc witnesses for relative ampleness

An ample pullback along an fpqc cover of an affine base remains ample after
refining to an affine faithfully flat cover. Both the refinement factorization
and the cartesian square of the actual line-bundle pullback are retained.
This reduces the affine-base descent problem to affine covering schemes;
it does not assert reflection of ampleness along the refined cover.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
variable {X Y S T : Scheme} {f : X ⟶ S} {g : T ⟶ S}
  {p : Y ⟶ X} {q : Y ⟶ T} {L : X.Modules}

/-- An actual ample cartesian pullback admits an affine fpqc refinement. -/
theorem RelativeAmple.exists_affine_fpqc_witness [IsAffine S]
    [Flat g] [Surjective g] [QuasiCompact g]
    (hL : RelativeAmple q ((Scheme.Modules.pullback p).obj L))
    (hline : LocallyFreeRankOne L) (sq : IsPullback p q f g) :
    ∃ (Z : Scheme) (_ : IsAffine Z) (k : Z ⟶ T),
      Flat (k ≫ g) ∧ Surjective (k ≫ g) ∧
      ∃ (W : Scheme) (a : W ⟶ X) (b : W ⟶ Z),
        IsPullback a b f (k ≫ g) ∧ RelativeAmple b ((Scheme.Modules.pullback a).obj L) := by
  obtain ⟨Z, hZ, k, hkflat, hksurj⟩ := exists_affine_fpqc_refinement g
  let := hZ
  let a := Limits.pullback.fst q k
  let b := Limits.pullback.snd q k
  have hs : IsPullback a b q k := IsPullback.of_hasPullback q k
  refine ⟨Z, hZ, k, hkflat, hksurj, Limits.pullback q k, a ≫ p, b,
    hs.paste_horiz sq, ?_⟩
  exact (hL.of_isPullback (hline.pullback p) hs).of_iso
    ((pullbackComp a p).app L).symm

end FLT.Mazur.FCurve
