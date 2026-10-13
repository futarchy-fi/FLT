/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperLineArbitraryBaseChange
public import FLT.Mazur.ProperLineGeometricSectionRank
public import FLT.Mazur.FiniteProjectiveRankFrames

/-!
# Exact-rank frames after unrestricted base change

The geometric section rank of an acyclic proper line determines the precise
number of entries in a local frame of the actual changed direct image.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.LineSectionBaseChange
open FCurve Chow
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (f : X ⟶ S) [IsProper f] [Flat f] (L : X.Modules) (hL : LocallyFreeRankOne L)
  (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
    Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1)))

include hL hV in
/-- The actual section-module stalk rank is the intrinsic residue-fiber section dimension. -/
theorem properLineSectionRank_eq_geometric (s : S) :
    Module.rankAtStalk (R := Γ(S, ⊤)) (baseSections L f.appTop.hom ⊤)
      (S.isoSpec.hom s) = properLineFiberSectionRank f L s := by
  have hh := properLineSectionRank_fieldFiber f L hL hV
    (IsPullback.of_hasPullback f (S.fromSpecResidueField s))
    (IsLocalRing.closedPoint (S.residueField s))
  have hs := S.fromSpecResidueField_apply s (IsLocalRing.closedPoint (S.residueField s))
  exact (congrArg (fun y : S ↦ Module.rankAtStalk (R := Γ(S, ⊤))
    (baseSections L f.appTop.hom ⊤) (S.isoSpec.hom y)) hs).symm.trans hh

include hL hV in
/-- Arbitrary changed bases admit actual direct-image frames of the exact geometric rank. -/
theorem properLineBaseChanged_exactRank_frame {P T : Scheme.{0}}
    {p : P ⟶ X} {q : P ⟶ T} {g : T ⟶ S} (h : IsPullback p q f g)
    (t : T) (d : ℕ) (hd : properLineFiberSectionRank f L (g t) = d) :
    ∃ W : T.Opens, t ∈ W ∧ Nonempty
      (((pushforward q).obj ((pullback p).obj L)).restrict W.ι ≅
        SheafOfModules.free (Fin d)) := by
  let _ := hL.isFinitePresentation
  let _ := proper_sections_finite f L
  let _ := projective_sections_of_residue_fibers f L hL hV
  let M := ModuleCat.of Γ(S, ⊤) (baseSections L f.appTop.hom ⊤)
  obtain ⟨W, ht, ⟨e⟩⟩ := finiteProjective_rank_pullback_frame M (g ≫ S.isoSpec.hom) d t
    ((properLineSectionRank_eq_geometric f L hL hV (g t)).trans hd)
  let a : (pullback (g ≫ S.isoSpec.hom)).obj (tilde M) ≅
      (pushforward q).obj ((pullback p).obj L) :=
    ((pullbackComp g S.isoSpec.hom).app (tilde M)).symm ≪≫
      (pullback g).mapIso (properPushforwardTildeIso f L) ≪≫
        properLineArbitraryBaseChangeIso h L hL hV
  exact ⟨W, ht, ⟨((restrictFunctor W.ι).mapIso a).symm ≪≫ e⟩⟩

end FLT.Mazur.LineSectionBaseChange
