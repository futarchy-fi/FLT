/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperLineRankOneDirectImage
public import FLT.Mazur.AffinePicardSections

/-!
# Detection of the rank-one open on affine test schemes

The converse uses the invertibility of actual affine line sections. Thus
mapping into the open is equivalent to the test family's direct image being
a line bundle, with no extra Noetherian hypothesis on the test scheme.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.LineSectionBaseChange
open FCurve Chow

/-- An invertible module has rank one at every actual prime. -/
lemma invertibleModule_rankAtStalk_one {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [Module.Invertible R M] (z : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) M z = 1 := by
  let _ : Module.Free (Localization.AtPrime z.asIdeal)
    (LocalizedModule.AtPrime z.asIdeal M) := Module.free_of_flat_of_isLocalRing
  exact Module.Invertible.finrank_eq_one _ _

variable {X S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (f : X ⟶ S) [IsProper f] [Flat f] (L : X.Modules) (hL : LocallyFreeRankOne L)
  (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
    Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1)))
  {P T : Scheme.{0}} [IsAffine T]
  {p : P ⟶ X} {q : P ⟶ T} {g : T ⟶ S} (h : IsPullback p q f g)

include h in
/-- A line as actual direct image forces the original rank to be one at each test prime. -/
theorem properLineBaseChanged_rankOne_detect
    (hN : LocallyFreeRankOne ((pushforward q).obj ((pullback p).obj L)))
    (z : PrimeSpectrum Γ(T, ⊤)) :
    PrimeSpectrum.comap g.appTop.hom z ∈ properLineSectionRankOpen f L hL hV 1 := by
  let _ : IsProper q := MorphismProperty.of_isPullback h inferInstance
  let _ : Module.Invertible Γ(T, ⊤)
      ((AffineModuleGlobalSections.sections T).obj ((pushforward q).obj ((pullback p).obj L))) :=
    SchemePicard.sections_invertible _ hN
  let _ := Module.Invertible.congr (properPushforwardSectionsEquiv q ((pullback p).obj L))
  change Module.rankAtStalk (R := Γ(S, ⊤)) (baseSections L f.appTop.hom ⊤)
    (PrimeSpectrum.comap g.appTop.hom z) = 1
  rw [← properLineSectionRank_baseChange f L hL hV h z]
  exact invertibleModule_rankAtStalk_one z

include h in
/-- An affine test lies in the open exactly when its actual direct image is a line. -/
theorem properLineBaseChanged_rankOne_iff_affine :
    LocallyFreeRankOne ((pushforward q).obj ((pullback p).obj L)) ↔
      ∀ t : T, g t ∈ properLineRankOneOpen f L hL hV := by
  refine ⟨fun hN t ↦ ?_, properLineBaseChanged_rankOne f L hL hV h⟩
  have hz := properLineBaseChanged_rankOne_detect f L hL hV h hN (T.isoSpec.hom t)
  have he := congrArg (fun a : T ⟶ Spec Γ(S, ⊤) ↦ a t)
    (Scheme.isoSpec_hom_naturality g)
  change PrimeSpectrum.comap g.appTop.hom (T.isoSpec.hom t) = S.isoSpec.hom (g t) at he
  change S.isoSpec.hom (g t) ∈ properLineSectionRankOpen f L hL hV 1
  exact he ▸ hz

end FLT.Mazur.LineSectionBaseChange
