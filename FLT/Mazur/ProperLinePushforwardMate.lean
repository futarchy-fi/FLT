/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DirectImageBaseChangeMate
public import FLT.Mazur.ProperPushforwardReconstructionUnit
public import FLT.Mazur.ProperLinePushforwardBaseChange

/-!
# Proper line base change is the Beck-Chevalley mate

The reconstruction isomorphism built from cohomological base change agrees
with the map constructed directly from the sheaf adjunctions. The proof
compares unit tensors under the affine and scalar-extension adjunctions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FLT.Mazur.LineSectionBaseChange
open FCurve Chow AffineModuleGlobalSections IncreasingCechCoefficients
variable {P X T S : Scheme.{0}} [IsAffine S] [IsAffine T]
  [IsNoetherianRing Γ(S, ⊤)]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  [IsProper f] [Flat f] (h : IsPullback p q f g)
  (L : X.Modules) (hL : LocallyFreeRankOne L)
  (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
    Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1)))

omit [IsNoetherianRing Γ(S, ⊤)] in
/-- The affine pullback comparison on unit tensors, expressed as sheaf sections. -/
lemma affineTildePullback_unit_app (N : ModuleCat Γ(S, ⊤)) (s : N) :
    ((AffineQuasiCoherentBaseChange.tildePullbackIso g).hom.app N).app ⊤
        ((affineAdjunction T).unit.app _
          ((ModuleCat.extendRestrictScalarsAdj g.appTop.hom).unit.app N s)) =
      pullGlobal g _ ((affineAdjunction S).unit.app N s) :=
  AffineQuasiCoherentBaseChange.tildePullbackIso_unit g N s

/-- The mate has the same affine reconstruction normalization as the section comparison. -/
lemma properLinePushforwardMate_normalization :
    let _ : IsProper q := MorphismProperty.of_isPullback h inferInstance
    let _ := (hL.pullback p).isFinitePresentation
    (AffineQuasiCoherentBaseChange.tildePullbackIso g).hom.app
        (ModuleCat.of Γ(S, ⊤) (baseSections L f.appTop.hom ⊤)) ≫
      (pullback g).map (properLinePushforwardTildeIso f L hL).hom ≫
      DirectImageBaseChange.comparison p q f g h.w.symm L =
    (affineTilde T).map (residueSectionsIso h L hL hV).hom ≫
      (properPushforwardTildeIso q ((pullback p).obj L)).hom := by
  let _ : IsProper q := MorphismProperty.of_isPullback h inferInstance
  let _ := (hL.pullback p).isFinitePresentation
  let _ := hL.isFinitePresentation
  apply ((affineAdjunction T).homEquiv _ _).injective
  apply ((ModuleCat.extendRestrictScalarsAdj g.appTop.hom).homEquiv _ _).injective
  ext s
  change (DirectImageBaseChange.comparison p q f g h.w.symm L).app ⊤
      (((pullback g).map (properLinePushforwardTildeIso f L hL).hom).app ⊤
        (((AffineQuasiCoherentBaseChange.tildePullbackIso g).hom.app _).app ⊤
          ((affineAdjunction T).unit.app _
            ((ModuleCat.extendRestrictScalarsAdj g.appTop.hom).unit.app _ s)))) =
    (properPushforwardTildeIso q ((pullback p).obj L)).hom.app ⊤
      (((affineTilde T).map (residueSectionsIso h L hL hV).hom).app ⊤
        ((affineAdjunction T).unit.app _
          ((ModuleCat.extendRestrictScalarsAdj g.appTop.hom).unit.app _ s)))
  rw [affineTildePullback_unit_app]
  change (DirectImageBaseChange.comparison p q f g h.w.symm L).app ⊤
      (((pullback g).map (properPushforwardTildeIso f L).hom).app ⊤
        (pullGlobal g _ ((affineAdjunction S).unit.app _ s))) = _
  rw [properPushforwardTildeIso_pull_unit, DirectImageBaseChange.comparison_unit]
  have hn := congrArg (fun k ↦ k
    ((ModuleCat.extendRestrictScalarsAdj g.appTop.hom).unit.app _ s))
      ((affineAdjunction T).unit.naturality (residueSectionsIso h L hL hV).hom)
  change (affineAdjunction T).unit.app _
      ((residueSectionsIso h L hL hV).hom
        ((ModuleCat.extendRestrictScalarsAdj g.appTop.hom).unit.app _ s)) =
    ((affineTilde T).map (residueSectionsIso h L hL hV).hom).app ⊤
      ((affineAdjunction T).unit.app _
        ((ModuleCat.extendRestrictScalarsAdj g.appTop.hom).unit.app _ s)) at hn
  rw [← hn, properPushforwardTildeIso_unit]
  let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  change pullGlobal p L s = globalComparison h L (1 ⊗ₜ[Γ(S, ⊤)] s)
  rw [globalComparison_tmul, one_smul]

/-- The cohomological isomorphism is exactly the actual sheaf base-change mate. -/
theorem properLinePushforwardBaseChangeIso_eq_mate :
    (properLinePushforwardBaseChangeIso h L hL hV).hom =
      DirectImageBaseChange.comparison p q f g h.w.symm L := by
  let _ : IsProper q := MorphismProperty.of_isPullback h inferInstance
  let _ := (hL.pullback p).isFinitePresentation
  apply (cancel_epi ((pullback g).map (properLinePushforwardTildeIso f L hL).hom)).mp
  apply (cancel_epi ((AffineQuasiCoherentBaseChange.tildePullbackIso g).hom.app _)).mp
  have hn := congrArg Iso.hom (properLinePushforwardBaseChangeIso_normalization h L hL hV)
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc] using
    hn.trans (properLinePushforwardMate_normalization h L hL hV).symm

/-- The original cohomological comparison satisfies the actual counit mate identity. -/
@[reassoc]
theorem properLinePushforwardBaseChangeIso_counit :
    (pullback q).map (properLinePushforwardBaseChangeIso h L hL hV).hom ≫
        (pullbackPushforwardAdjunction q).counit.app ((pullback p).obj L) =
      (SchemePullbackSquare.squareIso f q g p h.w.symm).hom.app
          ((pushforward f).obj L) ≫
        (pullback p).map ((pullbackPushforwardAdjunction f).counit.app L) := by
  rw [properLinePushforwardBaseChangeIso_eq_mate]
  exact DirectImageBaseChange.comparison_counit p q f g h.w.symm L

include hL hV in
/-- Residue-fiber vanishing makes the independently constructed mate invertible. -/
theorem properLineBaseChangeMate_isIso :
    IsIso (DirectImageBaseChange.comparison p q f g h.w.symm L) := by
  rw [← properLinePushforwardBaseChangeIso_eq_mate h L hL hV]
  infer_instance

end FLT.Mazur.LineSectionBaseChange
