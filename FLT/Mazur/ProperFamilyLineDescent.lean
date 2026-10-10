/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineDescentDiagonalRigidity
public import FLT.Mazur.LocallyNoetherianUniversalStructureSheaf
public import FLT.Mazur.SchemeFppfLineDescentEquivalence

/-!
# Unpointed line-isomorphism descent after arbitrary family base change

The double overlap has its actual diagonal section. Relative functions and
line rigidity make every pulled-line isomorphism compatible with canonical
descent. Effective fppf descent then recovers the original base lines.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.ProperFamilyLineDescent
open FCurve SchemeGeometricDescent SchemeAffineDescent SchemePicard
variable {P X T S : Scheme.{0}} [IsLocallyNoetherian S]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  [IsProper f] [Flat f] [Surjective f]
  [GeometricallyConnected f] [GeometricallyReduced f] (h : IsPullback p q f g)

omit [Surjective f] in
include h in
/-- The changed double overlap is a base change of the original pointed double overlap. -/
lemma doubleOverlap_appTop_surjective :
    Function.Surjective (Limits.pullback.fst q q).appTop := by
  let _ := LocallyOfFiniteType.isLocallyNoetherian f
  have outer := (IsPullback.of_hasPullback q q).flip.paste_horiz h
  have outer' : IsPullback (Limits.pullback.snd q q ≫ p)
      (Limits.pullback.fst q q) f (p ≫ f) := by
    simpa only [h.w] using outer
  have H := outer'.of_right' (IsPullback.of_hasPullback f f).flip
  exact (LocallyNoetherianUniversalStructureSheaf.appTop_bijective H
    (Limits.pullback.diagonal f) (Limits.pullback.diagonal_fst f)).surjective

omit [Surjective f] in
include h in
/-- Every actual pulled-line isomorphism satisfies its canonical descent square. -/
lemma canonical_iso_compatible {M N : T.Modules} (hM : LocallyFreeRankOne M)
    (hN : LocallyFreeRankOne N) (e : (pullback q).obj M ≅ (pullback q).obj N) :
    (canonical q M).MapCompatible q (canonical q N) e.hom :=
  iso_mapCompatible q (doubleOverlap_appTop_surjective h)
    ((lineCanonical q).obj ⟨M, hM⟩) ((lineCanonical q).obj ⟨N, hN⟩) e

/-- The original isomorphism as an isomorphism of canonical geometric descent data. -/
def canonicalIso {M N : T.Modules} (hM : LocallyFreeRankOne M) (hN : LocallyFreeRankOne N)
    (e : (pullback q).obj M ≅ (pullback q).obj N) :
    (lineCanonical q).obj ⟨M, hM⟩ ≅ (lineCanonical q).obj ⟨N, hN⟩ :=
  LineData.isoMk q e (canonical_iso_compatible h hM hN e)

/-- Descend the specified isomorphism without choosing a section of the original family. -/
def descendIso {M N : T.Modules} (hM : LocallyFreeRankOne M) (hN : LocallyFreeRankOne N)
    (e : (pullback q).obj M ≅ (pullback q).obj N) : M ≅ N := by
  let _ : Flat q := MorphismProperty.of_isPullback h inferInstance
  let _ : Surjective q := MorphismProperty.of_isPullback h inferInstance
  let _ : LocallyOfFinitePresentation q := MorphismProperty.of_isPullback h inferInstance
  exact (lineBundleForget T).mapIso
    ((lineDescentEquivalence q).fullyFaithfulFunctor.preimageIso
      (X := (⟨M, hM⟩ : LineBundleCat T)) (Y := (⟨N, hN⟩ : LineBundleCat T))
      (canonicalIso h hM hN e))

/-- Pullback of the descended isomorphism is the full original total-space isomorphism. -/
lemma mapIso_descendIso {M N : T.Modules} (hM : LocallyFreeRankOne M)
    (hN : LocallyFreeRankOne N) (e : (pullback q).obj M ≅ (pullback q).obj N) :
    (pullback q).mapIso (descendIso h hM hN e) = e := by
  let _ : Flat q := MorphismProperty.of_isPullback h inferInstance
  let _ : Surjective q := MorphismProperty.of_isPullback h inferInstance
  let _ : LocallyOfFinitePresentation q := MorphismProperty.of_isPullback h inferInstance
  apply Iso.ext
  exact congrArg Subtype.val ((lineDescentEquivalence q).fullyFaithfulFunctor.map_preimage
    (X := (⟨M, hM⟩ : LineBundleCat T)) (Y := (⟨N, hN⟩ : LineBundleCat T))
    (canonicalIso h hM hN e).hom)

end FLT.Mazur.ProperFamilyLineDescent
