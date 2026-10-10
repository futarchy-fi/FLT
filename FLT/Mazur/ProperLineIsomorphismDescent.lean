/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineDescentDiagonalRigidity
public import FLT.Mazur.NoetherianProperStructureSheaf
public import FLT.Mazur.SchemeFppfLineDescentEquivalence

/-!
# Unpointed descent of line isomorphisms for proper connected families

The double overlap has its actual diagonal section. Relative functions and
line rigidity make every pulled-line isomorphism compatible with canonical
descent. Effective fppf descent then recovers the original base lines.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.ProperLineIsomorphismDescent
open FCurve SchemeGeometricDescent SchemeAffineDescent SchemePicard
variable {X S : Scheme.{0}} (f : X ⟶ S) [IsLocallyNoetherian S]
  [IsProper f] [Flat f] [Surjective f]
  [GeometricallyConnected f] [GeometricallyReduced f]

omit [Surjective f] in
/-- The diagonal supplies the needed section on the actual double overlap. -/
lemma doubleOverlap_appTop_surjective :
    Function.Surjective (Limits.pullback.fst f f).appTop := by
  let _ := LocallyOfFiniteType.isLocallyNoetherian f
  exact (NoetherianProperStructureSheaf.appTop_bijective (Limits.pullback.fst f f)
    (Limits.pullback.diagonal f) (Limits.pullback.diagonal_fst f)).surjective

omit [Surjective f] in
/-- Every actual pulled-line isomorphism satisfies its canonical descent square. -/
lemma canonical_iso_compatible {M N : S.Modules} (hM : LocallyFreeRankOne M)
    (hN : LocallyFreeRankOne N) (e : (pullback f).obj M ≅ (pullback f).obj N) :
    (canonical f M).MapCompatible f (canonical f N) e.hom :=
  iso_mapCompatible f (doubleOverlap_appTop_surjective f)
    ((lineCanonical f).obj ⟨M, hM⟩) ((lineCanonical f).obj ⟨N, hN⟩) e

/-- The original isomorphism as an isomorphism of canonical geometric descent data. -/
def canonicalIso {M N : S.Modules} (hM : LocallyFreeRankOne M) (hN : LocallyFreeRankOne N)
    (e : (pullback f).obj M ≅ (pullback f).obj N) :
    (lineCanonical f).obj ⟨M, hM⟩ ≅ (lineCanonical f).obj ⟨N, hN⟩ :=
  LineData.isoMk f e (canonical_iso_compatible f hM hN e)

/-- Descend the specified isomorphism without choosing a section of the original family. -/
def descendIso {M N : S.Modules} (hM : LocallyFreeRankOne M) (hN : LocallyFreeRankOne N)
    (e : (pullback f).obj M ≅ (pullback f).obj N) : M ≅ N := by
  exact (lineBundleForget S).mapIso
    ((lineDescentEquivalence f).fullyFaithfulFunctor.preimageIso
      (X := (⟨M, hM⟩ : LineBundleCat S)) (Y := (⟨N, hN⟩ : LineBundleCat S))
      (canonicalIso f hM hN e))

/-- Pullback of the descended isomorphism is the full original total-space isomorphism. -/
lemma mapIso_descendIso {M N : S.Modules} (hM : LocallyFreeRankOne M)
    (hN : LocallyFreeRankOne N) (e : (pullback f).obj M ≅ (pullback f).obj N) :
    (pullback f).mapIso (descendIso f hM hN e) = e := by
  apply Iso.ext
  exact congrArg Subtype.val ((lineDescentEquivalence f).fullyFaithfulFunctor.map_preimage
    (X := (⟨M, hM⟩ : LineBundleCat S)) (Y := (⟨N, hN⟩ : LineBundleCat S))
    (canonicalIso f hM hN e).hom)

end FLT.Mazur.ProperLineIsomorphismDescent
