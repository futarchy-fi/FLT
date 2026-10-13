/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteMarkingSectionDescent
public import FLT.Mazur.SchemeFppfFamilyCover

/-!
# Full marking-line recovery on every member of a parameter atlas

Effective descent along the actual coproduct of an arbitrary small fppf cover
recovers the original positive line on every original covering total space.
The recovery also retains the canonical marking section on each member.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve SchemePicard SchemeFppfFamily
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completeMarkingDivisor completeFiberMarking completeMarkingLineBaseChangeIso
  SchemeFppfFamily.projection
  completeMarkingGluedLine completeMarkingDescentIso completeMarkingGluedSection
/-- A functor retains a recovered section after transport of its target by an isomorphism. -/
theorem markingAtlasSectionRecovery {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {O L M : C} {P N : D} (e : L ≅ M) (s : O ⟶ M) (t : O ⟶ L)
    (ht : s ≫ e.inv = t) (v : F.obj L ≅ N) (u : F.obj O ⟶ P) (k : P ⟶ N)
    (hv : F.map t ≫ v.hom = u ≫ k) :
    F.map s ≫ (F.mapIso e.symm ≪≫ v).hom = u ≫ k := by
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    ← Category.assoc, ← Functor.map_comp, ht] using hv

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (𝒰 : Scheme.Cover.{0} Scheme.fppfPrecoverage (Spec (.of (PowerSeries K))))

/-- Recovery of the glued positive line on each original atlas member. -/
def completeMarkingAtlasLineIso (i : 𝒰.I₀) :
    (Scheme.Modules.pullback (pullback.fst (exactVeroneseProjToBase K n h) (𝒰.f i))).obj
      (completeMarkingGluedLine K n h (projection 𝒰)).val ≅
        completeFiberMarkingLine K n h (𝒰.f i) :=
  (Scheme.Modules.pullback (pullback.fst (exactVeroneseProjToBase K n h) (𝒰.f i))).mapIso
    ((lineBundleForget _).mapIso (completeMarkingDescentIso K n h (projection 𝒰))).symm ≪≫
      completeMarkingLineBaseChangeIso K n h (𝒰.f i)

/-- Every atlas recovery returns the original marking section with its unit normalization. -/
theorem completeMarkingAtlasLineIso_section (i : 𝒰.I₀) :
    (Scheme.Modules.pullback (pullback.fst (exactVeroneseProjToBase K n h) (𝒰.f i))).map
      (completeMarkingGluedSection K n h (projection 𝒰)) ≫
        (completeMarkingAtlasLineIso K n h 𝒰 i).hom =
          (modulePullbackUnitIso _).hom ≫
            divisorSectionMap (completeFiberMarkingDivisor_relativeCartier K n h (𝒰.f i)).1 := by
  exact markingAtlasSectionRecovery
    (Scheme.Modules.pullback (pullback.fst (exactVeroneseProjToBase K n h) (𝒰.f i)))
    ((lineBundleForget _).mapIso (completeMarkingDescentIso K n h (projection 𝒰)))
    (completeMarkingGluedSection K n h (projection 𝒰)) _
    (completeMarkingGluedSection_original K n h (projection 𝒰))
    (completeMarkingLineBaseChangeIso K n h (𝒰.f i)) _ _
    (completeMarkingLineBaseChangeIso_section K n h (𝒰.f i)).section

/-- The atlas-descended line remains relatively ample on the original complete family. -/
theorem completeMarkingAtlasLine_relativelyAmple :
    RelativelyAmpleLineBundle (exactVeroneseProjToBase K n h)
      (completeMarkingGluedLine K n h (projection 𝒰)).val :=
  (completeMarkingGluedLine_ample K n h (projection 𝒰)).relative_of_affine _

end FLT.Mazur.PolygonInfinitesimalStages
