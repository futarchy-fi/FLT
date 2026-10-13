/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteMarkingDescent
public import FLT.Mazur.SchemeFppfLineDescentEquivalence

/-!
# Effective descent of the full complete-family marking line

A surjective fppf parameter map gives an effective descent datum on the full
total space. The glued line is canonically identified with the original
positive marking line, and its recovery is the specified geometric comparison.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve SchemePicard SchemeGeometricDescent SchemeAffineDescent
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completeMarkingDivisor completeFiberMarking completeMarkingLineBaseChangeIso
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  {S : Scheme} (s : S ⟶ Spec (.of (PowerSeries K)))
  [Flat s] [Surjective s] [LocallyOfFinitePresentation s]
local notation "p" => pullback.fst (exactVeroneseProjToBase K n h) s

/-- The actual glued positive marking line on the original complete family. -/
def completeMarkingGluedLine : LineBundleCat (exactVeroneseProj K n h) :=
  (lineGluing p).obj (completeMarkingLineDatum K n h s)

/-- Effective descent recovers the original marking-line datum with its overlap. -/
def completeMarkingGluedRecovery :
    (lineCanonical p).obj (completeMarkingGluedLine K n h s) ≅
      completeMarkingLineDatum K n h s :=
  lineSourceRecoveryIso p (completeMarkingLineDatum K n h s)

/-- Identification of the descended line with the original complete marking line. -/
def completeMarkingDescentIso :
    completeMarkingLineObject K n h ≅ completeMarkingGluedLine K n h s :=
  lineBaseRecoveryIso p (completeMarkingLineObject K n h) ≪≫
    (lineGluing p).mapIso (completeMarkingCanonicalIso K n h s)

/-- The specified global identification recovers the original comparison as descent maps. -/
theorem completeMarkingDescentIso_recovery :
    (lineCanonical p).map (completeMarkingDescentIso K n h s).hom ≫
      (completeMarkingGluedRecovery K n h s).hom =
        (completeMarkingCanonicalIso K n h s).hom := by
  dsimp only [completeMarkingDescentIso, completeMarkingGluedRecovery,
    Iso.trans_hom, Functor.mapIso_hom]
  rw [Functor.map_comp, Category.assoc]
  have hn := (lineSourceRecovery p).hom.naturality (completeMarkingCanonicalIso K n h s).hom
  change (lineCanonical p).map ((lineGluing p).map _) ≫ _ = _ at hn
  change (lineCanonical p).map (lineBaseRecoveryIso p _).hom ≫
    (lineCanonical p).map ((lineGluing p).map _) ≫
      (lineSourceRecovery p).hom.app _ = _
  have ht := lineBaseRecovery_triangle p (completeMarkingLineObject K n h)
  change (lineCanonical p).map (lineBaseRecoveryIso p _).hom ≫
    (lineSourceRecovery p).hom.app _ = 𝟙 _ at ht
  rw [hn, ← Category.assoc]
  exact (congrArg (fun f ↦ f ≫ (completeMarkingCanonicalIso K n h s).hom) ht).trans
    (Category.id_comp _)

/-- Recovery keeps the actual marking-line sheaf comparison, including its section normalization. -/
theorem completeMarkingDescentIso_sheaf_recovery :
    (Scheme.Modules.pullback p).map (completeMarkingDescentIso K n h s).hom.hom ≫
      (completeMarkingGluedRecovery K n h s).hom.val =
        (completeMarkingLineBaseChangeIso K n h s).hom :=
  congrArg Subtype.val (completeMarkingDescentIso_recovery K n h s)

/-- The line constructed by effective descent is ample on the original complete family. -/
theorem completeMarkingGluedLine_ample :
    AmpleLineBundle (completeMarkingGluedLine K n h s).val :=
  (completeMarkingLine_ample K n h).of_iso
    ((lineBundleForget _).mapIso (completeMarkingDescentIso K n h s)).symm

end FLT.Mazur.PolygonInfinitesimalStages
