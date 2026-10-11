/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierIdealDescentDatum
public import FLT.Mazur.SchemeFppfLineDescentEquivalence

/-!
# Effective line gluing from matching full Cartier ideals

The canonical overlap constructed from actual ideal equality feeds the
existing effective fppf line descent. This constructs a global line and a
recovery respecting the prescribed ideal-line overlap. Descending its
embedding into the structure sheaf is a further step.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
open SchemePicard SchemeGeometricDescent SchemeAffineDescent
variable {X Y : Scheme.{0}} (p : Y ⟶ X)
  [Flat p] [Surjective p] [LocallyOfFinitePresentation p]
  (I : Y.IdealSheafData) (hI : EffectiveCartier I)
  (h : I.comap (Limits.pullback.fst p p) = I.comap (Limits.pullback.snd p p))

/-- The actual global line constructed from matching full Cartier ideals. -/
def cartierIdealGluedLine : LineBundleCat X :=
  (lineGluing p).obj (cartierIdealLineDatum p I hI h)

/-- The glued line recovers the original ideal line as geometric descent data. -/
def cartierIdealGluedLineRecovery :
    (lineCanonical p).obj (cartierIdealGluedLine p I hI h) ≅
      cartierIdealLineDatum p I hI h :=
  lineSourceRecoveryIso p (cartierIdealLineDatum p I hI h)

/-- The actual global line pulls back to the original full ideal module. -/
def cartierIdealGluedLineIso :
    (pullback p).obj (cartierIdealGluedLine p I hI h).val ≅ idealModule I :=
  (LineData.forget p).mapIso (cartierIdealGluedLineRecovery p I hI h)

/-- Recovery intertwines the canonical global overlap with the original full-ideal overlap. -/
theorem cartierIdealGluedLineIso_compatible :
    (canonical p (cartierIdealGluedLine p I hI h).val).MapCompatible p
      (cartierIdealDescentData p I hI h) (cartierIdealGluedLineIso p I hI h).hom :=
  (cartierIdealGluedLineRecovery p I hI h).hom.property

end FLT.Mazur.FCurve
