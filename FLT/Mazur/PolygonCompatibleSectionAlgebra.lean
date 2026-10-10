/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompatibleSectionScalars

/-!
# A sealed algebra of compatible actual sections

A named carrier and named algebra structures keep homogeneous constructions
from repeatedly unfolding the entire ring of stagewise coefficient functions.
The carrier and evaluation maps remain those of the actual compatible ring.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (R : Type) [CommRing R] (n : ℕ) (h : 2 ≤ n)

/-- The carrier of compatible sections of the actual infinitesimal system. -/
def CompatibleSections : Type := compatibleSectionRing R n h

/-- The original compatible-section ring operations on the named carrier. -/
instance compatibleSectionsCommRing : CommRing (CompatibleSections R n h) :=
  inferInstanceAs (CommRing (compatibleSectionRing R n h))

/-- The complete-base algebra structure on the named compatible-section carrier. -/
instance compatibleSectionsAlgebra : Algebra (PowerSeries R) (CompatibleSections R n h) :=
  inferInstanceAs (Algebra (PowerSeries R) (compatibleSectionRing R n h))

/-- Evaluation on the sealed carrier is the original actual stage evaluation. -/
def compatibleEval (m : ℕ) : CompatibleSections R n h →+* boundaryGradedSections R n h m :=
  compatibleSectionEval R n h m

/-- The specified stage maps still commute with evaluation on the named carrier. -/
theorem compatibleEval_transition {a b : ℕ} (f : a ⟶ b) :
    (boundarySectionsMap R n h f).comp (compatibleEval R n h b) = compatibleEval R n h a :=
  compatibleSectionEval_transition R n h f

/-- The original structural scalar at each stage is retained. -/
theorem compatibleEval_algebraMap (m : ℕ) (r : PowerSeries R) :
    compatibleEval R n h m (algebraMap (PowerSeries R) (CompatibleSections R n h) r) =
      boundarySeriesScalars R n h m r := rfl

/-- The actual stage projections jointly determine a section on the named carrier. -/
theorem compatibleEval_ext {s t : CompatibleSections R n h}
    (he : ∀ m, compatibleEval R n h m s = compatibleEval R n h m t) : s = t :=
  compatibleSection_ext R n h he

attribute [irreducible] CompatibleSections

end FLT.Mazur.PolygonInfinitesimalStages
