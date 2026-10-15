/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticCompatibleScalars

/-!
# A sealed algebra of compatible actual sections

A named carrier and named algebra structures keep homogeneous constructions
from repeatedly unfolding the entire ring of stagewise coefficient functions.
The carrier and evaluation maps remain those of the actual compatible ring.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonArithmeticStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (A : Type) [CommRing A] (π : A) (n : ℕ) (h : 2 ≤ n)

/-- The carrier of compatible sections of the actual arithmetic system. -/
def CompatibleSections : Type := compatibleSectionRing A π n h

/-- The original compatible-section ring operations on the named carrier. -/
instance compatibleSectionsCommRing : CommRing (CompatibleSections A π n h) :=
  inferInstanceAs (CommRing (compatibleSectionRing A π n h))

/-- The integral-base algebra structure on the named compatible-section carrier. -/
instance compatibleSectionsAlgebra : Algebra A (CompatibleSections A π n h) :=
  inferInstanceAs (Algebra A (compatibleSectionRing A π n h))

/-- Evaluation on the sealed carrier is the original actual stage evaluation. -/
def compatibleEval (m : ℕ) : CompatibleSections A π n h →+* boundaryGradedSections A π n h m :=
  compatibleSectionEval A π n h m

/-- The specified stage maps still commute with evaluation on the named carrier. -/
theorem compatibleEval_transition {a b : ℕ} (f : a ⟶ b) :
    (boundarySectionsMap A π n h f).comp (compatibleEval A π n h b) = compatibleEval A π n h a :=
  compatibleSectionEval_transition A π n h f

/-- The original structural scalar at each stage is retained. -/
theorem compatibleEval_algebraMap (m : ℕ) (r : A) :
    compatibleEval A π n h m (algebraMap A (CompatibleSections A π n h) r) =
      boundaryIntegralScalars A π n h m r := rfl

/-- The actual stage projections jointly determine a section on the named carrier. -/
theorem compatibleEval_ext {s t : CompatibleSections A π n h}
    (he : ∀ m, compatibleEval A π n h m s = compatibleEval A π n h m t) : s = t :=
  compatibleSection_ext A π n h he

attribute [irreducible] CompatibleSections

end FLT.Mazur.PolygonArithmeticStages
