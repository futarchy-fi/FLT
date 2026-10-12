/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionPoleMultiplicativeCoordinates

/-!
# Actual section multiplication on the relative pole cohomology modules

The degree-zero cohomology comparison transfers multiplication of original
sections. Its leading coefficient is the product in one common section-line frame.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor

variable {X S : Scheme} (f : X ⟶ S) (s : S ⟶ X) (hI : EffectiveCartier s.ker)

/-- Multiply the original global sections while retaining the relative H0 module types. -/
def sectionPoleHZeroProduct (m n : ℕ)
    (x : ModuleRingH f.appTop.hom (tensorPower (divisorLineBundle s.ker hI) m) 0)
    (y : ModuleRingH f.appTop.hom (tensorPower (divisorLineBundle s.ker hI) n) 0) :
    ModuleRingH f.appTop.hom (tensorPower (divisorLineBundle s.ker hI) (m + n)) 0 :=
  (moduleH0Equiv _).symm
    (SectionGradedMultiplication.mul _ ⊤ m n (moduleH0Equiv _ x) (moduleH0Equiv _ y))

/-- The H0 product is precisely the tensor-degree product of the original sections. -/
theorem sectionPoleHZeroProduct_sections (m n : ℕ)
    (x : ModuleRingH f.appTop.hom (tensorPower (divisorLineBundle s.ker hI) m) 0)
    (y : ModuleRingH f.appTop.hom (tensorPower (divisorLineBundle s.ker hI) n) 0) :
    moduleH0Equiv _ (sectionPoleHZeroProduct f s hI m n x y) =
      SectionGradedMultiplication.mul _ ⊤ m n (moduleH0Equiv _ x) (moduleH0Equiv _ y) :=
  (moduleH0Equiv _).apply_symm_apply _

/-- In one original frame, the H0 product multiplies leading coefficients. -/
theorem sectionPoleHZeroProduct_coefficient
    (e : (pullback s).obj (divisorLineBundle s.ker hI) ≅ structureModule S) (m n : ℕ)
    (x : ModuleRingH f.appTop.hom (tensorPower (divisorLineBundle s.ker hI) m) 0)
    (y : ModuleRingH f.appTop.hom (tensorPower (divisorLineBundle s.ker hI) n) 0) :
    sectionPoleCoefficient s hI e (m + n)
      (moduleH0Equiv _ (sectionPoleHZeroProduct f s hI m n x y)) =
        sectionPoleCoefficient s hI e m (moduleH0Equiv _ x) *
          sectionPoleCoefficient s hI e n (moduleH0Equiv _ y) := by
  rw [sectionPoleHZeroProduct_sections, sectionPoleCoefficient_mul]

end FLT.Mazur.FCurve
