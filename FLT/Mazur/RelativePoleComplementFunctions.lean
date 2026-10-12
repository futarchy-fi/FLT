/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorComplementLinear
public import FLT.Mazur.RelativeGenusOneInitialPoleStep
public import FLT.Mazur.SectionPoleHZeroMultiplication

/-!
# Relative pole sections as original complement functions

The original H0 sections define actual functions on the divisor complement.
The maps retain the base-ring scalars, products and canonical pole inclusions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle divisorComplementFunction

variable {X S : Scheme.{0}} (f : X ⟶ S) (s : S ⟶ X) (hI : EffectiveCartier s.ker)

/-- The actual complement function represented by a relative pole section. -/
def relativePoleFunction (m : ℕ)
    (x : ModuleRingH f.appTop.hom (tensorPower (divisorLineBundle s.ker hI) m) 0) :
    Γ(Scheme.Opens.toScheme (X := X) s.ker.support.compl, ⊤) :=
  divisorComplementFunction hI m (moduleH0Equiv _ x)

/-- Addition of relative sections is addition of their actual functions. -/
theorem relativePoleFunction_add (m : ℕ)
    (x y : ModuleRingH f.appTop.hom (tensorPower (divisorLineBundle s.ker hI) m) 0) :
    relativePoleFunction f s hI m (x + y) =
      relativePoleFunction f s hI m x + relativePoleFunction f s hI m y := by
  unfold relativePoleFunction
  rw [map_add, divisorComplementFunction_add]

/-- The function map as an additive homomorphism, for finite relation sums. -/
def relativePoleFunctionAddHom (m : ℕ) :
    ModuleRingH f.appTop.hom (tensorPower (divisorLineBundle s.ker hI) m) 0 →+
      Γ(Scheme.Opens.toScheme (X := X) s.ker.support.compl, ⊤) where
  toFun := relativePoleFunction f s hI m
  map_zero' := by
    unfold relativePoleFunction
    rw [map_zero, divisorComplementFunction_zero]
  map_add' := relativePoleFunction_add f s hI m

/-- Base scalars act through the two original structure-sheaf maps. -/
theorem relativePoleFunction_smul (m : ℕ) (r : Γ(S, ⊤))
    (x : ModuleRingH f.appTop.hom (tensorPower (divisorLineBundle s.ker hI) m) 0) :
    relativePoleFunction f s hI m (r • x) =
      (Scheme.Opens.ι (X := X) s.ker.support.compl).appTop (f.appTop r) *
        relativePoleFunction f s hI m x := by
  have h := (ringHZeroPushforwardSections f
    (tensorPower (divisorLineBundle s.ker hI) m)).map_smul r x
  change moduleH0Equiv _ (r • x) = f.appTop r • moduleH0Equiv _ x at h
  exact (congrArg (divisorComplementFunction hI m) h).trans
    (divisorComplementFunction_smul hI m (f.appTop r) _)

/-- The actual tensor-degree product represents multiplication of complement functions. -/
theorem relativePoleFunction_product (m n : ℕ)
    (x : ModuleRingH f.appTop.hom (tensorPower (divisorLineBundle s.ker hI) m) 0)
    (y : ModuleRingH f.appTop.hom (tensorPower (divisorLineBundle s.ker hI) n) 0) :
    relativePoleFunction f s hI (m + n) (sectionPoleHZeroProduct f s hI m n x y) =
      relativePoleFunction f s hI m x * relativePoleFunction f s hI n y :=
  (congrArg (divisorComplementFunction hI (m + n))
    (sectionPoleHZeroProduct_sections f s hI m n x y)).trans
      (divisorComplementFunction_mul hI m n _ _)

/-- The original canonical pole inclusion preserves the represented function. -/
theorem relativePoleFunction_step (m : ℕ)
    (x : ModuleRingH f.appTop.hom (tensorPower (divisorLineBundle s.ker hI) m) 0) :
    relativePoleFunction f s hI (m + 1) (divisorPowerRingStep f.appTop.hom hI m x) =
      relativePoleFunction f s hI m x := by
  unfold relativePoleFunction
  rw [divisorPowerRingStep_sections, divisorTwistedComplex_leftUnitor,
    divisorComplementFunction_cons]

end FLT.Mazur.FCurve
