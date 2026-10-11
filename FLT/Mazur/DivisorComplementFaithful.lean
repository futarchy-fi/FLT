/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorPowerComplementTransition
public import FLT.Mazur.LineCartierComplementRestriction

/-!
# Faithful functions of original pole sections

The complement coordinate of an original pole section determines the section.
The actual H0 pole-step range is consequently detected by the lower function space.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme} {I : X.IdealSheafData} (hI : EffectiveCartier I)

/-- An original global pole section is determined by its complement function. -/
theorem divisorComplementFunction_injective (m : ℕ) :
    Function.Injective (divisorComplementFunction hI m) := by
  intro s t he
  have hh := SectionGradedLocalCoordinates.coordinate_injective
    (divisorComplementTrivialization hI) m ⊤ he
  apply LocallyFreeRankOne.cartierComplement_restrict_injective
    (hI.divisorLineBundle_locallyFreeRankOne.tensorPower m) hI ⊤
  have hu : (⊤ : X.Opens) ⊓ I.support.compl ≤ (Scheme.Opens.ι (X := X) I.support.compl) ''ᵁ ⊤ := by
    simp only [Scheme.Opens.ι_image_top, top_inf_eq, le_refl]
  have ht := congrArg ((tensorPower (divisorLineBundle I hI) m).presheaf.map
    (homOfLE hu).op) hh
  simpa only [← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← op_comp, homOfLE_comp] using ht

variable {k : Type} [Field k] (f : X ⟶ Spec (.of k))

/-- The actual degree-zero cohomology is faithfully represented by complement functions. -/
theorem divisorPowerH0Function_injective (m : ℕ) :
    Function.Injective (divisorPowerH0Function f hI m) :=
  (divisorComplementFunction_injective hI m).comp (moduleScalarH0Equiv f _).injective

/-- A function has a lower pole bound exactly when its section is in the original step range. -/
theorem divisorPowerH0Function_mem_lower_iff (m : ℕ)
    (x : ModuleScalarH f (tensorPower (divisorLineBundle I hI) (m + 1)) 0) :
    divisorPowerH0Function f hI (m + 1) x ∈ divisorPoleFunctions hI m ↔
      x ∈ LinearMap.range (divisorPowerH0Step f hI m) := by
  rw [mem_divisorPoleFunctions_iff_h0 f hI]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, divisorPowerH0Function_injective hI f (m + 1) ?_⟩
    rw [divisorPowerH0Function_step]
    exact hy
  · rintro ⟨y, rfl⟩
    exact ⟨y, (divisorPowerH0Function_step f hI m y).symm⟩

end FLT.Mazur.FCurve
