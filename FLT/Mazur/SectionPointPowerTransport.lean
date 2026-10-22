/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionPointLineCoherence

/-!
# Equality transport of cartesian marking comparisons

Canonical comparisons depend only on the actual section, including its
Cartier proof. Heterogeneous equality retains the independently typed target.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
  Scheme.Modules.pullback sectionPointLineIso
variable {P X T S : Scheme} {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  [IsSeparated f] (h : IsPullback p q f g)
  (s : S ⟶ X) (t : T ⟶ P) (hs : s ≫ f = 𝟙 _) (ht : t ≫ q = 𝟙 _)
  (hst : t ≫ p = g ≫ s) (hI : EffectiveCartier s.ker) (hJ : EffectiveCartier t.ker)

variable {t' : T ⟶ P} (ht' : t' ≫ q = 𝟙 _) (hst' : t' ≫ p = g ≫ s)
  (hJ' : EffectiveCartier t'.ker) (w : t = t')
include w

/-- Equal actual sections give the same canonical line comparison after transport. -/
theorem sectionPointLineIso_heq :
    HEq (sectionPointLineIso h s t hs ht hst hI hJ)
      (sectionPointLineIso h s t' hs ht' hst' hI hJ') := by
  cases w
  rfl

/-- Every original pole comparison retains equality of the independently typed section. -/
theorem sectionPointPowerIso_heq (m : ℕ) :
    HEq (sectionPointPowerIso h s t hs ht hst hI hJ m)
      (sectionPointPowerIso h s t' hs ht' hst' hI hJ' m) := by
  cases w
  rfl

end FLT.Mazur.FCurve
