/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorComplementFunctionPullback
public import FLT.Mazur.SectionPoleBaseChangeDifference
public import FLT.Mazur.RelativePoleComplementFunctions

/-!
# Pole functions on the actual base-changed complement

The original cartesian section square induces a map of its actual Cartier
complements. Pullback of functions agrees with transport of every positive
pole section through the original point-power comparison.
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
  (hst : t ≫ p = g ≫ s)

include h hs ht hst in
/-- The actual new complement is the inverse image of the original marking complement. -/
theorem sectionPointComplement_preimage :
    t.ker.support.compl = p ⁻¹ᵁ s.ker.support.compl := by
  rw [← section_ker_comap_of_cartesian h t s ht hs hst,
    Scheme.IdealSheafData.support_comap]
  rfl

/-- The original projection restricted to the actual marking complements. -/
def sectionPointComplementMap :
    Scheme.Opens.toScheme (X := P) t.ker.support.compl ⟶
      Scheme.Opens.toScheme (X := X) s.ker.support.compl :=
  p.resLE s.ker.support.compl t.ker.support.compl
    (sectionPointComplement_preimage h s t hs ht hst).le

/-- The complement projection retains its original total-space square. -/
@[reassoc] theorem sectionPointComplementMap_ι :
    sectionPointComplementMap h s t hs ht hst ≫
      Scheme.Opens.ι (X := X) s.ker.support.compl =
        Scheme.Opens.ι (X := P) t.ker.support.compl ≫ p :=
  Scheme.Hom.resLE_comp_ι _ _

/-- Base scalars agree through the actual complement and original base-change morphisms. -/
@[reassoc] theorem sectionPointComplementMap_base :
    sectionPointComplementMap h s t hs ht hst ≫
      Scheme.Opens.ι (X := X) s.ker.support.compl ≫ f =
        Scheme.Opens.ι (X := P) t.ker.support.compl ≫ q ≫ g := by
  rw [← Category.assoc, sectionPointComplementMap_ι, Category.assoc, h.w]

variable (hI : EffectiveCartier s.ker) (hJ : EffectiveCartier t.ker)

/-- Actual complement pullback agrees with the original point-power section transport. -/
theorem sectionPointComplementMap_function (n : ℕ) (hn : 0 < n)
    (z : Γ(tensorPower (divisorLineBundle s.ker hI) n, ⊤)) :
    (sectionPointComplementMap h s t hs ht hst).appTop (divisorComplementFunction hI n z) =
      divisorComplementFunction hJ n
        (sectionPointPowerPullGlobal h s t hs ht hst hI hJ n z) := by
  exact divisorComplementFunction_pullback p hI hJ
    (sectionPointLineIso h s t hs ht hst hI hJ)
    (sectionPointLineIso_section h s t hs ht hst hI hJ)
    (sectionPointComplement_preimage h s t hs ht hst).le n hn z

/-- The original cohomological pole class has the pulled-back regular function. -/
theorem sectionPointComplementMap_relativeFunction (m : ℕ)
    (z : ModuleRingH f.appTop.hom
      (tensorPower (divisorLineBundle s.ker hI) (m + 1)) 0) :
    (sectionPointComplementMap h s t hs ht hst).appTop
        (relativePoleFunction f s hI (m + 1) z) =
      relativePoleFunction q t hJ (m + 1)
        (sectionPolePullH0 h s t hs ht hst hI hJ m z) := by
  unfold relativePoleFunction sectionPolePullH0
  rw [LinearEquiv.apply_symm_apply]
  exact sectionPointComplementMap_function h s t hs ht hst hI hJ (m + 1)
    (Nat.zero_lt_succ m) _

end FLT.Mazur.FCurve
