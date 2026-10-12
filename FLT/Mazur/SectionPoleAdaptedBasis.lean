/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionPoleSplit
public import Mathlib.LinearAlgebra.Basis.Prod

/-!
# Bases adapted to the original pole inclusion

Extend an actual lower-pole basis by a basis of the base pole line. The old
vectors are transported by the original divisor transition, and the new
vectors have the prescribed leading sections. This is a filtration basis;
no assertion about multiplication of the chosen lifts is made here.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules Module
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X S : Scheme} [IsAffine S] (f : X ⟶ S) [IsSeparated f]
  (s : S ⟶ X) (hs : s ≫ f = 𝟙 S) (hI : EffectiveCartier s.ker)
  (m : ℕ) [Subsingleton (ModuleH (tensorPower (divisorLineBundle s.ker hI) m) 1)]
  {ι κ : Type} (b : Basis ι Γ(S, ⊤)
    (ModuleRingH f.appTop.hom (tensorPower (divisorLineBundle s.ker hI) m) 0))
  (c : Basis κ Γ(S, ⊤) Γ(sectionPoleLine s hI (m + 1), ⊤))

/-- Extend a lower-pole basis using actual lifts of a leading-line basis. -/
def sectionPoleAdaptedBasis : Basis (ι ⊕ κ) Γ(S, ⊤)
    (ModuleRingH f.appTop.hom (tensorPower (divisorLineBundle s.ker hI) (m + 1)) 0) :=
  (b.prod c).map (sectionPoleSplit f s hs hI m).val.symm

/-- Every old basis vector is included by the original divisor step. -/
theorem sectionPoleAdaptedBasis_old (i : ι) :
    sectionPoleAdaptedBasis f s hs hI m b c (Sum.inl i) =
      divisorPowerRingStep f.appTop.hom hI m (b i) := by
  rw [sectionPoleAdaptedBasis, Basis.map_apply, Basis.prod_apply]
  exact (LinearMap.congr_fun (sectionPoleSplit f s hs hI m).property.1 (b i)).symm

/-- New basis vectors lift precisely the chosen leading-line basis. -/
theorem sectionPoleAdaptedBasis_new_leading (j : κ) :
    sectionPoleLeading f s hs hI m
      (sectionPoleAdaptedBasis f s hs hI m b c (Sum.inr j)) = c j := by
  rw [← sectionPoleSplit_leading]
  change ((sectionPoleSplit f s hs hI m).val
    ((sectionPoleSplit f s hs hI m).val.symm ((b.prod c) (Sum.inr j)))).2 = _
  rw [LinearEquiv.apply_symm_apply, Basis.prod_apply_inr_snd]

/-- The leading coefficients are exactly the new coordinates of the adapted basis. -/
theorem sectionPoleAdaptedBasis_leading_repr
    (x : ModuleRingH f.appTop.hom (tensorPower (divisorLineBundle s.ker hI) (m + 1)) 0)
    (j : κ) :
    (sectionPoleAdaptedBasis f s hs hI m b c).repr x (Sum.inr j) =
      c.repr (sectionPoleLeading f s hs hI m x) j := by
  rw [sectionPoleAdaptedBasis, Basis.map_repr, LinearEquiv.trans_apply,
    LinearEquiv.symm_symm, Basis.prod_repr_inr, sectionPoleSplit_leading]

/-- A frame of the actual leading line supplies a lift with leading coefficient one. -/
def sectionPoleNormalizedLift
    (e : Γ(sectionPoleLine s hI (m + 1), ⊤) ≃ₗ[Γ(S, ⊤)] Γ(S, ⊤)) :
    ModuleRingH f.appTop.hom (tensorPower (divisorLineBundle s.ker hI) (m + 1)) 0 :=
  (sectionPoleSplit f s hs hI m).val.symm (0, e.symm 1)

/-- The constructed normalized lift has the specified original leading coefficient. -/
theorem sectionPoleNormalizedLift_leading
    (e : Γ(sectionPoleLine s hI (m + 1), ⊤) ≃ₗ[Γ(S, ⊤)] Γ(S, ⊤)) :
    e (sectionPoleLeading f s hs hI m (sectionPoleNormalizedLift f s hs hI m e)) = 1 := by
  rw [← sectionPoleSplit_leading]
  change e (((sectionPoleSplit f s hs hI m).val
    ((sectionPoleSplit f s hs hI m).val.symm (0, e.symm 1))).2) = 1
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- A normalized lift extends any actual basis of the preceding pole module. -/
def sectionPoleNormalizedBasis
    (e : Γ(sectionPoleLine s hI (m + 1), ⊤) ≃ₗ[Γ(S, ⊤)] Γ(S, ⊤)) :
    Basis (ι ⊕ Unit) Γ(S, ⊤)
      (ModuleRingH f.appTop.hom (tensorPower (divisorLineBundle s.ker hI) (m + 1)) 0) :=
  sectionPoleAdaptedBasis f s hs hI m b ((Basis.singleton Unit Γ(S, ⊤)).map e.symm)

/-- The new basis vector is precisely the normalized lift constructed above. -/
theorem sectionPoleNormalizedBasis_new
    (e : Γ(sectionPoleLine s hI (m + 1), ⊤) ≃ₗ[Γ(S, ⊤)] Γ(S, ⊤)) :
    sectionPoleNormalizedBasis f s hs hI m b e (Sum.inr ()) =
      sectionPoleNormalizedLift f s hs hI m e := by
  simp only [sectionPoleNormalizedBasis, sectionPoleAdaptedBasis, Basis.map_apply,
    Basis.prod_apply, Sum.elim_inr, Function.comp_apply, LinearMap.inr_apply,
    Basis.singleton_apply, sectionPoleNormalizedLift]

end FLT.Mazur.FCurve
