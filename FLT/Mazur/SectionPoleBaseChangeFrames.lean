/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineModuleGlobalSections
public import FLT.Mazur.SectionPointPowerBaseChange
public import FLT.Mazur.SectionPoleLineFrames

/-!
# Common leading frames on the original changed family

The actual cartesian comparison of point powers transports the leading lines
along the retained section. A single frame of the original restricted divisor
line therefore frames every leading line of the changed family.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle

variable {P X T S : Scheme} {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  [IsSeparated f] (h : IsPullback p q f g)
  (s : S ⟶ X) (t : T ⟶ P) (hs : s ≫ f = 𝟙 _) (ht : t ≫ q = 𝟙 _)
  (hst : t ≫ p = g ≫ s) (hI : EffectiveCartier s.ker) (hJ : EffectiveCartier t.ker)

/-- The original leading line pulls back to the leading line of the retained section. -/
def sectionPoleLineBaseChangeIso (m : ℕ) :
    (pullback g).obj (sectionPoleLine s hI m) ≅ sectionPoleLine t hJ m :=
  (pullbackComp g s).app _ ≪≫ (pullbackCongr hst.symm).app _ ≪≫
    ((pullbackComp t p).app _).symm ≪≫
      (pullback t).mapIso (sectionPointPowerIso h s t hs ht hst hI hJ m)

/-- One frame of the pulled original line gives all actual changed-family leading frames. -/
def sectionPoleChangedFrame
    (e : (pullback g).obj ((pullback s).obj (divisorLineBundle s.ker hI)) ≅
      structureModule T) (m : ℕ) : sectionPoleLine t hJ m ≅ structureModule T :=
  (sectionPoleLineBaseChangeIso h s t hs ht hst hI hJ m).symm ≪≫
    (pullback g).mapIso (tensorPowerIso s (divisorLineBundle s.ker hI) m) ≪≫
      tensorPowerIso g ((pullback s).obj (divisorLineBundle s.ker hI)) m ≪≫
        tensorPowerTrivialization e m

/-- Restriction frames transfer through the actual square, with the same open in every degree. -/
def sectionPoleOpenChangedFrame {U : S.Opens} {P : Scheme}
    {p : P ⟶ X} {q : P ⟶ U.toScheme} (h : IsPullback p q f U.ι)
    (t : U.toScheme ⟶ P) (ht : t ≫ q = 𝟙 _) (hst : t ≫ p = U.ι ≫ s)
    (hJ : EffectiveCartier t.ker)
    (e : ((pullback s).obj (divisorLineBundle s.ker hI)).restrict U.ι ≅
      structureModule U.toScheme) (m : ℕ) :
    sectionPoleLine t hJ m ≅ structureModule U.toScheme :=
  sectionPoleChangedFrame h s t hs ht hst hI hJ
    (((restrictFunctorIsoPullback U.ι).app _).symm ≪≫ e) m

/-- Global leading coordinates retain the actual changed-base scalar action. -/
def sectionPoleChangedCoordinates
    (e : (pullback g).obj ((pullback s).obj (divisorLineBundle s.ker hI)) ≅
      structureModule T) (m : ℕ) :
    Γ(sectionPoleLine t hJ m, ⊤) ≃ₗ[Γ(T, ⊤)] Γ(T, ⊤) :=
  ((AffineModuleGlobalSections.sections T).mapIso
    (sectionPoleChangedFrame h s t hs ht hst hI hJ e m)).toLinearEquiv

include hI in
/-- One affine restriction of the actual family admits all compatible leading-line frames. -/
theorem sectionPoleFrames_on_affine_family (x : S) :
    ∃ U : S.Opens, x ∈ U ∧ IsAffineOpen U ∧
      ∃ hJ : EffectiveCartier (sectionBaseChange f U.ι s hs).ker,
        ∀ m : ℕ, Nonempty
          (sectionPoleLine (sectionBaseChange f U.ι s hs) hJ m ≅
            structureModule U.toScheme) := by
  obtain ⟨U, hx, hU, ⟨e⟩⟩ := sectionPoleLine_affine_frame s hI x
  let t := sectionBaseChange f U.ι s hs
  have ht : t ≫ Limits.pullback.snd f U.ι = 𝟙 _ := sectionBaseChange_snd f U.ι s hs
  have hst : t ≫ Limits.pullback.fst f U.ι = U.ι ≫ s := by
    simp only [t, sectionBaseChange, Limits.pullback.lift_fst]
  let hJ := sectionPoint_cartier_baseChange (IsPullback.of_hasPullback f U.ι)
    s t hs ht hst hI
  exact ⟨U, hx, hU, hJ, fun m ↦ ⟨sectionPoleOpenChangedFrame s hs hI
    (IsPullback.of_hasPullback f U.ι) t ht hst hJ e m⟩⟩

end FLT.Mazur.FCurve
