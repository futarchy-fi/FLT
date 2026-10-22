/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionSquareTensorFrame
public import FLT.Mazur.SectionPoleBaseChangeNormalization
public import FLT.Mazur.SectionPoleFrameChange

/-!
# Multiplicative frames on the actual changed pole line

Transporting the original multiplicative leading frame agrees with taking
powers of the constructed transported marked-line frame. Consequently all
changed leading-frame transition units are powers of one line unit.
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
  (a : (pullback s).obj (divisorLineBundle s.ker hI) ≅ structureModule S)

/-- The actual transported frame on the new marking's divisor line. -/
def sectionPointTransportedFrame :
    (pullback t).obj (divisorLineBundle t.ker hJ) ≅ structureModule T :=
  sectionSquareTransportFrame p t g s hst (sectionPointLineIso h s t hs ht hst hI hJ) a

/-- Base change of every original multiplicative frame uses that same transported line frame. -/
theorem sectionPoleBaseChangeFrame_multiplicative (n : ℕ) :
    sectionPoleBaseChangeFrame h s t hs ht hst hI hJ n
        (sectionPoleMultiplicativeFrame s hI a n) =
      sectionPoleMultiplicativeFrame t hJ
        (sectionPointTransportedFrame h s t hs ht hst hI hJ a) n := by
  have he := sectionSquareTransportFrame_tensor p t g s hst
    (sectionPointLineIso h s t hs ht hst hI hJ) a n
  apply Iso.ext
  have hh := congrArg Iso.hom he
  change (sectionPoleLineBaseChangeIso h s t hs ht hst hI hJ n).hom ≫
    (sectionPoleMultiplicativeFrame t hJ
      (sectionPointTransportedFrame h s t hs ht hst hI hJ a) n).hom =
    ((pullback g).mapIso (sectionPoleMultiplicativeFrame s hI a n) ≪≫
      modulePullbackUnitIso g).hom at hh
  simp only [Iso.trans_hom] at hh
  simp only [sectionPoleBaseChangeFrame, Iso.trans_hom, Iso.symm_hom]
  rw [← hh, Iso.inv_hom_id_assoc]

/-- Leading-frame transition units on one marked line are powers of its actual unit. -/
theorem sectionPoleMultiplicativeFrame_unit {Y B : Scheme} (v : B ⟶ Y)
    (hK : EffectiveCartier v.ker)
    (a b : (pullback v).obj (divisorLineBundle v.ker hK) ≅ structureModule B) (n : ℕ) :
    frameComparisonUnit (sectionPoleMultiplicativeFrame v hK a n)
      (sectionPoleMultiplicativeFrame v hK b n) ⊤ = frameComparisonUnit a b ⊤ ^ n := by
  rw [← tensorPowerFrameComparisonUnit a b n]
  apply Units.ext
  change (tensorPowerTrivialization a n).hom.app ⊤
    ((tensorPowerIso v (divisorLineBundle v.ker hK) n).hom.app ⊤
      ((tensorPowerIso v (divisorLineBundle v.ker hK) n).inv.app ⊤
        ((tensorPowerTrivialization b n).inv.app ⊤ (1 : Γ(B, ⊤))))) = _
  rw [sectionIso_hom_inv]
  rfl

/-- The independent changed frame contributes one common unit in all pole degrees. -/
theorem sectionPoleBaseChangeFrame_unit
    (b : (pullback t).obj (divisorLineBundle t.ker hJ) ≅ structureModule T) (n : ℕ) :
    frameComparisonUnit
        (sectionPoleBaseChangeFrame h s t hs ht hst hI hJ n
          (sectionPoleMultiplicativeFrame s hI a n))
        (sectionPoleMultiplicativeFrame t hJ b n) ⊤ =
      frameComparisonUnit (sectionPointTransportedFrame h s t hs ht hst hI hJ a) b ⊤ ^ n := by
  rw [sectionPoleBaseChangeFrame_multiplicative, sectionPoleMultiplicativeFrame_unit]

end FLT.Mazur.FCurve
