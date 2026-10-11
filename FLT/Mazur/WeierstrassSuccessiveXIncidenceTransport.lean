/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXModificationLocalization

/-!
# Transport of two original chart maps through a common incidence open

Localizing the product of the two incidence functions allows both the input
and output maps to land in the original successive chart. Any residue map
whose two incidence images are units factors through this same integral open.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S C : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [CommRing C] [Algebra R C]
  (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
local notation "A" => Coordinate W s π b3 b4 b6
local notation "B" => WeierstrassModificationX.Coordinate W (s * π) b3 b4 b6
local notation "t" => WeierstrassModificationX.t W (s * π) b3 b4 b6
variable (f g : WeierstrassModificationX.Coordinate W (s * π) b3 b4 b6 →ₐ[R] S)

/-- The common principal open for the original input and output incidences. -/
abbrev IncidencePairOpen := Localization.Away ((f t : S) * (g t : S))
local notation "L" => IncidencePairOpen W s π b3 b4 b6 f g
local notation "j" => IsScalarTower.toAlgHom R S L

/-- The first incidence becomes a unit on the common principal open. -/
theorem incidencePair_first_unit : IsUnit (algebraMap S L (f t)) := by
  apply isUnit_of_mul_isUnit_left (y := algebraMap S L (g t))
  rw [← map_mul]
  exact IsLocalization.Away.algebraMap_isUnit _

/-- The second incidence becomes a unit on the same principal open. -/
theorem incidencePair_second_unit : IsUnit (algebraMap S L (g t)) := by
  apply isUnit_of_mul_isUnit_right (x := algebraMap S L (f t))
  rw [← map_mul]
  exact IsLocalization.Away.algebraMap_isUnit _

/-- The original first map transported to the successive chart on the common open. -/
def incidencePairFirst : A →ₐ[R] L :=
  modificationIncidenceInverse W s π b3 b4 b6 ((j).comp f)
    (incidencePair_first_unit W s π b3 b4 b6 f g).unit
    (IsUnit.unit_spec _).symm

/-- The original second map transported to the successive chart on the common open. -/
def incidencePairSecond : A →ₐ[R] L :=
  modificationIncidenceInverse W s π b3 b4 b6 ((j).comp g)
    (incidencePair_second_unit W s π b3 b4 b6 f g).unit
    (IsUnit.unit_spec _).symm

/-- Transport retains every original input modification function. -/
theorem incidencePairFirst_original :
    (incidencePairFirst W s π b3 b4 b6 f g).comp
      (modificationMap W s π b3 b4 b6) = (j).comp f :=
  modificationIncidenceInverse_comp ..

/-- Transport retains every original output modification function. -/
theorem incidencePairSecond_original :
    (incidencePairSecond W s π b3 b4 b6 f g).comp
      (modificationMap W s π b3 b4 b6) = (j).comp g :=
  modificationIncidenceInverse_comp ..

variable (e : S →ₐ[R] C)
  (hf : IsUnit (e (f (WeierstrassModificationX.t W (s * π) b3 b4 b6))))
  (hg : IsUnit (e (g (WeierstrassModificationX.t W (s * π) b3 b4 b6))))

/-- The original residue map factors through the common integral incidence open. -/
def incidencePairResidue : L →ₐ[R] C :=
  IsLocalization.Away.liftAlgHom ((f t : S) * (g t : S)) (f := e) (by
    rw [map_mul]
    exact hf.mul hg)

/-- The factorization preserves all original functions, including independent parameters. -/
@[simp] theorem incidencePairResidue_base (q : S) :
    incidencePairResidue W s π b3 b4 b6 f g e hf hg (algebraMap S L q) = e q := by
  rw [incidencePairResidue, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl

/-- The transported first residue still agrees on every original modification function. -/
theorem incidencePairResidue_first_original (q : B) :
    incidencePairResidue W s π b3 b4 b6 f g e hf hg
      (incidencePairFirst W s π b3 b4 b6 f g (modificationMap W s π b3 b4 b6 q)) =
        e (f q) := by
  rw [show incidencePairFirst W s π b3 b4 b6 f g
      (modificationMap W s π b3 b4 b6 q) = algebraMap S L (f q) from
    AlgHom.congr_fun (incidencePairFirst_original W s π b3 b4 b6 f g) q]
  exact incidencePairResidue_base ..

/-- The transported second residue still agrees on every original modification function. -/
theorem incidencePairResidue_second_original (q : B) :
    incidencePairResidue W s π b3 b4 b6 f g e hf hg
      (incidencePairSecond W s π b3 b4 b6 f g (modificationMap W s π b3 b4 b6 q)) =
        e (g q) := by
  rw [show incidencePairSecond W s π b3 b4 b6 f g
      (modificationMap W s π b3 b4 b6 q) = algebraMap S L (g q) from
    AlgHom.congr_fun (incidencePairSecond_original W s π b3 b4 b6 f g) q]
  exact incidencePairResidue_base ..

end FLT.Mazur.WeierstrassSuccessiveX
