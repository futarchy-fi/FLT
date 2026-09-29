/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocalizationDegreeShift

/-!
# Homogeneous localization restrictions

Deleting a tuple entry gives the canonical localization map, preserving every
integer degree. Chart shifts intertwine this map with the twist transition.
The existing section and term comparisons respect the constant base-ring action
induced on the actual Cech complex by multiplication on the twisting sheaf.
-/

@[expose] public noncomputable section

open MvPolynomial HomogeneousLocalization AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.Limits FLT.Mazur.FCurve FLT.Mazur.FCurve.ModuleSheafUnitCocycle

namespace FLT.Mazur.ProjectiveSpace.LocalizationDegree

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (ι : Type u)

attribute [local instance] MvPolynomial.gradedAlgebra

variable (q : ℕ) (a : Fin (q + 2) → ι) (k : Fin (q + 2))

/-- The canonical restriction between the full polynomial localizations. -/
def fullFace : Full R ι (a ∘ k.succAbove) →+* Full R ι a :=
  Localization.awayLift (algebraMap (MvPolynomial ι R) _) _
    (IsLocalization.Away.isUnit_of_dvd (TwistCech.coordinateProduct R ι a)
      ⟨X (a k), TwistCech.coordinateProduct_face R ι q a k⟩)

@[simp] lemma fullFace_algebraMap (f : MvPolynomial ι R) :
    fullFace R ι q a k (algebraMap (MvPolynomial ι R) _ f) =
      algebraMap (MvPolynomial ι R) _ f :=
  IsLocalization.Away.lift_eq _
    (IsLocalization.Away.isUnit_of_dvd (TwistCech.coordinateProduct R ι a)
      ⟨X (a k), TwistCech.coordinateProduct_face R ι q a k⟩) f

lemma fullFace_fraction (f : MvPolynomial ι R) (l : ℕ) :
    fullFace R ι q a k (fraction R ι (a ∘ k.succAbove) f l) =
      fraction R ι a (f * X (a k) ^ l) l := by
  have h : algebraMap (MvPolynomial ι R) (Full R ι a)
      (TwistCech.coordinateProduct R ι (a ∘ k.succAbove)) *
        fraction R ι a (X (a k)) 1 = 1 := by
    rw [← Localization.mk_one_eq_algebraMap, fraction, Localization.mk_mul]
    simpa only [pow_one, OneMemClass.coe_one, one_mul,
      ← TwistCech.coordinateProduct_face] using
      Localization.mk_self ⟨TwistCech.coordinateProduct R ι a, Submonoid.mem_powers _⟩
  rw [fullFace, fraction, Localization.awayLift_mk (hv := h)]
  rw [← Algebra.smul_def, fraction, Localization.mk_pow, Localization.smul_mk]
  simp only [Algebra.smul_def, pow_one]
  rfl

lemma fullFace_mem {n : ℤ} {x : Full R ι (a ∘ k.succAbove)}
    (hx : x ∈ piece R ι (a ∘ k.succAbove) n) :
    fullFace R ι q a k x ∈ piece R ι a n := by
  obtain ⟨l, d, f, hf, hd, rfl⟩ := hx
  refine ⟨l, d + l, f * X (a k) ^ l, ?_, ?_, (fullFace_fraction R ι q a k f l).symm⟩
  · simpa using SetLike.mul_mem_graded hf
      (SetLike.pow_mem_graded l (isHomogeneous_X R (a k)))
  · push_cast at hd ⊢
    nlinarith

lemma fullFace_smul (r : R) (x : Full R ι (a ∘ k.succAbove)) :
    fullFace R ι q a k (r • x) = r • fullFace R ι q a k x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  congr 1
  rw [IsScalarTower.algebraMap_apply R (MvPolynomial ι R)
    (Full R ι (a ∘ k.succAbove)), fullFace_algebraMap,
    ← IsScalarTower.algebraMap_apply R (MvPolynomial ι R) (Full R ι a)]

/-- Restriction on each concrete homogeneous degree piece. -/
def faceLinear (n : ℤ) : piece R ι (a ∘ k.succAbove) n →ₗ[R] piece R ι a n where
  toFun x := ⟨fullFace R ι q a k x, fullFace_mem R ι q a k x.property⟩
  map_add' x y := Subtype.ext (map_add _ x.val y.val)
  map_smul' r x := Subtype.ext (fullFace_smul R ι q a k r x.val)

/-- The degree-zero restriction is the existing homogeneous face map. -/
lemma fullFace_zero (x : TwistCech.intersectionRing R ι (a ∘ k.succAbove)) :
    fullFace R ι q a k x.val = (TwistCech.faceRingMap R ι q a k x).val :=
  (val_awayMap (grading R ι) (isHomogeneous_X R (a k))
    (TwistCech.coordinateProduct_face R ι q a k) x).symm

lemma faceLinear_zero (x : TwistCech.intersectionRing R ι (a ∘ k.succAbove)) :
    faceLinear R ι q a k 0 (zeroEquiv R ι (a ∘ k.succAbove) x) =
      zeroEquiv R ι a (TwistCech.faceRingMap R ι q a k x) :=
  Subtype.ext (fullFace_zero R ι q a k x)

lemma fullFace_variableUnit (j : Fin (q + 1)) :
    Units.map (fullFace R ι q a k).toMonoidHom
      (variableUnit R ι (a ∘ k.succAbove) j) = variableUnit R ι a (k.succAbove j) := by
  apply Units.ext
  change fullFace R ι q a k (variableUnit R ι (a ∘ k.succAbove) j).val = _
  simp only [variableUnit_val, fullFace_algebraMap, Function.comp_apply]

/-- Restriction commutes with shifts in the same chart. -/
lemma faceLinear_shift (j : Fin (q + 1)) (n : ℤ)
    (x : piece R ι (a ∘ k.succAbove) 0) :
    faceLinear R ι q a k n (shift R ι (a ∘ k.succAbove) j n x) =
      shift R ι a (k.succAbove j) n (faceLinear R ι q a k 0 x) := by
  apply Subtype.ext
  change fullFace R ι q a k (↑(variableUnit R ι (a ∘ k.succAbove) j ^ n) * x.val) = _
  rw [map_mul]
  have h := congrArg Units.val (show Units.map (fullFace R ι q a k).toMonoidHom
      (variableUnit R ι (a ∘ k.succAbove) j ^ n) =
        variableUnit R ι a (k.succAbove j) ^ n by rw [map_zpow, fullFace_variableUnit])
  exact congrArg (fun z ↦ z * fullFace R ι q a k x.val) h

/-- The geometric face transition is precisely the homogeneous unit ratio. -/
lemma faceCoefficient_eq (n : ℤ) :
    TwistCech.faceRingCoefficient R ι n q a k =
      (coefficientUnit R ι a 0 (k.succAbove 0) ^ n).val := by
  apply (TwistCech.intersectionRingEquiv R ι (q + 1) a).injective
  change TwistCech.intersectionRingEquiv R ι (q + 1) a
    ((TwistCech.intersectionRingEquiv R ι (q + 1) a).symm _) = _
  rw [RingEquiv.apply_symm_apply, TwistCech.faceUnit_eq]
  have h := coefficientUnit_sections R ι a 0 (k.succAbove 0) 1
  simp only [zpow_one] at h
  exact (congrArg Units.val ((map_zpow _ _ n).trans (congrArg (fun z ↦ z ^ n) h))).symm

/-- In first-chart bases the shift square has exactly the prescribed face coefficient. -/
lemma face_shift_coefficient (n : ℤ) (x : piece R ι (a ∘ k.succAbove) 0) :
    ((shift R ι a 0 n).symm
      (faceLinear R ι q a k n (shift R ι (a ∘ k.succAbove) 0 n x)) : Full R ι a) =
      (TwistCech.faceRingCoefficient R ι n q a k).val * fullFace R ι q a k x := by
  rw [faceLinear_shift, shift_change_coefficient, faceCoefficient_eq]
  rfl


variable {q a k}

/-- A base scalar is a degree-zero constant polynomial. -/
def constantPolynomial : R →+* grading R ι 0 :=
  { toFun := fun r ↦ ⟨C r, isHomogeneous_C ι r⟩
    map_one' := Subtype.ext (map_one C)
    map_mul' := fun r s ↦ Subtype.ext (map_mul C r s)
    map_zero' := Subtype.ext (map_zero C)
    map_add' := fun r s ↦ Subtype.ext (map_add C r s) }

/-- The canonical constant regular section, represented everywhere by `r/1`. -/
def constantSection (U : (space R ι).Opens) : R →+* Γ(space R ι, U) :=
  (res (show U ≤ Proj.basicOpen (grading R ι) 1 by rw [Proj.basicOpen_one]; exact le_top)).comp
    ((Proj.awayToSection (grading R ι) 1).hom.comp
      ((fromZeroRingHom (grading R ι) _).comp (constantPolynomial R ι)))

lemma constantSection_res {U V : (space R ι).Opens} (h : V ≤ U) (r : R) :
    res h (constantSection R ι U r) = constantSection R ι V r := by
  simp only [constantSection, RingHom.comp_apply, res_res]

lemma constantSection_intersection {m : ℕ} (b : Fin (m + 1) → ι) (r : R) :
    constantSection R ι (TwistCech.intersection R ι m b) r =
      TwistCech.intersectionRingEquiv R ι m b (r • 1) := by
  have h := congrArg (fun f ↦ f.hom
      (fromZeroRingHom (grading R ι) _ (constantPolynomial R ι r)))
    (Proj.awayMap_awayToSection (grading R ι)
      (TwistCech.coordinateProduct_homogeneous R ι b)
      (show TwistCech.coordinateProduct R ι b =
        1 * TwistCech.coordinateProduct R ι b by rw [one_mul]))
  change (Proj.awayToSection (grading R ι)
    (TwistCech.coordinateProduct R ι b)).hom
      (awayMap (grading R ι) (TwistCech.coordinateProduct_homogeneous R ι b)
        (show TwistCech.coordinateProduct R ι b =
          1 * TwistCech.coordinateProduct R ι b by rw [one_mul])
        (fromZeroRingHom (grading R ι) _ (constantPolynomial R ι r))) =
      res _ ((Proj.awayToSection (grading R ι) 1).hom
        (fromZeroRingHom (grading R ι) _ (constantPolynomial R ι r))) at h
  rw [awayMap_fromZeroRingHom] at h
  have hc : fromZeroRingHom (grading R ι)
      (Submonoid.powers (TwistCech.coordinateProduct R ι b))
        (constantPolynomial R ι r) = r • (1 : TwistCech.intersectionRing R ι b) := by
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.val_smul, HomogeneousLocalization.val_one]
    change Localization.mk (C r) 1 = _
    rw [Localization.mk_one_eq_algebraMap, Algebra.smul_def, mul_one,
      IsScalarTower.algebraMap_apply R (MvPolynomial ι R) (Full R ι b)]
    rfl
  rw [hc] at h
  rw [TwistCech.intersectionRingEquiv_apply, h]
  simp only [constantSection, RingHom.comp_apply, res_res]

/-- Scalar multiplication on the actual categorical Cech term comes from the sheaf. -/
def termScalar (n : ℤ) (m : ℕ) (r : R) :
    (TwistCech.complex R ι n).X m ⟶ (TwistCech.complex R ι n).X m :=
  ((cechComplexFunctor (chart R ι)).map
    (moduleMultiply (twistingSheaf R ι n) (constantSection R ι ⊤ r)).hom).f m

/-- The section comparison commutes with multiplication by constant regular functions. -/
lemma sectionsEquiv_scalar (n : ℤ) (m : ℕ) (r : R)
    (x : (TwistCech.complex R ι n).X m) (b : Fin (m + 1) → ι) :
    TwistCech.sectionsEquiv R ι n m (termScalar R ι n m r x) b =
      constantSection R ι (TwistCech.intersection R ι m b) r •
        TwistCech.sectionsEquiv R ι n m x b := by
  let F := moduleAbelianSheaf (twistingSheaf R ι n)
  let f := moduleMultiply (twistingSheaf R ι n) (constantSection R ι ⊤ r)
  have hp : termScalar R ι n m r ≫
      Pi.π (fun c : Fin (m + 1) → ι ↦ F.obj.obj (op (∏ᶜ (chart R ι ∘ c)))) b =
      Pi.π (fun c : Fin (m + 1) → ι ↦ F.obj.obj (op (∏ᶜ (chart R ι ∘ c)))) b ≫
        f.hom.app (op (∏ᶜ (chart R ι ∘ b))) := by
    change Limits.Pi.map (fun c : Fin (m + 1) → ι ↦
      f.hom.app (op (∏ᶜ (chart R ι ∘ c)))) ≫ Pi.π _ b = _
    rw [Pi.map_π]
  change CechSheafHZero.termEquiv (chart R ι) F m _ b = _
  rw [CechSheafHZero.termEquiv_apply]
  simp only [← ConcreteCategory.comp_apply]
  erw [← ConcreteCategory.comp_apply]
  rw [← Category.assoc, hp, Category.assoc]
  erw [← f.hom.naturality]
  change (res (show TwistCech.intersection R ι m b ≤ ⊤ from le_top)
    (constantSection R ι ⊤ r)) •
    (TwistCech.sectionsEquiv R ι n m x b) = _
  rw [constantSection_res]

/-- First-chart evaluation intertwines the same constant action. -/
lemma coefficientEquiv_scalar (n : ℤ) (m : ℕ) (r : R)
    (x : (TwistCech.complex R ι n).X m) (b : Fin (m + 1) → ι) :
    TwistCech.coefficientEquiv R ι n m (termScalar R ι n m r x) b =
      constantSection R ι (TwistCech.intersection R ι m b) r *
        TwistCech.coefficientEquiv R ι n m x b := by
  change (twistCocycle R ι n).evaluate (b 0) (TwistCech.intersection_le R ι m b 0)
    (TwistCech.sectionsEquiv R ι n m (termScalar R ι n m r x) b) = _
  rw [sectionsEquiv_scalar, Cocycle.evaluate_smul]
  rfl

/-- Homogeneous chart coefficients carry the ordinary base-ring scalar action. -/
lemma termEquiv_scalar (n : ℤ) (m : ℕ) (r : R)
    (x : (TwistCech.complex R ι n).X m) (b : Fin (m + 1) → ι) :
    TwistCech.termEquiv R ι n m (termScalar R ι n m r x) b =
      r • TwistCech.termEquiv R ι n m x b := by
  apply (TwistCech.intersectionRingEquiv R ι m b).injective
  change TwistCech.intersectionRingEquiv R ι m b
    ((TwistCech.intersectionRingEquiv R ι m b).symm
      (TwistCech.coefficientEquiv R ι n m (termScalar R ι n m r x) b)) = _
  rw [RingEquiv.apply_symm_apply, coefficientEquiv_scalar, constantSection_intersection]
  have h (z : TwistCech.intersectionRing R ι b) : (r • 1) * z = r • z := by
    apply HomogeneousLocalization.val_injective
    simp only [val_mul, val_smul, val_one, smul_mul_assoc, one_mul]
  rw [← h (TwistCech.termEquiv R ι n m x b), map_mul]
  congr 1
  exact (TwistCech.intersectionRingEquiv R ι m b).apply_symm_apply _ |>.symm

end FLT.Mazur.ProjectiveSpace.LocalizationDegree
