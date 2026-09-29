/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CechSheafHZero
public import FLT.Mazur.ProjectiveTwistingSheaf

/-!
# Chart coefficients of the projective twisting Cech complex

We use the categorical Cech complex of the constructed twisting sheaf. Each
intersection is the basic open of the product of its coordinates. Evaluation
in the first chart identifies its sections with the degree-zero homogeneous
localization. In these bases the differential includes the twisting transition
when the first chart changes. The degree-n localization and monomial basis
interpretation is a separate algebraic comparison.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MvPolynomial HomogeneousLocalization
open FLT.Mazur.FCurve FLT.Mazur.FCurve.ModuleSheafUnitCocycle
open scoped Simplicial

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.ProjectiveSpace.TwistCech

variable (R : Type u) [CommRing R] (ι : Type u)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual categorical Cech complex of the twisting sheaf. -/
abbrev complex (n : ℤ) :=
  CechSheafHZero.C (chart R ι) (moduleAbelianSheaf (twistingSheaf R ι n))

/-- The intersection belonging to an ordered tuple, including repetitions. -/
abbrev intersection (q : ℕ) (a : Fin (q + 1) → ι) : (space R ι).Opens :=
  CechSheafHZero.V (chart R ι) q a

/-- The coordinate monomial defining an intersection. -/
def coordinateProduct {m : ℕ} (a : Fin m → ι) : MvPolynomial ι R := ∏ j, X (a j)

lemma coordinateProduct_homogeneous {m : ℕ} (a : Fin m → ι) :
    coordinateProduct R ι a ∈ grading R ι m := by
  simpa only [coordinateProduct, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one] using
    SetLike.prod_mem_graded (grading R ι) (fun _ : Fin m ↦ 1) (fun j ↦ X (a j))
      (F := Finset.univ)
      (fun j _ ↦ isHomogeneous_X R (a j))

lemma basicOpen_coordinateProduct {m : ℕ} (a : Fin m → ι) :
    Proj.basicOpen (grading R ι) (coordinateProduct R ι a) = ⨅ j, chart R ι (a j) := by
  induction m with
  | zero => simp [coordinateProduct, Proj.basicOpen_one]
  | succ m ih =>
    simp only [coordinateProduct, Fin.prod_univ_succ, Proj.basicOpen_mul]
    rw [show Proj.basicOpen (grading R ι) (∏ j : Fin m, X (a j.succ)) =
      ⨅ j : Fin m, chart R ι (a j.succ) from ih (fun j ↦ a j.succ)]
    apply le_antisymm
    · apply le_iInf
      intro j
      refine Fin.cases inf_le_left (fun k ↦ ?_) j
      exact inf_le_right.trans (iInf_le _ k)
    · exact le_inf (iInf_le _ 0) (le_iInf fun j ↦ iInf_le _ j.succ)

/-- All chart intersections are the expected product basic opens. -/
lemma intersection_eq (q : ℕ) (a : Fin (q + 1) → ι) :
    intersection R ι q a = Proj.basicOpen (grading R ι) (coordinateProduct R ι a) :=
  (basicOpen_coordinateProduct R ι a).symm

/-- The degree-zero homogeneous localization of an intersection. -/
abbrev intersectionRing {q : ℕ} (a : Fin (q + 1) → ι) :=
  Away (grading R ι) (coordinateProduct R ι a)

/-- The homogeneous localization is the ring of functions on the intersection. -/
def intersectionRingEquiv (q : ℕ) (a : Fin (q + 1) → ι) :
    intersectionRing R ι a ≃+* Γ(space R ι, intersection R ι q a) :=
  ((Proj.basicOpenIsoAway (grading R ι) (coordinateProduct R ι a)
    (coordinateProduct_homogeneous R ι a) (Nat.succ_pos q)) ≪≫
    (space R ι).presheaf.mapIso
      (eqToIso (congrArg op (intersection_eq R ι q a).symm))).commRingCatIsoToRingEquiv

/-- The tuple intersection lies in any of its charts. -/
lemma intersection_le (q : ℕ) (a : Fin (q + 1) → ι) (j : Fin (q + 1)) :
    intersection R ι q a ≤ chart R ι (a j) := iInf_le _ j

/-- Categorical terms in the actual twisting-sheaf section coordinates. -/
def sectionsEquiv (n : ℤ) (q : ℕ) :
    (complex R ι n).X q ≃+
      (∀ a : Fin (q + 1) → ι, (twistCocycle R ι n).sections (intersection R ι q a)) :=
  CechSheafHZero.termEquiv (chart R ι) (moduleAbelianSheaf (twistingSheaf R ι n)) q

/-- Evaluate each tuple's section in its first chart basis. -/
def coefficientEquiv (n : ℤ) (q : ℕ) :
    (complex R ι n).X q ≃+
      (∀ a : Fin (q + 1) → ι, Γ(space R ι, intersection R ι q a)) :=
  (sectionsEquiv R ι n q).trans (AddEquiv.piCongrRight fun a ↦
    (twistCocycle R ι n).evaluationEquiv (a 0) (intersection_le R ι q a 0))

/-- Every term is a product of explicit homogeneous coordinate rings in chart bases. -/
def termEquiv (n : ℤ) (q : ℕ) :
    (complex R ι n).X q ≃+ (∀ a : Fin (q + 1) → ι, intersectionRing R ι a) :=
  (coefficientEquiv R ι n q).trans (AddEquiv.piCongrRight fun a ↦
    (intersectionRingEquiv R ι q a).symm.toAddEquiv)

/-- Deleting a tuple entry enlarges its intersection. -/
lemma face_le (q : ℕ) (a : Fin (q + 2) → ι) (k : Fin (q + 2)) :
    intersection R ι (q + 1) a ≤ intersection R ι q (a ∘ k.succAbove) :=
  le_iInf fun j ↦ iInf_le _ (k.succAbove j)

/-- The coface in the actual categorical complex. -/
abbrev coface (n : ℤ) (q : ℕ) (k : Fin (q + 2)) :
    (complex R ι n).X q ⟶ (complex R ι n).X (q + 1) :=
  (CechSheafHZero.cosimplicial (chart R ι)
    (moduleAbelianSheaf (twistingSheaf R ι n))).δ k

/-- Every differential is the alternating sum of cofaces. -/
lemma differential (n : ℤ) (q : ℕ) :
    (complex R ι n).d q (q + 1) =
      ∑ k : Fin (q + 2), (-1 : ℤ) ^ (k : ℕ) • coface R ι n q k := by
  change (AlgebraicTopology.AlternatingCofaceMapComplex.obj
    (CechSheafHZero.cosimplicial (chart R ι)
      (moduleAbelianSheaf (twistingSheaf R ι n)))).d q (q + 1) = _
  simp only [AlgebraicTopology.AlternatingCofaceMapComplex.obj, CochainComplex.of_d]
  rfl

/-- In section coordinates each coface is restriction after deleting an entry. -/
lemma sectionsEquiv_coface (n : ℤ) (q : ℕ) (k : Fin (q + 2))
    (x : (complex R ι n).X q) (a : Fin (q + 2) → ι) :
    sectionsEquiv R ι n (q + 1) (coface R ι n q k x) a =
      (twistCocycle R ι n).restrict (face_le R ι q a k)
        (sectionsEquiv R ι n q x (a ∘ k.succAbove)) := by
  let U := chart R ι
  let F := moduleAbelianSheaf (twistingSheaf R ι n)
  have hp : coface R ι n q k ≫
      Pi.π (fun b : Fin (q + 2) → ι ↦ F.obj.obj (op (∏ᶜ (U ∘ b)))) a =
      Pi.π (fun b : Fin (q + 1) → ι ↦ F.obj.obj (op (∏ᶜ (U ∘ b))))
        (a ∘ k.succAbove) ≫
          F.obj.map (Pi.lift (fun j : Fin (q + 1) ↦ Pi.π (U ∘ a) (k.succAbove j))).op := by
    change Pi.lift _ ≫ Pi.π _ a = _
    rw [Pi.lift_comp_π]
    rfl
  change CechSheafHZero.termEquiv U F (q + 1) _ a =
    F.obj.map (homOfLE (face_le R ι q a k)).op
      (CechSheafHZero.termEquiv U F q x (a ∘ k.succAbove))
  rw [CechSheafHZero.termEquiv_apply, CechSheafHZero.termEquiv_apply]
  simp only [← ConcreteCategory.comp_apply]
  erw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply]
  apply ConcreteCategory.congr_hom
  rw [← Category.assoc, hp]
  simp only [Category.assoc, ← Functor.map_comp]
  congr 2

/-- The transition needed to express a face in the target tuple's first chart. -/
def faceUnit (n : ℤ) (q : ℕ) (a : Fin (q + 2) → ι) (k : Fin (q + 2)) :
    Γ(space R ι, intersection R ι (q + 1) a)ˣ :=
  (twistCocycle R ι n).unit (a 0) (a (k.succAbove 0)) _
    (intersection_le R ι (q + 1) a 0)
    (intersection_le R ι (q + 1) a (k.succAbove 0))

/-- The transition is the specified integer power of the homogeneous ratio. -/
lemma faceUnit_eq (n : ℤ) (q : ℕ) (a : Fin (q + 2) → ι) (k : Fin (q + 2)) :
    faceUnit R ι n q a k =
      restrictUnits R ι (le_inf (intersection_le R ι (q + 1) a 0)
        (intersection_le R ι (q + 1) a (k.succAbove 0)))
          (twistTransition R ι 1 (a 0) (a (k.succAbove 0))) ^ n :=
  twistCocycle_unit R ι n _ _ _ _ _

/-- A coface restricts its coefficient and then changes the chosen chart basis. -/
lemma coefficientEquiv_coface (n : ℤ) (q : ℕ) (k : Fin (q + 2))
    (x : (complex R ι n).X q) (a : Fin (q + 2) → ι) :
    coefficientEquiv R ι n (q + 1) (coface R ι n q k x) a =
      (faceUnit R ι n q a k : Γ(space R ι, intersection R ι (q + 1) a)) *
        res (face_le R ι q a k) (coefficientEquiv R ι n q x (a ∘ k.succAbove)) := by
  change (twistCocycle R ι n).evaluate (a 0) (intersection_le R ι (q + 1) a 0)
    (sectionsEquiv R ι n (q + 1) (coface R ι n q k x) a) = _
  rw [sectionsEquiv_coface]
  rw [(twistCocycle R ι n).transition (a 0) (a (k.succAbove 0))
    (intersection_le R ι (q + 1) a 0)
    ((face_le R ι q a k).trans (intersection_le R ι q (a ∘ k.succAbove) 0))]
  rw [(twistCocycle R ι n).evaluate_restrict (a (k.succAbove 0))
    (intersection_le R ι q (a ∘ k.succAbove) 0) (face_le R ι q a k)]
  rfl

/-- The full differential in chart coefficients, with all alternating signs. -/
lemma differential_coefficients (n : ℤ) (q : ℕ) (x : (complex R ι n).X q)
    (a : Fin (q + 2) → ι) :
    coefficientEquiv R ι n (q + 1) ((complex R ι n).d q (q + 1) x) a =
      ∑ k : Fin (q + 2), (-1 : ℤ) ^ (k : ℕ) •
        ((faceUnit R ι n q a k : Γ(space R ι, intersection R ι (q + 1) a)) *
          res (face_le R ι q a k)
            (coefficientEquiv R ι n q x (a ∘ k.succAbove))) := by
  rw [differential]
  change coefficientEquiv R ι n (q + 1)
    ((∑ k : Fin (q + 2), (-1 : ℤ) ^ (k : ℕ) • coface R ι n q k).hom x) a = _
  rw [show (∑ k : Fin (q + 2), (-1 : ℤ) ^ (k : ℕ) • coface R ι n q k).hom =
    ∑ k : Fin (q + 2), ((-1 : ℤ) ^ (k : ℕ) • coface R ι n q k).hom from
      map_sum AddCommGrpCat.homAddEquiv _ _]
  simp only [AddCommGrpCat.hom_zsmul, AddMonoidHom.finsetSum_apply,
    AddMonoidHom.zsmul_apply, map_sum, map_zsmul, Finset.sum_apply, Pi.smul_apply,
    coefficientEquiv_coface]

/-- Deleting one factor describes the coordinate product on a face. -/
lemma coordinateProduct_face (q : ℕ) (a : Fin (q + 2) → ι) (k : Fin (q + 2)) :
    coordinateProduct R ι a = coordinateProduct R ι (a ∘ k.succAbove) * X (a k) := by
  dsimp only [coordinateProduct, Function.comp_apply]
  rw [Fin.prod_univ_succAbove _ k, mul_comm]

/-- The canonical homogeneous localization map for a face. -/
def faceRingMap (q : ℕ) (a : Fin (q + 2) → ι) (k : Fin (q + 2)) :
    intersectionRing R ι (a ∘ k.succAbove) →+* intersectionRing R ι a :=
  awayMap (grading R ι) (isHomogeneous_X R (a k)) (coordinateProduct_face R ι q a k)

lemma intersectionRingEquiv_apply (q : ℕ) (a : Fin (q + 1) → ι)
    (r : intersectionRing R ι a) :
    intersectionRingEquiv R ι q a r = res (intersection_eq R ι q a).le
      ((Proj.awayToSection (grading R ι) (coordinateProduct R ι a)).hom r) := rfl

/-- The geometric restriction agrees with the explicit homogeneous localization map. -/
lemma faceRingMap_sections (q : ℕ) (a : Fin (q + 2) → ι) (k : Fin (q + 2))
    (r : intersectionRing R ι (a ∘ k.succAbove)) :
    intersectionRingEquiv R ι (q + 1) a (faceRingMap R ι q a k r) =
      res (face_le R ι q a k)
        (intersectionRingEquiv R ι q (a ∘ k.succAbove) r) := by
  have h := congrArg (fun f ↦ f.hom r)
    (Proj.awayMap_awayToSection (grading R ι) (isHomogeneous_X R (a k))
      (coordinateProduct_face R ι q a k))
  change (Proj.awayToSection (grading R ι) (coordinateProduct R ι a)).hom
    (faceRingMap R ι q a k r) = res _
      ((Proj.awayToSection (grading R ι)
        (coordinateProduct R ι (a ∘ k.succAbove))).hom r) at h
  rw [intersectionRingEquiv_apply, intersectionRingEquiv_apply, h]
  simp only [res_res]

/-- The transition coefficient as an element of the homogeneous intersection ring. -/
def faceRingCoefficient (n : ℤ) (q : ℕ) (a : Fin (q + 2) → ι) (k : Fin (q + 2)) :
    intersectionRing R ι a :=
  (intersectionRingEquiv R ι (q + 1) a).symm (faceUnit R ι n q a k)

/-- Each coface is localization followed by the explicit change of chart basis. -/
lemma termEquiv_coface (n : ℤ) (q : ℕ) (k : Fin (q + 2))
    (x : (complex R ι n).X q) (a : Fin (q + 2) → ι) :
    termEquiv R ι n (q + 1) (coface R ι n q k x) a =
      faceRingCoefficient R ι n q a k *
        faceRingMap R ι q a k (termEquiv R ι n q x (a ∘ k.succAbove)) := by
  apply (intersectionRingEquiv R ι (q + 1) a).injective
  change intersectionRingEquiv R ι (q + 1) a
    ((intersectionRingEquiv R ι (q + 1) a).symm
      (coefficientEquiv R ι n (q + 1) (coface R ι n q k x) a)) = _
  rw [RingEquiv.apply_symm_apply, map_mul, faceRingMap_sections]
  change _ = intersectionRingEquiv R ι (q + 1) a
    ((intersectionRingEquiv R ι (q + 1) a).symm (faceUnit R ι n q a k)) *
      res (face_le R ι q a k) (intersectionRingEquiv R ι q (a ∘ k.succAbove)
        ((intersectionRingEquiv R ι q (a ∘ k.succAbove)).symm
          (coefficientEquiv R ι n q x (a ∘ k.succAbove))))
  rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, coefficientEquiv_coface]

/-- In homogeneous chart coordinates the differential is an alternating localization sum. -/
lemma differential_localizations (n : ℤ) (q : ℕ) (x : (complex R ι n).X q)
    (a : Fin (q + 2) → ι) :
    termEquiv R ι n (q + 1) ((complex R ι n).d q (q + 1) x) a =
      ∑ k : Fin (q + 2), (-1 : ℤ) ^ (k : ℕ) •
        (faceRingCoefficient R ι n q a k *
          faceRingMap R ι q a k (termEquiv R ι n q x (a ∘ k.succAbove))) := by
  rw [differential]
  change termEquiv R ι n (q + 1)
    ((∑ k : Fin (q + 2), (-1 : ℤ) ^ (k : ℕ) • coface R ι n q k).hom x) a = _
  rw [show (∑ k : Fin (q + 2), (-1 : ℤ) ^ (k : ℕ) • coface R ι n q k).hom =
    ∑ k : Fin (q + 2), ((-1 : ℤ) ^ (k : ℕ) • coface R ι n q k).hom from
      map_sum AddCommGrpCat.homAddEquiv _ _]
  simp only [AddCommGrpCat.hom_zsmul, AddMonoidHom.finsetSum_apply,
    AddMonoidHom.zsmul_apply, map_sum, map_zsmul, Finset.sum_apply, Pi.smul_apply,
    termEquiv_coface]

end FLT.Mazur.ProjectiveSpace.TwistCech
