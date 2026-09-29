/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CechSheafHZero
public import FLT.Mazur.LocalizationCech

/-!
# Localization and sheaf Cech complexes

The section terms on principal opens agree with the categorical products in the
sheaf Cech complex. Their identifications commute with restriction and hence with
the alternating differential. Degree `n` here is degree `n + 1` in the augmented
localization complex.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open scoped Simplicial

universe u

namespace FLT.Mazur.LocalizationCechIso

open CechSheafHZero

variable {R : CommRingCat.{u}} {ι : Type u} (f : ι → R) (M : ModuleCat.{u} R)

local notation "W" => (fun i ↦ PrimeSpectrum.basicOpen (f i))
local notation "F" => FCurve.moduleAbelianSheaf (tilde M)
local notation "S" => cosimplicial (X := TopCat.of (Spec R)) W F
local notation "K" => C (X := TopCat.of (Spec R)) W F

/-- The principal open of a product is the categorical intersection open. -/
lemma intersection_eq (n : ℕ) (a : Fin (n + 1) → ι) :
    PrimeSpectrum.basicOpen (∏ j, f (a j)) = ∏ᶜ (W ∘ a) :=
  (TildePrincipalOpen.cechTerm_open f n a).trans
    (productOpen_eq (X := TopCat.of (Spec R)) W n a).symm

/-- The term equivalence uses the same principal-open sections as A5. -/
def termIso (n : ℕ) :
    (forget₂ (ModuleCat R) AddCommGrpCat).obj (LocalizationCech.term f M n) ≅
      (K).X n :=
  (AddEquiv.piCongrRight fun a : Fin (n + 1) → ι ↦
    ((F).obj.mapIso
      (eqToIso (congrArg op (intersection_eq f n a)))).addCommGroupIsoToAddEquiv).toAddCommGrpIso ≪≫
    (productIso (fun a : Fin (n + 1) → ι ↦ (F).obj.obj (op (∏ᶜ (W ∘ a))))).symm

/-- In localization coordinates this is A5's product of principal-open comparisons. -/
def localizationTermEquiv (n : ℕ) :
    (K).X n ≃+
      (∀ a : Fin (n + 1) → ι, LocalizedModule (.powers (∏ j, f (a j))) M) :=
  (termIso f M n).symm.addCommGroupIsoToAddEquiv.trans
    (LocalizationCech.termEquiv f M n).toAddEquiv

/-- The localization coordinates of a compared section use the principal-open equivalence. -/
lemma localizationTermEquiv_termIso (n : ℕ) (x : LocalizationCech.term f M n)
    (a : Fin (n + 1) → ι) :
    localizationTermEquiv f M n ((termIso f M n).hom x) a =
      TildePrincipalOpen.sectionsEquiv M (∏ j, f (a j)) (x a) := by
  change LocalizationCech.termEquiv f M n
    ((termIso f M n).inv ((termIso f M n).hom x)) a = _
  rw [← ConcreteCategory.comp_apply, Iso.hom_inv_id]
  rfl

/-- A coordinate of the comparison is restriction along the equality of opens. -/
@[reassoc]
lemma termIso_hom_π (n : ℕ) (a : Fin (n + 1) → ι) :
    (termIso f M n).hom ≫ Pi.π (fun b ↦ (F).obj.obj (op (∏ᶜ (W ∘ b)))) a =
      AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ a) ≫
        (F).obj.map (eqToHom (congrArg op (intersection_eq f n a))) := by
  apply AddCommGrpCat.ext
  intro x
  change (productIso (fun b : Fin (n + 1) → ι ↦ (F).obj.obj (op (∏ᶜ (W ∘ b))))).hom
    ((productIso _).inv _) a = _
  rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id]
  rfl

/-- The categorical cofaces are the actual restrictions to smaller intersections. -/
lemma coface_π (n : ℕ) (k : Fin (n + 2)) (a : Fin (n + 2) → ι) :
    (S).δ k ≫
      Pi.π (fun b : Fin (n + 2) → ι ↦ (F).obj.obj (op (∏ᶜ (W ∘ b)))) a =
    Pi.π (fun b : Fin (n + 1) → ι ↦ (F).obj.obj (op (∏ᶜ (W ∘ b)))) (a ∘ k.succAbove) ≫
      (F).obj.map (Pi.lift (fun j : Fin (n + 1) ↦ Pi.π (W ∘ a) (k.succAbove j))).op := by
  change Pi.lift _ ≫ Pi.π _ a = _
  rw [Pi.lift_comp_π]
  rfl

set_option maxHeartbeats 800000 in
-- Normalizing the two bundled presentations of principal-open sections is expensive.
/-- The term comparisons commute with every coface. -/
lemma termIso_coface (n : ℕ) (k : Fin (n + 2)) :
    (forget₂ (ModuleCat R) AddCommGrpCat).map (LocalizationCech.reindex f M k.succAbove) ≫
        (termIso f M (n + 1)).hom =
      (termIso f M n).hom ≫ (S).δ k := by
  apply Pi.hom_ext (f := fun a : Fin (n + 2) → ι ↦ (F).obj.obj (op (∏ᶜ (W ∘ a))))
  intro a
  simp only [Category.assoc, coface_π, termIso_hom_π_assoc, termIso_hom_π]
  apply AddCommGrpCat.ext
  intro x
  change (F).obj.map _ ((F).obj.map _ (x (a ∘ k.succAbove))) =
    (F).obj.map _ ((F).obj.map _ (x (a ∘ k.succAbove)))
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

set_option maxHeartbeats 800000 in
-- Unfolding the categorical section complex requires the same bundled identifications.
/-- The sheaf Cech differential is the alternating coface sum. -/
lemma differential (n : ℕ) :
    (K).d n (n + 1) =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) • (S).δ k := by
  change CochainComplex.of.d
    (fun q ↦ (S).obj ⦋q⦌)
    (AlgebraicTopology.AlternatingCofaceMapComplex.objD (S)) n (n + 1) = _
  rw [CochainComplex.of_d]
  rfl

/-- The term comparisons commute with the alternating differentials. -/
lemma termIso_differential (n : ℕ) :
    (forget₂ (ModuleCat R) AddCommGrpCat).map ((LocalizationCech.complex f M).d n (n + 1)) ≫
        (termIso f M (n + 1)).hom =
      (termIso f M n).hom ≫ (K).d n (n + 1) := by
  rw [LocalizationCech.differential, differential]
  simp only [Functor.map_sum, Functor.map_zsmul, Preadditive.sum_comp,
    Preadditive.comp_sum, Preadditive.zsmul_comp, Preadditive.comp_zsmul]
  apply Finset.sum_congr rfl
  intro k _
  rw [termIso_coface]

end FLT.Mazur.LocalizationCechIso

namespace FLT.Mazur

/-- The localization Cech complex computes the same complex as the tilde sheaf. -/
def localizationCechIso {R : CommRingCat.{u}} {ι : Type u}
    (f : ι → R) (M : ModuleCat.{u} R) :
    ((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (LocalizationCech.complex f M) ≅
    (cechComplexFunctor (fun i ↦ PrimeSpectrum.basicOpen (f i))).obj
      (FCurve.moduleAbelianSheaf (tilde M)).obj :=
  HomologicalComplex.Hom.isoOfComponents (LocalizationCechIso.termIso f M)
    (by
      intro p q h
      obtain rfl : p + 1 = q := h
      exact (LocalizationCechIso.termIso_differential f M p).symm)

end FLT.Mazur
