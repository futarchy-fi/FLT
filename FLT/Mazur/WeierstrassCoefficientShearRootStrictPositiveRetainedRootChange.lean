/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRootStrictPositiveCoordinateComponents
public import FLT.Mazur.WeierstrassCoefficientShearAdjacentComponentRootChange
import all FLT.Mazur.WeierstrassCoefficientShearRootFinalAdjacent
import all FLT.Mazur.WeierstrassCoefficientShearRootOrderedAdjacent

/-!
# Independent companion-root retained components at the final stage

Transport the independently glued retained pair to the actual final index.
Root exchange identifies both entire projective components, including their origins.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (j : Fin s)
local notation "K" => ResidueField R
local notation "hj" => show j.val + 1 ≤ n from by omega
local notation "hjNext" => show j.val + 2 ≤ n from by omega
local notation "m" => s - (j.val + 1)
local notation "hm" => show j.val + 2 + m ≤ n from by omega
local notation "e" => data ⟨j.val + 2, Nat.lt_succ_of_le hjNext⟩
local notation "hscale" => residue_scale_eq_zero D (start + j.val) (by omega)
local notation "hπ₀" => Iff.mpr (residue_eq_zero_iff π)
  (D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π)
local notation "h3" => Iff.mpr (residue_eq_zero_iff _)
  (And.left (divided_linear_mem D (start + (j.val + 1) + 1) (by omega)
    (Data.b3 e) (Data.b4 e) (Data.factor3 e) (Data.factor4 e)))
local notation "h4" => Iff.mpr (residue_eq_zero_iff _)
  (And.right (divided_linear_mem D (start + (j.val + 1) + 1) (by omega)
    (Data.b3 e) (Data.b4 e) (Data.factor3 e) (Data.factor4 e)))
local notation "hr" => show (0 : K) ^ 2 + algebraMap R K W.a₁ * 0 -
    algebraMap R K W.a₂ = 0 from by
  rw [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add, zero_sub, neg_eq_zero]
  exact (residue_eq_zero_iff _).mpr D.a₂_mem
local notation "a" => residueTangentUnit D
local notation "ha" => Eq.trans (residueTangentUnit_val D)
  (Eq.symm (rootShearZero_tangent (W.map (residue R))))
local notation "transport" => eqToHom
  (finiteGlobalTensorModel_index_congr hπ data K hm hs (by omega))
variable (t : ResidueField R) (b : (ResidueField R)ˣ)
  (hb : (b : ResidueField R) =
    (rootShearCurve (W.map (algebraMap R (ResidueField R))) t).a₁)
  (ht : t ^ 2 + algebraMap R (ResidueField R) W.a₁ * t -
    algebraMap R (ResidueField R) W.a₂ = 0)
local notation "Gt" => coefficientShearGluedIso hπ data K t (j.val + 2 + m) hm
local notation "Ft" => coefficientShearGluedIso hπ data K t (s + 1) hs
local notation "C" => coefficientShearRootChange hπ data K 0 t (s + 1) hs

/-- Independently glue each companion-root retained pair and keep its actual final index. -/
def coefficientShearRootCompanionFinalAdjacentComponent (i : Fin 2) :
    ProjectiveLine.scheme K ⟶ coefficientShearGlued hπ data K t (s + 1) hs :=
  Fin.cases
    (coefficientShearAdjacentFirstComponent
      hπ data K t j.val hj hjNext m hm hscale hπ₀ h3 h4 ht b hb)
    (fun _ => coefficientShearAdjacentSecondComponent
      hπ data K t j.val hj hjNext m hm hscale hπ₀ h3 h4 ht b hb) i ≫
    (Gt).hom ≫ transport ≫ (Ft).inv

variable (hrt : 0 + t = -algebraMap R (ResidueField R) W.a₁)
include hrt

/-- The complete original first retained component changes to the independent companion second. -/
@[reassoc] theorem coefficientShearRootCompanionFinalAdjacent_first_rootChange :
    coefficientShearRootFinalAdjacentComponent hπ data D s hs hk j 0 ≫ (C).hom =
      coefficientShearRootCompanionFinalAdjacentComponent
        hπ data D s hs hstart hk j t b hb ht 1 := by
  simp only [coefficientShearRootFinalAdjacentComponent,
    coefficientShearRootOrderedAdjacent, dite_eq_left (show 0 < start + j.val by omega),
    coefficientShearRootCompanionFinalAdjacentComponent, Fin.cases_zero,
    show (1 : Fin 2) = Fin.succ 0 from rfl, Fin.cases_succ,
    coefficientShearRootChange, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc]
  rw [← coefficientShearRootChange_reconstruction hπ data K 0 t (j.val + 2 + m) hm]
  simpa only [Category.assoc] using coefficientShearAdjacentFirstComponent_rootChange_assoc
    hπ data K 0 j.val hj hjNext m hm hscale hπ₀ h3 h4 hr a ha t b hb ht hrt
    ((Gt).hom ≫ transport ≫ (Ft).inv)

/-- The complete original second retained component changes to the independent companion first. -/
@[reassoc] theorem coefficientShearRootCompanionFinalAdjacent_second_rootChange :
    coefficientShearRootFinalAdjacentComponent hπ data D s hs hk j 1 ≫ (C).hom =
      coefficientShearRootCompanionFinalAdjacentComponent
        hπ data D s hs hstart hk j t b hb ht 0 := by
  simp only [coefficientShearRootFinalAdjacentComponent,
    coefficientShearRootOrderedAdjacent, dite_eq_left (show 0 < start + j.val by omega),
    coefficientShearRootCompanionFinalAdjacentComponent, Fin.cases_zero,
    show (1 : Fin 2) = Fin.succ 0 from rfl, Fin.cases_succ,
    coefficientShearRootChange, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc]
  rw [← coefficientShearRootChange_reconstruction hπ data K 0 t (j.val + 2 + m) hm]
  simpa only [Category.assoc] using coefficientShearAdjacentSecondComponent_rootChange_assoc
    hπ data K 0 j.val hj hjNext m hm hscale hπ₀ h3 h4 hr a ha t b hb ht hrt
    ((Gt).hom ≫ transport ≫ (Ft).inv)

end FLT.Mazur.WeierstrassDividedDepth
