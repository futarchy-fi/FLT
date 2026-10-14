/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRootStrictPositiveCoordinateComponents
public import FLT.Mazur.WeierstrassCoefficientShearRootInitialRootChange
import all FLT.Mazur.WeierstrassCoefficientShearRootFinalInitial

/-!
# Independent companion-root initial components at the final stage

Transport the independently glued initial pair to the actual final index.
Root exchange identifies both entire projective components, including their origins.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hsFinal : s + 1 ≤ n)
  (hstart : 0 < start) (hkFinal : 2 * (start + s + 1) ≤ depth)
local notation "h1" => show 1 ≤ n from by omega
local notation "hk" => show 2 * (start + 1) ≤ depth from by omega
local notation "m" => s
local notation "hm" => show 1 + s ≤ n from by omega
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "e" => data (Fin.mk 1 (Nat.lt_succ_of_le h1))
local notation "V" => W.map (residue R)
local notation "U" => rootShearCurve V 0
local notation "c" => residue R (Data.b6 d)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D start (by omega) (Data.b6 d) (Data.factor6 d))
local notation "hs" => WeierstrassDilatation.residue_scale_eq_zero D start hstart
local notation "hp" => Iff.mpr (residue_eq_zero_iff π)
  (D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π)
local notation "g3" => Iff.mpr (residue_eq_zero_iff _)
  (And.left (WeierstrassDilatation.divided_linear_mem
    D start (by omega) (Data.b3 d) (Data.b4 d) (Data.factor3 d) (Data.factor4 d)))
local notation "g4" => Iff.mpr (residue_eq_zero_iff _)
  (And.right (WeierstrassDilatation.divided_linear_mem
    D start (by omega) (Data.b3 d) (Data.b4 d) (Data.factor3 d) (Data.factor4 d)))
local notation "h3" => Iff.mpr (residue_eq_zero_iff _)
  (And.left (WeierstrassDilatation.divided_linear_mem
    D (start + 1) hk (Data.b3 e) (Data.b4 e) (Data.factor3 e) (Data.factor4 e)))
local notation "h4" => Iff.mpr (residue_eq_zero_iff _)
  (And.right (WeierstrassDilatation.divided_linear_mem
    D (start + 1) hk (Data.b3 e) (Data.b4 e) (Data.factor3 e) (Data.factor4 e)))
local notation "hr" => show (0 : K) ^ 2 + algebraMap R K W.a₁ * 0 -
    algebraMap R K W.a₂ = 0 from by
  rw [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add, zero_sub, neg_eq_zero]
  exact (residue_eq_zero_iff _).mpr D.a₂_mem
local notation "a" => WeierstrassDilatation.residueTangentUnit D
local notation "ha" => Eq.trans (WeierstrassDilatation.residueTangentUnit_val D)
  (Eq.symm (rootShearZero_tangent V))
local notation "transport" => eqToHom
  (finiteGlobalTensorModel_index_congr hπ data K hm hsFinal (by omega))
local notation "Efinal" => coefficientShearGluedIso hπ data K 0 (s + 1) hsFinal
local notation "p" => coefficientShearGluedStructure hπ data K 0 (s + 1) hsFinal

variable (t : ResidueField R) (b : (ResidueField R)ˣ)
  (hb : (b : ResidueField R) =
    (rootShearCurve (W.map (algebraMap R (ResidueField R))) t).a₁)
  (ht : t ^ 2 + algebraMap R (ResidueField R) W.a₁ * t -
    algebraMap R (ResidueField R) W.a₂ = 0)
local notation "Gt" => coefficientShearGluedIso hπ data K t (1 + s) hm
local notation "Ft" => coefficientShearGluedIso hπ data K t (s + 1) hsFinal
local notation "G" => coefficientShearGluedIso hπ data K 0 (1 + s) hm
local notation "C" => coefficientShearRootChange hπ data K 0 t (s + 1) hsFinal

/-- The independent companion-root initial pair at the actual final index. -/
def coefficientShearRootCompanionFinalInitialComponent (i : Fin 2) :
    ProjectiveLine.scheme K ⟶ coefficientShearGlued hπ data K t (s + 1) hsFinal :=
  Fin.cases
    (coefficientShearRootInitialFirstComponent
      hπ data K t h1 s hm hs hp h3 h4 ht g3 g4 hc b hb)
    (fun _ => coefficientShearRootInitialSecondComponent
      hπ data K t h1 s hm hs hp h3 h4 ht g3 g4 hc b hb) i ≫
    (Gt).hom ≫ transport ≫ (Ft).inv

variable (hrt : 0 + t = -algebraMap R (ResidueField R) W.a₁)
include hrt

/-- Root change sends the complete original first initial component to its companion second. -/
@[reassoc] theorem coefficientShearRootCompanionFinalInitial_first_rootChange :
    coefficientShearRootFinalInitialComponent hπ data D s hsFinal hstart hkFinal 0 ≫
        (C).hom =
      coefficientShearRootCompanionFinalInitialComponent
        hπ data D s hsFinal hstart hkFinal t b hb ht 1 := by
  simp only [coefficientShearRootFinalInitialComponent,
    coefficientShearRootCompanionFinalInitialComponent, Fin.cases_zero,
    show (1 : Fin 2) = Fin.succ 0 from rfl, Fin.cases_succ,
    coefficientShearRootChange, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc]
  rw [← coefficientShearRootChange_reconstruction hπ data K 0 t (1 + s) hm]
  simpa only [Category.assoc] using coefficientShearRootInitialFirstComponent_rootChange_assoc
      hπ data K 0 h1 s hm hs hp h3 h4 hr g3 g4 hc a ha t b hb ht hrt
      ((Gt).hom ≫ transport ≫ (Ft).inv)

/-- Root change sends the complete original second initial component to its companion first. -/
@[reassoc] theorem coefficientShearRootCompanionFinalInitial_second_rootChange :
    coefficientShearRootFinalInitialComponent hπ data D s hsFinal hstart hkFinal 1 ≫
        (C).hom =
      coefficientShearRootCompanionFinalInitialComponent
        hπ data D s hsFinal hstart hkFinal t b hb ht 0 := by
  simp only [coefficientShearRootFinalInitialComponent,
    coefficientShearRootCompanionFinalInitialComponent, Fin.cases_zero,
    show (1 : Fin 2) = Fin.succ 0 from rfl, Fin.cases_succ,
    coefficientShearRootChange, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc]
  rw [← coefficientShearRootChange_reconstruction hπ data K 0 t (1 + s) hm]
  simpa only [Category.assoc] using coefficientShearRootInitialSecondComponent_rootChange_assoc
      hπ data K 0 h1 s hm hs hp h3 h4 hr g3 g4 hc a ha t b hb ht hrt
      ((Gt).hom ≫ transport ≫ (Ft).inv)

end FLT.Mazur.WeierstrassDividedDepth
