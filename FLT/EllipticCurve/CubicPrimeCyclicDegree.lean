/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicPrimeCyclicSubgroups
public import Mathlib.Algebra.GroupWithZero.Units.Fintype
/-! # Number of geometric prime-level cyclic subgroups

Every fiber over a generator image is a torsor on field-valued points
for the scalar unit group. The finite quotient has p+1 geometric points
over each algebraically closed coefficient field.
-/

open AlgebraicGeometry CategoryTheory
@[expose] public noncomputable section
namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsDomain R]
variable (W : WeierstrassCurve R) [W.IsElliptic]
variable (p : ℕ) [Fact p.Prime] [NeZero p] [Fact (IsUnit (p : R))]
variable (K : Type u) [Field K] [Algebra R K]

/-- Distinct scalar units give distinct prime-torsion generators. -/
theorem scalarOrbitPoint_injective
    (x : pointSource K ⟶ nonzeroTorsionModel W p) :
    Function.Injective (fun a : (ZMod p)ˣ =>
      x ≫ (nonzeroTorsionScalarAction W p a).hom) := by
  classical
  intro a b h
  let P := (primeTorsionClassicalEquiv W p Fact.out K x).val
  have he := congrArg (fun y =>
    (nonzeroTorsionClassicalEquiv W p Fact.out K y).val.val) h
  change (nonzeroTorsionClassicalEquiv W p Fact.out K
      (x ≫ (nonzeroTorsionScalarIso W p a).hom)).val.val =
    (nonzeroTorsionClassicalEquiv W p Fact.out K
      (x ≫ (nonzeroTorsionScalarIso W p b).hom)).val.val at he
  rw [nonzeroTorsionScalarIso_classical, nonzeroTorsionScalarIso_classical] at he
  have hm : a.val.val ≡ b.val.val [MOD p] := by
    have hm' : a.val.val ≡ b.val.val [MOD addOrderOf P] :=
      nsmul_eq_nsmul_iff_modEq.mp he
    have hP : addOrderOf P = p := (primeTorsionClassicalEquiv W p Fact.out K x).property
    simpa only [hP] using hm'
  apply Units.ext
  simpa using (ZMod.natCast_eq_natCast_iff _ _ p).mpr hm

/-- Scalar units parametrize the entire quotient fiber over a generator image. -/
def scalarQuotientGeneratorFiberEquiv
    (x : pointSource K ⟶ nonzeroTorsionModel W p) :
    (ZMod p)ˣ ≃ {y : pointSource K ⟶ nonzeroTorsionModel W p //
      y ≫ scalarQuotientMap W p = x ≫ scalarQuotientMap W p} :=
  Equiv.ofBijective
    (fun a => ⟨x ≫ (nonzeroTorsionScalarAction W p a).hom, by
      rw [Category.assoc, scalarQuotientMap_invariant]⟩)
    ⟨fun _ _ h => scalarOrbitPoint_injective W p K x (congrArg Subtype.val h), by
      rintro ⟨y, hy⟩
      obtain ⟨a, ha⟩ := (scalarQuotientFieldPoint_fiber_hom W p K y x).mp hy
      exact ⟨a, Subtype.ext ha.symm⟩⟩

/-- The actual prime-level scalar quotient has p+1 geometric points. -/
theorem scalarQuotientFieldPoints_card [IsAlgClosed K] :
    Nat.card (pointSource K ⟶ scalarQuotientModel W p) = p + 1 := by
  classical
  let f := fun x : pointSource K ⟶ nonzeroTorsionModel W p => x ≫ scalarQuotientMap W p
  have he : ∀ y, {x // f x = y} ≃ (ZMod p)ˣ := by
    intro y
    apply Classical.choice
    obtain ⟨x, rfl⟩ := scalarQuotientFieldPoint_surjective W p K y
    exact ⟨(scalarQuotientGeneratorFiberEquiv W p K x).symm⟩
  have hc := Nat.card_congr
    ((Equiv.sigmaFiberEquiv f).symm.trans (Equiv.sigmaEquivProdOfEquiv he))
  rw [Nat.card_prod, Nat.card_units, Nat.card_zmod,
    nonzeroTorsionFieldPoints_card W p Fact.out K] at hc
  have hp := (Fact.out : p.Prime).two_le
  have hs : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
  have hs2 : p ^ 2 - 1 + 1 = p ^ 2 := Nat.sub_add_cancel (by nlinarith)
  nlinarith

end WeierstrassCurve.CubicCharts
