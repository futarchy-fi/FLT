/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticInitialIntersection
public import FLT.Mazur.WeierstrassModificationXUnitIncidence
public import FLT.Mazur.SchemePairSymmetryPoints
public import FLT.Mazur.SchemeOpenChartRange

/-!
# The entire unit-scale initial arithmetic pair transfers to a punctured retained input

The original initial chart needs no smoothness or residue premise: its incidence
coordinate is already a unit. Both actual arithmetic inputs remain unchanged.
Creation depth zero is included because its scale is one.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassDividedDepth
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open PolygonArithmeticStages
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (m : ℕ)
  (h1 : 1 ≤ n) (r : ℕ) (hr : 1 + r ≤ n)
local notation "Q" => Quotient R π m
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "e" => data (Fin.mk 1 (Nat.lt_succ_of_le h1))
local notation "a" => WeierstrassModificationX.overlapEquiv W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "b" => previousBoundaryEquiv hπ d e
local notation "x" => WeierstrassDilatation.x W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "t" => WeierstrassModificationX.t W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "u" => WeierstrassSuccessiveX.coord W (π ^ start) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) 2
local notation "A" => PrincipalOpenTensor.transitionIso Q x t a
local notation "B" => PrincipalOpenTensor.transitionIso Q x u b

local notation "left" => (A).inv ≫ PrincipalOpenTensor.inclusion Q t
local notation "right" => (B).inv ≫ PrincipalOpenTensor.inclusion Q u
local notation "old" => finiteArithmeticInitialTensorChart hπ data m (1 + r) hr
local notation "next" => finiteArithmeticOlderTensorChart hπ data m 0 h1 r hr
local notation "s" => finiteGlobalArithmeticStructure hπ data (1 + r) hr m
local notation "f" => old ≫ s
local notation "f'" => next ≫ s
local notation "H" => initialArithmeticTensor_isPullback hπ data m h1 r hr
variable {Y : Scheme}
  (otherMap : Y ⟶ Spec (.of (PolygonArithmeticStages.Quotient R π m)))

/-- The original incidence domain in the full initial arithmetic pair. -/
def initialArithmeticPairOpen : (pullback f otherMap).Opens :=
  SchemePairBoundaryTransfer.domain f otherMap left

local notation "O" => initialArithmeticPairOpen hπ data m r hr otherMap

/-- At unit scale every original initial input lies in the actual incidence domain. -/
theorem initialArithmeticPairOpen_mem_of_unit (hs : IsUnit (π ^ start))
    (p : (pullback f otherMap : Scheme)) : p ∈ O := by
  change pullback.fst f otherMap p ∈ Set.range left
  have he := SchemeOpenChartRange.range_iso_comp (A).symm
    (PrincipalOpenTensor.inclusion Q t)
  apply (congrArg (fun U => pullback.fst f otherMap p ∈ U) he).to_iff.mpr
  exact WeierstrassModificationX.tensor_incidence_mem_of_scale_isUnit
    W (π ^ start) (Data.b3 d) (Data.b4 d) (Data.b6 d) Q hs _

/-- The complete original initial pair is covered, including all of its nilpotents. -/
theorem initialArithmeticPairOpen_eq_top (hs : IsUnit (π ^ start)) : O = ⊤ := by
  apply top_unique
  intro p _
  exact initialArithmeticPairOpen_mem_of_unit hπ data m r hr otherMap hs p

/-- At creation depth zero the unit-scale premise is discharged by the actual scale one. -/
theorem initialArithmeticPairOpen_zero_eq_top (hstart : start = 0) : O = ⊤ := by
  apply initialArithmeticPairOpen_eq_top hπ data m r hr otherMap
  rw [hstart, pow_zero]
  exact isUnit_one

/-- Change the initial input to its actual first retained chart on the full incidence domain. -/
def initialArithmeticPairTransfer : (O).toScheme ⟶ pullback f' otherMap :=
  SchemePairBoundaryTransfer.transfer f f' otherMap left right (by
    simpa only [Category.assoc] using congrArg (fun z => z ≫ s) (H).w)

local notation "T" => initialArithmeticPairTransfer hπ data m h1 r hr otherMap

/-- The entire original resolved first input survives the initial transfer. -/
@[reassoc] theorem initialArithmeticPairTransfer_first :
    T ≫ pullback.fst f' otherMap ≫ next = (O).ι ≫ pullback.fst f otherMap ≫ old :=
  SchemePairBoundaryTransfer.transfer_first_ambient f f' otherMap left right _ old next (H).w

/-- The arbitrary second input remains its original morphism. -/
@[reassoc] theorem initialArithmeticPairTransfer_second :
    T ≫ pullback.snd f' otherMap = (O).ι ≫ pullback.snd f otherMap :=
  SchemePairBoundaryTransfer.transfer_snd f f' otherMap left right _

/-- Every transferred input lies in the full first retained horizontal puncture. -/
theorem initialArithmeticPairTransfer_punctured (p : (O).toScheme) :
    (1 : Q) ⊗ₜ[R] u ∉ (pullback.fst f' otherMap (T p)).asIdeal := by
  obtain ⟨z, hz⟩ :=
    SchemePairBoundaryTransfer.transfer_fst_mem_range f f' otherMap left right _ p
  exact (PrincipalOpenTensor.mem_inclusion_range Q u _).mp ⟨(B).inv z, hz⟩

/-- The full unit-scale initial pair has a punctured representative preserving both inputs. -/
theorem initialArithmeticPair_unit_target (hs : IsUnit (π ^ start))
    (p : (pullback f otherMap : Scheme)) :
    ∃ z : (pullback f' otherMap : Scheme),
      next (pullback.fst f' otherMap z) = old (pullback.fst f otherMap p) ∧
      pullback.snd f' otherMap z = pullback.snd f otherMap p ∧
      (1 : Q) ⊗ₜ[R] u ∉ (pullback.fst f' otherMap z).asIdeal := by
  let v : (O).toScheme :=
    ⟨p, initialArithmeticPairOpen_mem_of_unit hπ data m r hr otherMap hs p⟩
  exact ⟨T v,
    congrArg (fun morphism => morphism v)
      (initialArithmeticPairTransfer_first hπ data m h1 r hr otherMap),
    congrArg (fun morphism => morphism v)
      (initialArithmeticPairTransfer_second hπ data m h1 r hr otherMap),
    initialArithmeticPairTransfer_punctured hπ data m h1 r hr otherMap v⟩

end FLT.Mazur.WeierstrassDividedDepth
