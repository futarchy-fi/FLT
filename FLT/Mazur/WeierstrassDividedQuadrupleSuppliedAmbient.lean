/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedQuadrupleAmbientCoverage

/-!
# The actual quadruple ambient law in a supplied doubled-depth family

Uniqueness of divided coefficients identifies the entire supplied family with
its constructed counterpart. Transport along this proved equality retains the
whole ambient law, its source coverage, and both coefficient structure maps.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  [IsLocalRing R] [IsNoetherianRing R] {W : WeierstrassCurve R} {π : R} {k : ℕ}
  (D : SplitNodeDepth W π (4 * k))
  (data : (i : Fin (k + k + 1)) → Data W π (0 + i.val)) (d : Data W π k)

omit [IsBezout R] [IsNoetherianRing R] in
/-- Every supplied doubled-depth family is the actual constructed coefficient family. -/
theorem quadrupleSuppliedFamily_eq : data = splitNodeDoubledFamily D := by
  funext i
  exact (splitNodeDoubledFamily_agrees D i (data i)).symm

local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ data (k + k) le_rfl
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "a" => dividedPairLeft W (π ^ k) d.b3 d.b4 d.b6
local notation "c" => dividedPairRight W (π ^ k) d.b3 d.b4 d.b6
local notation "V" => quadrupleSmoothSourceOpen D d a c
local notation "Old" => finiteResolvedReciprocalExtendedOpen hπ data (k + k) le_rfl

/-- The actual universal smooth pair in the supplied doubled-depth resolved product. -/
def quadrupleSuppliedCommonInput :
    (V).toScheme ⟶ finiteResolvedProduct hπ data (k + k) le_rfl := by
  have h := quadrupleSuppliedFamily_eq D data
  subst data
  exact quadrupleCommonInput D d a c

instance quadrupleSuppliedCommonInput_open :
    IsOpenImmersion (quadrupleSuppliedCommonInput D data d) := by
  have h := quadrupleSuppliedFamily_eq D data
  subst data
  exact quadrupleCommonInput_universal_open D d

/-- Transport the whole constructed ambient domain using coefficient uniqueness. -/
def quadrupleSuppliedAmbientOpen :
    (finiteResolvedProduct hπ data (k + k) le_rfl).Opens := by
  have h := quadrupleSuppliedFamily_eq D data
  subst data
  exact quadrupleAmbientOpen D d

local notation "O" => quadrupleSuppliedAmbientOpen D data d

/-- The whole actual quadruple ambient law in the supplied coefficient family. -/
def quadrupleSuppliedAmbientAddition : (O).toScheme ⟶ (U).toScheme := by
  have h := quadrupleSuppliedFamily_eq D data
  subst data
  exact quadrupleAmbientAddition D d

/-- Transport preserves exactly the old domain union the actual quadruple image. -/
theorem quadrupleSuppliedAmbientOpen_eq :
    O = Old ⊔ (quadrupleSuppliedCommonInput D data d).opensRange := by
  have h := quadrupleSuppliedFamily_eq D data
  subst data
  exact quadrupleAmbientOpen_eq D d

/-- The transported law keeps the first input's coefficient structure. -/
@[reassoc] theorem quadrupleSuppliedAmbientAddition_structure :
    quadrupleSuppliedAmbientAddition D data d ≫ t = (O).ι ≫ pullback.fst t t ≫ t := by
  have h := quadrupleSuppliedFamily_eq D data
  subst data
  exact quadrupleAmbientAddition_structure D d

/-- The transported law keeps the second input's coefficient structure. -/
@[reassoc] theorem quadrupleSuppliedAmbientAddition_structure_snd :
    quadrupleSuppliedAmbientAddition D data d ≫ t = (O).ι ≫ pullback.snd t t ≫ t := by
  have h := quadrupleSuppliedFamily_eq D data
  subst data
  exact quadrupleAmbientAddition_structure_snd D d

local notation "P" => suppliedDividedSmoothInputOpen d a c
local notation "S" => DividedPairRing W (π ^ k) d.b3 d.b4 d.b6
local notation "dx" => a (x W (π ^ k) d.b3 d.b4 d.b6) - c (x W (π ^ k) d.b3 d.b4 d.b6)
local notation "E" => dividedTangentDenominator W (π ^ k) d.b3 d.b4 d.b6 a c

/-- Every relatively smooth quadruple nodal formula input remains covered after transport. -/
theorem quadrupleSuppliedAmbientOpen_covers (hpos : 0 < k) (p : PrimeSpectrum S)
    (hp : algebraMap R S π ∈ p.asIdeal) (hs : p ∈ P)
    (hformula : dx ∉ p.asIdeal ∨ E ∉ p.asIdeal) :
    finiteSuppliedSmoothPair hπ data k (by omega) d (Nat.zero_add k)
      (k + k) (by omega) le_rfl a c ⟨p, hs⟩ ∈ O := by
  have h := quadrupleSuppliedFamily_eq D data
  subst data
  exact quadrupleAmbientOpen_covers D d hpos p hp hs hformula

end FLT.Mazur.WeierstrassDividedDepth
