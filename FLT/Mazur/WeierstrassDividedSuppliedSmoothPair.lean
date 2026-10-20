/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSuppliedSmoothChart
public import FLT.Mazur.WeierstrassDividedResolvedProductOpens

/-!
# Actual supplied inputs in the common resolved product

Restrict the original affine source to the full relative smooth locus of both
supplied inputs. The constructed maps promote both inputs to the same chosen
finite model without requiring either vertical derivative to be invertible.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n k : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (i : ℕ) (hi : i ≤ n)
  (d : Data W π k) (hk : start + i = k) (j : ℕ) (hij : i ≤ j) (hj : j ≤ n)
local notation "A" => WeierstrassDilatation.Coordinate W (π ^ k) d.b3 d.b4 d.b6
variable (a c : WeierstrassDilatation.Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "s" => Spec.map (CommRingCat.ofHom (algebraMap R A))
local notation "V" => (s).smoothLocus
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "a'" => Spec.map (CommRingCat.ofHom a.toRingHom)
local notation "c'" => Spec.map (CommRingCat.ofHom c.toRingHom)
local notation "emb" => finiteSuppliedDividedSmoothChart hπ data i hi d hk j hij hj

/-- The original source open where both actual divided inputs are relatively smooth. -/
def suppliedDividedSmoothInputOpen : (Spec (.of S)).Opens :=
  (a' ⁻¹ᵁ V) ⊓ (c' ⁻¹ᵁ V)

local notation "O" => suppliedDividedSmoothInputOpen d a c

/-- Both smooth inputs are promoted from the same unchanged affine source open. -/
def finiteSuppliedSmoothInput (b : Bool) : (O).toScheme ⟶ (U).toScheme :=
  if b then
    Scheme.homOfLE (Spec (.of S)) (show O ≤ a' ⁻¹ᵁ V from inf_le_left) ≫ (a' ∣_ V) ≫ emb
  else Scheme.homOfLE (Spec (.of S)) (show O ≤ c' ⁻¹ᵁ V from inf_le_right) ≫ (c' ∣_ V) ≫ emb

/-- Each promoted input retains its exact original cubic contraction. -/
@[reassoc] theorem finiteSuppliedSmoothInput_contraction (b : Bool) :
    finiteSuppliedSmoothInput hπ data i hi d hk j hij hj a c b ≫ (U).ι ≫
        finiteGlobalContraction hπ data j hj =
      (O).ι ≫ (if b then a' else c') ≫ toCurve d := by
  cases b <;>
    simp only [finiteSuppliedSmoothInput, Bool.false_eq_true, ↓reduceIte, Category.assoc,
      finiteSuppliedDividedSmoothChart_contraction, morphismRestrict_ι_assoc,
      Scheme.homOfLE_ι_assoc]

/-- Both inputs keep precisely the original coefficient point of the common source. -/
@[reassoc] theorem finiteSuppliedSmoothInput_structure (b : Bool) :
    finiteSuppliedSmoothInput hπ data i hi d hk j hij hj a c b ≫ t =
      (O).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  cases b <;>
    simp only [finiteSuppliedSmoothInput, Bool.false_eq_true, ↓reduceIte, Category.assoc,
      finiteSuppliedDividedSmoothChart_structure, morphismRestrict_ι_assoc,
      Scheme.homOfLE_ι_assoc, WeierstrassIntegralChart.specAlgHom_structure]

/-- The two actual smooth inputs define a map to the same full resolved product as the old law. -/
def finiteSuppliedSmoothPair : (O).toScheme ⟶ finiteResolvedProduct hπ data j hj :=
  pullback.lift (finiteSuppliedSmoothInput hπ data i hi d hk j hij hj a c true)
    (finiteSuppliedSmoothInput hπ data i hi d hk j hij hj a c false) (by
      rw [finiteSuppliedSmoothInput_structure, finiteSuppliedSmoothInput_structure])

/-- The first resolved product projection is exactly the promoted first input. -/
@[reassoc] theorem finiteSuppliedSmoothPair_fst :
    finiteSuppliedSmoothPair hπ data i hi d hk j hij hj a c ≫ pullback.fst t t =
      finiteSuppliedSmoothInput hπ data i hi d hk j hij hj a c true :=
  pullback.lift_fst _ _ _

/-- The second resolved product projection is exactly the promoted second input. -/
@[reassoc] theorem finiteSuppliedSmoothPair_snd :
    finiteSuppliedSmoothPair hπ data i hi d hk j hij hj a c ≫ pullback.snd t t =
      finiteSuppliedSmoothInput hπ data i hi d hk j hij hj a c false :=
  pullback.lift_snd _ _ _

end FLT.Mazur.WeierstrassDividedDepth
