/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedShearFiniteIteration
public import FLT.Mazur.WeierstrassDividedShearInitialExterior
public import FLT.Mazur.WeierstrassDividedFiniteContraction

/-!
# The shear of the original finite modification

Instantiate the finite comparison with the proved original incidence exterior.
This identifies the entire original finite modification, with no assumed
comparison square, and retains its original integral cubic contraction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (r : R)
local notation "dat" => fun a => shearData (data a) r
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "E" => initialExterior d
local notation "F" => initialExterior (shearData d r)
local notation "i" => shearInitialExteriorIso d r
local notation "hi" => shearInitialExteriorIso_attach d r

/-- The entire original finite modification is isomorphic to its actual shear. -/
def shearFiniteModificationIso (j : ℕ) (hj : j ≤ n) :
    finiteModification hπ dat j hj ≅ finiteModification hπ data j hj :=
  finiteWholeShearIso hπ data r E F i hi j hj

/-- The original finite exterior is identified with its actual shear at every depth. -/
def shearFiniteExteriorIso (j : ℕ) (hj : j ≤ n) :
    (finiteExterior hπ dat F j hj).carrier ≅ (finiteExterior hπ data E j hj).carrier :=
  finiteExteriorShearIso hπ data r E F i hi j hj

/-- The whole comparison retains the complete final divided chart. -/
@[reassoc] theorem shearFiniteModificationIso_divided (j : ℕ) (hj : j ≤ n) :
    (finiteExterior hπ dat F j hj).dividedChart ≫ (shearFiniteModificationIso hπ data r j hj).hom =
      (shearChartIso (data ⟨j, Nat.lt_succ_of_le hj⟩) r).hom ≫
        (finiteExterior hπ data E j hj).dividedChart :=
  finiteWholeShearIso_divided hπ data r E F i hi j hj

/-- The whole comparison retains the entire enlarged original exterior. -/
@[reassoc] theorem shearFiniteModificationIso_exterior (j : ℕ) (hj : j ≤ n) :
    (finiteExterior hπ dat F j hj).exteriorChart ≫
        (shearFiniteModificationIso hπ data r j hj).hom =
      (shearFiniteExteriorIso hπ data r j hj).hom ≫
        (finiteExterior hπ data E j hj).exteriorChart :=
  finiteWholeShearIso_exterior hπ data r E F i hi j hj

/-- The original finite-model contraction to the initial local modification is retained. -/
@[reassoc] theorem shearFiniteModificationIso_contraction (j : ℕ) (hj : j ≤ n) :
    (shearFiniteModificationIso hπ data r j hj).hom ≫ finiteContraction hπ data E j hj =
      finiteContraction hπ dat F j hj ≫ (shearInitialWholeIso d r).hom :=
  finiteWholeShearIso_contraction hπ data r E F i hi j hj

/-- The entire finite modification comparison retains the original integral cubic map. -/
@[reassoc] theorem shearFiniteModificationIso_toCurve (j : ℕ) (hj : j ≤ n) :
    (shearFiniteModificationIso hπ data r j hj).hom ≫ finiteToCurve hπ data j hj =
      finiteToCurve hπ dat j hj ≫
        (WeierstrassIntegralChart.integralVariableChangeIso W (rootShearCurve W r)
          (⟨1, 0, r, 0⟩) rfl).hom := by
  rw [finiteToCurve, shearFiniteModificationIso_contraction_assoc,
    shearInitialWholeIso_toCurve, finiteToCurve, Category.assoc]

/-- The initial original incidence chart is retained throughout the whole finite comparison. -/
@[reassoc] theorem shearFiniteExteriorIso_retained (j : ℕ) (hj : j ≤ n) :
    finiteRetained hπ dat F j hj ≫ (shearFiniteExteriorIso hπ data r j hj).hom =
      (shearInitialExteriorIso d r).hom ≫ finiteRetained hπ data E j hj :=
  finiteExteriorShearIso_retained hπ data r E F i hi j hj

end FLT.Mazur.WeierstrassDividedDepth
