/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFamilyRigidifiedUniqueDescent
public import FLT.Mazur.RelativePicardFppfSheafCriterion

/-!
# Fppf sheafness of rigidified and pointed Picard classes

Unique effective descent proves the sheaf condition. The established natural
kernel equivalence transfers it to the commutative-group-valued pointed kernel.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemePicard
variable {X S : Scheme.{0}} (f : X ⟶ S) (e : S ⟶ X) (he : e ≫ f = 𝟙 S)
  [IsLocallyNoetherian S] [IsProper f] [Flat f]
  [GeometricallyConnected f] [GeometricallyReduced f]

/-- Actual rigidified classes form an fppf sheaf for the proper pointed family. -/
theorem rigidifiedPresheaf_isSheaf :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (rigidifiedPresheaf f e he) :=
  relativeFppf_isSheaf_of_families _ (rigidifiedFamily_isSheafFor f e he)

/-- The original pointed kernel presheaf is an fppf sheaf of commutative groups. -/
theorem pointedKernelPresheaf_isSheaf :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (pointedKernelPresheaf f e he) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget CommGrpCat.{1})]
  exact (Presheaf.isSheaf_of_iso_iff (J := Scheme.fppfTopology.over S)
    (rigidifiedPresheafKernelIso f e he)).mp (rigidifiedPresheaf_isSheaf f e he)

/-- The sheaf retains the actual rigidified presheaf and its original restriction maps. -/
def rigidifiedFppfSheaf : Sheaf (Scheme.fppfTopology.over S) (Type 1) :=
  ⟨rigidifiedPresheaf f e he, rigidifiedPresheaf_isSheaf f e he⟩

/-- The sheaf retains the actual kernel presheaf and its original group restriction maps. -/
def pointedKernelFppfSheaf : Sheaf (Scheme.fppfTopology.over S) CommGrpCat.{1} :=
  ⟨pointedKernelPresheaf f e he, pointedKernelPresheaf_isSheaf f e he⟩

end FLT.Mazur.SchemePicard
