/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompatibleSubgroupIso

/-!
# Sections around compatible subgroup squares

Equality of full compatible comparisons controls actual section paths. Keeping
this calculation abstract avoids unfolding the geometric pullback constructions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
variable {S : Scheme} {n : ℕ} {E F G D : GeneralizedEllipticCurve S}
  {H : E.FiniteSubgroup n} {J : F.FiniteSubgroup n}
  {A : G.FiniteSubgroup n} {B : D.FiniteSubgroup n}

/-- An actual subgroup section has the same image along equal compatible comparison paths. -/
theorem CompatibleIso.section_square (a : CompatibleIso H J) (b : CompatibleIso J A)
    (c : CompatibleIso A B) (d : CompatibleIso H B) (w : (a.trans b).trans c = d)
    (P : 𝟙_ (Over S) ⟶ H.carrier) :
    P ≫ a.subgroup.hom ≫ b.subgroup.hom ≫ c.subgroup.hom = P ≫ d.subgroup.hom := by
  have hs := congrArg (fun e : CompatibleIso H B ↦ e.subgroup.hom) w
  change (a.subgroup.hom ≫ b.subgroup.hom) ≫ c.subgroup.hom = d.subgroup.hom at hs
  simpa only [Category.assoc] using congrArg (fun f ↦ P ≫ f) hs

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
