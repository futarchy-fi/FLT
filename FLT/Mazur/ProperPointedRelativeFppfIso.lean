/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFamilyPointedComparisonIsomorphisms

/-!
# Relative classes and the actual Picard sheaf for proper pointed families

The original sheafification comparison is an isomorphism on every test,
including non-Noetherian tests. The section is used only in the proof.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.SchemePicard
variable {X S : Scheme.{0}} (f : X ⟶ S) (e : S ⟶ X) (he : e ≫ f = 𝟙 S)
  [IsLocallyNoetherian S] [IsProper f] [Flat f]
  [GeometricallyConnected f] [GeometricallyReduced f]

include e he in
/-- A proper pointed family's original relative comparison is invertible on all tests. -/
theorem properPointed_relativeFppfComparison_isIso : IsIso (relativeFppfComparison f) := by
  have h : relativeFppfComparison f =
      (relativePointedKernelIso f e he).hom ≫ pointedFppfComparison f e he := by
    simp only [pointedFppfComparison, Iso.hom_inv_id_assoc]
  rw [h]
  infer_instance

/-- The comparison isomorphism uses the actual sheafification map. -/
def properPointedRelativeFppfIso : relativePresheaf f ≅ (relativeFppfSheaf f).obj := by
  let _ := properPointed_relativeFppfComparison_isIso f e he
  exact asIso (relativeFppfComparison f)

include e he in
/-- Relative classes already satisfy fppf descent under these proper pointed hypotheses. -/
theorem properPointed_relativePresheaf_isSheaf :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (relativePresheaf f) :=
  (Presheaf.isSheaf_of_iso_iff (properPointedRelativeFppfIso f e he)).mpr
    (relativeFppfSheaf f).property

/-- Every actual Picard-sheaf section has a unique global relative class on each test. -/
def properPointedRelativeFppfEquiv (T : Over S) :
    RelativePic (Limits.pullback.snd f T.hom) ≃
      (relativeFppfSheaf f).obj.obj (op T) :=
  ((properPointedRelativeFppfIso f e he).app (op T)).commGroupIsoToMulEquiv.toEquiv

/-- The equivalence sends a class to its original sheaf section. -/
lemma properPointedRelativeFppfEquiv_apply (T : Over S)
    (c : RelativePic (Limits.pullback.snd f T.hom)) :
    properPointedRelativeFppfEquiv f e he T c = relativeFppfClass f T c := rfl

/-- Recovering the global relative representative commutes with arbitrary test maps. -/
lemma properPointedRelativeFppfEquiv_symm_natural {T U : Over S} (g : T ⟶ U)
    (s : (relativeFppfSheaf f).obj.obj (op U)) :
    (properPointedRelativeFppfEquiv f e he T).symm ((relativeFppfSheaf f).obj.map g.op s) =
      relativeBaseMap f g ((properPointedRelativeFppfEquiv f e he U).symm s) :=
  (properPointedRelativeFppfIso f e he).inv.naturality_apply g.op s

end FLT.Mazur.SchemePicard
