/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OpenRestrictionInclusion

/-!
# Section colimits on fixed compact opens

The sections on the inverse images of a compact open form a filtered ring
colimit. Inclusions of opens give compatible maps between these colimits.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u})
  (c : Cone D) (i : I)

/-- Global sections of the restricted inverse diagram. -/
def openSectionSystem (U : (D.obj i).Opens) : (Over i)ᵒᵖ ⥤ CommRingCat.{u} :=
  (opensDiagram D i U).op ⋙ Scheme.Γ

/-- Sections of the restricted cone define a cocone of rings. -/
def openSectionCocone (U : (D.obj i).Opens) : Cocone (openSectionSystem D i U) :=
  Scheme.Γ.mapCocone (opensCone D c i U).op

/-- Inclusion of opens induces restriction on the section systems. -/
def openSectionRestriction {U V : (D.obj i).Opens} (h : U ≤ V) :
    openSectionSystem D i V ⟶ openSectionSystem D i U :=
  Functor.whiskerRight (NatTrans.op (opensDiagramInclusion D i h)) Scheme.Γ

/-- Restrictions commute with the section cocone maps. -/
theorem openSectionCocone_restriction {U V : (D.obj i).Opens} (h : U ≤ V)
    (j : (Over i)ᵒᵖ) :
    (openSectionRestriction D i h).app j ≫ (openSectionCocone D c i U).ι.app j =
      (openSectionCocone D c i V).ι.app j ≫
        (c.pt.homOfLE ((c.π.app i).preimage_mono h)).appTop := by
  exact congrArg Scheme.Hom.appTop (opensCone_inclusion D i c h j.unop)

/-- Compactness and quasi-separatedness suffice for the section colimit. -/
def openSectionIsColimit [IsCofiltered I] (hc : IsLimit c)
    [∀ {j k} (f : j ⟶ k), IsAffineHom (D.map f)]
    [∀ j, QuasiSeparatedSpace (D.obj j)] (U : (D.obj i).Opens)
    (hU : IsCompact (U : Set (D.obj i))) : IsColimit (openSectionCocone D c i U) := by
  let _ (j : Over i) : CompactSpace ((opensDiagram D i U).obj j) :=
    isCompact_iff_compactSpace.mp (QuasiCompact.isCompact_preimage _ U.isOpen hU)
  let _ (j : Over i) : QuasiSeparatedSpace ((opensDiagram D i U).obj j) :=
    (isQuasiSeparated_iff_quasiSeparatedSpace _ (D.map j.hom ⁻¹ᵁ U).isOpen).mp
      (.of_quasiSeparatedSpace _)
  exact (nonempty_isColimit_Γ_mapCocone (opensDiagram D i U) (opensCone D c i U)
    (isLimitOpensCone D c hc i U)).some

end FLT.Mazur.Approximation
