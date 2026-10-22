/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PointLocalizedRingColimit
public import FLT.Mazur.PointLocalizedRingMap
public import FLT.Mazur.FilteredIdealTensorKernel

/-!
# Eventual obstruction vanishing in the constructed local diagrams

For a point of the limiting target, the local rings, their maps and colimit
identifications are constructed from the original affine systems. Flatness at
that point kills the entire fixed maximal-ideal obstruction at a later stage.
The conclusion is vanishing after localization, not in the affine stage ring.
-/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace FLT.Mazur.PointLocalizedObstructionVanishing
open PointLocalizedRingDiagram PointLocalizedRingMap
universe u
variable {I : Type u} [SmallCategory I] [IsFiltered I]
  {F G : I ⥤ CommRingCat.{u}} (c : Cocone F) (d : Cocone G)
  (hc : IsColimit c) (hd : IsColimit d) (η : F ⟶ G) (φ : c.pt →+* d.pt)
  (hφ : ∀ i, (d.ι.app i).hom.comp (η.app i).hom = φ.comp (c.ι.app i).hom)
  (Q : Ideal d.pt) [Q.IsPrime]

omit [IsFiltered I] in
/-- The square used by the tensor transition is the actual localized affine square. -/
theorem stage_square {i j : I} (f : i ⟶ j) :
    (transition d Q f).comp (stageMap c d η φ hφ Q i) =
      (stageMap c d η φ hφ Q j).comp (transition c (Q.comap φ) f) :=
  congrArg CommRingCat.Hom.hom ((localizedMap c d η φ hφ Q).naturality f).symm

include hc hd in
/-- Pointwise flatness forces uniform later vanishing of the original local obstruction. -/
theorem exists_maximal_obstruction_vanishing
    (hflat : (pointMap c d φ Q).Flat) (i : I)
    [IsNoetherianRing (F.obj i)] [IsNoetherianRing (G.obj i)] :
    ∃ (j : I) (g : i ⟶ j), ∀ (k : I) (e : j ⟶ k),
      let _ := (stageMap c d η φ hφ Q i).toAlgebra
      let _ := (stageMap c d η φ hφ Q k).toAlgebra
      ∀ z : IdealTensorKernel.obstruction (S := Stage d Q i)
        (IsLocalRing.maximalIdeal (Stage c (Q.comap φ) i)),
      IdealTensorKernel.transition (transition c (Q.comap φ) (g ≫ e))
        (transition d Q (g ≫ e)) (stage_square c d η φ hφ Q (g ≫ e))
        (IsLocalRing.maximalIdeal (Stage c (Q.comap φ) i)) z.val = 0 := by
  let _ : IsNoetherianRing ((diagram c (Q.comap φ)).obj i) :=
    stage_noetherian c (Q.comap φ) i
  let _ : IsNoetherianRing ((diagram d Q).obj i) := stage_noetherian d Q i
  exact Approximation.exists_obstruction_vanishing_stage
    (diagram c (Q.comap φ)) (diagram d Q) (cocone c (Q.comap φ)) (cocone d Q)
    (localizedIsColimit c (Q.comap φ) hc) (localizedIsColimit d Q hd)
    (localizedMap c d η φ hφ Q) (pointMap c d φ Q)
    (pointMap_square c d η φ hφ Q) hflat i
    (IsLocalRing.maximalIdeal (Stage c (Q.comap φ) i)) (IsNoetherian.noetherian _)

include hc hd in
/-- A flat limiting affine map supplies the pointwise flatness used above. -/
theorem exists_maximal_obstruction_vanishing_of_flat
    (hflat : φ.Flat) (i : I)
    [IsNoetherianRing (F.obj i)] [IsNoetherianRing (G.obj i)] :
    ∃ (j : I) (g : i ⟶ j), ∀ (k : I) (e : j ⟶ k),
      let _ := (stageMap c d η φ hφ Q i).toAlgebra
      let _ := (stageMap c d η φ hφ Q k).toAlgebra
      ∀ z : IdealTensorKernel.obstruction (S := Stage d Q i)
        (IsLocalRing.maximalIdeal (Stage c (Q.comap φ) i)),
      IdealTensorKernel.transition (transition c (Q.comap φ) (g ≫ e))
        (transition d Q (g ≫ e)) (stage_square c d η φ hφ Q (g ≫ e))
        (IsLocalRing.maximalIdeal (Stage c (Q.comap φ) i)) z.val = 0 :=
  exists_maximal_obstruction_vanishing c d hc hd η φ hφ Q
    (pointMap_flat c d φ Q hflat) i

end FLT.Mazur.PointLocalizedObstructionVanishing
