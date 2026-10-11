/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedHilbertEtaleGeometricCoverage

/-!
# Étale translation coverage for arbitrary geometric base maps

The kernel of any map from the original coefficient ring to a geometric
field supplies its actual residue field. No chosen residue factorization
is needed to construct an étale translation chart of the original class.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve OrderedCurvePower
set_option backward.isDefEq.respectTransparency false
variable {R K : Type} [CommRing R] [Field K] [IsAlgClosed K]
  [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)

/-- Every geometric original class lifts to a constructed étale translation chart. -/
theorem exists_orderedHilbert_etale_geometric_lift
    (g : Spec (.of K) ⟶ Spec (.of R))
    (s : (relativeFppfSheaf f).obj.obj (op (Over.mk g))) :
    ∃ (i : SmoothHilbertTranslationIndex) (E : Over (Spec (.of R)))
      (b : E ⟶ smoothTranslationTest f i.1)
      (q : Over.mk g ⟶ variableHilbertTest f i.2 E),
      let c := (relativeFppfSheaf f).obj.map b.op (smoothTranslationClass f hL.2.1 i.1)
      Etale E.hom ∧ variableHilbertPoint f i.2 hL E c _ q = s ∧
        Etale (variableChartRelationFst f hL i.2 E c).left ∧
        Etale (variableChartRelationSnd f hL i.2 E c).left := by
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective g
  let p := RingHom.ker ψ.hom
  let _ : p.IsPrime := RingHom.ker_isPrime ψ.hom
  have hu : p.primeCompl ≤ (IsUnit.submonoid K).comap ψ.hom := by
    intro r hr
    change IsUnit (ψ.hom r)
    exact isUnit_iff_ne_zero.mpr hr
  let θ := Ideal.ResidueField.lift p ψ.hom le_rfl hu
  let _ := θ.toAlgebra
  have he : (algebraMap p.ResidueField K).comp (algebraMap R p.ResidueField) = ψ.hom := by
    ext r
    exact Ideal.ResidueField.lift_algebraMap p ψ.hom le_rfl hu r
  have h := exists_orderedHilbert_etale_geometric_chart (K := K) f hL
    (algebraMap R p.ResidueField) p.surjectiveOnStalks_residueField
  rw [he] at h
  exact h s

end FLT.Mazur.HilbertChart
