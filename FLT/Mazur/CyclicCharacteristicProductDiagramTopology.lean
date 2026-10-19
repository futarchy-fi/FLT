/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicProductComparisonGluing
public import FLT.Mazur.CyclicCharacteristicProductSubgroupGluing

/-!
# Topology of the concrete comparison diagrams

Expose the open transition maps and local directedness already supplied by
relative gluing, so maps between the two colimits use the same diagrams.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
variable (n : ℕ) [NeZero n] (b c : Bool)
local notation "X" => normalizedProduct n b c

instance productComparisonDiagram_map_open {U V : (X).affineOpens} (h : U ⟶ V) :
    IsOpenImmersion ((productComparisonDiagram n b c).map h) :=
  by
    apply MorphismProperty.of_isPullback
      ((productComparisonProjection_equifibered n b c) h).flip
    change IsOpenImmersion ((X).homOfLE (leOfHom h))
    infer_instance

instance productComparisonDiagram_locallyDirected :
    (productComparisonDiagram n b c ⋙ Scheme.forget).IsLocallyDirected :=
  inferInstanceAs ((productComparisonGluing n b c).functor ⋙ Scheme.forget).IsLocallyDirected

instance productSubgroupDiagram_map_open {U V : (X).affineOpens} (h : U ⟶ V) :
    IsOpenImmersion ((productSubgroupDiagram n b c).map h) :=
  by
    apply MorphismProperty.of_isPullback
      ((productSubgroupProjection_equifibered n b c) h).flip
    change IsOpenImmersion ((X).homOfLE (leOfHom h))
    infer_instance

instance productSubgroupDiagram_locallyDirected :
    (productSubgroupDiagram n b c ⋙ Scheme.forget).IsLocallyDirected :=
  inferInstanceAs ((productSubgroupGluing n b c).functor ⋙ Scheme.forget).IsLocallyDirected

end FLT.Mazur.CyclicCharacteristicAtlas
