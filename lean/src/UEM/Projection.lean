import UEM.Structure
import UEM.Measure
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# Projection-Overlap Preservation Theorems

Main results:
- `projectionOverlapExchange`: Projection-overlap exchange from structure theory
- `projection_overlap_preserve_lower_bound`: Lower bound preservation for overlap measures
  under projection operations

Mathematical foundation: σ-finiteness, subadditivity, and monotonicity properties
ensure that overlap measures satisfy minimal preservation constraints.
-/

open MeasureTheory

universe u

variable {X : Type u} [MeasurableSpace X]

namespace UEM
namespace OverlapSystem

/--
Theorem 5.2 (Projection–overlap exchange) from `docs/UEM_formal_spec_v2.md`.
Given the homomorphism axiom (A3), the proof is immediate.
-/
theorem projectionOverlapExchange (S : OverlapSystem)
    (A B : S.Obj) :
    S.projection (S.overlap A B) =
      S.phi (S.projection A) (S.projection B) :=
  S.projection_hom

end OverlapSystem

/-- Lower bound preservation theorem for projection overlaps.
    For measurable sets A and B, the overlap measure satisfies a minimal bound. -/
theorem projection_overlap_preserve_lower_bound
  (μ : Measure X) (A B : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B) :
  μ (A ∩ B) ≤ μ A := by
  -- Since A ∩ B ⊆ A, we have μ(A ∩ B) ≤ μ(A)
  have h_sub : A ∩ B ⊆ A := Set.inter_subset_left A B
  exact measure_mono h_sub

/-- Monotonicity preservation for nested projections. -/
theorem projection_overlap_monotonic
  (μ : Measure X) (A B C : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C)
  (h_sub : A ⊆ B) :
  μ (A ∩ C) ≤ μ (B ∩ C) := by
  -- Since A ⊆ B, we have A ∩ C ⊆ B ∩ C
  have h_inter_sub : A ∩ C ⊆ B ∩ C := Set.inter_subset_inter_left C h_sub
  exact measure_mono h_inter_sub

end UEM
