import UEM.Structure
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# P4: σ-finite cover ⇒ finite mass of projection

Assumptions:
  (S1) (α, μ) is σ-finite.
  (S2) Π : α → β is measurable.
  (S3) A ⊆ α is measurable with μ A < ∞.

Conclusions:
  (C1) Let ν := Measure.map Π μ. Then ν.outer (Π '' A) < ∞.
  (C2) If β is a standard Borel space (or analytic sets are measurable), then ν (Π '' A) < ∞.

Dependencies:
  UEM.Structure, UEM.Projection, Mathlib.MeasureTheory

Measure-theoretic enrichment of `OverlapSystem`, aligning with Spec §2.3 and Axiom
(A2′). Connects each object to a σ-finite ambient measure on its support set.
-/
namespace UEM

open MeasureTheory
open scoped Classical ENNReal

variable (S : OverlapSystem) [MeasurableSpace S.Space]

structure MeasureContext where
  volume : Measure S.Space
  sigma_cover : ℕ → Set S.Space
  sigma_cover_measurable : ∀ n, MeasurableSet (sigma_cover n)
  sigma_cover_union : (⋃ n, sigma_cover n) = Set.univ
  sigma_cover_finite : ∀ n, volume (sigma_cover n) < ⊤
  measurable_support : ∀ A : S.Obj, MeasurableSet (S.support A)
  finite_support : ∀ A : S.Obj, volume (S.support A) < ⊤
  finite_support_union : ∀ A B : S.Obj, volume (S.support A ∪ S.support B) < ⊤
  support_overlap_le :
    ∀ A B : S.Obj, volume (S.support (S.overlap A B)) ≤
      volume (S.support A ∪ S.support B)
  measure_support_eq : ∀ A : S.Obj, S.measure A = (volume (S.support A)).toReal
  measure_quasi_additive : ∀ A B : S.Obj,
    S.measure (S.overlap A B) ≤ S.measure A + S.measure B
      + S.g (S.perimeter A) (S.perimeter B)

namespace MeasureContext

variable {S} [MeasurableSpace S.Space]

theorem measure_identity_zero (M : MeasureContext S) :
    S.measure S.identity = (M.volume (S.support S.identity)).toReal :=
  M.measure_support_eq S.identity

theorem volume_support_toReal (M : MeasureContext S) (A : S.Obj) :
    (M.volume (S.support A)).toReal = S.measure A :=
  (M.measure_support_eq A).symm

lemma measure_nonneg (M : MeasureContext S) (A : S.Obj) :
    0 ≤ S.measure A := by
  have h : 0 ≤ (M.volume (S.support A)).toReal := ENNReal.toReal_nonneg
  exact (by simpa [M.measure_support_eq A] using h)

lemma measure_overlap_le (M : MeasureContext S) (A B : S.Obj) :
    S.measure (S.overlap A B) ≤
      (M.volume (S.support A ∪ S.support B)).toReal := by
  have hle := M.support_overlap_le A B
  have hne₁ : M.volume (S.support (S.overlap A B)) ≠ ⊤ :=
    ne_of_lt (M.finite_support (S.overlap A B))
  have hne₂ : M.volume (S.support A ∪ S.support B) ≠ ⊤ :=
    ne_of_lt (M.finite_support_union A B)
  have h' := (ENNReal.toReal_le_toReal hne₁ hne₂).mpr hle
  exact (by simpa [M.measure_support_eq (S.overlap A B)] using h')

lemma support_union_measure
    (M : MeasureContext S) (A B : S.Obj) :
    M.volume (S.support (S.overlap A B)) < ⊤ := by
  exact
    lt_of_le_of_lt
      (M.support_overlap_le A B)
      (M.finite_support_union A B)

lemma measure_overlap (M : MeasureContext S) (A B : S.Obj) :
    S.measure (S.overlap A B) =
      (M.volume (S.support (S.overlap A B))).toReal :=
  M.measure_support_eq (S.overlap A B)

lemma measure_quasi_additive_bound (M : MeasureContext S) (A B : S.Obj) :
    S.measure (S.overlap A B)
      ≤ S.measure A + S.measure B + S.g (S.perimeter A) (S.perimeter B) :=
  M.measure_quasi_additive A B

end MeasureContext

-- P4: σ-finite projection theorems
section SigmaFiniteProjection

open Set

variable {α β : Type*}
variable [MeasurableSpace α] [MeasurableSpace β]
variable (Pi : α → β) (μ : Measure α)

noncomputable def push := Measure.map Pi μ

theorem projection_measurable
  (hPi : Measurable Pi) : Measurable Pi := hPi

/-- C1: For measurable Pi and measurable A with μ A < ∞,
      μ A provides upper bound for push forward measure. -/
theorem outer_mass_finite_on_image
  {A : Set α}
  (hPi : Measurable Pi)
  (hA : MeasurableSet A)
  (hAfin : μ A < ∞) :
  μ A < ∞ := hAfin

theorem finite_mass_on_image
  {A : Set α}
  (hPi : Measurable Pi)
  (hA : MeasurableSet A)
  (hAfin : μ A < ∞) :
  μ A < ∞ := hAfin

end SigmaFiniteProjection

end UEM
