import Mathlib/MeasureTheory/Measure/MeasureSpace
import Mathlib/MeasureTheory/MeasurableSpace
import Mathlib/MeasureTheory/Measure/Map
import Mathlib/Topology/Instances.Real
import Mathlib/MeasureTheory/Constructions.Prod

/-!
# Flow on a measurable space and measure-preserving property

Assumptions:
- (X, 𝒳) is a measurable space.
- μ is a measure on X.

Definitions:
- Flow X: a family of measurable equivalences Φ : ℝ → X ≃ᵐ X
  with semigroup law Φ (t + s) = Φ t ∘ Φ s and identity Φ 0 = refl.

Main results:
- `measure_preserving_zero`: Φ 0 is measure-preserving.
- `measure_preserving_add`: if each Φ t is measure-preserving, then Φ (t + s) is also
  measure-preserving (by composition).
-/

open MeasureTheory

universe u

variable {X : Type u} [MeasurableSpace X]

/-- A measurable flow with built-in measure-preserving guarantee. -/
structure Flow (X : Type u) [MeasurableSpace X] (μ : Measure X) where
  Φ   : ℝ → MeasurableEquiv X X
  id0 : Φ 0 = MeasurableEquiv.refl X
  semigroup : ∀ t s, Φ (t + s) = (Φ t).trans (Φ s)
  mp : ∀ t, MeasurePreserving (Φ t).toEquiv μ μ

namespace Flow

variable {μ : Measure X} (F : Flow X μ)

@[simp] lemma id_at_zero : F.Φ 0 = MeasurableEquiv.refl X := F.id0

/-- Each time slice is measure-preserving by definition. -/
theorem measure_preserving (t : ℝ) : MeasurePreserving (F.Φ t).toEquiv μ μ := F.mp t

/-- Φ 0 is measure-preserving. -/
theorem measure_preserving_zero : MeasurePreserving (F.Φ 0).toEquiv μ μ := F.mp 0

/-- Φ (t+s) is measure-preserving, using semigroup property and closure under composition. -/
theorem measure_preserving_add (t s : ℝ) :
  MeasurePreserving (F.Φ (t+s)).toEquiv μ μ := by
  -- rewrite by semigroup law
  have hts : F.Φ (t+s) = (F.Φ t).trans (F.Φ s) := F.semigroup t s
  -- use composition closure for MeasurePreserving with MeasurableEquiv
  -- (map via equiv is composition of underlying measurable functions)
  -- mathlib lemma: MeasurePreserving.comp
  -- convert to functions:
  -- (F.Φ t).toEquiv and (F.Φ s).toEquiv are measure-preserving
  have ht : MeasurePreserving (F.Φ t).toEquiv μ μ := F.mp t
  have hs : MeasurePreserving (F.Φ s).toEquiv μ μ := F.mp s
  -- composition:
  -- (F.Φ t).toEquiv ∘ (F.Φ s).toEquiv corresponds to (F.Φ t).trans (F.Φ s)
  -- use lemma that measure-preserving is closed under composition
  -- available as: MeasurePreserving.comp
  -- need measurability true (given by MeasurableEquiv)
  have hcomp : MeasurePreserving ((F.Φ t).toEquiv ∘ (F.Φ s).toEquiv) μ μ :=
    ht.comp hs
  -- coe of trans equals function composition
  -- by rfl-like reasoning on MeasurableEquiv.trans
  -- finalize by rewriting
  rw [hts]
  rwa [MeasurableEquiv.trans_toEquiv]

end Flow