import UEM.Structure
import UEM.Measure
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
Flow structure for unobservable epistemic mathematics.
Minimal skeleton preserving type dependencies.
-/

namespace UEM

open MeasureTheory

universe u v w

variable (S : OverlapSystem) [MeasurableSpace S.Space]

structure Flow where
  map : S.Space → S.Space
  measurable_map : Measurable map
  injective_map : Function.Injective map

namespace Flow

variable {S} [MeasurableSpace S.Space]

def measure_preserving (M : MeasureContext S) (f : Flow S) : Prop :=
  ∀ A : Set S.Space, MeasurableSet A → M.volume (f.map '' A) = M.volume A

theorem trivial_flow_measure_preserving (M : MeasureContext S) :
    measure_preserving M ⟨id, measurable_id, Function.injective_id⟩ := by
  intro A _
  simp [measure_preserving, Set.image_id]

end Flow

end UEM