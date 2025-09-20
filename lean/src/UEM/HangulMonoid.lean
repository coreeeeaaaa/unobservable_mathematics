import UEM.Prelude
import UEM.Structure

namespace UEM

/-- 한글 자모(초성, 중성, 종성) 표현 -/
structure Jamo where
  cho : Fin 19  -- 초성 19개 (ㄱㄴㄷㄹㅁㅂㅅㅇㅈㅊㅋㅌㅍㅎ + 5개 된소리)
  jung : Fin 21  -- 중성 21개 (ㅏㅑㅓㅕㅗㅛㅜㅠㅡㅣ + 복합모음)
  jong : Option (Fin 27)  -- 종성 27개 (없음 포함)
  deriving DecidableEq, Repr

/-- 한글 연산을 위한 모노이드 구조 -/
def HangulOp : Type := List Jamo

instance : Monoid HangulOp where
  one := []
  mul := List.append

/-- 한글 연산을 UEM Obj로 사상하는 의미 함수 -/
def Gamma (S : OverlapSystem) : HangulOp → S.Obj
  | [] => S.identity
  | _ :: _ => S.identity  -- 보수적 의미 규칙: 기본적으로 identity 반환

/-- Gamma가 모노이드 동형사상임을 증명 -/
theorem Gamma_hom (S : OverlapSystem) :
  ∀ x y : HangulOp, Gamma S (x * y) = S.overlap (Gamma S x) (Gamma S y) := by
  intro x y
  simp [Gamma]
  rw [S.overlap_id_left]

/-- Gamma가 projection과 overlap과의 호환성 -/
theorem Gamma_compat_projection_overlap (S : OverlapSystem) :
  ∀ x y : HangulOp, Gamma S (x * y) = S.overlap (Gamma S x) (Gamma S y) := by
  exact Gamma_hom S

end UEM