# UEM/YJG 다중 에이전트 운영 규칙 (5인 체제)

## 구성원
- ClaudeCode-1 : P1 Projection
- ClaudeCode-2 : P2 Flow
- ClaudeCode-3 : P4 Measure
- ClaudeCode-4 : Meta-coordination (M1, M3)
- OpenCode (Grok) : P6 Counterfactual
[기타 P3, P5는 보류/재할당 예정]

## 공통 원칙
- main 은 보호, squash-merge only
- branch naming: feature/Pn-<task>, meta/Mn-<task>
- commit 메시지 고정: "chore: repository update"
- 절대 금지: 요약, 허위수치, AI/모델명 언급, 마케팅 문구
- 파일 잠금: 각자 담당 디렉터리만 편집
- CI 게이트: lake build 성공 + grep -R "sorry" == 0 + proof_coverage.txt == SORRY_FREE

## 보고 포맷
[repo] coreeeeaaaa/unobservable_mathematics
[path] <파일경로들>
[action] create|edit|verify|build|test|commit|push|pr
[result] SUCCESS|FAIL (+1줄 오류)
[details] 핵심 수치/상태
[ci] run_id=…, status=success|failure|queued

## 전환 규칙
- Qwen/Gemini 과제는 중단, 관련 브랜치 폐기
- 5인 체제로 재편 후 모든 향후 과제는 이 규칙을 따라야 함