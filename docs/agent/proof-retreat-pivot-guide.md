# 証明 撤退・Pivot 判断ガイド

- 作成日: 2026-04-23
- 対象: Lean 証明作業中に戦略変更・撤退判断が必要になったエージェント
- 関連: `AGENTS.md` §証明作業、[agent-operations-playbook.md](agent-operations-playbook.md)

## このガイドの目的

「方針を諦める／切り替える」判断を、再現可能な手順に整形する。何を試し、何が詰まり、次に何を実装すべきかを sorry-card と sorry-plan.json に標準形式で残すことで、**次セッション着手者が冒頭 30 行 read するだけで進行可能な状態** を保つ。

## ⚠️ Pivot を検討する前に（必須 3 ステップ）

「推論で難しそう」だけで撤退してはならない。AGENTS.md `userMemory` の通り、以下を順に実施してから pivot 判断に入る:

1. **`lean-proof-planning` SKILL.md を読む**（未読なら必ず）
2. **REPL で sorry-skeleton を試す** — `example ... := by sorry` でゴール形状を確認
3. **`lean-goal-advisor` エージェントを呼ぶ** — ゴールと sorry 行を渡して候補タクティクを試す

この 3 ステップを経ずに pivot したら、セッションメモに記録して次セッションで補完する。

## 撤退判断チェックリスト

以下のいずれかに該当した場合、pivot 可能:

| 種別 | 判定条件 |
|---|---|
| **反例** | `lean-counterexample` / `by plausible` / 具体値 `#eval` で反例が見つかった |
| **循環依存** | 代替補題の仮定の充足に元のゴールが必要（1〜2 ステップで確認可能） |
| **scaffold 構造** | 現在の induction motive / generalize / type class 設定では前提が再確立できないと静的分析で確定 |
| **REPL 失敗** | 3 以上のタクティク候補が REPL で全滅（`lean-goal-advisor` 使用後） |
| **累積失敗** | 3 セッション or 8 アプローチ失敗（AGENTS.md 準拠） |

## Pivot 記録テンプレート（sorry-card マイルストーン表）

sorry-card の「マイルストーン」テーブルに以下 5 項目を 1 行で追記する:

| 項目 | 内容 |
|---|---|
| **報番** | `#第NN報` 形式 |
| **障害種別** | 反例 / 循環依存 / scaffold 構造 / REPL 失敗 / 累積失敗 のいずれか |
| **発見方法** | 静的分析 / REPL 失敗 / plausible 反例 / Lean source grep など |
| **障害の性質** | 1〜3 行で要約 |
| **pivot 提案** | 代替戦略の名前と候補補題名 |

### 記述例（#51 実績）

```markdown
| 2026-04-23 (#51) | **案 3 単純長さ帰納の構造的障害を crystallize**。
step lemma の `h_obs : s_obs.layers = (s.clearPositions settlingPos).layers`
前提は再帰先 (foldl 後の obs') では満たせない。d=1 pin 着地空性も
clearPositions 構造に本質依存。→ **案 3' aux-lemma 設計を確定**:
(1) obs 抽象化 + 不変量 I1/I2 carry 版の `_aux`、(2) step lemma の
obs 抽象版 `_step_generic`、(3) 新規補題「foldl 後第一グループ pin
着地 empty 再確立」で I2' 再確立、(4) main theorem は aux に clearPositions
初期値を供給して呼出。Lean 変更なし、lake build OK、sorry 総数 1 のまま。 |
```

## sorry-plan.json への step 追加ルール

pivot で発生した新規実装項目は `remaining_steps` に追加する。`status` の使い分け:

| status | 用途 |
|---|---|
| `done` | 完了 |
| `pending-recommended` | 推奨経路の次ステップ |
| `pending-required` | 推奨経路を進める上で必須の補助補題・補助設計 |
| `pending-if-needed` | fallback 案として確保するが現時点では不要 |
| `blocked-by-scaffold` | 上位 scaffold の構造的障害により現状では閉じない |

### 記述例

```json
{
  "id": "B3b-new-helper-pin-landing-preservation",
  "title": "[案 3' 新規補題] foldl 後の残りリスト第一グループ pin 着地 empty 再確立",
  "status": "pending-required",
  "description": "aux の I2' 再確立に必要。placeLDGroupsLandings の定義上、残りリストの先頭グループ pin の着地は obs' 上で「landed」。d ≥ 2 は landingDistance_not_occupied_at_landing で閉じる。d = 1 は第一グループ cluster 位置との disjoint 性が必要。"
}
```

## チェックリスト（pivot 時に実施）

1. [ ] 必須 3 ステップ（SKILL / REPL / advisor）を実施した、または実施ログをセッションメモに記録
2. [ ] 撤退判断チェックリストの 1 項目以上に該当することを確認
3. [ ] sorry-card のマイルストーン表に 5 項目形式で記録
4. [ ] sorry-plan.json の `remaining_steps` に新規 step を登録（status を明示）
5. [ ] sorry-card の「次アクション」セクションを新経路に合わせて更新
6. [ ] sorry-card の事前埋込が自動更新対象であることを確認（build フックで更新される）
7. [ ] git commit のコミットメッセージに障害種別と pivot 提案を明記
